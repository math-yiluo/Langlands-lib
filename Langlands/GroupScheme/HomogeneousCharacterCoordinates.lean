import Langlands.GroupScheme.HomogeneousCharacterFinite
import Langlands.GroupScheme.Reductive.AffineInducedRegular

/-! # Coordinate form of covariant functions on homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

section Inversion

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Pullback of actual global functions along the group inversion. -/
def inversionAlgHom :
    ((algΓ (CommRingCat.of k)).obj G.X).unop →ₐ[k] ((algΓ (CommRingCat.of k)).obj G.X).unop :=
  ((algΓ (CommRingCat.of k)).map ι[G.X]).unop.hom

/-- Pulling back an inverted function along a point is pulling back along the inverse point. -/
theorem appTop_inversionAlgHom (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (f : ((algΓ (CommRingCat.of k)).obj G.X).unop) :
    g.left.appTop (inversionAlgHom G f) = (g⁻¹).left.appTop f := by
  rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

/-- Pullback along inversion is an involution of the global functions. -/
theorem inversionAlgHom_inversionAlgHom (f : ((algΓ (CommRingCat.of k)).obj G.X).unop) :
    inversionAlgHom G (inversionAlgHom G f) = f := by
  have h := appTop_inversionAlgHom G G.X ι[G.X] f
  rw [Hom.inv_def, GrpObj.inv_comp_inv] at h
  exact h

/-- Inversion on actual global functions, as an algebra involution. -/
def inversionAlgEquiv :
    ((algΓ (CommRingCat.of k)).obj G.X).unop ≃ₐ[k] ((algΓ (CommRingCat.of k)).obj G.X).unop :=
  AlgEquiv.ofAlgHom (inversionAlgHom G) (inversionAlgHom G)
    (AlgHom.ext (inversionAlgHom_inversionAlgHom G))
    (AlgHom.ext (inversionAlgHom_inversionAlgHom G))

end Inversion

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left]

/-- The point over a relative spectrum determined by an algebra map out of the coordinates. -/
def algPoint {B : CommAlgCat (CommRingCat.of k)} (φ : algebra G ⟶ B) :
    (algSpec (CommRingCat.of k)).obj (op B) ⟶ G.X :=
  (algSpec (CommRingCat.of k)).map φ.op ≫ (groupSchemeIso G).hom.hom.hom

/-- Evaluation at the point of an algebra map is that map followed by the spectrum counit. -/
theorem pointAlgebraHom_algPoint {B : CommAlgCat (CommRingCat.of k)} (φ : algebra G ⟶ B) :
    pointAlgebraHom G _ (algPoint G φ) =
      ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom.comp φ.hom := by
  rw [pointAlgebraHom_eq]
  have h : algPoint G φ ≫ (groupSchemeIso G).inv.hom.hom =
      𝟙 _ ≫ (algSpec (CommRingCat.of k)).map φ.op := by
    rw [Category.id_comp, algPoint, Category.assoc]
    exact (congrArg (fun z => (algSpec (CommRingCat.of k)).map φ.op ≫ z.hom.hom)
      (groupSchemeIso G).hom_inv_id).trans (Category.comp_id _)
  rw [h, Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The spectrum counit on any algebra is injective. -/
theorem counit_unop_injective (B : CommAlgCat (CommRingCat.of k)) :
    Function.Injective
      ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom := by
  have : IsIso ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)) := by
    have : (algSpec (CommRingCat.of k)).Full := algSpec.fullyFaithful.full
    have : (algSpec (CommRingCat.of k)).Faithful := algSpec.fullyFaithful.faithful
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop).1

/-- Evaluation of coordinates at the identity point of the group. -/
def globalAlgHom : algebra G →ₐ[k] ((algΓ (CommRingCat.of k)).obj G.X).unop :=
  pointAlgebraHom G G.X (𝟙 G.X)

/-- Evaluation at any point is pullback of the corresponding actual global function. -/
theorem pointAlgebraHom_apply_eq (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (b : algebra G) :
    pointAlgebraHom G T g b = g.left.appTop (globalAlgHom G b) := by
  have h := pointAlgebraHom_naturality G g (𝟙 G.X)
  rw [Category.comp_id] at h
  rw [h]
  rfl

/-- Evaluation at the identity point identifies coordinates with actual global functions. -/
theorem globalAlgHom_bijective : Function.Bijective (globalAlgHom G) := by
  have : IsIso (groupSchemeIso G).inv.hom.hom :=
    ⟨⟨(groupSchemeIso G).hom.hom.hom,
      congrArg (fun z => z.hom.hom) (groupSchemeIso G).inv_hom_id,
      congrArg (fun z => z.hom.hom) (groupSchemeIso G).hom_inv_id⟩⟩
  have : (algSpec (CommRingCat.of k)).Full := algSpec.fullyFaithful.full
  have : (algSpec (CommRingCat.of k)).Faithful := algSpec.fullyFaithful.faithful
  have h : globalAlgHom G =
      ((algΓ (CommRingCat.of k)).map (groupSchemeIso G).inv.hom.hom ≫
        (algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op (algebra G))).unop.hom := by
    rw [globalAlgHom, pointAlgebraHom_eq, Category.id_comp, Adjunction.homEquiv_counit]
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

/-- Coordinates are the actual global functions on the group. -/
def globalAlgEquiv : algebra G ≃ₐ[k] ((algΓ (CommRingCat.of k)).obj G.X).unop :=
  AlgEquiv.ofBijective (globalAlgHom G) (globalAlgHom_bijective G)

@[simp] theorem globalAlgEquiv_apply (b : algebra G) :
    globalAlgEquiv G b = globalAlgHom G b := rfl

/-- The coordinate of a rational character, namely its actual global unit function. -/
def characterCoordinate (χ : rationalCharacters G) : algebra G :=
  (globalAlgEquiv G).symm (characterEval χ G.X (𝟙 G.X)).1

/-- The character coordinate evaluates to the character on every test point. -/
theorem pointAlgebraHom_characterCoordinate (χ : rationalCharacters G)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    pointAlgebraHom G T g (characterCoordinate G χ) = (characterEval χ T g).1 := by
  rw [pointAlgebraHom_apply_eq, characterCoordinate, ← globalAlgEquiv_apply,
    AlgEquiv.apply_symm_apply]
  have h := characterEval_naturality χ g (𝟙 G.X)
  rw [Category.comp_id] at h
  rw [h]
  rfl

/-- The coordinate of a global function composed with inversion. -/
def coordinateEquiv : ((algΓ (CommRingCat.of k)).obj G.X).unop ≃ₐ[k] algebra G :=
  (inversionAlgEquiv G).trans (globalAlgEquiv G).symm

/-- The coordinate of `f` evaluates to `f` at the inverse point. -/
theorem pointAlgebraHom_coordinateEquiv (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X)
    (f : ((algΓ (CommRingCat.of k)).obj G.X).unop) :
    pointAlgebraHom G T g (coordinateEquiv G f) = (g⁻¹).left.appTop f := by
  rw [pointAlgebraHom_apply_eq, coordinateEquiv, AlgEquiv.trans_apply, ← globalAlgEquiv_apply,
    AlgEquiv.apply_symm_apply]
  exact appTop_inversionAlgHom G T g f

end AffineCoordinates

/-- The value of the negative of a character is the inverse value. -/
theorem characterEval_neg {S : Scheme.{u}} {G : GroupScheme S} (χ : rationalCharacters G)
    (T : Over S) (x : T ⟶ G.X) :
    characterEval (-χ) T x = (characterEval χ T x)⁻¹ := by
  rw [← neg_one_zsmul, characterEval_zsmul, zpow_neg_one]

theorem productMap_rTensor' {K B C A : Type*} [CommSemiring K]
    [CommSemiring B] [CommSemiring C] [CommSemiring A]
    [Algebra K B] [Algebra K C] [Algebra K A]
    (r : B →ₐ[K] C) (f : C →ₐ[K] A) (g : B →ₐ[K] A) (z : B ⊗[K] B) :
    Algebra.TensorProduct.productMap f g (r.toLinearMap.rTensor B z) =
      Algebra.TensorProduct.productMap (f.comp r) g z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem productMap_comp_include {K B C A : Type*} [CommSemiring K]
    [CommSemiring B] [CommSemiring C] [CommSemiring A]
    [Algebra K B] [Algebra K C] [Algebra K A]
    (ε : B ⊗[K] C →ₐ[K] A) (z : B ⊗[K] C) :
    Algebra.TensorProduct.productMap (ε.comp Algebra.TensorProduct.includeLeft)
      (ε.comp Algebra.TensorProduct.includeRight) z = ε z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance homogeneousCharacterCoordinatesInst1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance homogeneousCharacterCoordinatesInst2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- Covariance on every scheme test implies tensor covariance, using the universal test
over the spectrum of the tensor product of the two coordinate algebras. -/
theorem mem_leftCovariantSubspace_of_points (i : H ⟶ G) (χ : algebra H) (b : algebra G)
    (hb : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
      pointAlgebraHom G T ((h ≫ i.hom.hom) * g) b =
        pointAlgebraHom H T h χ * pointAlgebraHom G T g b) :
    b ∈ leftCovariantSubspace i χ := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  let r : algebra G →ₐ[k] algebra H := (AffineHomImageHopfAdapter.pullback i).hom.toAlgHom
  let B : CommAlgCat (CommRingCat.of k) := CommAlgCat.of _ (algebra H ⊗[k] algebra G)
  let ε : algebra H ⊗[k] algebra G →ₐ[k]
      ((algΓ (CommRingCat.of k)).obj ((algSpec (CommRingCat.of k)).obj (op B))).unop :=
    ((algΓAlgSpecAdjunction (CommRingCat.of k)).counit.app (op B)).unop.hom
  let φL : algebra H ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let φR : algebra G ⟶ B := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  have e := hb _ (algPoint H φL) (algPoint G φR)
  rw [pointAlgebraHom_mul, AffineHomImageHopfAdapter.pointAlgebraHom_pullback,
    pointAlgebraHom_algPoint, pointAlgebraHom_algPoint] at e
  rw [mem_leftCovariantSubspace]
  apply counit_unop_injective B
  change ε (r.toLinearMap.rTensor (algebra G) (Coalgebra.comul b)) = ε (χ ⊗ₜ[k] b)
  refine (productMap_comp_include ε _).symm.trans
    ((productMap_rTensor' r _ _ _).trans (e.trans ?_))
  change ε (χ ⊗ₜ[k] 1) * ε (1 ⊗ₜ[k] b) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Tensor covariance is exactly covariance on every scheme test. -/
theorem mem_leftCovariantSubspace_iff_points (i : H ⟶ G) (χ : algebra H) (b : algebra G) :
    b ∈ leftCovariantSubspace i χ ↔
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
        pointAlgebraHom G T ((h ≫ i.hom.hom) * g) b =
          pointAlgebraHom H T h χ * pointAlgebraHom G T g b :=
  ⟨fun hb T h g => pointAlgebraHom_leftCovariant i χ hb T h g,
    mem_leftCovariantSubspace_of_points i χ b⟩

/-- Left covariance is preserved by every right translation of the coordinate algebra. -/
theorem rightAct_mem_leftCovariantSubspace (i : H ⟶ G) (χ : algebra H)
    (ψ : Module.Dual k (algebra G)) {b : algebra G} (hb : b ∈ leftCovariantSubspace i χ) :
    letI : Coalgebra k (algebra G) :=
      (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
    AffineLinearEmbedding.rightAct ψ b ∈ leftCovariantSubspace i χ := by
  let : Coalgebra k (algebra G) :=
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra
  exact Chevalley.rightAct_mem_leftCovariantSubspace _ χ ψ hb

end AffineCoordinates

namespace HomogeneousQuotientFromEmbedding

open AffineCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (D : HomogeneousQuotient i)
  [Mono i.hom.hom] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance homogeneousCharacterCoordinatesInst3 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance homogeneousCharacterCoordinatesInst4 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- A function is right covariant for `χ` exactly when its composite with inversion has
left-covariant coordinate for `-χ`. -/
theorem mem_rightCharacterCovariantSpace_iff_coordinate (χ : rationalCharacters H)
    (f : ((algΓ (CommRingCat.of k)).obj G.X).unop) :
    f ∈ rightCharacterCovariantSpace i D χ ↔
      coordinateEquiv G f ∈ leftCovariantSubspace i (characterCoordinate H (-χ)) := by
  have key : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (g : T ⟶ G.X),
      (pointAlgebraHom G T ((h ≫ i.hom.hom) * g) (coordinateEquiv G f) =
        pointAlgebraHom H T h (characterCoordinate H (-χ)) *
          pointAlgebraHom G T g (coordinateEquiv G f)) ↔
      ((g⁻¹ * (h⁻¹ ≫ i.hom.hom)).left.appTop f =
        (characterEval χ T h⁻¹).1 * (g⁻¹).left.appTop f) := by
    intro T h g
    rw [pointAlgebraHom_coordinateEquiv, pointAlgebraHom_coordinateEquiv,
      pointAlgebraHom_characterCoordinate, characterEval_neg, ← map_inv, mul_inv_rev,
      GrpObj.inv_comp]
  rw [mem_leftCovariantSubspace_iff_points, mem_rightCharacterCovariantSpace]
  constructor
  · intro hf T h g
    exact (key T h g).mpr (hf T g⁻¹ h⁻¹)
  · intro hf T a b
    have e := (key T b⁻¹ a⁻¹).mp (hf T b⁻¹ a⁻¹)
    rwa [inv_inv, inv_inv] at e

/-- Composition with inversion identifies the entire right-covariant function space for `χ`
with the entire left-covariant coordinate subspace for `-χ`. -/
def rightCovariantCoordinateEquiv (χ : rationalCharacters H) :
    rightCharacterCovariantSpace i D χ ≃ₗ[k]
      leftCovariantSubspace i (characterCoordinate H (-χ)) where
  toFun f := ⟨coordinateEquiv G f.1,
    (mem_rightCharacterCovariantSpace_iff_coordinate i D χ f.1).mp f.2⟩
  invFun b := ⟨(coordinateEquiv G).symm b.1,
    (mem_rightCharacterCovariantSpace_iff_coordinate i D χ _).mpr
      (by rw [AlgEquiv.apply_symm_apply]; exact b.2)⟩
  left_inv f := Subtype.ext ((coordinateEquiv G).symm_apply_apply f.1)
  right_inv b := Subtype.ext ((coordinateEquiv G).apply_symm_apply b.1)
  map_add' f g := Subtype.ext (map_add (coordinateEquiv G) f.1 g.1)
  map_smul' r f := Subtype.ext (map_smul (coordinateEquiv G) r f.1)

@[simp] theorem rightCovariantCoordinateEquiv_apply (χ : rationalCharacters H)
    (f : rightCharacterCovariantSpace i D χ) :
    (rightCovariantCoordinateEquiv i D χ f).1 = coordinateEquiv G f.1 := rfl

/-- On a proper quotient the entire left-covariant coordinate subspace of every character
coordinate is finite. -/
theorem finite_leftCovariantSubspace_characterCoordinate [IsProper D.scheme.hom]
    (χ : rationalCharacters H) :
    Module.Finite k (leftCovariantSubspace i (characterCoordinate H χ)) := by
  let := finite_rightCharacterCovariantSpace i D (-χ)
  have h := Module.Finite.equiv (rightCovariantCoordinateEquiv i D (-χ))
  rwa [neg_neg] at h

end HomogeneousQuotientFromEmbedding

end Langlands.GroupScheme
