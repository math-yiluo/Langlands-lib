import Langlands.GroupScheme.Rational.SplitTorusVectorExtension
import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.Rational.VectorLieCoordinates
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Averaging additive functions over a diagonalizable group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DiagonalizableAverage

open PointedCoordinateWeights

variable {k : Type u} [Field k]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1

/-- Coefficient change of affine points along an algebra map. -/
abbrev pmap {V : Over (Spec (CommRingCat.of k))} {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (v : Points V A) : Points V B :=
  PointedCoordinateWeights.pointsMap f v

/-- Global functions on the affine test `Spec A`, read in `A`. -/
def gammaHom (A : Type u) [CommRing A] [Algebra k A] :
    Γ(((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))).left, ⊤) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

section Coordinates

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The coordinate of an additive point over an affine test, in its coefficient algebra. -/
def coord (v : Points (𝔾ₐ).X A) : A :=
  (RelativeRoot.vectorAffineCoordinates (VectorGroup.coordinates (CommRingCat.of k) 1) A
    v).toAdd 0

/-- The additive point over an affine test with a prescribed coordinate. -/
def ofCoord (a : A) : Points (𝔾ₐ).X A :=
  (RelativeRoot.vectorAffineCoordinates (VectorGroup.coordinates (CommRingCat.of k) 1) A).symm
    (Multiplicative.ofAdd fun _ => a)

@[simp] theorem coord_ofCoord (a : A) : coord (ofCoord (k := k) a) = a := by
  simp [coord, ofCoord]

theorem coord_injective {v w : Points (𝔾ₐ).X A} (h : coord v = coord w) : v = w := by
  apply (RelativeRoot.vectorAffineCoordinates
    (VectorGroup.coordinates (CommRingCat.of k) 1) A).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [Subsingleton.elim j 0]
  exact h

@[simp] theorem coord_mul (v w : Points (𝔾ₐ).X A) : coord (v * w) = coord v + coord w := by
  simp only [coord, map_mul, toAdd_mul, Pi.add_apply]

@[simp] theorem coord_one : coord (1 : Points (𝔾ₐ).X A) = 0 := by
  simp only [coord, map_one, toAdd_one, Pi.zero_apply]

@[simp] theorem coord_inv (v : Points (𝔾ₐ).X A) : coord v⁻¹ = -coord v := by
  simp only [coord, map_inv, toAdd_inv, Pi.neg_apply]

theorem coord_pmap (f : A →ₐ[k] B) (v : Points (𝔾ₐ).X A) :
    coord (pmap f v) = f (coord v) :=
  congrFun ((VectorGroup.isNaturalVectorCoordinates (k := k) (n := 1)).vectorAffineCoordinates_naturality
    f v) 0

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (χ : characterLattice S)

/-- The value of a character at an affine point, in the coefficient algebra. -/
def charCoeff (s : Points S.X A) : A :=
  gammaHom A (VectorGroup.charValue χ _ s)

theorem coord_weightAction (s : Points S.X A) (v : Points (𝔾ₐ).X A) :
    coord ((VectorGroup.weightAction (n := 1) χ).act s v) = charCoeff χ s * coord v := by
  change gammaHom A
      ((VectorGroup.coordinates (CommRingCat.of k) 1 _
        ((VectorGroup.weightAction (n := 1) χ).act s v)).toAdd 0) = _
  rw [VectorGroup.coordinates_weightAction_act, Pi.smul_apply, smul_eq_mul, map_mul]
  rfl

theorem charCoeff_pmap (f : A →ₐ[k] B) (s : Points S.X A) :
    charCoeff χ (pmap f s) = f (charCoeff χ s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom (VectorGroup.charValue χ _
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ s)) = _
  rw [VectorGroup.charValue_comp]
  exact congrArg (fun q => q.hom (VectorGroup.charValue χ _ s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom))

@[simp] theorem charCoeff_one : charCoeff χ (1 : Points S.X A) = 1 := by
  rw [charCoeff, VectorGroup.charValue_one, map_one]

theorem charCoeff_mul (s s' : Points S.X A) :
    charCoeff χ (s * s') = charCoeff χ s * charCoeff χ s' := by
  rw [charCoeff, VectorGroup.charValue_mul, map_mul]
  rfl

theorem charCoeff_mul_inv (s : Points S.X A) : charCoeff χ s * charCoeff χ s⁻¹ = 1 := by
  rw [← charCoeff_mul, mul_inv_cancel, charCoeff_one]

end Coordinates

variable (Λ : Type u) [AddCommGroup Λ]

local notation "𝔻" => Diagonalizable.groupScheme (CommRingCat.of k) Λ

instance isAffineHom_diagonalizable : IsAffineHom (𝔻).X.hom := by
  change IsAffineHom ((algSpec (CommRingCat.of k)).obj
    (op (Diagonalizable.algebra (CommRingCat.of k) Λ))).hom
  rw [algSpec_obj_hom]
  exact isAffineHom_of_isAffine
    (X := Spec (CommRingCat.of (Diagonalizable.algebra (CommRingCat.of k) Λ))) _

section GroupAlgebra

variable (A : Type u) [CommRing A] [Algebra k A] {B : Type u} [CommRing B] [Algebra k B]

variable (k) in
/-- Constant extension of coefficients to the group algebra. -/
abbrev const : A →ₐ[k] AddMonoidAlgebra A Λ :=
  IsScalarTower.toAlgHom k A (AddMonoidAlgebra A Λ)

variable (k) in
/-- The universal point of `D(Λ)` over the group algebra `A[Λ]`: the character `λ ↦ e_λ`. -/
def univPoint : Points (𝔻).X (AddMonoidAlgebra A Λ) :=
  CharacterAction.characterPoint (R := CommRingCat.of k)
    (C := CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra A Λ))
    (AddMonoidAlgebra.of A Λ).toHomUnits

variable {A}

/-- The character of an affine point of `D(Λ)`. -/
def character (d : Points (𝔻).X A) : Multiplicative Λ →* Aˣ :=
  Corepresented.affinePointsEquiv (Diagonalizable.functor (CommRingCat.of k) Λ)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
    (CommAlgCat.of (CommRingCat.of k) A) d

variable (k) in
/-- Translation of the group algebra by a character: `e_λ ↦ t(λ) e_λ`. -/
def translation (t : Multiplicative Λ →* Aˣ) :
    AddMonoidAlgebra A Λ →ₐ[k] AddMonoidAlgebra A Λ :=
  (AddMonoidAlgebra.lift A (AddMonoidAlgebra A Λ) Λ
    ((AddMonoidAlgebra.of A Λ) *
      ((algebraMap A (AddMonoidAlgebra A Λ)).toMonoidHom.comp
        ((Units.coeHom A).comp t)))).restrictScalars k

@[simp] theorem translation_single (t : Multiplicative Λ →* Aˣ) (m : Λ) (a : A) :
    translation k Λ t (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single m (a * (t (Multiplicative.ofAdd m) : A)) := by
  simp [translation, Algebra.smul_def, AddMonoidAlgebra.of_apply,
    AddMonoidAlgebra.single_mul_single]

theorem coeff_zero_translation (t : Multiplicative Λ →* Aˣ) (x : AddMonoidAlgebra A Λ) :
    (translation k Λ t x).coeff 0 = x.coeff 0 := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [AddMonoidAlgebra.coeff_add, hx, hy]
  | single m a =>
      rw [translation_single]
      by_cases h : m = 0
      · subst m
        simp
      · simp [AddMonoidAlgebra.coeff_single, h]

theorem translation_comp_const (t : Multiplicative Λ →* Aˣ) :
    (translation k Λ t).comp (const k Λ A) = const k Λ A :=
  AlgHom.ext fun a => by
    change (AddMonoidAlgebra.lift A (AddMonoidAlgebra A Λ) Λ _) (algebraMap A _ a) =
      algebraMap A _ a
    exact AlgHom.commutes _ a

theorem coeff_zero_const_mul (a : A) (x : AddMonoidAlgebra A Λ) :
    (const k Λ A a * x).coeff 0 = a * x.coeff 0 := by
  change (AddMonoidAlgebra.single 0 a * x).coeff 0 = _
  exact AddMonoidAlgebra.coeff_single_zero_mul x a 0

@[simp] theorem coeff_zero_const (a : A) : (const k Λ A a).coeff 0 = a := by
  change (AddMonoidAlgebra.single 0 a).coeff 0 = a
  simp [AddMonoidAlgebra.coeff_single]

theorem coeff_zero_add (x y : AddMonoidAlgebra A Λ) :
    (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem coeff_zero_mapAlgHom (f : A →ₐ[k] B) (x : AddMonoidAlgebra A Λ) :
    (AddMonoidAlgebra.mapAlgHom Λ f x).coeff 0 = f (x.coeff 0) :=
  AddMonoidAlgebra.coeff_mapAlgHom f x 0

theorem mapAlgHom_comp_const (f : A →ₐ[k] B) :
    (AddMonoidAlgebra.mapAlgHom Λ f).comp (const k Λ A) = (const k Λ B).comp f :=
  AlgHom.ext fun a => by
    change AddMonoidAlgebra.mapAlgHom Λ f (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 (f a)
    ext m
    simp [AddMonoidAlgebra.coeff_single]

theorem pmap_comp {V : Over (Spec (CommRingCat.of k))} {C : Type u} [CommRing C]
    [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) (v : Points V A) :
    pmap g (pmap f v) = pmap (g.comp f) v := by
  simp only [pmap, PointedCoordinateWeights.pointsMap, ← Category.assoc, ← Functor.map_comp]
  rfl

theorem pmap_lift {V W : Over (Spec (CommRingCat.of k))} (f : A →ₐ[k] B)
    (v : Points V A) (w : Points W A) :
    pmap f (lift v w) = lift (pmap f v) (pmap f w) := by
  simp only [pmap, PointedCoordinateWeights.pointsMap, comp_lift]

theorem pmap_comp_hom {V W : Over (Spec (CommRingCat.of k))} (f : A →ₐ[k] B)
    (v : Points V A) (Φ : V ⟶ W) : pmap f v ≫ Φ = pmap f (v ≫ Φ) := by
  simp only [pmap, PointedCoordinateWeights.pointsMap, Category.assoc]

theorem pmap_mul {G : GroupScheme (Spec (CommRingCat.of k))} (f : A →ₐ[k] B)
    (v w : Points G.X A) : pmap f (v * w) = pmap f v * pmap f w := by
  simp only [pmap, PointedCoordinateWeights.pointsMap, MonObj.comp_mul]

theorem pmap_univPoint (f : A →ₐ[k] B) :
    pmap (AddMonoidAlgebra.mapAlgHom Λ f) (univPoint k Λ A) = univPoint k Λ B := by
  unfold univPoint
  rw [pmap, PointedCoordinateWeights.pointsMap, ← CharacterAction.characterPoint_mapCharacter]
  congr 1
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change AddMonoidAlgebra.mapAlgHom Λ f (AddMonoidAlgebra.single m.toAdd 1) =
    AddMonoidAlgebra.single m.toAdd 1
  ext n
  simp [AddMonoidAlgebra.coeff_single]

/-- Translating the universal point by the constant extension of a point `d` is the coefficient
change of the universal point along the translation by the character of `d`. -/
theorem characterPoint_character (d : Points (𝔻).X A) :
    CharacterAction.characterPoint (R := CommRingCat.of k)
      (C := CommAlgCat.of (CommRingCat.of k) A) (character Λ d) = d :=
  (Corepresented.affinePointsEquiv (Diagonalizable.functor (CommRingCat.of k) Λ)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
    (CommAlgCat.of (CommRingCat.of k) A)).symm_apply_apply d

theorem pmap_translation_univPoint (d : Points (𝔻).X A) :
    pmap (translation k Λ (character Λ d)) (univPoint k Λ A) =
      univPoint k Λ A * pmap (const k Λ A) d := by
  conv_rhs => rw [← characterPoint_character Λ d]
  unfold univPoint
  rw [pmap, PointedCoordinateWeights.pointsMap, pmap, PointedCoordinateWeights.pointsMap,
    ← CharacterAction.characterPoint_mapCharacter, ← CharacterAction.characterPoint_mapCharacter,
    ← CharacterAction.characterPoint_mul]
  congr 1
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change translation k Λ (character Λ d) (AddMonoidAlgebra.single m.toAdd 1) =
    AddMonoidAlgebra.single m.toAdd 1 * const k Λ A ((character Λ d m : Aˣ) : A)
  rw [translation_single, one_mul]
  change _ = AddMonoidAlgebra.single m.toAdd 1 * AddMonoidAlgebra.single 0 _
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
  rfl

end GroupAlgebra

section Average

variable {X Y : Over (Spec (CommRingCat.of k))}
variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The point of `D(Λ) ⊗ X` over `A[Λ]` formed by the universal point and the constant
extension of `x`. -/
def pair (x : Points X A) : Points ((𝔻).X ⊗ X) (AddMonoidAlgebra A Λ) :=
  lift (univPoint k Λ A) (pmap (const k Λ A) x)

/-- The average of `Ψ` at an affine point: the constant coefficient of `Ψ` at the universal
point of `D(Λ)`. -/
def averagePoint (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) (A : Type u) [CommRing A] [Algebra k A]
    (x : Points X A) : Points (𝔾ₐ).X A :=
  ofCoord ((coord (pair Λ x ≫ Ψ)).coeff 0)

theorem pair_pmap (f : A →ₐ[k] B) (x : Points X A) :
    pair Λ (pmap f x) = pmap (AddMonoidAlgebra.mapAlgHom Λ f) (pair Λ x) := by
  rw [pair, pair, pmap_lift, pmap_univPoint, pmap_comp, pmap_comp,
    mapAlgHom_comp_const]

theorem averagePoint_naturality (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) (f : A →ₐ[k] B)
    (x : Points X A) :
    pmap f (averagePoint Λ Ψ A x) = averagePoint Λ Ψ B (pmap f x) := by
  apply coord_injective
  rw [coord_pmap, averagePoint, averagePoint, coord_ofCoord, coord_ofCoord, pair_pmap,
    pmap_comp_hom, coord_pmap, coeff_zero_mapAlgHom]

variable [IsAffineHom X.hom] [IsAffineHom Y.hom]

/-- The average of an additive function on `D(Λ) ⊗ X` over the `D(Λ)` factor. -/
def average (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) : X ⟶ (𝔾ₐ).X :=
  homOfAffinePoints (averagePoint Λ Ψ)

theorem comp_average (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) (x : Points X A) :
    x ≫ average Λ Ψ = averagePoint Λ Ψ A x :=
  comp_homOfAffinePoints _ (fun _ _ _ _ _ _ f x => averagePoint_naturality Λ Ψ f x) x

theorem coord_comp_average (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) (x : Points X A) :
    coord (x ≫ average Λ Ψ) = (coord (pair Λ x ≫ Ψ)).coeff 0 := by
  rw [comp_average, averagePoint, coord_ofCoord]

/-- Naturality: averaging commutes with pullback along a morphism of affine schemes. -/
theorem comp_average_eq (t : Y ⟶ X) (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) :
    t ≫ average Λ Ψ = average Λ (((𝔻).X ◁ t) ≫ Ψ) := by
  apply affine_hom_ext
  intro A _ _ y
  apply coord_injective
  rw [← Category.assoc, coord_comp_average, coord_comp_average, pair, pair,
    ← Category.assoc, lift_whiskerLeft, pmap_comp_hom]

/-- The average of a function that does not depend on the `D(Λ)` variable is the function. -/
theorem average_snd (Θ : X ⟶ (𝔾ₐ).X) : average Λ (snd (𝔻).X X ≫ Θ) = Θ := by
  apply affine_hom_ext
  intro A _ _ x
  apply coord_injective
  rw [coord_comp_average, pair, ← Category.assoc, lift_snd, pmap_comp_hom,
    coord_pmap, coeff_zero_const]

/-- Averaging is additive. -/
theorem average_mul (Ψ Ψ' : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) :
    average Λ (Ψ * Ψ') = average Λ Ψ * average Λ Ψ' := by
  apply affine_hom_ext
  intro A _ _ x
  apply coord_injective
  rw [MonObj.comp_mul, coord_mul, coord_comp_average, coord_comp_average, coord_comp_average,
    MonObj.comp_mul, coord_mul, coeff_zero_add]

/-- Averaging commutes with scaling by a character value depending only on the `X` variable. -/
theorem average_weightAction {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (s : X ⟶ S.X) (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) :
    average Λ ((VectorGroup.weightAction (n := 1) χ).act (snd (𝔻).X X ≫ s) Ψ) =
      (VectorGroup.weightAction (n := 1) χ).act s (average Λ Ψ) := by
  apply affine_hom_ext
  intro A _ _ x
  apply coord_injective
  have hs : pair Λ x ≫ snd (𝔻).X X ≫ s = pmap (const k Λ A) (x ≫ s) := by
    rw [pair, ← Category.assoc, lift_snd, pmap_comp_hom]
  rw [coord_comp_average, AutomorphicAction.naturality, AutomorphicAction.naturality,
    coord_weightAction, coord_weightAction, coord_comp_average, hs, charCoeff_pmap,
    coeff_zero_const_mul]

/-- Translation invariance: replacing the `D(Λ)` variable `z` by `z · d₀(x)` does not change
the average. -/
theorem average_translate (d₀ : X ⟶ (𝔻).X) (Ψ : (𝔻).X ⊗ X ⟶ (𝔾ₐ).X) :
    average Λ (lift (fst (𝔻).X X * (snd (𝔻).X X ≫ d₀)) (snd (𝔻).X X) ≫ Ψ) =
      average Λ Ψ := by
  apply affine_hom_ext
  intro A _ _ x
  apply coord_injective
  have hp : pair Λ x ≫ lift (fst (𝔻).X X * (snd (𝔻).X X ≫ d₀)) (snd (𝔻).X X) =
      pmap (translation k Λ (character Λ (x ≫ d₀))) (pair Λ x) := by
    rw [pair, comp_lift, MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd,
      pmap_lift, pmap_translation_univPoint, pmap_comp, translation_comp_const,
      pmap_comp_hom]
  rw [coord_comp_average, coord_comp_average, ← Category.assoc, hp, pmap_comp_hom,
    coord_pmap, coeff_zero_translation]

end Average

end Langlands.GroupScheme.DiagonalizableAverage
