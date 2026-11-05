import Langlands.Algebra.PolynomialCocycle.Coboundary
import Langlands.GroupScheme.Rational.SplitSeriesProductDecomposition
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent

/-! # Commutative split groups of exponent `char k` are vector groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  AlgebraicGeometry Opposite Polynomial Polynomial.Bivariate
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme.RelativeRoot

namespace SplitCommutativeVector

section CommGroup

variable {G : Type*} [CommGroup G]

theorem cocycle_identity (a b c d e f : G) :
    a * b * c⁻¹ * (c * d * e⁻¹) = b * d * f⁻¹ * (a * f * e⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem torsion_identity (a b c d e f : G) (h : a * e = b * d) :
    a * (e * c * f⁻¹) * f = b * c * d := by
  rw [show a * (e * c * f⁻¹) * f = a * e * c by group, h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

theorem section_identity (a b c d e : G) :
    e * (a * b * e⁻¹ * c * d) = a * c * (b * d) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem kernel_identity (a b c d : G) : a * b * (c * d)⁻¹ = a * c⁻¹ * (b * d⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end CommGroup

variable {k : Type u} [Field k]

section Coordinates

variable {V Z : GroupScheme (Spec (CommRingCat.of k))} {m : ℕ}
  {eV : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤))}
  {eZ : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ Z.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}

variable (eV) in
/-- The point of a one-dimensional vector group with a given coordinate. -/
def linePoint (A : Type u) [CommRing A] [Algebra k A] (a : A) : Lie.AffinePoints V A :=
  (vectorAffineCoordinates eV A).symm (Multiplicative.ofAdd fun _ => a)

variable (eV) in
/-- The coordinate of an affine point of a one-dimensional vector group. -/
def lineCoord {A : Type u} [CommRing A] [Algebra k A] (x : Lie.AffinePoints V A) : A :=
  (vectorAffineCoordinates eV A x).toAdd 0

@[simp] theorem lineCoord_linePoint (A : Type u) [CommRing A] [Algebra k A] (a : A) :
    lineCoord eV (linePoint eV A a) = a := by
  simp [lineCoord, linePoint]

theorem eq_linePoint {A : Type u} [CommRing A] [Algebra k A] (x : Lie.AffinePoints V A) :
    x = linePoint eV A (lineCoord eV x) := by
  apply (vectorAffineCoordinates eV A).injective
  apply Multiplicative.toAdd.injective
  funext i
  rw [Subsingleton.elim i 0]
  simp [linePoint, lineCoord]

theorem linePoint_mul (A : Type u) [CommRing A] [Algebra k A] (a b : A) :
    linePoint eV A a * linePoint eV A b = linePoint eV A (a + b) := by
  rw [linePoint, linePoint, linePoint, ← map_mul]
  rfl

theorem linePoint_pow (A : Type u) [CommRing A] [Algebra k A] (a : A) (i : ℕ) :
    linePoint eV A a ^ i = linePoint eV A ((i : A) * a) := by
  rw [linePoint, linePoint, ← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  funext l
  simp [toAdd_pow, nsmul_eq_mul]

theorem linePoint_zero (A : Type u) [CommRing A] [Algebra k A] : linePoint eV A 0 = 1 := by
  apply (vectorAffineCoordinates eV A).injective
  rw [map_one, linePoint, MulEquiv.apply_symm_apply]
  rfl

/-- Points of a one-dimensional vector group over a `k`-algebra of characteristic `char k`
are killed by `char k`. -/
theorem linePoint_pow_ringChar (A : Type u) [CommRing A] [Algebra k A] (a : A) :
    linePoint eV A a ^ ringChar k = 1 := by
  rw [linePoint_pow, ← map_natCast (algebraMap k A), ringChar.Nat.cast_ringChar, map_zero,
    zero_mul, linePoint_zero]

theorem affineMap_linePoint (heV : IsNaturalVectorCoordinates eV) {A B : Type u} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (a : A) :
    Lie.affineMap V f (linePoint eV A a) = linePoint eV B (f a) := by
  apply (vectorAffineCoordinates eV B).injective
  apply Multiplicative.toAdd.injective
  rw [heV.vectorAffineCoordinates_naturality]
  simp [linePoint]

/-- A natural map from pairs of points of a one-dimensional vector group to a vector group is
given by polynomials in the two coordinates. -/
theorem exists_bivariate (heV : IsNaturalVectorCoordinates eV)
    (heZ : IsNaturalVectorCoordinates eZ) (F : V.X ⊗ V.X ⟶ Z.X) :
    ∃ c : Fin m → k[X][X], ∀ (A : Type u) [CommRing A] [Algebra k A] (a b : A) (i : Fin m),
      (vectorAffineCoordinates eZ A
        (lift (linePoint eV A a) (linePoint eV A b) ≫ F)).toAdd i = aevalAeval a b (c i) := by
  refine ⟨fun i => (vectorAffineCoordinates eZ k[X][X]
    (lift (linePoint eV k[X][X] (C X)) (linePoint eV k[X][X] X) ≫ F)).toAdd i, ?_⟩
  intro A _ _ a b i
  have h := heZ.vectorAffineCoordinates_naturality (aevalAeval a b)
    (lift (linePoint eV k[X][X] (C X)) (linePoint eV k[X][X] X) ≫ F)
  have h2 : Lie.affineMap Z (aevalAeval a b)
      (lift (linePoint eV k[X][X] (C X)) (linePoint eV k[X][X] X) ≫ F) =
      lift (linePoint eV A a) (linePoint eV A b) ≫ F := by
    rw [Lie.affineMap_apply, comp_lift_assoc, ← Lie.affineMap_apply, ← Lie.affineMap_apply,
      affineMap_linePoint heV, affineMap_linePoint heV, aevalAeval_X, aevalAeval_Y]
  rw [h2] at h
  exact congrFun h i

variable [IsAffineHom V.X.hom]

variable (V) in
/-- The coordinate algebra of an affine group over the field. -/
abbrev universalAlgebra : CommAlgCat (CommRingCat.of k) :=
  ((algΓ (CommRingCat.of k)).obj V.X).unop

variable (V) in
/-- The universal affine point of an affine group. -/
def universalPoint : Lie.AffinePoints V (universalAlgebra V) :=
  Lie.affinizationFactor V (𝟙 V.X)

variable (eV eZ) in
/-- The regular map of a one-dimensional vector group to a vector group given by polynomials
in the coordinate. -/
def polyMap (g : Fin m → k[X]) : V.X ⟶ Z.X :=
  (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app V.X ≫
    (vectorAffineCoordinates eZ (universalAlgebra V)).symm
      (Multiplicative.ofAdd fun i => aeval (lineCoord eV (universalPoint V)) (g i))

theorem polyMap_coord (heV : IsNaturalVectorCoordinates eV)
    (heZ : IsNaturalVectorCoordinates eZ) (g : Fin m → k[X]) (A : Type u) [CommRing A]
    [Algebra k A] (a : A) (i : Fin m) :
    (vectorAffineCoordinates eZ A (linePoint eV A a ≫ polyMap eV eZ g)).toAdd i =
      aeval a (g i) := by
  let f' := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (linePoint eV A a ≫ (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app V.X)
  have hψ : (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f'.unop.hom).op =
      linePoint eV A a ≫ (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app V.X := by
    rw [CommAlgCat.ofHom_hom]
    exact (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hx : Lie.affineMap V f'.unop.hom (universalPoint V) = linePoint eV A a := by
    rw [Lie.affineMap_apply, hψ, Category.assoc, universalPoint, Lie.unit_affinizationFactor,
      Category.comp_id]
  have hcoord : f'.unop.hom (lineCoord eV (universalPoint V)) = a := by
    have h := congrFun (heV.vectorAffineCoordinates_naturality f'.unop.hom (universalPoint V)) 0
    rw [hx] at h
    rw [lineCoord, ← h]
    exact lineCoord_linePoint A a
  have hP : linePoint eV A a ≫ polyMap eV eZ g = Lie.affineMap Z f'.unop.hom
      ((vectorAffineCoordinates eZ (universalAlgebra V)).symm
        (Multiplicative.ofAdd fun i => aeval (lineCoord eV (universalPoint V)) (g i))) := by
    rw [Lie.affineMap_apply, hψ, polyMap, Category.assoc]
  rw [hP, heZ.vectorAffineCoordinates_naturality]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  rw [← Polynomial.aeval_algHom_apply, hcoord]

/-- A morphism from an affine group to a group is multiplicative on all points as soon as it is
multiplicative on affine points. -/
theorem comp_mul_of_affine (f : V.X ⟶ Z.X)
    (hf : ∀ (A : Type u) [CommRing A] [Algebra k A] (x y : Lie.AffinePoints V A),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f))
    {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ V.X) :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have key : ∀ (A : CommAlgCat (CommRingCat.of k))
      (x y : (algSpec (CommRingCat.of k)).obj (op A) ⟶ V.X),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f) := fun A x y => hf A x y
  have h := key ((algΓ (CommRingCat.of k)).obj T).unop (Lie.affinizationFactor V x)
    (Lie.affinizationFactor V y)
  calc (x * y) ≫ f
      = ((algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T ≫ Lie.affinizationFactor V x *
          (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T ≫ Lie.affinizationFactor V y) ≫
          f := by
        rw [Lie.unit_affinizationFactor, Lie.unit_affinizationFactor]
    _ = (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T ≫
          ((Lie.affinizationFactor V x * Lie.affinizationFactor V y) ≫ f) := by
        rw [← MonObj.comp_mul, Category.assoc]
    _ = (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T ≫
          ((Lie.affinizationFactor V x ≫ f) * (Lie.affinizationFactor V y ≫ f)) :=
        congrArg (fun z => (algΓAlgSpecAdjunction (CommRingCat.of k)).unit.app T ≫ z) h
    _ = (x ≫ f) * (y ≫ f) := by
        rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, Lie.unit_affinizationFactor,
          Lie.unit_affinizationFactor]

end Coordinates

section Step

variable {K W V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ} {j : K ⟶ W} {q : W ⟶ V}

/-- The commutative group of points of a group whose points commute. -/
abbrev pointsCommGroup (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ W.X),
    x * y = y * x) (T : Over (Spec (CommRingCat.of k))) : CommGroup (T ⟶ W.X) :=
  { (inferInstance : Group (T ⟶ W.X)) with mul_comm := hcomm T }

/-- A lift through the kernel inclusion of a point killed by the quotient map. -/
def kerLift (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ W.X) (hx : x ≫ q.hom.hom = 1) : T ⟶ K.X :=
  Classical.choose (SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hjq x hx)

theorem kerLift_comp (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ W.X) (hx : x ≫ q.hom.hom = 1) :
    kerLift hjq x hx ≫ j.hom.hom = x :=
  Classical.choose_spec (SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one hjq x hx)

theorem cocycleMap_aux (s : V.X ⟶ W.X) (hs : s ≫ q.hom.hom = 𝟙 V.X) :
    ((fst V.X V.X ≫ s) * (snd V.X V.X ≫ s) * ((fst V.X V.X * snd V.X V.X) ≫ s)⁻¹) ≫
      q.hom.hom = 1 := by
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc,
    Category.assoc, hs, Category.comp_id, Category.comp_id, Category.comp_id, mul_inv_cancel]

/-- The cocycle `(x, y) ↦ s(x) s(y) s(xy)⁻¹` of a section `s` of the quotient map, as a
morphism to the kernel. -/
def cocycleMap (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    (s : V.X ⟶ W.X) (hs : s ≫ q.hom.hom = 𝟙 V.X) : V.X ⊗ V.X ⟶ K.X :=
  kerLift hjq _ (cocycleMap_aux s hs)

theorem cocycleMap_comp (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    (s : V.X ⟶ W.X) (hs : s ≫ q.hom.hom = 𝟙 V.X) {T : Over (Spec (CommRingCat.of k))}
    (x y : T ⟶ V.X) :
    (lift x y ≫ cocycleMap hjq s hs) ≫ j.hom.hom = (x ≫ s) * (y ≫ s) * ((x * y) ≫ s)⁻¹ := by
  rw [Category.assoc, cocycleMap, kerLift_comp, MonObj.comp_mul, MonObj.comp_mul,
    GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, ← Category.assoc, MonObj.comp_mul,
    lift_fst, lift_snd]

section Cocycle

variable [Mono j.hom.hom] (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ W.X), x * y = y * x)
  {s : V.X ⟶ W.X} {hs : s ≫ q.hom.hom = 𝟙 V.X}
  {eV : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤))}
  {eK : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ K.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}
  {c : Fin n → k[X][X]}
  (hc : ∀ (A : Type u) [CommRing A] [Algebra k A] (a b : A) (l : Fin n),
    (vectorAffineCoordinates eK A
      (lift (linePoint eV A a) (linePoint eV A b) ≫ cocycleMap hjq s hs)).toAdd l =
      aevalAeval a b (c l))
include hcomm hc

theorem cocycle_symm (hV : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ V.X),
    x * y = y * x) (l : Fin n) (R : Type u) [CommRing R] [Algebra k R] (a b : R) :
    aevalAeval a b (c l) = aevalAeval b a (c l) := by
  have h : lift (linePoint eV R a) (linePoint eV R b) ≫ cocycleMap hjq s hs =
      lift (linePoint eV R b) (linePoint eV R a) ≫ cocycleMap hjq s hs := by
    rw [← cancel_mono j.hom.hom, cocycleMap_comp, cocycleMap_comp, hV _ (linePoint eV R a),
      hcomm _ (linePoint eV R a ≫ s)]
  rw [← hc R a b l, ← hc R b a l, h]

theorem cocycle_add (l : Fin n) (R : Type u) [CommRing R] [Algebra k R] (a b d : R) :
    aevalAeval a b (c l) + aevalAeval (a + b) d (c l) =
      aevalAeval b d (c l) + aevalAeval a (b + d) (c l) := by
  have h : (lift (linePoint eV R a) (linePoint eV R b) ≫ cocycleMap hjq s hs) *
      (lift (linePoint eV R (a + b)) (linePoint eV R d) ≫ cocycleMap hjq s hs) =
      (lift (linePoint eV R b) (linePoint eV R d) ≫ cocycleMap hjq s hs) *
      (lift (linePoint eV R a) (linePoint eV R (b + d)) ≫ cocycleMap hjq s hs) := by
    rw [← cancel_mono j.hom.hom, MonObj.mul_comp, MonObj.mul_comp, cocycleMap_comp,
      cocycleMap_comp, cocycleMap_comp, cocycleMap_comp, ← linePoint_mul, ← linePoint_mul,
      ← mul_assoc (linePoint eV R a)]
    exact @cocycle_identity _ (pointsCommGroup hcomm _) _ _ _ _ _ _
  have h2 := congrArg (fun z => (vectorAffineCoordinates eK R z).toAdd l) h
  simp only [map_mul, toAdd_mul, Pi.add_apply] at h2
  rwa [hc, hc, hc, hc] at h2

theorem cocycle_tors (hq : HasUniformPowerExponent W (ringChar k)) (l : Fin n) (R : Type u)
    [CommRing R] [Algebra k R] (a : R) :
    ∑ i ∈ Finset.range (ringChar k), aevalAeval ((i : R) * a) a (c l) = 0 := by
  have key : ∀ m : ℕ, ∃ κ : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k R)) ⟶ K.X,
      (κ ≫ j.hom.hom) * ((linePoint eV R a ^ m) ≫ s) = (linePoint eV R a ≫ s) ^ m * (1 ≫ s) ∧
      (vectorAffineCoordinates eK R κ).toAdd l =
        ∑ i ∈ Finset.range m, aevalAeval ((i : R) * a) a (c l) := by
    intro m
    induction m with
    | zero => exact ⟨1, by simp [MonObj.one_comp], by simp⟩
    | succ m ih =>
      obtain ⟨κ, h1, h2⟩ := ih
      refine ⟨κ * (lift (linePoint eV R a ^ m) (linePoint eV R a) ≫ cocycleMap hjq s hs), ?_, ?_⟩
      · rw [MonObj.mul_comp, cocycleMap_comp, pow_succ, pow_succ]
        exact @torsion_identity _ (pointsCommGroup hcomm _) _ _ _ _ _ _ h1
      · rw [map_mul, toAdd_mul, Pi.add_apply, h2, Finset.sum_range_succ, linePoint_pow, hc]
  obtain ⟨κ, h1, h2⟩ := key (ringChar k)
  rw [linePoint_pow_ringChar, hq _ (linePoint eV R a ≫ s), one_mul] at h1
  have hκ : κ = 1 := by
    rw [← cancel_mono j.hom.hom, MonObj.one_comp]
    exact mul_right_cancel (h1.trans (one_mul _).symm)
  rw [← h2, hκ, map_one, toAdd_one, Pi.zero_apply]

theorem exists_coboundaries (hV : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ V.X),
    x * y = y * x) (hq : HasUniformPowerExponent W (ringChar k)) :
    ∃ G : Fin n → k[X], ∀ (R : Type u) [CommRing R] [Algebra k R] (a b : R) (l : Fin n),
      aevalAeval a b (c l) = aeval (a + b) (G l) - aeval a (G l) - aeval b (G l) := by
  choose G hG using fun l => Langlands.Algebra.PolynomialCocycle.exists_coboundary (c l)
    (cocycle_symm hjq hcomm hc hV l) (cocycle_add hjq hcomm hc l) (cocycle_tors hjq hcomm hc hq l)
  exact ⟨G, fun R _ _ a b l => hG l R a b⟩

end Cocycle

section Correction

variable [IsAffineHom V.X.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ W.X), x * y = y * x)
  (s : V.X ⟶ W.X) (hs : s ≫ q.hom.hom = 𝟙 V.X)
  (eV : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))
  (eK : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ K.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

variable (j) in
/-- The section `s · j(P)` corrected by the polynomial map `P` with coordinates `G`. -/
def correctedSection (G : Fin n → k[X]) : V.X ⟶ W.X :=
  s * (polyMap eV eK G ≫ j.hom.hom)

variable {s eV eK}

include hjq hs in
theorem correctedSection_comp (G : Fin n → k[X]) :
    correctedSection j s eV eK G ≫ q.hom.hom = 𝟙 V.X := by
  rw [correctedSection, MonObj.mul_comp, hs, Category.assoc,
    SplitUnipotentAffineTorsor.comp_comp_eq_one hjq, mul_one]

include hcomm in
theorem correctedSection_affine (heV : IsNaturalVectorCoordinates eV)
    (heK : IsNaturalVectorCoordinates eK) {c : Fin n → k[X][X]}
    (hc : ∀ (A : Type u) [CommRing A] [Algebra k A] (a b : A) (l : Fin n),
      (vectorAffineCoordinates eK A
        (lift (linePoint eV A a) (linePoint eV A b) ≫ cocycleMap hjq s hs)).toAdd l =
        aevalAeval a b (c l))
    {G : Fin n → k[X]}
    (hG : ∀ (R : Type u) [CommRing R] [Algebra k R] (a b : R) (l : Fin n),
      aevalAeval a b (c l) = aeval (a + b) (G l) - aeval a (G l) - aeval b (G l))
    (A : Type u) [CommRing A] [Algebra k A] (x y : Lie.AffinePoints V A) :
    (x * y) ≫ correctedSection j s eV eK G =
      (x ≫ correctedSection j s eV eK G) * (y ≫ correctedSection j s eV eK G) := by
  obtain ⟨a, rfl⟩ : ∃ a, x = linePoint eV A a := ⟨_, eq_linePoint x⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = linePoint eV A b := ⟨_, eq_linePoint y⟩
  have hP : (linePoint eV A a * linePoint eV A b) ≫ polyMap eV eK G =
      (lift (linePoint eV A a) (linePoint eV A b) ≫ cocycleMap hjq s hs) *
        (linePoint eV A a ≫ polyMap eV eK G) * (linePoint eV A b ≫ polyMap eV eK G) := by
    apply (vectorAffineCoordinates eK A).injective
    apply Multiplicative.toAdd.injective
    funext l
    simp only [map_mul, toAdd_mul, Pi.add_apply]
    rw [linePoint_mul, polyMap_coord heV heK, hc, polyMap_coord heV heK, polyMap_coord heV heK,
      hG]
    ring
  rw [correctedSection, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc, hP,
    MonObj.mul_comp _ _ j.hom.hom, MonObj.mul_comp _ _ j.hom.hom, cocycleMap_comp]
  simp only [Category.assoc]
  exact @section_identity _ (pointsCommGroup hcomm _) _ _ _ _ _

end Correction

section ExtensionCoordinates

variable [Mono j.hom.hom] (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
  (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ W.X), x * y = y * x)

/-- The kernel component `w ↦ w · s(q(w))⁻¹` of a point, for a section `s`. -/
def kerMap (s : V.X ⟶ W.X) (hs : s ≫ q.hom.hom = 𝟙 V.X) : W.X ⟶ K.X :=
  kerLift hjq (𝟙 W.X * (q.hom.hom ≫ s)⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc, hs,
      Category.comp_id, mul_inv_cancel])

include hjq hcomm in
/-- A commutative extension of a vector group by a vector group, with a multiplicative section
of the quotient map, is a vector group. -/
theorem isVectorGroupOfDimension_of_section {m : ℕ} (s : V.X ⟶ W.X)
    (hs : s ≫ q.hom.hom = 𝟙 V.X)
    (hmul : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ V.X),
      (x * y) ≫ s = (x ≫ s) * (y ≫ s))
    (hK : IsVectorGroupOfDimension K n) (hV : IsVectorGroupOfDimension V m) :
    IsVectorGroupOfDimension W (n + m) := by
  obtain ⟨eK, heK⟩ := hK
  obtain ⟨eV, heV⟩ := hV
  have hκ : ∀ {T : Over (Spec (CommRingCat.of k))} (w : T ⟶ W.X),
      (w ≫ kerMap hjq s hs) ≫ j.hom.hom = w * (w ≫ q.hom.hom ≫ s)⁻¹ := by
    intro T w
    rw [Category.assoc, kerMap, kerLift_comp, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
  have hqs : ∀ {T : Over (Spec (CommRingCat.of k))} (w₁ w₂ : T ⟶ W.X),
      (w₁ * w₂) ≫ q.hom.hom ≫ s = (w₁ ≫ q.hom.hom ≫ s) * (w₂ ≫ q.hom.hom ≫ s) := by
    intro T w₁ w₂
    rw [← Category.assoc, MonObj.mul_comp, hmul, Category.assoc, Category.assoc]
  have hκmul : ∀ {T : Over (Spec (CommRingCat.of k))} (w₁ w₂ : T ⟶ W.X),
      (w₁ * w₂) ≫ kerMap hjq s hs = (w₁ ≫ kerMap hjq s hs) * (w₂ ≫ kerMap hjq s hs) := by
    intro T w₁ w₂
    rw [← cancel_mono j.hom.hom, MonObj.mul_comp _ _ j.hom.hom, hκ, hκ, hκ, hqs]
    exact @kernel_identity _ (pointsCommGroup hcomm _) _ _ _ _
  have hjκ : ∀ {T : Over (Spec (CommRingCat.of k))} (u : T ⟶ K.X) (v : T ⟶ V.X),
      (u ≫ j.hom.hom * v ≫ s) ≫ q.hom.hom = v := by
    intro T u v
    rw [MonObj.mul_comp, Category.assoc, SplitUnipotentAffineTorsor.comp_comp_eq_one hjq,
      Category.assoc, hs, Category.comp_id, one_mul]
  have hκj : ∀ {T : Over (Spec (CommRingCat.of k))} (u : T ⟶ K.X) (v : T ⟶ V.X),
      (u ≫ j.hom.hom * v ≫ s) ≫ kerMap hjq s hs = u := by
    intro T u v
    rw [← cancel_mono j.hom.hom, hκ, ← Category.assoc _ q.hom.hom, hjκ, mul_inv_cancel_right]
  have happ : ∀ (A : Type u) [AddCommMonoid A] (u₁ u₂ : Fin n → A) (v₁ v₂ : Fin m → A),
      Fin.append (u₁ + u₂) (v₁ + v₂) = Fin.append u₁ v₁ + Fin.append u₂ v₂ := by
    intro A _ u₁ u₂ v₁ v₂
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  refine ⟨fun T =>
    { toFun := fun w => Multiplicative.ofAdd
        (Fin.append (eK T (w ≫ kerMap hjq s hs)).toAdd (eV T (w ≫ q.hom.hom)).toAdd)
      invFun := fun f =>
        (eK T).symm (Multiplicative.ofAdd fun i => f.toAdd (Fin.castAdd m i)) ≫ j.hom.hom *
          (eV T).symm (Multiplicative.ofAdd fun i => f.toAdd (Fin.natAdd n i)) ≫ s
      left_inv := fun w => ?_
      right_inv := fun f => ?_
      map_mul' := fun w₁ w₂ => ?_ }, ?_⟩
  · simp only [toAdd_ofAdd, Fin.append_left, Fin.append_right, ofAdd_toAdd,
      MulEquiv.symm_apply_apply]
    rw [hκ, Category.assoc, inv_mul_cancel_right]
  · simp only [hκj, hjκ, MulEquiv.apply_symm_apply, toAdd_ofAdd, Fin.append_castAdd_natAdd,
      ofAdd_toAdd]
  · rw [hκmul, MonObj.mul_comp _ _ q.hom.hom, MulEquiv.map_mul, MulEquiv.map_mul, toAdd_mul, toAdd_mul, happ]
    rfl
  · intro T T' b w
    funext i
    simp only [MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd, Category.assoc]
    rw [heK, heV]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

end ExtensionCoordinates

end Step

end SplitCommutativeVector

open SplitCommutativeVector in
/-- The induction step: a commutative extension of a one-dimensional vector group by an
`n`-dimensional vector group, killed by `char k` and with a section of the quotient map, is an
`(n + 1)`-dimensional vector group. -/
theorem isVectorGroupOfDimension_succ {k : Type u} [Field k]
    {K W V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ} (j : K ⟶ W) (q : W ⟶ V)
    [Mono j.hom.hom] (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ W.X), x * y = y * x)
    (hq : HasUniformPowerExponent W (ringChar k)) (s : V.X ⟶ W.X) (hs : s ≫ q.hom.hom = 𝟙 V.X)
    (hK : IsVectorGroupOfDimension K n) (hV : IsVectorGroupOfDimension V 1) :
    IsVectorGroupOfDimension W (n + 1) := by
  have := hV.isAffineHom_overRing
  obtain ⟨eV, heV⟩ := id hV
  obtain ⟨eK, heK⟩ := id hK
  obtain ⟨c, hc⟩ := exists_bivariate heV heK (cocycleMap hjq s hs)
  obtain ⟨G, hG⟩ :=
    exists_coboundaries hjq hcomm hc (fun T x y => (hV.points_commute x y).eq) hq
  exact isVectorGroupOfDimension_of_section hjq hcomm (correctedSection j s eV eK G)
    (correctedSection_comp hjq hs G)
    (fun T x y => comp_mul_of_affine _ (correctedSection_affine hjq hcomm hs heV heK hc hG) x y)
    hK hV

/-- A commutative affine group over a field with a split series of length `n`, all of whose
points are killed by `char k`, is a vector group of dimension `n`. -/
theorem isVectorGroupOfDimension_of_hasSplitSeries_of_exponent {k : Type u} [Field k] {n : ℕ}
    (W : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom W.X.hom]
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ W.X), x * y = y * x)
    (hq : HasUniformPowerExponent W (ringChar k)) (hW : HasSplitSeries n W) :
    IsVectorGroupOfDimension W n := by
  induction n generalizing W with
  | zero => exact hW.isVectorGroupOfDimension_zero
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, -, -, -, hqq, hV, hK⟩ := hW
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have : IsAffineHom K.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    have hKcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ K.X), x * y = y * x := by
      intro T x y
      rw [← cancel_mono j.hom.hom, MonObj.mul_comp, MonObj.mul_comp, hcomm]
    obtain ⟨s, hs, -, -⟩ := SplitSeriesDecomposition.exists_section_isIso_mul j q hj hqq hV hK
    exact isVectorGroupOfDimension_succ j q hqq.2.2.2 hcomm hq s hs
      (ih K hKcomm (hq.of_mono j) hK) hV

/-- A commutative affine split unipotent group over a field, all of whose points are killed by
`char k`, is a vector group. -/
theorem isVectorGroup_of_isSplitUnipotent_of_exponent {k : Type u} [Field k]
    (W : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom W.X.hom] [IsCommMonObj W.X]
    (hW : IsSplitUnipotent W) (hq : HasUniformPowerExponent W (ringChar k)) :
    IsVectorGroup W := by
  obtain ⟨n, hn⟩ := hW
  exact ⟨n, isVectorGroupOfDimension_of_hasSplitSeries_of_exponent W
    (fun T x y => (Hom.commMonoid (X := T) (M := W.X)).mul_comm x y) hq hn⟩

end Langlands.GroupScheme.RelativeRoot
