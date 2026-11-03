import Langlands.GroupScheme.Rational.OrderedProductPoints

/-! # Factor maps and monomorphisms for actual ordered multiplication -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}}

section FactorMaps

variable {I : Type v} [Finite I] {H R : I → GroupScheme B}

/-- The actual scheme morphism induced by a finite family of factor
homomorphisms, with no restriction tying the index universe to the base. -/
def productFactorMap (p : ∀ i, H i ⟶ R i) : (∏ᶜ H).X ⟶ (∏ᶜ R).X :=
  (CategoryTheory.Limits.Pi.map p).hom.hom

/-- Each projection of the product factor map is the corresponding factor map. -/
@[reassoc (attr := simp)]
theorem productFactorMap_π (p : ∀ i, H i ⟶ R i) (i : I) :
    productFactorMap p ≫ (Pi.π R i).hom.hom =
      (Pi.π H i).hom.hom ≫ (p i).hom.hom := by
  have h := congrArg (fun f => f.hom.hom) (Pi.map_π p i)
  change productFactorMap p ≫ (Pi.π R i).hom.hom =
    (Pi.π H i).hom.hom ≫ (p i).hom.hom at h
  exact h

/-- The induced scheme map applies the factor homomorphisms to coordinates. -/
theorem finiteProductPointsEquiv_productFactorMap (p : ∀ i, H i ⟶ R i)
    {T : Over B} (x : T ⟶ (∏ᶜ H).X) :
    finiteProductPointsEquiv R T (x ≫ productFactorMap p) =
      fun i => finiteProductPointsEquiv H T x i ≫ (p i).hom.hom := by
  funext i
  simp only [finiteProductPointsEquiv_apply, Category.assoc, productFactorMap_π]

/-- Reassembling after factor homomorphisms equals mapping the reassembled point. -/
theorem finiteProductPointsEquiv_symm_productFactorMap (p : ∀ i, H i ⟶ R i)
    {T : Over B} (x : ∀ i, T ⟶ (H i).X) :
    (finiteProductPointsEquiv H T).symm x ≫ productFactorMap p =
      (finiteProductPointsEquiv R T).symm (fun i => x i ≫ (p i).hom.hom) := by
  apply (finiteProductPointsEquiv R T).injective
  rw [finiteProductPointsEquiv_productFactorMap, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

end FactorMaps

section OrderedMaps

variable {n : ℕ} {G Q : GroupScheme B}
    {H R : Fin n → GroupScheme B}

/-- A commuting family of factor maps and an ambient group homomorphism give
a commuting square of actual ordered multiplication morphisms. -/
theorem orderedMultiplication_map (j : ∀ i, H i ⟶ G) (k : ∀ i, R i ⟶ Q)
    (q : G ⟶ Q) (p : ∀ i, H i ⟶ R i)
    (h : ∀ i, j i ≫ q = p i ≫ k i) :
    productFactorMap p ≫ orderedMultiplication k =
      orderedMultiplication j ≫ q.hom.hom := by
  have hj : orderedMultiplication j =
      orderedPoints j (finiteProductPointsEquiv H (∏ᶜ H).X (𝟙 _)) := by
    simpa only [Category.id_comp] using comp_orderedMultiplication j (𝟙 _)
  rw [comp_orderedMultiplication, hj, orderedPoints_map j k q p h]
  apply congrArg (orderedPoints k)
  funext i
  simpa only [finiteProductPointsEquiv_apply, Category.id_comp]
    using productFactorMap_π p i

/-- Monomorphy of the scheme multiplication map is equivalent to injectivity
of ordered factorization on every test scheme. -/
theorem mono_orderedMultiplication_iff (j : ∀ i, H i ⟶ G) :
    Mono (orderedMultiplication j) ↔
      ∀ T : Over B, Function.Injective (orderedPoints j (T := T)) := by
  constructor
  · intro h T x y hxy
    have heq : (finiteProductPointsEquiv H T).symm x ≫ orderedMultiplication j =
        (finiteProductPointsEquiv H T).symm y ≫ orderedMultiplication j := by
      simpa only [finiteProductPointsEquiv_symm_orderedMultiplication] using hxy
    have hcoord := (cancel_mono (orderedMultiplication j)).mp heq
    exact (finiteProductPointsEquiv H T).symm.injective hcoord
  · intro h
    constructor
    intro T x y hxy
    apply (finiteProductPointsEquiv H T).injective
    apply h T
    simpa only [← comp_orderedMultiplication] using hxy

end OrderedMaps

section BoundaryCases

variable {G : GroupScheme B}

/-- The actual empty ordered product is the unit morphism. -/
@[simp]
theorem orderedMultiplication_zero {H : Fin 0 → GroupScheme B}
    (j : ∀ i, H i ⟶ G) : orderedMultiplication j = 1 := by
  simp [orderedMultiplication]

/-- Empty ordered point multiplication gives the unit on every test scheme. -/
@[simp]
theorem orderedPoints_zero {H : Fin 0 → GroupScheme B}
    (j : ∀ i, H i ⟶ G) {T : Over B} (x : ∀ i, T ⟶ (H i).X) :
    orderedPoints j x = 1 := by
  simp [orderedPoints]

/-- Singleton ordered point multiplication is the original factor map. -/
@[simp]
theorem orderedPoints_one {H : Fin 1 → GroupScheme B}
    (j : ∀ i, H i ⟶ G) {T : Over B} (x : ∀ i, T ⟶ (H i).X) :
    orderedPoints j x = x 0 ≫ (j 0).hom.hom := by
  simp [orderedPoints, List.ofFn_succ]

/-- The singleton scheme multiplication is the unique projection followed by
the original factor homomorphism. -/
@[simp]
theorem orderedMultiplication_one {H : Fin 1 → GroupScheme B}
    (j : ∀ i, H i ⟶ G) :
    orderedMultiplication j = (Pi.π H 0).hom.hom ≫ (j 0).hom.hom := by
  simp [orderedMultiplication, List.ofFn_succ]

/-- In the empty case the product map is an isomorphism exactly when the
target has only the unit on every test scheme. -/
theorem isIso_orderedMultiplication_zero_iff {H : Fin 0 → GroupScheme B}
    (j : ∀ i, H i ⟶ G) :
    IsIso (orderedMultiplication j) ↔
      ∀ T : Over B, Subsingleton (T ⟶ G.X) := by
  rw [isIso_orderedMultiplication_iff]
  constructor
  · intro h T
    constructor
    intro x y
    obtain ⟨a, ha⟩ := (h T).2 x
    obtain ⟨b, hb⟩ := (h T).2 y
    rw [orderedPoints_zero] at ha hb
    exact ha.symm.trans hb
  · intro h T
    let := h T
    exact Function.bijective_of_subsingleton' _

end BoundaryCases

end Langlands.GroupScheme.RelativeRoot
