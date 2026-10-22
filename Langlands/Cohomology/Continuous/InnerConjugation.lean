import Langlands.Cohomology.Continuous.EquivalenceTransport
import Mathlib.Tactic.Group

universe u v w

open CategoryTheory

namespace Langlands.Continuous

section Generic

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Equality of group maps and pointwise equality of coefficient maps give equal cochain maps.
The coefficient ring and the groups may lie in independent universes; the coefficient carriers
lie in `max v w`, as Mathlib's standard resolution requires. -/
theorem cochainsMap_congr_of_apply {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {X : TopRep.{max v w} k G} {Y : TopRep.{max v w} k H}
    {φ ψ : H →ₜ* G}
    (h : φ = ψ) (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ X ⟶ Y)
    (hfg : ∀ x : X, f.hom x = g.hom x) :
    ContinuousCohomology.cochainsMap φ f = ContinuousCohomology.cochainsMap ψ g := by
  subst ψ
  have hfg' : f = g := by
    ext x
    exact hfg x
  subst g
  rfl

/-- The cohomology version of `cochainsMap_congr_of_apply`. -/
theorem map_congr_of_apply {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {X : TopRep.{max v w} k G} {Y : TopRep.{max v w} k H}
    {φ ψ : H →ₜ* G}
    (h : φ = ψ) (f : TopRep.res φ X ⟶ Y) (g : TopRep.res ψ X ⟶ Y)
    (hfg : ∀ x : X, f.hom x = g.hom x) (n : ℕ) :
    ContinuousCohomology.map φ f n = ContinuousCohomology.map ψ g n := by
  rw [ContinuousCohomology.map, ContinuousCohomology.map,
    cochainsMap_congr_of_apply h f g hfg]

/-- Inner conjugation `c_a(g) = a * g * a⁻¹` as a continuous group homomorphism. -/
def innerConjugation (a : G) : G →ₜ* G where
  toFun g := a * g * a⁻¹
  map_one' := by simp
  map_mul' g h := by group
  continuous_toFun := IsTopologicalGroup.continuous_conj a

@[simp]
theorem innerConjugation_apply (a g : G) : innerConjugation a g = a * g * a⁻¹ := rfl

theorem innerConjugation_one : innerConjugation (1 : G) = ContinuousMonoidHom.id G := by
  ext g
  simp

theorem innerConjugation_mul (a b : G) :
    innerConjugation (a * b) = (innerConjugation a).comp (innerConjugation b) := by
  ext g
  change a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹
  group

/-- Inner conjugation `g ↦ a * g * a⁻¹` as a continuous group automorphism, with inverse
`g ↦ a⁻¹ * g * a`. -/
def innerConjugationEquiv (a : G) : G ≃ₜ* G where
  toFun g := a * g * a⁻¹
  invFun g := a⁻¹ * g * a
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]
  map_mul' g h := by group
  continuous_toFun := IsTopologicalGroup.continuous_conj a
  continuous_invFun := by simpa using IsTopologicalGroup.continuous_conj a⁻¹

@[simp]
theorem innerConjugationEquiv_apply (a g : G) : innerConjugationEquiv a g = a * g * a⁻¹ :=
  rfl

@[simp]
theorem innerConjugationEquiv_symm_apply (a g : G) :
    (innerConjugationEquiv a).symm g = a⁻¹ * g * a := rfl

/-- The continuous homomorphism underlying `innerConjugationEquiv a` is `innerConjugation a`. -/
theorem innerConjugationEquiv_toContinuousMonoidHom (a : G) :
    (innerConjugationEquiv a : G →ₜ* G) = innerConjugation a := rfl

variable (A : TopRep.{max v w} k G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The action of a product: `A.ρ g (A.ρ h x) = A.ρ (g * h) x`. -/
theorem ρ_apply_ρ_apply (g h : G) (x : A) : A.ρ g (A.ρ h x) = A.ρ (g * h) x := by
  rw [map_mul, mul_apply_eq_comp]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The compatibility of the inner automorphism `c_a` with the coefficient map `A.ρ a⁻¹`:
`A.ρ a⁻¹ (A.ρ (a * g * a⁻¹) x) = A.ρ g (A.ρ a⁻¹ x)`. -/
theorem innerConjugation_compatible (a g : G) (x : A) :
    A.ρ a⁻¹ (A.ρ (a * g * a⁻¹) x) = A.ρ g (A.ρ a⁻¹ x) := by
  rw [ρ_apply_ρ_apply, ρ_apply_ρ_apply, show a⁻¹ * (a * g * a⁻¹) = g * a⁻¹ by group]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The compatibility of the inner automorphism `c_a` with the coefficient map `A.ρ a`. -/
theorem innerConjugation_compatible_inv (a g : G) (x : A) :
    A.ρ a (A.ρ g x) = A.ρ (a * g * a⁻¹) (A.ρ a x) := by
  rw [ρ_apply_ρ_apply, ρ_apply_ρ_apply, show a * g * a⁻¹ * a = a * g by group]

/-- The equivariant coefficient morphism `res (c_a) A ⟶ A` given by `A.ρ a⁻¹`. -/
def innerConjugationCoefficient (a : G) :
    TopRep.res (innerConjugation a : G →* G) A ⟶ A :=
  TopRep.ofHom
    { toContinuousLinearMap := A.ρ a⁻¹
      isIntertwining' g := by
        ext x
        exact innerConjugation_compatible A a g x }

@[simp]
theorem innerConjugationCoefficient_hom_apply (a : G) (x : A) :
    (innerConjugationCoefficient A a).hom x = A.ρ a⁻¹ x := rfl

/-- The equivariant inverse coefficient morphism `A ⟶ res (c_a) A` given by `A.ρ a`. -/
def innerConjugationCoefficientInv (a : G) :
    A ⟶ TopRep.res (innerConjugation a : G →* G) A :=
  TopRep.ofHom
    { toContinuousLinearMap := A.ρ a
      isIntertwining' g := by
        ext x
        exact innerConjugation_compatible_inv A a g x }

@[simp]
theorem innerConjugationCoefficientInv_hom_apply (a : G) (x : A) :
    (innerConjugationCoefficientInv A a).hom x = A.ρ a x := rfl

/-- The coefficient isomorphism `res (c_a) A ≅ A` with forward map `A.ρ a⁻¹` and inverse
map `A.ρ a`. -/
def innerConjugationCoefficientIso (a : G) :
    TopRep.res (innerConjugation a : G →* G) A ≅ A where
  hom := innerConjugationCoefficient A a
  inv := innerConjugationCoefficientInv A a
  hom_inv_id := by
    ext x
    change A.ρ a (A.ρ a⁻¹ x) = x
    rw [ρ_apply_ρ_apply, mul_inv_cancel, map_one, one_apply_eq_self]
  inv_hom_id := by
    ext x
    change A.ρ a⁻¹ (A.ρ a x) = x
    rw [ρ_apply_ρ_apply, inv_mul_cancel, map_one, one_apply_eq_self]

@[simp]
theorem innerConjugationCoefficientIso_hom (a : G) :
    (innerConjugationCoefficientIso A a).hom = innerConjugationCoefficient A a := rfl

@[simp]
theorem innerConjugationCoefficientIso_inv (a : G) :
    (innerConjugationCoefficientIso A a).inv = innerConjugationCoefficientInv A a := rfl

/-- The maps between the terms of the standard resolution induced by `c_a` and `A.ρ a⁻¹`. -/
def innerConjugationResolution (a : G) (i : ℕ) :
    TopRep.res (innerConjugation a : G →* G) (TopRep.resolutionX A i) ⟶
      TopRep.resolutionX A i :=
  ContinuousCohomology.resolutionMap (innerConjugation a) (innerConjugationCoefficient A a) i

theorem innerConjugationResolution_zero_apply (a : G) (x : A) :
    (innerConjugationResolution A a 0).hom x = A.ρ a⁻¹ x := rfl

theorem innerConjugationResolution_succ_apply (a : G) (i : ℕ)
    (F : TopRep.resolutionX A (i + 1)) (g : G) :
    (innerConjugationResolution A a (i + 1)).hom F g =
      (innerConjugationResolution A a i).hom (F (a * g * a⁻¹)) := rfl

/-- The inner-conjugation cochain map `σ_a` on Mathlib's homogeneous continuous cochains. -/
def innerConjugationCochains (a : G) :
    TopRep.homogeneousCochains A ⟶ TopRep.homogeneousCochains A :=
  ContinuousCohomology.cochainsMap (innerConjugation a) (innerConjugationCoefficient A a)

theorem innerConjugationCochains_eq (a : G) :
    innerConjugationCochains A a =
      ContinuousCohomology.cochainsMap (innerConjugation a)
        (innerConjugationCoefficient A a) := rfl

theorem innerConjugationCochains_f_apply (a : G) (i : ℕ)
    (σ : (TopRep.homogeneousCochains A).X i) :
    (((innerConjugationCochains A a).f i).hom σ).1 =
      (innerConjugationResolution A a (i + 1)).hom σ.1 := rfl

theorem innerConjugationCochains_zero_apply (a : G)
    (σ : (TopRep.homogeneousCochains A).X 0) (g : G) :
    (((innerConjugationCochains A a).f 0).hom σ).1 g = A.ρ a⁻¹ (σ.1 (a * g * a⁻¹)) := rfl

theorem innerConjugationCochains_one_apply (a : G)
    (σ : (TopRep.homogeneousCochains A).X 1) (g h : G) :
    (((innerConjugationCochains A a).f 1).hom σ).1 g h =
      A.ρ a⁻¹ (σ.1 (a * g * a⁻¹) (a * h * a⁻¹)) := rfl

/-- The inner-conjugation map `σ_a : Hⁿ(G, A) ⟶ Hⁿ(G, A)` on Mathlib's continuous
cohomology. -/
noncomputable def innerConjugationMap (a : G) (n : ℕ) :
    continuousCohomology n A ⟶ continuousCohomology n A :=
  ContinuousCohomology.map (innerConjugation a) (innerConjugationCoefficient A a) n

theorem innerConjugationMap_eq (a : G) (n : ℕ) :
    innerConjugationMap A a n =
      ContinuousCohomology.map (innerConjugation a) (innerConjugationCoefficient A a) n := rfl

theorem innerConjugationMap_eq_homologyMap (a : G) (n : ℕ) :
    innerConjugationMap A a n =
      HomologicalComplex.homologyMap (innerConjugationCochains A a) n := rfl

/-- The inner-conjugation map `σ_a` on Mathlib's continuous `n`-cocycles. -/
noncomputable def innerConjugationCocycles (a : G) (n : ℕ) :
    ContinuousCohomology.cocycles A n ⟶ ContinuousCohomology.cocycles A n :=
  ContinuousCohomology.cocyclesMap (innerConjugation a) (innerConjugationCoefficient A a) n

theorem innerConjugationCocycles_eq_cyclesMap (a : G) (n : ℕ) :
    innerConjugationCocycles A a n =
      HomologicalComplex.cyclesMap (innerConjugationCochains A a) n := rfl

@[reassoc]
theorem π_innerConjugationMap (a : G) (n : ℕ) :
    ContinuousCohomology.π A n ≫ innerConjugationMap A a n =
      innerConjugationCocycles A a n ≫ ContinuousCohomology.π A n :=
  ContinuousCohomology.π_map _ _ n

theorem innerConjugationCochains_one :
    innerConjugationCochains A (1 : G) = 𝟙 (TopRep.homogeneousCochains A) := by
  rw [innerConjugationCochains, ← ContinuousCohomology.cochainsMap_id A]
  apply cochainsMap_congr_of_apply innerConjugation_one
  intro x
  change A.ρ (1 : G)⁻¹ x = x
  simp

theorem innerConjugationCocycles_one (n : ℕ) :
    innerConjugationCocycles A (1 : G) n = 𝟙 (ContinuousCohomology.cocycles A n) := by
  rw [innerConjugationCocycles_eq_cyclesMap, innerConjugationCochains_one]
  exact HomologicalComplex.cyclesMap_id _ _

theorem innerConjugationMap_one (n : ℕ) :
    innerConjugationMap A (1 : G) n = 𝟙 (continuousCohomology n A) := by
  rw [innerConjugationMap_eq_homologyMap, innerConjugationCochains_one]
  exact HomologicalComplex.homologyMap_id _ _

@[reassoc]
theorem innerConjugationCochains_mul (a b : G) :
    innerConjugationCochains A (a * b) =
      innerConjugationCochains A a ≫ innerConjugationCochains A b := by
  rw [innerConjugationCochains, innerConjugationCochains, innerConjugationCochains,
    ← ContinuousCohomology.cochainsMap_comp]
  apply cochainsMap_congr_of_apply (innerConjugation_mul a b)
  intro x
  change A.ρ (a * b)⁻¹ x = A.ρ b⁻¹ (A.ρ a⁻¹ x)
  rw [ρ_apply_ρ_apply, mul_inv_rev]

@[reassoc]
theorem innerConjugationCocycles_mul (a b : G) (n : ℕ) :
    innerConjugationCocycles A (a * b) n =
      innerConjugationCocycles A a n ≫ innerConjugationCocycles A b n := by
  rw [innerConjugationCocycles_eq_cyclesMap, innerConjugationCocycles_eq_cyclesMap,
    innerConjugationCocycles_eq_cyclesMap, innerConjugationCochains_mul,
    HomologicalComplex.cyclesMap_comp]

@[reassoc]
theorem innerConjugationMap_mul (a b : G) (n : ℕ) :
    innerConjugationMap A (a * b) n =
      innerConjugationMap A a n ≫ innerConjugationMap A b n := by
  rw [innerConjugationMap_eq_homologyMap, innerConjugationMap_eq_homologyMap,
    innerConjugationMap_eq_homologyMap, innerConjugationCochains_mul,
    HomologicalComplex.homologyMap_comp]

/-- The inner-conjugation cochain isomorphism, with inverse the cochain map for `a⁻¹`. -/
def innerConjugationCochainsIso (a : G) :
    TopRep.homogeneousCochains A ≅ TopRep.homogeneousCochains A where
  hom := innerConjugationCochains A a
  inv := innerConjugationCochains A a⁻¹
  hom_inv_id := by
    rw [← innerConjugationCochains_mul, mul_inv_cancel, innerConjugationCochains_one]
  inv_hom_id := by
    rw [← innerConjugationCochains_mul, inv_mul_cancel, innerConjugationCochains_one]

@[simp]
theorem innerConjugationCochainsIso_hom (a : G) :
    (innerConjugationCochainsIso A a).hom = innerConjugationCochains A a := rfl

@[simp]
theorem innerConjugationCochainsIso_inv (a : G) :
    (innerConjugationCochainsIso A a).inv = innerConjugationCochains A a⁻¹ := rfl

/-- The inner-conjugation isomorphism `σ_a` of `Hⁿ(G, A)`, with inverse `σ_{a⁻¹}`. -/
noncomputable def innerConjugationIso (a : G) (n : ℕ) :
    continuousCohomology n A ≅ continuousCohomology n A where
  hom := innerConjugationMap A a n
  inv := innerConjugationMap A a⁻¹ n
  hom_inv_id := by
    rw [← innerConjugationMap_mul, mul_inv_cancel, innerConjugationMap_one]
  inv_hom_id := by
    rw [← innerConjugationMap_mul, inv_mul_cancel, innerConjugationMap_one]

@[simp]
theorem innerConjugationIso_hom (a : G) (n : ℕ) :
    (innerConjugationIso A a n).hom = innerConjugationMap A a n := rfl

@[simp]
theorem innerConjugationIso_inv (a : G) (n : ℕ) :
    (innerConjugationIso A a n).inv = innerConjugationMap A a⁻¹ n := rfl

theorem innerConjugationIso_one (n : ℕ) :
    innerConjugationIso A (1 : G) n = Iso.refl (continuousCohomology n A) := by
  ext : 1
  exact innerConjugationMap_one A n

theorem innerConjugationIso_mul (a b : G) (n : ℕ) :
    innerConjugationIso A (a * b) n = innerConjugationIso A a n ≪≫ innerConjugationIso A b n := by
  ext : 1
  exact innerConjugationMap_mul A a b n

/-- Inner conjugation commutes with the cochain maps of an equivariant coefficient morphism. -/
@[reassoc]
theorem innerConjugationCochains_naturality {A B : TopRep.{max v w} k G} (f : A ⟶ B) (a : G) :
    innerConjugationCochains A a ≫
        ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f =
      ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f ≫
        innerConjugationCochains B a := by
  refine (ContinuousCohomology.cochainsMap_comp (innerConjugation a) (ContinuousMonoidHom.id G)
      (innerConjugationCoefficient A a) (Z := B) f).symm.trans
    (Eq.trans ?_ (ContinuousCohomology.cochainsMap_comp (ContinuousMonoidHom.id G)
      (innerConjugation a) (X := A) (Y := B) f (innerConjugationCoefficient B a)))
  apply cochainsMap_congr_of_apply (by ext g; rfl)
  intro x
  change f.hom (A.ρ a⁻¹ x) = B.ρ a⁻¹ (f.hom x)
  exact TopRep.hom_comm_apply f a⁻¹ x

/-- Inner conjugation commutes with the cohomology maps of an equivariant coefficient
morphism. -/
@[reassoc]
theorem innerConjugationMap_naturality {A B : TopRep.{max v w} k G} (f : A ⟶ B) (a : G) (n : ℕ) :
    innerConjugationMap A a n ≫ ContinuousCohomology.map (ContinuousMonoidHom.id G) f n =
      ContinuousCohomology.map (ContinuousMonoidHom.id G) f n ≫ innerConjugationMap B a n := by
  exact ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun φ => HomologicalComplex.homologyMap φ n)
      (innerConjugationCochains_naturality f a))).trans
    (HomologicalComplex.homologyMap_comp _ _ n)

end Generic

section Comparison

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : TopRep.{u} k G)

/-- In a common universe, the Library transport isomorphism along `innerConjugationEquiv a`
and `innerConjugationCoefficientIso A a` is the inner-conjugation isomorphism. -/
theorem continuousCohomologyIso_innerConjugation (a : G) (q : ℕ) :
    continuousCohomologyIso (innerConjugationEquiv a) (innerConjugationCoefficientIso A a) q =
      innerConjugationIso A a q := by
  ext : 1
  rfl

end Comparison

end Langlands.Continuous
