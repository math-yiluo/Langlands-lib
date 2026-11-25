/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Covering an abelian variety by opens on which a unit is not an `r`-th power

Let `E` be an abelian variety of positive dimension over a field and `2 ≤ r`. We cover `E` by
finitely many affine opens `U i`, each carrying a unit `f i ∈ Γ(E, U i)` which is not an `r`-th
power in the function field of `E`.

For a point `x`, choose an affine open `V ∋ x` and a closed point `y ∈ V` different from `x`.
Prime avoidance gives `a ∈ Γ(E, V)` which is invertible at `x` and lies in `𝔪_y \ 𝔪_y ^ 2` in the
local ring `𝒪_{E,y}`. This local ring is regular, hence a unique factorization domain, hence
integrally closed, so `a` is not an `r`-th power in its fraction field, the function field of `E`.
The opens `D(a) ∋ x` cover `E`, which is quasi-compact.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.isIntegral`: an abelian variety is an integral scheme.
- `AlgebraicGeometry.Scheme.exists_isAffineOpen_isUnit_not_exists_pow`: a point of a regular
  integral Jacobson scheme with at least two points has an affine open neighbourhood with a unit
  which is not an `n`-th power in the function field, for `2 ≤ n`.
- `AlgebraicGeometry.IsAbelianVariety.exists_finite_cover_units_not_pow`: the cover above.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing Opposite

/-- A noetherian local ring whose maximal ideal equals its square is a field, i.e. its maximal
ideal is zero (Nakayama's lemma). -/
theorem IsLocalRing.maximalIdeal_eq_bot_of_le_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _)
    (by rwa [smul_eq_mul, ← pow_two]) (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge

namespace AlgebraicGeometry

/-- An abelian variety is an integral scheme: it is smooth over a field, hence regular and locally
noetherian, and it is connected. -/
instance IsAbelianVariety.isIntegral {K : Type u} [Field K] (E : Over (Spec (.of K)))
    [IsAbelianVariety E] : IsIntegral E.left :=
  have := IsRegular.of_smooth E.hom
  have := LocallyOfFiniteType.isLocallyNoetherian E.hom
  IsRegular.isIntegral E.left

/-- In a Jacobson scheme with at least two points, every affine open `V` and point `x ∈ V`
admit a closed point `y ∈ V` different from `x`, provided the scheme is connected. -/
theorem Scheme.exists_isClosed_mem_ne {X : Scheme.{u}} [JacobsonSpace X] [ConnectedSpace X]
    [Nontrivial X] {V : X.Opens} {x : X} (hxV : x ∈ V) :
    ∃ y ∈ V, IsClosed ({y} : Set X) ∧ y ≠ x := by
  by_contra! h
  obtain ⟨z, hzV, hz⟩ := nonempty_inter_closedPoints ⟨x, hxV⟩ V.isOpen.isLocallyClosed
  obtain rfl := h z hzV hz
  have hV : (V : Set X) = {z} := by
    refine (Set.Subset.antisymm ?_ (by simpa using hzV))
    calc (V : Set X) ⊆ closure (V ∩ closedPoints X) := by
          rw [JacobsonSpace.closure_inter_closedPoints_eq_closure V.isOpen.isLocallyClosed]
          exact subset_closure
      _ ⊆ closure {z} := closure_mono fun w hw ↦ h w hw.1 hw.2
      _ = {z} := hz.closure_eq
  obtain ⟨w, hw⟩ := exists_ne z
  have := (IsClopen.eq_univ ⟨hz, hV ▸ V.isOpen⟩ ⟨z, rfl⟩).symm ▸ Set.mem_univ w
  exact hw this

/-- Let `X` be a regular integral Jacobson scheme with at least two points, `x ∈ X` and `2 ≤ n`.
Then `x` has an affine open neighbourhood `U` with a unit `f ∈ Γ(X, U)` which is not an `n`-th
power in the function field of `X`.

Choose an affine open `V ∋ x` and a closed point `y ∈ V` different from `x`. By prime avoidance
there is `a ∈ Γ(X, V)` invertible at `x` whose germ at `y` lies in `𝔪_y \ 𝔪_y ^ 2`; then
`U = D(a)` and the restriction of `a` work, as `𝒪_{X,y}` is integrally closed. -/
theorem Scheme.exists_isAffineOpen_isUnit_not_exists_pow (X : Scheme.{u}) [IsIntegral X]
    [IsRegular X] [JacobsonSpace X] [Nontrivial X] (x : X) {n : ℕ} (hn : 2 ≤ n) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : Γ(X, U)), IsAffineOpen U ∧ IsUnit f ∧
      haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
      ¬ ∃ u : X.functionField, u ^ n = X.germToFunctionField U f := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨y, hyV, hyc, hyx⟩ := Scheme.exists_isClosed_mem_ne hxV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : IsIntegrallyClosed (X.presheaf.stalk y) :=
    have := IsRegular.uniqueFactorizationMonoid_stalk y
    inferInstance
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨y, hyV⟩
  have hMy := IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk y)
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  have hMx := IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hyx' : ¬ (maximalIdeal (X.presheaf.stalk y)).under Γ(X, V) ≤
      (maximalIdeal (X.presheaf.stalk x)).under Γ(X, V) := by
    intro hle
    have := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hyc
    rw [hMy, hMx] at hle
    have heq := this.eq_of_le Ideal.IsPrime.ne_top' hle
    have h := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    rw [PrimeSpectrum.ext heq, hV.fromSpec_primeIdealOf ⟨x, hxV⟩] at h
    exact hyx h.symm
  have hsq : ¬ (maximalIdeal (X.presheaf.stalk y)).under Γ(X, V) ≤
      (maximalIdeal (X.presheaf.stalk y) ^ 2).under Γ(X, V) := by
    intro hle
    refine hyx' ?_
    have hbot : maximalIdeal (X.presheaf.stalk y) = ⊥ := by
      refine maximalIdeal_eq_bot_of_le_sq ?_
      conv_lhs =>
        rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
          (X.presheaf.stalk y), ← hMy]
      exact (Ideal.map_mono hle).trans Ideal.map_comap_le
    rw [hbot, Ideal.under, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot (algebraMap Γ(X, V) (X.presheaf.stalk y))).mp
        (germ_injective_of_isIntegral X y hyV)]
    exact bot_le
  obtain ⟨a, haM, ha⟩ := Set.not_subset.mp (mt Ideal.subset_union.mp (not_or.mpr ⟨hyx', hsq⟩))
  rw [Set.mem_union, not_or] at ha
  have hxa : x ∈ X.basicOpen a := by
    rw [Scheme.mem_basicOpen X a x hxV]
    by_contra h
    exact ha.1 h
  refine ⟨X.basicOpen a, hxa, X.presheaf.map (homOfLE (X.basicOpen_le a)).op a, hV.basicOpen a,
    X.toRingedSpace.isUnit_res_basicOpen a, ?_⟩
  rw [Scheme.germToFunctionField, X.presheaf.germ_res_apply, ← Scheme.germToFunctionField,
    ← X.algebraMap_germ_eq_germToFunctionField hyV]
  exact IsIntegrallyClosed.not_exists_pow_eq_algebraMap (R := X.presheaf.stalk y)
    (P := maximalIdeal _) haM ha.2 hn

/-- Blueprint `sk-rem-sf-fullcd-scope`: an abelian variety `E` of positive dimension over a
field is covered by finitely many affine opens `U i`, each carrying a unit `f i ∈ Γ(E, U i)` which
is not an `r`-th power in the function field of `E`, for `2 ≤ r`.

`E` is integral, regular and Jacobson, and it has at least two points since its dimension is
positive; so `AlgebraicGeometry.Scheme.exists_isAffineOpen_isUnit_not_exists_pow` provides such an
open around every point, and finitely many of them cover the quasi-compact `E`. -/
theorem IsAbelianVariety.exists_finite_cover_units_not_pow {K : Type u} [Field K]
    (E : Over (Spec (.of K))) [IsAbelianVariety E] (hE : 0 < IsAbelianVariety.dim E) {r : ℕ}
    (hr : 2 ≤ r) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → E.left.Opens) (_ : ∀ i, Nonempty (U i))
      (f : ∀ i, Γ(E.left, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, IsUnit (f i)) ∧ (⨆ i, U i) = ⊤ ∧
      ∀ i, ¬ ∃ u : E.left.functionField, u ^ r = E.left.germToFunctionField (U i) (f i) := by
  have := IsRegular.of_smooth E.hom
  have := LocallyOfFiniteType.jacobsonSpace E.hom
  have := QuasiCompact.compactSpace_of_compactSpace E.hom
  have : Nontrivial E.left := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := topologicalKrullDim_zero_of_discreteTopology E.left
    rw [IsAbelianVariety.topologicalKrullDim_eq] at h0
    have : IsAbelianVariety.dim E ≤ 0 := by exact_mod_cast h0
    omega
  choose U hxU f hU hf hpow using
    fun x ↦ E.left.exists_isAffineOpen_isUnit_not_exists_pow x hr
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set E.left))
    (fun x ↦ (U x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  refine ⟨t, inferInstance, fun i ↦ U i, fun i ↦ ⟨⟨i, hxU i⟩⟩, fun i ↦ f i, fun i ↦ hU i,
    fun i ↦ hf i, ?_, fun i ↦ hpow i⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hzi⟩

end AlgebraicGeometry
