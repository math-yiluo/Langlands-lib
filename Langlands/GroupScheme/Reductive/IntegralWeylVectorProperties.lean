import Langlands.GroupScheme.Reductive.IntegralWeylVector

/-! # Coroot regularity and the positive-root formula for the integral Weyl vector -/

noncomputable section

universe u v w

namespace Langlands.IntegralWeylVector

variable {J : Type u} {X : Type v} {Y : Type w}
  [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)

/-- The value of rho on an arbitrary coroot is its height in the dual base. -/
theorem pairing_rho_coroot_eq_height (i : J) :
    P.toLinearMap (rho P b hspan) (P.coroot i) = b.flip.height i := by
  obtain ⟨f, -, -, hf⟩ := b.flip.exists_root_eq_sum_int i
  have hheight := b.flip.height_eq_sum hf
  change P.coroot i = ∑ j ∈ b.support, f j • P.coroot j at hf
  rw [hf, map_sum]
  calc
    ∑ j ∈ b.support, P.toLinearMap (rho P b hspan) (f j • P.coroot j) =
        ∑ j ∈ b.support, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, pairing_rho_simple P b hspan ⟨j, hj⟩]
      simp
    _ = b.flip.height i := hheight.symm

/-- Rho is regular on every coroot, with no finiteness or reducedness premise. -/
theorem pairing_rho_coroot_ne_zero (i : J) :
    P.toLinearMap (rho P b hspan) (P.coroot i) ≠ 0 := by
  rw [pairing_rho_coroot_eq_height]
  exact b.flip.height_ne_zero i

/-- Negative rho is regular on every coroot as well. -/
theorem pairing_neg_rho_coroot_ne_zero (i : J) :
    P.toLinearMap (-rho P b hspan) (P.coroot i) ≠ 0 := by
  simpa using neg_ne_zero.mpr (pairing_rho_coroot_ne_zero P b hspan i)

/-- The integral Weyl vector as a weight certified to be regular on all coroots. -/
def regularRho : {x : X // ∀ i : J, P.toLinearMap x (P.coroot i) ≠ 0} :=
  ⟨rho P b hspan, pairing_rho_coroot_ne_zero P b hspan⟩

@[simp] theorem regularRho_val :
    (regularRho P b hspan).val = rho P b hspan := rfl

@[simp] theorem reflection_rho_simple (i : b.support) :
    P.reflection i (rho P b hspan) = rho P b hspan - P.root i := by
  rw [RootPairing.reflection_apply]
  change rho P b hspan -
    P.toLinearMap (rho P b hspan) (P.coroot i) • P.root i = _
  rw [pairing_rho_simple, one_smul]

section PositiveSum

variable [Fintype J] [P.IsReduced]

/-- A simple coroot evaluates the sum of positive roots to two. -/
theorem pairing_positiveRootSum_simple (j : b.support) :
    P.toLinearMap (positiveRootSum P b) (P.coroot j) = 2 := by
  classical
  let s : Finset J := (Finset.univ.filter b.IsPos).erase j
  let f : J → ℤ := fun i => P.toLinearMap (P.root i) (P.coroot j)
  have hanti (i : J) : f (P.reflectionPerm j i) = -f i := by
    change P.pairing (P.reflectionPerm j i) j = -P.pairing i j
    rw [← P.pairing_reflectionPerm, P.pairing_reflectionPerm_self_right]
  have hperm (i : J) (hi : i ∈ s) : P.reflectionPerm j i ∈ s := by
    have hi' : i ≠ (j : J) ∧ b.IsPos i := by simpa [s] using hi
    have hpos := hi'.2.reflectionPerm j.property hi'.1
    have hne : P.reflectionPerm j i ≠ (j : J) := by
      intro heq
      have hi_eq : i = P.reflectionPerm j j := by
        calc
          i = P.reflectionPerm j (P.reflectionPerm j i) :=
            (P.reflectionPerm_self j i).symm
          _ = P.reflectionPerm j j := congrArg (P.reflectionPerm j) heq
      have hheight : b.height (P.reflectionPerm j j) = -1 := by
        have h := b.height_reflectionPerm_self j
        change b.height (P.reflectionPerm j j) = -b.height j at h
        simpa only [b.height_one_of_mem_support j.property] using h
      rw [hi_eq, RootPairing.Base.isPos_iff, hheight] at hi'
      omega
    simpa [s] using And.intro hne hpos
  have hsum_neg : (∑ i ∈ s, f i) = -(∑ i ∈ s, f i) := by
    calc
      (∑ i ∈ s, f i) = ∑ i ∈ s, -f i := by
        refine Finset.sum_nbij' (P.reflectionPerm j) (P.reflectionPerm j)
          hperm hperm ?_ ?_ ?_
        · intro i hi
          exact P.reflectionPerm_self j i
        · intro i hi
          exact P.reflectionPerm_self j i
        · intro i hi
          simp only [hanti, neg_neg]
      _ = -(∑ i ∈ s, f i) := Finset.sum_neg_distrib f
  have hsum : (∑ i ∈ s, f i) = 0 := by omega
  unfold positiveRootSum
  simp only [map_sum, LinearMap.sum_apply]
  change (∑ i ∈ Finset.univ.filter b.IsPos, f i) = 2
  have hj : (j : J) ∈ Finset.univ.filter b.IsPos := by
    simpa using b.isPos_of_mem_support j.property
  rw [← Finset.sum_erase_add _ _ hj]
  change (∑ i ∈ s, f i) + f j = 2
  rw [hsum]
  simp [f]

/-- The integral rho is half the positive-root sum, without dividing in the lattice. -/
theorem two_smul_rho_eq_positiveRootSum :
    (2 : ℤ) • rho P b hspan = positiveRootSum P b := by
  apply eq_of_pairing_simple_eq P b hspan
  intro i
  rw [LinearMap.map_smul₂, pairing_rho_simple,
    pairing_positiveRootSum_simple]
  simp

end PositiveSum

end Langlands.IntegralWeylVector
