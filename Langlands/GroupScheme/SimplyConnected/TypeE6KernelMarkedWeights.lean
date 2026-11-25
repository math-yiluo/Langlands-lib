import Langlands.GroupScheme.Reductive.SplitLeviIsotypicWeights
import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit
import Langlands.GroupScheme.SimplyConnected.TypeE6KernelWeights
import Langlands.LinearAlgebra.CartanE6Root

/-! # The distinguished E6 root and the characters of the actual kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The actual simple root at vertex one in an E6 numbering. -/
def e6DistinguishedRoot (e : d.Vertex ≃ Fin 6) :
    characterLattice d.pinning.toSplitPinning.torus :=
  d.pinning.rootDatum.root (e.symm 1).val

variable {d}

private theorem e6DistinguishedWeight_eq_rootSum (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hsc : IsSimplyConnected G) :
    Langlands.RootDatum.fundamentalWeightBasis d.pinning.rootDatum d.pinning.base
        (d.pinning_corootSpan_eq_top hsc) (e.symm 1) =
      ∑ i : Fin 6, CartanE6Root.coefficients i • d.pinning.rootDatum.root (e.symm i).val := by
  classical
  apply IntegralWeylVector.eq_of_pairing_simple_eq d.pinning.rootDatum d.pinning.base
    (d.pinning_corootSpan_eq_top hsc)
  intro a
  have hcoeff : ∀ j : Fin 6, (∑ i : Fin 6, CartanE6Root.coefficients i *
      CartanMatrix.E 6 i j) = if j = 1 then 1 else 0 := by decide
  rw [Langlands.RootDatum.fundamentalWeightBasis_pairing]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    d.pinning.rootDatum.root_coroot_eq_pairing, zsmul_eq_mul]
  change _ = ∑ i : Fin 6, CartanE6Root.coefficients i * d.cartan (e.symm i) a
  simp only [h.1, Equiv.apply_symm_apply, hcoeff]
  exact if_congr e.eq_symm_apply rfl rfl

private theorem eq_zero_of_e6Branch_kernel_and_split_restrictions (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hsc : IsSimplyConnected G) (x : characterLattice d.pinning.toSplitPinning.torus)
    (hk : d.anisotropicKernelIndex.comparison.weightRestriction x = 0)
    (hs : d.splitTorusDatum.restriction x = 0) : x = 0 := by
  classical
  let c := d.anisotropicKernelIndex.comparison
  let a := e.symm 1
  let P := d.pinning.rootDatum
  let w := Langlands.RootDatum.fundamentalWeightBasis P d.pinning.base
    (d.pinning_corootSpan_eq_top hsc) a
  let m := P.toLinearMap x (P.coroot a.val)
  have hx : x = m • w := by
    apply IntegralWeylVector.eq_of_pairing_simple_eq P d.pinning.base
      (d.pinning_corootSpan_eq_top hsc)
    intro v
    simp only [w, map_zsmul, LinearMap.smul_apply,
      Langlands.RootDatum.fundamentalWeightBasis_pairing]
    by_cases hv : v = a
    · simp [hv, m]
    · have hz : v ∈ d.zeroVertices :=
        (e6Branch_zero_iff e h v).mpr (fun he => hv (e.eq_symm_apply.mpr he))
      obtain ⟨b, hb⟩ := c.vertexEquiv.surjective ⟨v, hz⟩
      have hp := c.pairing_weightRestriction_simple x b
      rw [hb] at hp
      change d.anisotropicKernelIndex.index.pinning.rootDatum.toLinearMap
        (c.weightRestriction x)
        (d.anisotropicKernelIndex.index.pinning.rootDatum.coroot b.val) = _ at hp
      rw [show c.weightRestriction x = 0 from hk, map_zero, LinearMap.zero_apply] at hp
      simpa only [ite_eq_right hv, smul_zero] using hp.symm
  have hsw : d.splitTorusDatum.restriction w =
      (2 : ℤ) • d.rootRestriction a.val := by
    change d.splitTorusDatum.restriction (Langlands.RootDatum.fundamentalWeightBasis
      P d.pinning.base (d.pinning_corootSpan_eq_top hsc) a) = _
    rw [e6DistinguishedWeight_eq_rootSum e h hsc, map_sum, Finset.sum_eq_single (1 : Fin 6)]
    · rw [map_zsmul, d.splitTorusDatum_restriction_root]
      rfl
    · intro i _ hi
      have hz : e.symm i ∈ d.zeroVertices :=
        (e6Branch_zero_iff e h _).mpr (by simpa only [Equiv.apply_symm_apply] using hi)
      rw [map_zsmul, d.splitTorusDatum_restriction_root, show
        d.rootRestriction (e.symm i).val = 0 from hz, smul_zero]
    · exact fun h1 => absurd (Finset.mem_univ _) h1
  have hnonzero : d.rootRestriction a.val ≠ 0 :=
    fun hz => (e6Branch_zero_iff e h a).mp hz (e.apply_symm_apply 1)
  have hpos := (d.compatible a.val hnonzero).mp
    (RootPairing.Base.isPos_of_mem_support a.property)
  change 0 < latticePairing d.splitTorus (d.rootRestriction a.val)
    d.positiveCocharacter at hpos
  let degree := (latticePairing d.splitTorus).flip d.positiveCocharacter
  have hm := congrArg degree hs
  rw [hx, map_zsmul, hsw, map_zsmul, map_zsmul, map_zero] at hm
  change m * (2 * latticePairing d.splitTorus (d.rootRestriction a.val)
    d.positiveCocharacter) = 0 at hm
  have hm0 := (mul_eq_zero.mp hm).resolve_right (by omega)
  rw [hx, hm0, zero_smul]

/-- The two actual character restrictions to the anisotropic kernel torus and the
maximal split torus together distinguish all absolute characters. -/
theorem eq_of_e6Branch_kernel_and_split_restrictions (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hsc : IsSimplyConnected G) {x y : characterLattice d.pinning.toSplitPinning.torus}
    (hk : d.anisotropicKernelIndex.comparison.weightRestriction x =
      d.anisotropicKernelIndex.comparison.weightRestriction y)
    (hs : d.splitTorusDatum.splitCharacter x = d.splitTorusDatum.splitCharacter y) :
    x = y := by
  apply sub_eq_zero.mp
  exact eq_zero_of_e6Branch_kernel_and_split_restrictions e h hsc _
    (by rw [map_sub, hk, sub_self]) (d.splitTorusDatum.restriction_eq_zero_of_splitCharacter_eq hs)

/-- The restricted distinguished root and three times the first kernel weight
sum to an element of the integral kernel root span in any A5 numbering. -/
theorem three_zsmul_kernelFirstWeight_add_e6DistinguishedRoot_mem_rootSpan
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hsc : IsSimplyConnected G)
    (number : d.anisotropicKernelIndex.index.Vertex ≃ Fin 5)
    (hnumber : ∀ a b, d.anisotropicKernelIndex.index.cartan a b =
      CartanMatrix.A 5 (number a) (number b)) :
    (3 : ℤ) • Langlands.RootDatum.fundamentalWeightBasis
        d.anisotropicKernelIndex.index.pinning.rootDatum
        d.anisotropicKernelIndex.index.pinning.base
        (d.anisotropicKernelIndex.index.pinning_corootSpan_eq_top
          (d.anisotropicKernelIndex.isSimplyConnected hsc)) (number.symm 0) +
      d.anisotropicKernelIndex.comparison.weightRestriction (d.e6DistinguishedRoot e) ∈
        d.anisotropicKernelIndex.index.pinning.rootDatum.rootSpan ℤ := by
  classical
  let p := d.anisotropicKernelIndex
  let c := p.comparison
  let branch := c.e6BranchNumbering e h
  let P := p.index.pinning.rootDatum
  let f := branch.symm.trans number
  have hf (i j : Fin 5) : CartanMatrix.A 5 (f i) (f j) = CartanMatrix.A 5 i j := by
    calc
      _ = p.index.cartan (branch.symm i) (branch.symm j) := (hnumber _ _).symm
      _ = _ := by
        have hc := c.e6BranchNumbering_cartan e h (branch.symm i) (branch.symm j)
        change _ = CartanMatrix.A 5 (branch (branch.symm i)) (branch (branch.symm j)) at hc
        simpa only [Equiv.apply_symm_apply] using hc
  have hmid (v : p.index.Vertex) : branch v = 2 ↔ number v = 2 := by
    have hnumber_v : f (branch v) = number v := by
      change number (branch.symm (branch v)) = number v
      exact congrArg number (branch.symm_apply_apply v)
    rcases TypeACartan.eq_id_or_rev_of_preserves f hf with hid | hrev
    · rw [← hnumber_v, hid]
    · rw [← hnumber_v, hrev]
      have h2 : ∀ i : Fin 5, i = 2 ↔ Fin.rev i = 2 := by decide
      exact h2 (branch v)
  have hentry : ∀ i : Fin 5, CartanMatrix.E 6 1 ((1 : Fin 6).succAbove i) =
      if i = 2 then -1 else 0 := by decide
  have hA : ∀ i : Fin 5, 3 * (if i = 0 then 1 else (0 : ℤ)) +
      (if i = 2 then -1 else 0) = 2 * CartanMatrix.A 5 0 i + CartanMatrix.A 5 1 i := by decide
  have heq : (3 : ℤ) • Langlands.RootDatum.fundamentalWeightBasis P
      p.index.pinning.base (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc))
      (number.symm 0) + c.weightRestriction (d.e6DistinguishedRoot e) =
      (2 : ℤ) • P.root (number.symm 0).val + P.root (number.symm 1).val := by
    apply IntegralWeylVector.eq_of_pairing_simple_eq P p.index.pinning.base
      (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc))
    intro v
    simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul,
      Langlands.RootDatum.fundamentalWeightBasis_pairing]
    rw [c.pairing_weightRestriction_simple]
    unfold e6DistinguishedRoot
    rw [d.pinning.rootDatum.root_coroot_eq_pairing]
    change _ + d.cartan (e.symm 1) (c.vertexEquiv v).val = _
    rw [h.1, Equiv.apply_symm_apply,
      c.e6BranchNumbering_ambient e h v, hentry]
    change _ + (if branch v = 2 then (-1 : ℤ) else 0) = _
    have hfirst : v = number.symm 0 ↔ number v = 0 := number.eq_symm_apply
    rw [if_congr (hmid v) rfl rfl, if_congr hfirst rfl rfl]
    rw [P.root_coroot_eq_pairing, P.root_coroot_eq_pairing]
    change _ = 2 * p.index.cartan (number.symm 0) v + p.index.cartan (number.symm 1) v
    rw [hnumber, hnumber, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hA (number v)
  rw [heq]
  exact add_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (number.symm 0).val)))
    (Submodule.subset_span (Set.mem_range_self (number.symm 1).val))

end Langlands.GroupScheme.TitsIndexData
