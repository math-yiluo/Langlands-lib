import Langlands.HarmonicAnalysis.Distribution.TensorProductStatements
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Renard II.1.3: proof of the product, tensor, Fubini and support assertions

Proves `Langlands.HarmonicAnalysis.Distribution.TensorProductStatements.Assertions`
(Renard, 9 July 2026, II.1.3, printed p.32 / PDF p.38).
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct

universe uX uY uZ

namespace Langlands.HarmonicAnalysis.Distribution.TensorProductProof

open Langlands.HarmonicAnalysis.Distribution.TensorProductStatements
open Langlands.Hecke.TestFunction (characteristic characteristic_apply)

section Rectangles

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every test on `X × Y` is constant on each member of a finite family of disjoint
compact clopen rectangles, with nonzero values, and vanishes off their union. The
rectangles are the fibers of `z ↦ (f (z.1, ·), f z)` over its finitely many values
with `f z ≠ 0`. -/
theorem exists_rectangle_expansion [T2Space X] (f : SchwartzBruhat (X × Y)) :
    ∃ (n : ℕ) (U : Fin n → Set X) (V : Fin n → Set Y) (c : Fin n → ℂ),
      (∀ i, IsClopen (U i) ∧ IsCompact (U i)) ∧
      (∀ i, IsClopen (V i) ∧ IsCompact (V i)) ∧
      Pairwise (fun i j => Disjoint (U i ×ˢ V i) (U j ×ˢ V j)) ∧
      (∀ i, c i ≠ 0) ∧
      (∀ i, ∀ z ∈ U i ×ˢ V i, f z = c i) ∧
      (∀ z, f z ≠ 0 → ∃ i, z ∈ U i ×ˢ V i) := by
  classical
  let F : X → Y → ℂ := fun x y => f (x, y)
  have hF : IsLocallyConstant F := SchwartzBruhat.isLocallyConstant_curry f
  let S : Set ((Y → ℂ) × ℂ) := {p | ∃ z : X × Y, f z ≠ 0 ∧ (F z.1, f z) = p}
  have hS : S.Finite := by
    apply ((finite_range_of_locallyConstant_of_hasCompactSupport hF
      (SchwartzBruhat.hasCompactSupport_curry f)).prod
      (finite_range_of_locallyConstant_of_hasCompactSupport
        f.locallyConstant f.hasCompactSupport)).subset
    rintro _ ⟨z, _, rfl⟩
    exact ⟨⟨z.1, rfl⟩, ⟨z, rfl⟩⟩
  let : Fintype S := hS.fintype
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hw (i : Fin (Fintype.card S)) :
      ∃ z : X × Y, f z ≠ 0 ∧ (F z.1, f z) = (e i).val := (e i).property
  choose z hz0 hze using hw
  let U (i : Fin (Fintype.card S)) : Set X := {x | F x = F (z i).1}
  let V (i : Fin (Fintype.card S)) : Set Y := {y | f ((z i).1, y) = f (z i)}
  have hUo (i) : IsClopen (U i) := hF.isClopen_fiber (F (z i).1)
  have hVo (i) : IsClopen (V i) :=
    (f.locallyConstant.comp_continuous
      (continuous_const.prodMk continuous_id)).isClopen_fiber (f (z i))
  have hUc (i) : IsCompact (U i) := by
    apply (f.hasCompactSupport.image continuous_fst).of_isClosed_subset (hUo i).isClosed
    intro x hx
    have hx' : f (x, (z i).2) = f (z i) := congrFun hx (z i).2
    exact ⟨(x, (z i).2), subset_tsupport _ (by
      change f (x, (z i).2) ≠ 0
      rw [hx']
      exact hz0 i), rfl⟩
  have hVc (i) : IsCompact (V i) := by
    apply (f.hasCompactSupport.image continuous_snd).of_isClosed_subset (hVo i).isClosed
    intro y hy
    have hy' : f ((z i).1, y) = f (z i) := hy
    exact ⟨((z i).1, y), subset_tsupport _ (by
      change f ((z i).1, y) ≠ 0
      rw [hy']
      exact hz0 i), rfl⟩
  have hval (i) : ∀ w ∈ U i ×ˢ V i, f w = f (z i) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : F x = F (z i).1 := hx
    have hy' : f ((z i).1, y) = f (z i) := hy
    calc f (x, y) = F x y := rfl
      _ = F (z i).1 y := by rw [hx']
      _ = f (z i) := hy'
  refine ⟨Fintype.card S, U, V, fun i => f (z i), fun i => ⟨hUo i, hUc i⟩,
    fun i => ⟨hVo i, hVc i⟩, ?_, hz0, hval, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ hi hj
    apply hij
    apply e.injective
    apply Subtype.ext
    rw [← hze i, ← hze j]
    have hxi : F x = F (z i).1 := hi.1
    have hxj : F x = F (z j).1 := hj.1
    rw [← hval i (x, y) hi, ← hval j (x, y) hj, ← hxi, ← hxj]
  · intro w hw
    let p : S := ⟨(F w.1, f w), ⟨w, hw, rfl⟩⟩
    refine ⟨e.symm p, ?_, ?_⟩
    · have h := congrArg Prod.fst ((hze (e.symm p)).trans
        (congrArg Subtype.val (e.apply_symm_apply p)))
      exact h.symm
    · have h := (hze (e.symm p)).trans (congrArg Subtype.val (e.apply_symm_apply p))
      have h1 : F (z (e.symm p)).1 = F w.1 := congrArg Prod.fst h
      have h2 : f (z (e.symm p)) = f w := congrArg Prod.snd h
      change f ((z (e.symm p)).1, w.2) = f (z (e.symm p))
      calc f ((z (e.symm p)).1, w.2) = F (z (e.symm p)).1 w.2 := rfl
        _ = F w.1 w.2 := by rw [h1]
        _ = f w := rfl
        _ = f (z (e.symm p)) := h2.symm

/-- The characteristic function of a product of compact clopen sets is the external
product of the two coordinate characteristic functions. -/
theorem characteristic_prod {U : Set X} {V : Set Y} (hUo : IsClopen U) (hUc : IsCompact U)
    (hVo : IsClopen V) (hVc : IsCompact V) :
    characteristic (hUo.prod hVo) (hUc.prod hVc) =
      SchwartzBruhat.tensor (characteristic hUo hUc) (characteristic hVo hVc) := by
  ext ⟨x, y⟩
  rw [SchwartzBruhat.tensor_apply, characteristic_apply, characteristic_apply,
    characteristic_apply]
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ V <;> simp [Set.indicator, hx, hy]

end Rectangles

section Geometry

theorem productLocallyProfinite : ProductLocallyProfinite.{uX, uY} := by
  intro X Y _ _ hX hY
  let : T2Space X := hX.t2Space
  let : LocallyCompactSpace X := hX.locallyCompactSpace
  let : TotallyDisconnectedSpace X := hX.totallyDisconnectedSpace
  let : T2Space Y := hY.t2Space
  let : LocallyCompactSpace Y := hY.locallyCompactSpace
  let : TotallyDisconnectedSpace Y := hY.totallyDisconnectedSpace
  exact Langlands.Topology.isLocallyProfinite_of_mathlib

theorem compactOpenRectangleBasis : CompactOpenRectangleBasis.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro W ⟨U, V, hUo, -, hVo, -, rfl⟩
    exact hUo.prod hVo
  · rintro ⟨x, y⟩ W hxy hW
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hW x y hxy
    obtain ⟨U', hxU', hU'o, hU'c, hU'U⟩ :=
      Langlands.Topology.hasCompactOpenNeighborhoodBasis_of_mathlib x U (hU.mem_nhds hxU)
    obtain ⟨V', hyV', hV'o, hV'c, hV'V⟩ :=
      Langlands.Topology.hasCompactOpenNeighborhoodBasis_of_mathlib y V (hV.mem_nhds hyV)
    exact ⟨U' ×ˢ V', ⟨U', V', hU'o, hU'c, hV'o, hV'c, rfl⟩, ⟨hxU', hyV'⟩,
      (Set.prod_mono hU'U hV'V).trans hUV⟩

theorem compactOpenRectanglePartition : CompactOpenRectanglePartition.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _ K hKo hKc
  have hK : IsClopen K := ⟨hKc.isClosed, hKo⟩
  obtain ⟨n, U, V, c, hU, hV, hdisj, hc, hval, hcov⟩ :=
    exists_rectangle_expansion (characteristic hK hKc)
  refine ⟨n, U, V, fun i => ⟨(hU i).1.isOpen, (hU i).2⟩,
    fun i => ⟨(hV i).1.isOpen, (hV i).2⟩, hdisj, ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    have h := hval i w hi
    rw [characteristic_apply] at h
    by_contra hwK
    rw [Set.indicator_of_notMem hwK] at h
    exact hc i h.symm
  · intro hw
    obtain ⟨i, hi⟩ := hcov w (by
      rw [characteristic_apply, Set.indicator_of_mem hw]
      exact one_ne_zero)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

theorem rectangleIndicatorDecomposition : RectangleIndicatorDecomposition.{uX, uY} := by
  classical
  intro X Y _ _ _ _ _ _ _ _ f
  obtain ⟨n, U, V, c, hU, hV, hdisj, hc, hval, hcov⟩ := exists_rectangle_expansion f
  have hUo (i) : IsClopen (U i) := (hU i).1
  have hUc (i) : IsCompact (U i) := (hU i).2
  have hVo (i) : IsClopen (V i) := (hV i).1
  have hVc (i) : IsCompact (V i) := (hV i).2
  have hsum : f = ∑ i, c i • characteristic ((hUo i).prod (hVo i)) ((hUc i).prod (hVc i)) := by
    ext w
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    symm
    by_cases hw : f w = 0
    · have hnot (i) : w ∉ U i ×ˢ V i := by
        intro hi
        exact hc i ((hval i w hi).symm.trans hw)
      rw [hw]
      apply Finset.sum_eq_zero
      intro i _
      change c i * characteristic _ _ w = 0
      rw [characteristic_apply, Set.indicator_of_notMem (hnot i), mul_zero]
    · obtain ⟨i, hi⟩ := hcov w hw
      rw [Finset.sum_eq_single i]
      · rw [characteristic_apply, Set.indicator_of_mem hi, mul_one, hval i w hi]
      · intro j _ hji
        have hnot : w ∉ U j ×ˢ V j := fun hj =>
          Set.disjoint_left.mp (hdisj hji) hj hi
        change c j * characteristic _ _ w = 0
        rw [characteristic_apply, Set.indicator_of_notMem hnot, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
  refine ⟨n, U, V, hUo, hUc, hVo, hVc, c, hdisj, hsum, ?_⟩
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [characteristic_prod]

end Geometry

section Tensor

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]

/-- Every product test is a finite sum of external products, as an equality of tests. -/
theorem exists_eq_sum_tensor (f : SchwartzBruhat (X × Y)) :
    ∃ (N : ℕ) (α : Fin N → SchwartzBruhat X) (β : Fin N → SchwartzBruhat Y),
      f = ∑ j, SchwartzBruhat.tensor (α j) (β j) := by
  obtain ⟨N, α, β, hf⟩ := SchwartzBruhat.exists_tensor_expansion f
  refine ⟨N, α, β, ?_⟩
  ext ⟨x, y⟩
  simp only [Submodule.coe_sum, Finset.sum_apply]
  exact hf x y

theorem tensorLinearMap_surjective :
    Function.Surjective (SchwartzBruhat.tensorLinearMap :
      SchwartzBruhat X ⊗[ℂ] SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat (X × Y)) := by
  intro f
  obtain ⟨N, α, β, hf⟩ := exists_eq_sum_tensor f
  refine ⟨∑ j, α j ⊗ₜ[ℂ] β j, ?_⟩
  rw [map_sum, hf]
  rfl

omit [T2Space X] [T2Space Y] in
theorem tensorLinearMap_injective :
    Function.Injective (SchwartzBruhat.tensorLinearMap :
      SchwartzBruhat X ⊗[ℂ] SchwartzBruhat Y →ₗ[ℂ] SchwartzBruhat (X × Y)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  let b := Module.Basis.ofVectorSpace ℂ (SchwartzBruhat X)
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hval (x : X) (y : Y) : ∑ i ∈ c.support, b i x * c i y = 0 := by
    have h := congrArg (fun F : SchwartzBruhat (X × Y) => F (x, y)) ht
    simp only [Finsupp.sum, map_sum, SchwartzBruhat.tensorLinearMap_tmul] at h
    simpa only [Submodule.coe_sum, Finset.sum_apply, SchwartzBruhat.tensor_apply,
      ZeroMemClass.coe_zero, Pi.zero_apply] using h
  have hc : c = 0 := by
    ext i y
    by_cases hi : i ∈ c.support
    · have hzero : ∑ j ∈ c.support, (c j y) • b j = 0 := by
        ext x
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
        rw [← hval x y]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      exact linearIndependent_iff'.mp b.linearIndependent c.support (fun j => c j y)
        hzero i hi
    · rw [Finsupp.notMem_support_iff.mp hi]
      rfl
  rw [hc]
  simp

theorem tensorLinearMapBijective : TensorLinearMapBijective.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _
  exact ⟨tensorLinearMap_injective, tensorLinearMap_surjective⟩

theorem tensorExistsUnique : TensorExistsUnique.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _ T S
  refine ⟨fun f g => Distribution.tensor_apply_tensor T S f g, ?_⟩
  intro D hD
  ext f
  obtain ⟨N, α, β, hf⟩ := exists_eq_sum_tensor f
  rw [hf, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [hD, Distribution.tensor_apply_tensor]

theorem fubini : Fubini.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _ T S f
  refine ⟨rfl, ?_⟩
  obtain ⟨N, α, β, hf⟩ := exists_eq_sum_tensor f
  rw [hf, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Distribution.tensor_apply_tensor, Distribution.partialApplyFst_tensor, map_smul,
    smul_eq_mul]

end Tensor

section Support

variable {Z : Type uZ} [TopologicalSpace Z] [T2Space Z] [LocallyCompactSpace Z]
  [TotallyDisconnectedSpace Z]

/-- A distribution whose restriction to an open set vanishes kills every test
vanishing off that open set. -/
theorem apply_eq_zero_of_restrictOpen_eq_zero {W : Set Z} (hW : IsOpen W)
    {D : Distribution Z} (hD : Distribution.restrictOpen hW D = 0)
    (f : SchwartzBruhat Z) (hf : ∀ z ∉ W, f z = 0) : D f = 0 := by
  have hsupp : Distribution.support D ⊆ Wᶜ := by
    intro z hz hzW
    exact ((Distribution.not_mem_support_iff D z).mpr ⟨W, hW, hzW, hD⟩) hz
  exact (Distribution.support_subset_iff_mem_supportedOn hW.isClosed_compl D).mp hsupp f
    (fun z hz => hf z hz)

omit [LocallyCompactSpace Z] [TotallyDisconnectedSpace Z] in
/-- A point of the support has, inside every open neighborhood, a test vanishing off
that neighborhood on which the distribution is nonzero. -/
theorem exists_apply_ne_zero_of_mem_support {D : Distribution Z} {x : Z}
    (hx : x ∈ Distribution.support D) {U : Set Z} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ f : SchwartzBruhat Z, (∀ z ∉ U, f z = 0) ∧ D f ≠ 0 := by
  by_contra h
  apply (Distribution.not_mem_support_iff D x).mpr _ hx
  refine ⟨U, hU, hxU, ?_⟩
  ext g
  rw [Distribution.restrictOpen_apply, LinearMap.zero_apply]
  by_contra hne
  exact h ⟨_, fun z hz => SchwartzBruhat.extendZero_apply_of_not_mem hU g hz, hne⟩

theorem supportTensor : SupportTensor.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _ T S
  apply Set.Subset.antisymm
  · apply (Distribution.support_subset_iff_mem_supportedOn
      ((Distribution.isClosed_support T).prod (Distribution.isClosed_support S))
      (Distribution.tensor T S)).mpr
    intro f hf
    rw [Distribution.tensor_apply]
    apply Distribution.mem_supportedOn_support T
    intro x hx
    rw [Distribution.partialApplySnd_apply]
    apply Distribution.mem_supportedOn_support S
    intro y hy
    exact hf (x, y) ⟨hx, hy⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    by_contra hxy
    obtain ⟨W, hW, hxyW, hD⟩ := (Distribution.not_mem_support_iff _ _).mp hxy
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := isOpen_prod_iff.mp hW x y hxyW
    obtain ⟨φ, hφ, hTφ⟩ := exists_apply_ne_zero_of_mem_support hx hU hxU
    obtain ⟨ψ, hψ, hSψ⟩ := exists_apply_ne_zero_of_mem_support hy hV hyV
    have h0 := apply_eq_zero_of_restrictOpen_eq_zero hW hD (SchwartzBruhat.tensor φ ψ) (by
      rintro ⟨x', y'⟩ hz
      rw [SchwartzBruhat.tensor_apply]
      by_cases hx' : x' ∈ U
      · by_cases hy' : y' ∈ V
        · exact absurd (hUV ⟨hx', hy'⟩) hz
        · rw [hψ y' hy', mul_zero]
      · rw [hφ x' hx', zero_mul])
    rw [Distribution.tensor_apply_tensor] at h0
    exact mul_ne_zero hTφ hSψ h0

theorem compactSupportTensor : CompactSupportTensor.{uX, uY} := by
  intro X Y _ _ _ _ _ _ _ _ T S
  have h (hT : IsCompact (Distribution.support T)) (hS : IsCompact (Distribution.support S)) :
      IsCompact (Distribution.support (Distribution.tensor T S)) := by
    rw [supportTensor X Y T S]
    exact hT.prod hS
  exact ⟨h, fun hT hS => h hT hS⟩

end Support

/-- All nine assertions of Renard II.1.3. -/
theorem assertions : Assertions.{uX, uY} :=
  ⟨productLocallyProfinite, compactOpenRectangleBasis, compactOpenRectanglePartition,
    rectangleIndicatorDecomposition, tensorLinearMapBijective, tensorExistsUnique, fubini,
    supportTensor, compactSupportTensor⟩

end Langlands.HarmonicAnalysis.Distribution.TensorProductProof
