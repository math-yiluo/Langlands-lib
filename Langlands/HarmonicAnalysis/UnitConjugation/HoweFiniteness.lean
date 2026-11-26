import Langlands.HarmonicAnalysis.UnitConjugation.HoweRestriction

/-! # Finiteness of lattice restrictions from decreasing test averages -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function Filter Submodule _root_.Topology

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  (L : AddSubgroup A) (hLo : IsOpen (L : Set A)) (hLc : IsCompact (L : Set A))

include hLo in
private theorem quotient_isLocallyConstant : IsLocallyConstant (QuotientAddGroup.mk' L) := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  have ho : IsOpen (Homeomorph.addLeft x '' (L : Set A)) := (Homeomorph.addLeft x).isOpenMap _ hLo
  have hx : x ∈ Homeomorph.addLeft x '' (L : Set A) := ⟨0, L.zero_mem, by simp⟩
  filter_upwards [ho.mem_nhds hx] with y hy
  obtain ⟨t, ht, rfl⟩ := hy
  exact ((QuotientAddGroup.mk'_eq_mk' L).2 ⟨t, ht, rfl⟩).symm

private theorem mem_span_latticeCosets_of_support (f : SchwartzBruhat A)
    (hf : f ∈ latticeInvariantTests L) (U : Set A) (hU : support (f : A → ℂ) ⊆ U) :
    f ∈ Submodule.span ℂ (latticeCosetTest L hLo hLc '' U) := by
  classical
  let π := QuotientAddGroup.mk' L
  let ψ (q : A ⧸ L) : ℂ := if q ∈ π '' U then 1 else 0
  let χ : LocallyConstant A ℂ := ⟨ψ ∘ π, (quotient_isLocallyConstant L hLo).comp ψ⟩
  let m := Distribution.multiplyTest χ
  let W := Submodule.span ℂ (latticeCosetTest L hLo hLc '' U)
  have hmul (g : SchwartzBruhat A) (h : g ∈ latticeInvariantTests L) : m g ∈ W := by
    rw [← latticeCosetSpan L hLo hLc] at h
    refine Submodule.span_induction (fun f' hf' => ?_) (by simp)
      (fun _ _ _ _ ha hb => by rw [map_add]; exact W.add_mem ha hb)
      (fun c _ _ hf' => by rw [map_smul]; exact W.smul_mem c hf') h
    obtain ⟨x, rfl⟩ := hf'
    by_cases hx : π x ∈ π '' U
    · obtain ⟨y, hy, hxy⟩ := hx
      have he : m (latticeCosetTest L hLo hLc x) = latticeCosetTest L hLo hLc y := by
        apply Hecke.TestFunction.ext
        intro z
        rw [Distribution.multiplyTest_apply, latticeCosetTest_apply, latticeCosetTest_apply]
        change ψ (π z) * (if π z = π x then 1 else 0) = if π z = π y then 1 else 0
        by_cases hz : π z = π x
        · have hyz : π z = π y := hz.trans hxy.symm
          have hm : π z ∈ π '' U := ⟨y, hy, hyz.symm⟩
          simp only [ψ, ite_eq_left hz, ite_eq_left hyz, ite_eq_left hm, one_mul]
        · have hzy : π z ≠ π y := fun h => hz (h.trans hxy)
          simp only [ite_eq_right hz, ite_eq_right hzy, mul_zero]
      rw [he]
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · suffices he : m (latticeCosetTest L hLo hLc x) = 0 by rw [he]; exact W.zero_mem
      apply Hecke.TestFunction.ext
      intro z
      rw [Distribution.multiplyTest_apply, latticeCosetTest_apply]
      change ψ (π z) * (if π z = π x then 1 else 0) = 0
      by_cases hz : π z = π x
      · have hn : π z ∉ π '' U := hz ▸ hx
        simp only [ψ, ite_eq_left hz, ite_eq_right hn, zero_mul]
      · simp only [ite_eq_right hz, mul_zero]
  have he : m f = f := by
    apply Hecke.TestFunction.ext
    intro x
    rw [Distribution.multiplyTest_apply]
    change ψ (π x) * f x = f x
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
    · have hm : π x ∈ π '' U := ⟨x, hU hx, rfl⟩
      simp only [ψ, ite_eq_left hm, one_mul]
  exact he ▸ hmul f hf

/-- A decreasing averaging identity implies finite-dimensionality of the allowable
lattice restrictions. The nonnegative integer `height` orders the centers by size. -/
def HoweFinitenessFromAveragesStatement (B K : Set A) (height : A → ℕ) : Prop :=
  IsCompact K →
  (∀ x, x ∉ B → x ∉ K →
    ∃ f : latticeInvariantTests L, support ((f.val : SchwartzBruhat A) : A → ℂ) ⊆ {y | height y < height x} ∧
      ∀ T : Distribution A, IsConjugationInvariant T → T f.val = T (latticeCosetTest L hLo hLc x)) →
  FiniteDimensional ℂ ((vanishingOnLatticeCosets L hLo hLc B).map (restrictToLatticeTests L))

/-- Evaluations on the finitely many cosets meeting `K` separate the restrictions.
A nonzero test value outside `K` or the vanishing set would force one at smaller height. -/
theorem howeFinitenessFromAverages (B K : Set A) (height : A → ℕ) :
    HoweFinitenessFromAveragesStatement L hLo hLc B K height := by
  classical
  intro hK hreduce
  let J := vanishingOnLatticeCosets L hLo hLc B
  let j := restrictToLatticeTests L
  let W := J.map j
  let Q := QuotientAddGroup.mk' L '' K
  let : TopologicalSpace (A ⧸ L) := ⊥
  let : DiscreteTopology (A ⧸ L) := ⟨rfl⟩
  let : Fintype Q := (hK.image (quotient_isLocallyConstant L hLo).continuous).finite_of_discrete.fintype
  have hrep (q : Q) : ∃ x ∈ K, QuotientAddGroup.mk' L x = q.val := q.property
  choose r _ hr using hrep
  let φ (x : A) : latticeInvariantTests L := ⟨latticeCosetTest L hLo hLc x, latticeCosetTest_mem L hLo hLc x⟩
  let E : W →ₗ[ℂ] (Q → ℂ) := LinearMap.pi fun q =>
    (Module.Dual.eval ℂ (latticeInvariantTests L) (φ (r q))).comp W.subtype
  apply FiniteDimensional.of_injective E
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨T, hT, hTa⟩ := a.property
  have hsmall (x : A) (hx : x ∈ K) : T (φ x).val = 0 := by
    let q : Q := ⟨QuotientAddGroup.mk' L x, ⟨x, hx, rfl⟩⟩
    have he : φ (r q) = φ x := by
      apply Subtype.ext
      apply Hecke.TestFunction.ext
      intro y
      change latticeCosetTest L hLo hLc (r q) y = latticeCosetTest L hLo hLc x y
      simp only [latticeCosetTest_apply, hr q]
      rfl
    have hEval := congrFun (LinearMap.mem_ker.mp ha) q
    change a.val (φ (r q)) = 0 at hEval
    rw [he, ← hTa] at hEval
    exact hEval
  obtain ⟨hTI, hTV⟩ := (mem_vanishingOnLatticeCosets L hLo hLc B T).1 hT
  have hzero (m : ℕ) : ∀ x : A, height x = m → T (latticeCosetTest L hLo hLc x) = 0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro x hm
      by_cases hxB : x ∈ B
      · exact hTV x hxB
      by_cases hxK : x ∈ K
      · exact hsmall x hxK
      obtain ⟨f, hf, havg⟩ := hreduce x hxB hxK
      rw [← havg T hTI]
      have hspan : Submodule.span ℂ (latticeCosetTest L hLo hLc '' {y | height y < height x}) ≤
          LinearMap.ker T := by
        apply Submodule.span_le.mpr
        rintro _ ⟨y, hy, rfl⟩
        change T (latticeCosetTest L hLo hLc y) = 0
        exact ih (height y) (hm ▸ hy) y rfl
      exact hspan (mem_span_latticeCosets_of_support L hLo hLc f.val f.property _ hf)
  have hker : latticeInvariantTests L ≤ LinearMap.ker T := by
    rw [← latticeCosetSpan L hLo hLc]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hzero (height x) x rfl
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  rw [← hTa]
  exact hker f.property

end Langlands.HarmonicAnalysis.UnitConjugation
