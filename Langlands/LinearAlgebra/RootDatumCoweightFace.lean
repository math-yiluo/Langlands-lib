import Langlands.LinearAlgebra.RootDatumBasedCorrection
import Langlands.LinearAlgebra.RootDatumBaseExists
import Langlands.LinearAlgebra.LeviCorootSpan

/-! # Simple bases compatible with an integral coweight face -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function IsAddIndecomposable

namespace Langlands.LinearAlgebra.RootDatumCoweightFace

open Langlands.GroupScheme.SplitExistence

variable {J M N : Type*} [Fintype J] [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N)

/-- A regular integral coweight can refine the nonzero signs of any coweight. -/
theorem exists_regular_refinement (ν : N) :
    ∃ f : N, (∀ i, P.root' i f ≠ 0) ∧
      ∀ i, P.root' i ν ≠ 0 → (0 < P.root' i f ↔ 0 < P.root' i ν) := by
  obtain ⟨q, hq⟩ := RootDatumBase.exists_regular_functional P
  let f₀ := P.flip.toPerfPair.symm q
  have he : P.flip.toLinearMap f₀ = q :=
    P.flip.toPerfPair.apply_symm_apply q
  have hf₀ (i : J) : P.root' i f₀ ≠ 0 := by
    change (P.flip.toLinearMap f₀) (P.root i) ≠ 0
    rw [he]
    exact hq i
  let n : ℤ := ∑ i, |P.root' i f₀| + 1
  have hn : 0 < n := by
    dsimp [n]
    have := Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (P.root' i f₀))
    omega
  have hb (i : J) : |P.root' i f₀| < n := by
    have := Finset.single_le_sum (f := fun j => |P.root' j f₀|)
      (fun j _ => abs_nonneg (P.root' j f₀)) (Finset.mem_univ i)
    dsimp [n]
    omega
  refine ⟨n • ν + f₀, ?_, ?_⟩
  · intro i hz
    have hz' : n * P.root' i ν + P.root' i f₀ = 0 := by
      simpa only [map_add, map_smul, smul_eq_mul] using hz
    have hbound := hb i
    have hlo := neg_abs_le (P.root' i f₀)
    have hhi := le_abs_self (P.root' i f₀)
    rcases lt_trichotomy (P.root' i ν) 0 with hneg | hzero | hpos
    · have : P.root' i ν ≤ -1 := by omega
      nlinarith
    · exact hf₀ i (by simpa only [hzero, mul_zero, zero_add] using hz')
    · have : 1 ≤ P.root' i ν := by omega
      nlinarith
  · intro i hi
    rw [map_add, map_smul, smul_eq_mul]
    have hbound := hb i
    have hlo := neg_abs_le (P.root' i f₀)
    have hhi := le_abs_self (P.root' i f₀)
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · have : P.root' i ν ≤ -1 := by omega
      constructor <;> intro h <;> nlinarith
    · have : 1 ≤ P.root' i ν := by omega
      constructor <;> intro h <;> nlinarith

variable [P.IsReduced]

/-- A prescribed regular coweight defines the support of a genuine integral base. -/
theorem exists_base_support (f : N) (hf : ∀ i, P.root' i f ≠ 0) :
    ∃ B : P.Base, (B.support : Set J) =
      baseOf P.root ((P.flip.toLinearMap f) : M →+ ℤ) := by
  classical
  let q := P.flip.toLinearMap f
  let g : Module.Dual ℤ N := q ∘ₗ P.CoPolarization
  have hq (i : J) : q (P.root i) ≠ 0 := hf i
  have hg (i : J) : g (P.coroot i) ≠ 0 :=
    dual_polarization_root_ne_zero P.flip hq i
  have hqg (i : J) : 0 < q (P.root i) ↔ 0 < g (P.coroot i) :=
    (dual_polarization_root_pos_iff P.flip q i).symm
  have heq := RootDatumBase.baseOf_root_eq_baseOf_coroot P q g hq hg hqg
  let := P.indexNeg
  refine ⟨{
    support := (Set.toFinite (baseOf P.root (q : M →+ ℤ))).toFinset
    linearIndepOn_root := by
      simpa only [Set.Finite.coe_toFinset] using P.linearIndepOn_root_baseOf' q hq
    linearIndepOn_coroot := by
      rw [Set.Finite.coe_toFinset, heq]
      exact P.flip.linearIndepOn_root_baseOf' g hg
    root_mem_or_neg_mem := fun i => by
      simpa only [Set.Finite.coe_toFinset] using
        mem_or_neg_mem_closure_baseOf P.root (q : M →+ ℤ) i (hq i) (by simp)
    coroot_mem_or_neg_mem := fun i => by
      simpa only [Set.Finite.coe_toFinset, heq] using
        mem_or_neg_mem_closure_baseOf P.coroot (g : N →+ ℤ) i (hg i) (by simp)
    }, Set.Finite.coe_toFinset _⟩

omit [P.IsReduced] in
/-- A sign-refining base has exactly the simple zero-root coroot span. -/
theorem coroot_span_zero_eq (ν f : N)
    (hface : ∀ i, P.root' i ν ≠ 0 → (0 < P.root' i f ↔ 0 < P.root' i ν))
    (B : P.Base)
    (hB : (B.support : Set J) =
      baseOf P.root ((P.flip.toLinearMap f) : M →+ ℤ)) :
    Submodule.span ℤ (P.coroot '' {i | P.root' i ν = 0}) =
      Submodule.span ℤ (P.coroot '' {i | i ∈ B.support ∧ P.root' i ν = 0}) := by
  let q := P.flip.toLinearMap ν
  let g : Module.Dual ℤ N := q ∘ₗ P.CoPolarization
  have hz (i : J) : g (P.coroot i) = 0 ↔ P.root' i ν = 0 :=
    dual_copolarization_coroot_eq_zero_iff P q i
  have hpos (i : J) : 0 < g (P.coroot i) ↔ 0 < P.root' i ν :=
    dual_polarization_root_pos_iff P.flip q i
  have hnonneg (i : J) (hi : i ∈ B.support) : 0 ≤ g (P.coroot i) := by
    by_cases hzero : P.root' i ν = 0
    · exact ((hz i).mpr hzero).ge
    · have hmem : i ∈ baseOf P.root ((P.flip.toLinearMap f) : M →+ ℤ) := by
        rw [← hB]
        exact hi
      exact ((hpos i).mpr ((hface i hzero).mp hmem.1)).le
  have h := coroot_span_zero_eq_span_simple P B g hnonneg
  simpa only [hz] using h

/-- A regular refinement and a base adapted to a coweight, with the full
zero-root coroot span identified with the simple zero-root coroot span. -/
structure Face (ν : N) where
  regular : N
  nonzero : ∀ i, P.root' i regular ≠ 0
  signs : ∀ i, P.root' i ν ≠ 0 → (0 < P.root' i regular ↔ 0 < P.root' i ν)
  base : P.Base
  support_eq : (base.support : Set J) =
    baseOf P.root ((P.flip.toLinearMap regular) : M →+ ℤ)
  span_eq : Submodule.span ℤ (P.coroot '' {i | P.root' i ν = 0}) =
    Submodule.span ℤ (P.coroot '' {i | i ∈ base.support ∧ P.root' i ν = 0})

/-- Choose a base and simple-coroot face adapted to any integral coweight. -/
noncomputable def coweightFace (ν : N) : Face P ν :=
  Classical.choice <| by
    obtain ⟨f, hf, hface⟩ := exists_regular_refinement P ν
    obtain ⟨B, hB⟩ := exists_base_support P f hf
    exact ⟨⟨f, hf, hface, B, hB, coroot_span_zero_eq P ν f hface B hB⟩⟩

namespace Face

variable {P}

omit [P.IsReduced] [Fintype J] in
/-- The simple zero-root annihilator is the full zero-root annihilator. -/
theorem annihilator_iff {ν : N} (C : Face P ν) (x : M) :
    (∀ i, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0) ↔
      ∀ i ∈ C.base.support, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0 := by
  constructor
  · exact fun h i _ hi => h i hi
  · intro h i hi
    have hspan : Submodule.span ℤ
        (P.coroot '' {i | i ∈ C.base.support ∧ P.root' i ν = 0}) ≤
        LinearMap.ker (P.toLinearMap x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      exact h j hj.1 hj.2
    apply hspan
    rw [← C.span_eq]
    exact Submodule.subset_span ⟨i, hi, rfl⟩

omit [P.IsReduced] in
/-- Choose a based correction for this compatible face. -/
noncomputable def correction {ν : N} (C : Face P ν)
    [Finite (RootDatumWeylChambers.reflectionSubgroup P {i | P.root' i ν = 0})]
    (δ : P.Aut) (hδ : δ.coweightEquiv ν = ν) :
    RootDatumBasedCorrection.Correction P ν C.base δ :=
  RootDatumBasedCorrection.correction P ν C.regular C.nonzero C.signs C.base C.support_eq δ hδ

omit [P.IsReduced] in
/-- The chosen correction fixes every weight annihilating the selected simple
coroots, including all weights outside the ambient root span. -/
theorem correction_fixed {ν : N} (C : Face P ν)
    [Finite (RootDatumWeylChambers.reflectionSubgroup P {i | P.root' i ν = 0})]
    (δ : P.Aut) (hδ : δ.coweightEquiv ν = ν) (x : M)
    (hx : ∀ i ∈ C.base.support, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0) :
    (C.correction δ hδ).weyl.val.weightEquiv x = x :=
  (C.correction δ hδ).fixed x ((C.annihilator_iff x).mpr hx)

end Face

end Langlands.LinearAlgebra.RootDatumCoweightFace
