import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Representation.Archimedean.RealStandardConstituentPermutation
import Langlands.Representation.Archimedean.RealSwapSurjectiveProof

/-! # Permuting the inducing blocks in real ordinary normalized generation -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator MonoidAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean Langlands.Automorphic
open ArchimedeanLocal ConstituentCompression RealSwapSurjective

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "Std" => realStandardKFinite
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ

private def HasCompactInjection (n : ℕ) (ds es : List RealBlock) : Prop :=
  ∃ T : Std n ds →ₗ[ℂ] Std n es, Function.Injective T ∧
    ∀ k f, T (realStandardRep n ds k f) = realStandardRep n es k (T f)

private theorem HasCompactInjection.trans {n : ℕ} {ds es fs : List RealBlock}
    (h₁ : HasCompactInjection n ds es) (h₂ : HasCompactInjection n es fs) :
    HasCompactInjection n ds fs := by
  obtain ⟨T, hT, hTk⟩ := h₁
  obtain ⟨S, hS, hSk⟩ := h₂
  exact ⟨S.comp T, hS.comp hT, fun k f => (congrArg S (hTk k f)).trans (hSk k (T f))⟩

private theorem compactInjection_of_perm {n : ℕ} {ds es : List RealBlock}
    (h : ds.Perm es) (hr : realRank ds = n) : HasCompactInjection n es ds := by
  suffices ∀ pre, realRank (pre ++ ds) = n → HasCompactInjection n (pre ++ es) (pre ++ ds) from
    this [] hr
  clear hr
  induction h with
  | nil => exact fun _ _ => ⟨LinearMap.id, Function.injective_id, fun _ _ => rfl⟩
  | @cons x ds es h ih =>
    intro pre hr
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [x]) (by simpa only [List.append_assoc, List.singleton_append] using hr)
  | swap y x post =>
    intro pre hr
    have hp : (pre ++ x :: y :: post).Perm (pre ++ y :: x :: post) :=
      (List.Perm.swap y x post).append_left pre
    have hr' := (realRank_perm hp).symm.trans hr
    obtain ⟨T, hT, hTi⟩ := exists_perm_injection hr hr'
      (swap_positionCharacter x y hr) (swap_inducedBlock x y hr)
    exact ⟨T, hTi, hT⟩
  | trans hp hq ihp ihq =>
    intro pre hr
    exact (ihq pre ((realRank_perm (hp.append_left pre)).symm.trans hr)).trans (ihp pre hr)

private theorem lie_mem_of_real {n : ℕ} {ds : List RealBlock} (U : Submodule ℂ (Std n ds))
    (h : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : Std n ds), f ∈ U →
      realStandardLie n ds (1 ⊗ₜ[ℝ] X) f ∈ U)
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (f : Std n ds) (hf : f ∈ U) :
    realStandardLie n ds X f ∈ U := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : (z ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, LinearMap.smul_apply]
    exact U.smul_mem z (h X f hf)
  | add X Y hX hY =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hX hY

private theorem standardIntertwiner_of_generators {n : ℕ} {ds es : List RealBlock}
    (T : Std n ds →ₗ[ℂ] Std n es)
    (hK : ∀ k f, T (realStandardRep n ds k f) = realStandardRep n es k (T f))
    (hL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) f,
      T (realStandardLie n ds (1 ⊗ₜ[ℝ] X) f) = realStandardLie n es (1 ⊗ₜ[ℝ] X) (T f)) :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T := by
  constructor
  · intro k f
    let u : K n := ⟨k.val.val, k.2⟩
    have hu : Unitary.toUnits u = k.val := Units.ext rfl
    have hcoe := realStandardRep_apply_coe n ds u f
    rw [hu] at hcoe
    refine ⟨hcoe ▸ (realStandardRep n ds u f).2, ?_⟩
    exact (congrArg T (Subtype.ext hcoe.symm)).trans (hK u f)
  · intro X f
    have hcoe := realStandardLie_one_tmul_apply_coe n ds X f
    refine ⟨hcoe ▸ (realStandardLie n ds (1 ⊗ₜ[ℝ] X) f).2, ?_⟩
    exact (congrArg T (Subtype.ext hcoe.symm)).trans (hL X f)

/-- A permutation of the blocks of an irreducible real standard module has the
same standard module up to bijective compact and Lie intertwining. -/
theorem realStandardEquiv_of_perm_irreducible {n : ℕ} {ds es : List RealBlock}
    (hp : ds.Perm es) (hr : realRank ds = n)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)) :
    ∃ T : Std n es →ₗ[ℂ] Std n ds, Function.Bijective T ∧
      IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) es T := by
  let ρ := realStandardRep n ds
  let σ := realStandardRep n es
  let L := realStandardLie n ds
  let : Nontrivial (Std n ds) := hirr.1
  have hSelf : IsOperatorConstituent (realStandardOperators n ds) (realStandardOperators n ds) := by
    refine ⟨⊤, fun _ _ _ => Submodule.mem_top, (⊤ : Submodule ℂ (Std n ds)).subtype, ?_, fun _ _ => rfl⟩
    exact fun f => ⟨⟨f, Submodule.mem_top⟩, rfl⟩
  obtain ⟨S, hS, f, hfs, hf⟩ := realStandardConstituent_perm ρ (fun X => L (1 ⊗ₜ[ℝ] X)) hp hr
    (fun U hK hL => hirr.2 U hK (lie_mem_of_real U hL)) hSelf
  let S' : Subrepresentation σ := ⟨S, fun k x hx => hS (.inl k) x hx⟩
  let τ : Representation ℂ (K n) S := S'.toRepresentation
  let j : Representation.IntertwiningMap τ σ :=
    S.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let fK : Representation.IntertwiningMap τ ρ :=
    f.intertwiningMap_of_isIntertwiningMap _ _ (fun k x => hf (.inl k) x)
  let j' := Representation.IntertwiningMap.equivLinearMapAsModule τ σ j
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ fK
  have hσ := isRealGKModule_realStandardModule n es
  let : IsSemisimpleModule ℂ[K n] σ.asModule := KFiniteDual.isSemisimpleModule hσ.1 hσ.2.1
  let : AddCommGroup τ.asModule := inferInstanceAs (AddCommGroup S)
  have hj' : Function.Injective j' := by
    intro x y hxy
    exact Subtype.ext hxy
  let : IsSemisimpleModule ℂ[K n] τ.asModule :=
    IsSemisimpleModule.of_injective (R := ℂ[K n]) (M := σ.asModule) (N := τ.asModule) j' hj'
  have hfs' : Function.Surjective f' := hfs
  obtain ⟨g', hg'⟩ := IsSemisimpleModule.lifting_property (R := ℂ[K n]) (M := τ.asModule)
    (N := ρ.asModule) f' hfs' LinearMap.id
  let g := (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ).symm g'
  have hg (x : Std n ds) : f (g x) = x := LinearMap.congr_fun hg' x
  let B : Std n ds →ₗ[ℂ] Std n es := S.subtype.comp g.toLinearMap
  have hB : Function.Injective B := by
    intro x y hxy
    exact (hg x).symm.trans ((congrArg f (Subtype.ext hxy : g x = g y)).trans (hg y))
  have hBK (k : K n) (x : Std n ds) : B (ρ k x) = σ k (B x) := by
    change ((g (ρ k x) : S) : Std n es) = σ k ((g x : S) : Std n es)
    rw [g.isIntertwining]
    rfl
  obtain ⟨A, hA, hAK⟩ := compactInjection_of_perm hp hr
  have hBs : Function.Surjective B := surjective_of_injective
    (realStandardAdmissible n ds) (realStandardAdmissible n es) hσ.1 hσ.2.1 B hBK hB A hAK hA
  have hTop (x : Std n es) : x ∈ S := by
    obtain ⟨y, rfl⟩ := hBs x
    exact (g y : S).2
  let incl : Std n es →ₗ[ℂ] S := LinearMap.codRestrict S LinearMap.id hTop
  let T := f.comp incl
  have hInv (x : Std n ds) : T (B x) = x := hg x
  have hInv' (x : Std n es) : B (T x) = x := by
    obtain ⟨y, rfl⟩ := hBs x
    rw [hInv]
  refine ⟨T, ⟨(show Function.LeftInverse B T from hInv').injective, fun x => ⟨B x, hInv x⟩⟩,
    standardIntertwiner_of_generators T (fun k x => hf (.inl k) (incl x))
      (fun X x => hf (.inr X) (incl x))⟩

/-- Pulling back coefficient maps through a surjective standard intertwiner
includes the target Whittaker model in the source Whittaker model. -/
theorem realWhittakerModel_le_of_surjective {r : ℕ} {ds es : List RealBlock} (a : ℝˣ)
    (h : RealSurjectiveIntertwinerExists (r + 1) ds es) :
    realWhittakerModel r es a ≤ realWhittakerModel r ds a := by
  obtain ⟨T, hs, hT⟩ := h
  refine iSup₂_le fun B hB => ?_
  have hBT : IsRealWhittakerIntertwiner r ds a (B.comp T) := by
    refine ⟨fun f => hB.1 (T f), fun f => hB.2.1 (T f), fun f => hB.2.2.1 (T f), ?_, ?_⟩
    · intro k f f' hf
      obtain ⟨hmem, hTf⟩ := hT.1 k f
      have he : f' = ⟨_, hmem⟩ := Subtype.ext hf
      refine hB.2.2.2.1 k (T f) (T f') ?_
      rw [he, hTf, realStandardRep_apply_coe]
      have hk : Unitary.toUnits (⟨k.val.val, k.2⟩ : K (r + 1)) = k.val := Units.ext rfl
      rw [hk]
    · intro X f f' hf
      obtain ⟨hmem, hTf⟩ := hT.2 X f
      have he : f' = ⟨_, hmem⟩ := Subtype.ext hf
      refine hB.2.2.2.2 X (T f) (T f') ?_
      rw [he, hTf, realStandardLie_one_tmul_apply_coe]
  rintro _ ⟨v, rfl⟩
  obtain ⟨w, rfl⟩ := hs v
  exact Submodule.mem_iSup_of_mem (B.comp T) (Submodule.mem_iSup_of_mem hBT ⟨w, rfl⟩)

private theorem standardIntertwiner_symm {n : ℕ} {ds es : List RealBlock}
    (T : Std n ds ≃ₗ[ℂ] Std n es)
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T.toLinearMap) :
    IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) es T.symm.toLinearMap := by
  apply standardIntertwiner_of_generators
  · intro k f
    apply T.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      (hT.map_realStandardRep k (T.symm f)).symm
  · intro X f
    apply T.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    have h := hT.map_realStandardLie ((1 : ℂ) ⊗ₜ[ℝ] X) (T.symm f)
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h.symm

/-- Reordering the blocks of an irreducible real standard module preserves
irreducibility and the actual ordinary Whittaker models. -/
theorem realWhittakerModels_of_perm_irreducible {r : ℕ} {ds es : List RealBlock}
    (hp : ds.Perm es) (hr : realRank ds = r + 1)
    (hirr : IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)) :
    IsIrreducibleGKModule (realStandardRep (r + 1) es) (realStandardLie (r + 1) es) ∧
      ∀ a, realWhittakerModel r es a = realWhittakerModel r ds a := by
  obtain ⟨T, hT, hTi⟩ := realStandardEquiv_of_perm_irreducible hp hr hirr
  let e := LinearEquiv.ofBijective T hT
  have hInv := standardIntertwiner_symm e hTi
  have hIrr' : IsIrreducibleGKModule (realStandardRep (r + 1) es) (realStandardLie (r + 1) es) := by
    let : Nontrivial (Std (r + 1) ds) := hirr.1
    refine ⟨hT.2.nontrivial, fun U hK hL => ?_⟩
    have hEq := hirr.2 (U.map T)
      (fun k _ h => by
        obtain ⟨x, hx, rfl⟩ := h
        exact ⟨_, hK k x hx, hTi.map_realStandardRep k x⟩)
      (fun X _ h => by
        obtain ⟨x, hx, rfl⟩ := h
        exact ⟨_, hL X x hx, hTi.map_realStandardLie X x⟩)
    have hinj := Submodule.map_injective_of_injective hT.1
    rcases hEq with h | h
    · exact Or.inl (hinj (h.trans (by simp)))
    · exact Or.inr (hinj (h.trans (by rw [Submodule.map_top, LinearMap.range_eq_top.mpr hT.2])))
  refine ⟨hIrr', fun a => le_antisymm (realWhittakerModel_le_of_surjective a ?_)
    (realWhittakerModel_le_of_surjective a ?_)⟩
  · exact ⟨e.symm.toLinearMap, e.symm.surjective, hInv⟩
  · exact ⟨T, hT.2, hTi⟩

private theorem exists_ordered_perm (ds : List RealBlock) :
    ∃ es, ds.Perm es ∧ Langlands.Archimedean.IsRealLanglandsOrdered es := by
  let le (x y : RealBlock) := decide (realBlockExponent y ≤ realBlockExponent x)
  refine ⟨ds.mergeSort le, (List.mergeSort_perm _ _).symm, ?_⟩
  exact (List.pairwise_mergeSort (le := le)
    (fun _ _ _ hab hbc => decide_eq_true ((of_decide_eq_true hbc).trans (of_decide_eq_true hab)))
    (fun a b => by
      simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using
        (le_total (realBlockExponent b) (realBlockExponent a))) ds).imp
      fun hab => of_decide_eq_true hab

local notation "Coefficients" => fun r => Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ)

private def UnequalGeneration {r t : ℕ} (hrt : t < r) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (S : Coefficients r) (T : Coefficients t) (L : ReciprocalEntire) : Prop :=
  let I (i : S × T) := realUnequalIntegral hrt D i.1 i.2
  HasCoveringOrdinaryNormalizations I L ∧
    (t + 1 = r → (a = 1 ∨ a = -1) → HasFiniteOrdinaryNormalizationSum I L)

private theorem unequalGeneration_congr {r t : ℕ} {hrt : t < r} {a : ℝˣ}
    {D : RealQuotientMeasureData t} {S S' : Coefficients r} {T T' : Coefficients t}
    {L L' : ReciprocalEntire} (hS : S = S') (hT : T = T') (hL : L = L') :
    UnequalGeneration hrt a D S T L → UnequalGeneration hrt a D S' T' L' := by
  subst S' T' L'
  exact id

private def EqualGeneration {r : ℕ} (a : ℝˣ) (D : RealQuotientMeasureData r)
    (S T : Coefficients r) (L : ReciprocalEntire) : Prop :=
  let I (i : S × T × SchwartzMap (Fin (r + 1) → ℝ) ℂ) := realEqualIntegral D i.1 i.2.1 i.2.2
  HasCoveringOrdinaryNormalizations I L ∧
    ((a = 1 ∨ a = -1) → HasFiniteOrdinaryNormalizationSum I L)

private theorem equalGeneration_congr {r : ℕ} {a : ℝˣ} {D : RealQuotientMeasureData r}
    {S S' T T' : Coefficients r} {L L' : ReciprocalEntire}
    (hS : S = S') (hT : T = T') (hL : L = L') :
    EqualGeneration a D S T L → EqualGeneration a D S' T' L' := by
  subst S' T' L'
  exact id

/-- Ordinary real normalized generation with both inducing lists in Langlands order. -/
def RealOrdinaryOrderedGenerationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List RealBlock), realRank d = r + 1 → realRank e = t + 1 →
    Langlands.Archimedean.IsRealLanglandsOrdered d → Langlands.Archimedean.IsRealLanglandsOrdered e →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (t + 1) e) (realStandardLie (t + 1) e) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData t),
      realWhittakerModel r d a ≠ ⊥ → realWhittakerModel t e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e) ∧
      (t + 1 = r → (a = 1 ∨ a = -1) →
        HasFiniteOrdinaryNormalizationSum (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e))) ∧
  ∀ (r : ℕ) (d e : List RealBlock), realRank d = r + 1 → realRank e = r + 1 →
    Langlands.Archimedean.IsRealLanglandsOrdered d → Langlands.Archimedean.IsRealLanglandsOrdered e →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (r + 1) e) (realStandardLie (r + 1) e) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
      realWhittakerModel r d a ≠ ⊥ → realWhittakerModel r e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e) ∧
      ((a = 1 ∨ a = -1) →
        HasFiniteOrdinaryNormalizationSum (realOrdinaryEqualTest r d e a D) (realPairLFactor d e))

/-- It suffices to prove normalized generation for real block lists in Langlands order. -/
def RealOrdinaryOrderedGenerationReductionStatement : Prop :=
  RealOrdinaryOrderedGenerationStatement → RealOrdinaryNormalizedGenerationStatement

theorem realOrdinaryOrderedGenerationReduction : RealOrdinaryOrderedGenerationReductionStatement := by
  intro h
  constructor
  · intro r t hrt d e hd he hdI heI a D hdV heV
    obtain ⟨d', hd', hdo⟩ := exists_ordered_perm d
    obtain ⟨e', he', heo⟩ := exists_ordered_perm e
    obtain ⟨hdI', hdM⟩ := realWhittakerModels_of_perm_irreducible hd' hd hdI
    obtain ⟨heI', heM⟩ := realWhittakerModels_of_perm_irreducible he' he heI
    have hOrdered : UnequalGeneration hrt a D (realWhittakerModel r d' a)
        (realWhittakerModel t e' (-a)) (realPairLFactor d' e') :=
      h.1 r t hrt d' e' ((realRank_perm hd').symm.trans hd)
        ((realRank_perm he').symm.trans he) hdo heo hdI' heI' a D
        ((hdM a).symm ▸ hdV) ((heM (-a)).symm ▸ heV)
    exact unequalGeneration_congr (hdM a) (heM (-a))
      (realPairLFactor_perm hd' he').symm hOrdered
  · intro r d e hd he hdI heI a D hdV heV
    obtain ⟨d', hd', hdo⟩ := exists_ordered_perm d
    obtain ⟨e', he', heo⟩ := exists_ordered_perm e
    obtain ⟨hdI', hdM⟩ := realWhittakerModels_of_perm_irreducible hd' hd hdI
    obtain ⟨heI', heM⟩ := realWhittakerModels_of_perm_irreducible he' he heI
    have hOrdered : EqualGeneration a D (realWhittakerModel r d' a)
        (realWhittakerModel r e' (-a)) (realPairLFactor d' e') :=
      h.2 r d' e' ((realRank_perm hd').symm.trans hd)
        ((realRank_perm he').symm.trans he) hdo heo hdI' heI' a D
        ((hdM a).symm ▸ hdV) ((heM (-a)).symm ▸ heV)
    exact equalGeneration_congr (hdM a) (heM (-a))
      (realPairLFactor_perm hd' he').symm hOrdered

end Langlands.Global.RankinSelbergGlobal
