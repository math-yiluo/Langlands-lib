import Langlands.Global.Factors.CuspidalSupportEveryPlaceStatement
import Langlands.Global.Factors.CuspidalIsobaricFiniteSupport
import Langlands.Representation.Archimedean.ComplexStandardConstituent
import Langlands.Representation.Archimedean.RealStandardConstituentPermutation

/-! # Induced support of a cuspidal isobaric sum -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Automorphic.OperatorSubquotient

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ConstituentCompression (IsOperatorConstituent)

/-- Apply a transfer of simple constituents to the range of a map into a fixed space.
The transferred map uses a subspace of the ambient model and has the same range. -/
private theorem transferOperatorImage
    {K ι M E V : Type*} [Monoid K] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup V] [Module ℂ V]
    (src : K ⊕ ι → Module.End ℂ M) (T : Submodule ℂ E)
    (dst : K ⊕ ι → Module.End ℂ T) (ambient : K ⊕ ι → E → E)
    (hcompat : ∀ i x, (dst i x : E) = ambient i (x : E))
    (ρ : Representation ℂ K V) (L : ι → Module.End ℂ V) (A : M →ₗ[ℂ] V)
    (hA : ∀ i x, A (src i x) = Sum.elim (fun k => ρ k) L i (A x))
    (h0 : LinearMap.range A ≠ ⊥)
    (hirr : ∀ U : Submodule ℂ V, U ≤ LinearMap.range A →
      (∀ k x, x ∈ U → ρ k x ∈ U) → (∀ i x, x ∈ U → L i x ∈ U) →
      U = ⊥ ∨ U = LinearMap.range A)
    (transfer : ∀ [Nontrivial (LinearMap.range A)]
      (ρJ : Representation ℂ K (LinearMap.range A))
      (LJ : ι → Module.End ℂ (LinearMap.range A)),
      (∀ U : Submodule ℂ (LinearMap.range A), (∀ k x, x ∈ U → ρJ k x ∈ U) →
        (∀ i x, x ∈ U → LJ i x ∈ U) → U = ⊥ ∨ U = ⊤) →
      IsOperatorConstituent src (Sum.elim (fun k => ρJ k) LJ) →
      IsOperatorConstituent dst (Sum.elim (fun k => ρJ k) LJ)) :
    ∃ (W : Submodule ℂ E) (_ : W ≤ T) (B : W →ₗ[ℂ] V), LinearMap.range B = LinearMap.range A ∧
      ∀ i (f : W), ∃ hf : ambient i (f : E) ∈ W,
        B ⟨_, hf⟩ = Sum.elim (fun k => ρ k) L i (B f) := by
  let J := LinearMap.range A
  let H : K ⊕ ι → Module.End ℂ V := Sum.elim (fun k => ρ k) L
  have hstable (i : K ⊕ ι) : J ≤ J.comap (H i) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨src i x, hA i x⟩
  let ρJ := ρ.subrepresentation J (fun k => hstable (.inl k))
  let LJ (i : ι) : Module.End ℂ J := (L i).restrict (hstable (.inr i))
  let HJ : K ⊕ ι → Module.End ℂ J := Sum.elim (fun k => ρJ k) LJ
  have hJcoe (i : K ⊕ ι) (x : J) : (HJ i x : V) = H i (x : V) := by cases i <;> rfl
  let : Nontrivial J := J.nontrivial_iff_ne_bot.mpr h0
  have hJirr (U : Submodule ℂ J) (hK : ∀ k x, x ∈ U → ρJ k x ∈ U)
      (hL : ∀ i x, x ∈ U → LJ i x ∈ U) : U = ⊥ ∨ U = ⊤ := by
    have hle : U.map J.subtype ≤ J := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hstab (i : K ⊕ ι) (y : V) (hy : y ∈ U.map J.subtype) :
        H i y ∈ U.map J.subtype := by
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨HJ i x, ?_, hJcoe i x⟩
      cases i with
      | inl k => exact hK k x hx
      | inr X => exact hL X x hx
    rcases hirr _ hle (fun k => hstab (.inl k)) (fun i => hstab (.inr i)) with he | he
    · left
      apply Submodule.map_injective_of_injective J.injective_subtype
      simpa only [Submodule.map_bot] using he
    · right
      apply Submodule.map_injective_of_injective J.injective_subtype
      simpa only [Submodule.map_top, Submodule.range_subtype] using he
  have hsrc : IsOperatorConstituent src HJ := by
    refine ⟨⊤, fun _ _ _ => Submodule.mem_top,
      A.rangeRestrict.comp (⊤ : Submodule ℂ M).subtype, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := y.2
      exact ⟨⟨x, Submodule.mem_top⟩, Subtype.ext hx⟩
    · intro i x
      apply Subtype.ext
      exact (hA i x).trans (hJcoe i (A.rangeRestrict (x : M))).symm
  obtain ⟨S, hS, C, hC, heq⟩ := transfer ρJ LJ hJirr hsrc
  let W := S.map T.subtype
  let e : S ≃ₗ[ℂ] W := S.equivMapOfInjective T.subtype T.injective_subtype
  let B := (J.subtype.comp C).comp e.symm.toLinearMap
  have hB : LinearMap.range B = J := by
    dsimp only [B]
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr e.symm.surjective, Submodule.map_top,
      LinearMap.range_comp, LinearMap.range_eq_top.mpr hC, Submodule.map_top, Submodule.range_subtype]
  refine ⟨W, ?_, B, hB, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · intro i f
    obtain ⟨x, rfl⟩ := e.surjective f
    let y : S := ⟨dst i x, hS i x x.2⟩
    have hy : (e y : E) = ambient i (e x : E) := hcompat i x
    refine ⟨hy ▸ (e y).2, ?_⟩
    have hy' : (⟨_, hy ▸ (e y).2⟩ : W) = e y := Subtype.ext hy.symm
    rw [hy']
    change (C (e.symm (e y)) : V) = H i (C (e.symm (e x)) : V)
    rw [e.symm_apply_apply, e.symm_apply_apply, show C y = HJ i (C x) from heq i x]
    exact hJcoe i (C x)

section Places

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance supportRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance supportContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance supportSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance supportFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance supportStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance supportRealizationGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

set_option maxHeartbeats 450000 in
private theorem hasRealPlaceStandardConstituent_of_perm (Q : OperatorSubquotient F n)
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    {ds es : List RealBlock} (hperm : ds.Perm es)
    (hQ : Q.HasRealPlaceLanglandsQuotient v ds) :
    Q.HasRealPlaceStandardConstituent v es := by
  obtain ⟨hn, _, A, hK, hL, h0, hirr⟩ := hQ
  let ρ := Q.realPlaceCompactRepresentation v
  let L (X : Matrix (Fin n) (Fin n) ℝ) := Q.realPlaceLieAction v (1 ⊗ₜ X)
  have hA : IsRealStandardIntertwiner n ρ (Q.realPlaceLieAction v) ds A := ⟨hK, hL⟩
  let ambient : Matrix.unitaryGroup (Fin n) ℝ ⊕ Matrix (Fin n) (Fin n) ℝ →
      (Langlands.GeneralLinear n ℝ → ℂ) → (Langlands.GeneralLinear n ℝ → ℂ) :=
    Sum.elim (fun k => Whittaker.rightTranslation ℂ _ (Unitary.toUnits k))
      (rightDerivative (matrixModel ℝ n))
  have hcompat (i) (f : realStandardKFinite n es) :
      (realStandardOperators n es i f : Langlands.GeneralLinear n ℝ → ℂ) = ambient i f := by
    cases i with
    | inl k => exact realStandardRep_apply_coe n es k f
    | inr X => exact realStandardLie_one_tmul_apply_coe n es X f
  have heq (i) (f : realStandardKFinite n ds) :
      A (realStandardOperators n ds i f) = Sum.elim (fun k => ρ k) L i (A f) := by
    cases i with
    | inl k => exact hA.map_realStandardRep k f
    | inr X => exact hA.map_realStandardLie (1 ⊗ₜ X) f
  obtain ⟨W, hW, B, hB, hBeq⟩ := transferOperatorImage (realStandardOperators n ds)
    (realStandardKFinite n es) (realStandardOperators n es) ambient hcompat ρ L A heq
    h0 hirr (fun ρJ LJ hJ => realStandardConstituent_perm ρJ LJ hperm hn hJ)
  refine ⟨(realRank_perm hperm).symm.trans hn, W, hW, B, ?_, ?_, ?_, ?_⟩
  · intro k f
    let k' : Matrix.unitaryGroup (Fin n) ℝ :=
      ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩
    have hk : (Unitary.toUnits k' : Langlands.GeneralLinear n ℝ) = k := Units.ext rfl
    have hf := hBeq (.inl k') f
    change ∃ hm : Whittaker.rightTranslation ℂ _ (Unitary.toUnits k')
        (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ W, B ⟨_, hm⟩ = ρ k' (B f) at hf
    simpa only [hk] using hf
  · intro X f
    exact hBeq (.inr X) f
  · rw [hB]
    exact h0
  · intro U hU hKU hLU
    have hUA : U ≤ LinearMap.range A := hU.trans_eq hB
    rcases hirr U hUA hKU hLU with hb | hr
    · exact Or.inl hb
    · exact Or.inr (hr.trans hB.symm)

set_option maxHeartbeats 450000 in
private theorem hasComplexPlaceStandardConstituent_of_perm (Q : OperatorSubquotient F n)
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v})
    {ds es : List ComplexCharacterData} (hperm : ds.Perm es)
    (hQ : Q.HasComplexPlaceLanglandsQuotient v ds) :
    Q.HasComplexPlaceStandardConstituent v es := by
  obtain ⟨hn, _, A, hK, hL, h0, hirr⟩ := hQ
  let ρ := Q.complexPlaceCompactRepresentation v
  let L (X : Matrix (Fin n) (Fin n) ℂ) := Q.complexPlaceLieAction v (1 ⊗ₜ X)
  have hA : IsComplexStandardIntertwining n ρ (Q.complexPlaceLieAction v) ds A := ⟨hK, hL⟩
  let ambient : Matrix.unitaryGroup (Fin n) ℂ ⊕ Matrix (Fin n) (Fin n) ℂ →
      (Langlands.GeneralLinear n ℂ → ℂ) → (Langlands.GeneralLinear n ℂ → ℂ) :=
    Sum.elim (fun k => Whittaker.rightTranslation ℂ _ (Unitary.toUnits k))
      (rightDerivative (matrixModel ℂ n))
  have hcompat (i) (f : complexStandardKFinite n es) :
      (complexStandardOperators n es i f : Langlands.GeneralLinear n ℂ → ℂ) = ambient i f := by
    cases i with
    | inl k => exact principalSeriesRep_apply_coe ℂ n _ k f
    | inr X => exact principalSeriesLie_one_tmul_apply_coe ℂ n _ X f
  have heq (i) (f : complexStandardKFinite n ds) :
      A (complexStandardOperators n ds i f) = Sum.elim (fun k => ρ k) L i (A f) := by
    cases i with
    | inl k => exact hA.map_rep k f
    | inr X => exact hA.map_lie (1 ⊗ₜ X) f
  obtain ⟨W, hW, B, hB, hBeq⟩ := transferOperatorImage (complexStandardOperators n ds)
    (complexStandardKFinite n es) (complexStandardOperators n es) ambient hcompat ρ L A heq
    h0 hirr (fun ρJ LJ hJ => complexStandardConstituent_of_perm ρJ LJ hJ hn hperm)
  refine ⟨hperm.length_eq.symm.trans hn, W, hW, B, ?_, ?_, ?_, ?_⟩
  · intro k f
    let k' : Matrix.unitaryGroup (Fin n) ℂ :=
      ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩
    have hk : (Unitary.toUnits k' : Langlands.GeneralLinear n ℂ) = k := Units.ext rfl
    have hf := hBeq (.inl k') f
    change ∃ hm : Whittaker.rightTranslation ℂ _ (Unitary.toUnits k')
        (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ W, B ⟨_, hm⟩ = ρ k' (B f) at hf
    simpa only [hk] using hf
  · intro X f
    exact hBeq (.inr X) f
  · rw [hB]
    exact h0
  · intro U hU hKU hLU
    have hUA : U ≤ LinearMap.range A := hU.trans_eq hB
    rcases hirr U hUA hKU hLU with hb | hr
    · exact Or.inl hb
    · exact Or.inr (hr.trans hB.symm)

end Places

end Langlands.Automorphic.OperatorSubquotient

namespace Langlands.Global

/-- An isobaric sum of cuspidal automorphic representations is a constituent of
induction from the summands at every place. -/
theorem cuspidalIsobaricSupport : CuspidalIsobaricSupportStatement.{u, uQ} := by
  intro F _ _ _ r k m hm T P h Q hQ
  refine ⟨cuspidalIsobaricSum_finiteSupport hm hQ, ?_, ?_⟩
  · intro v
    obtain ⟨ds, hds, ls, hperm, hquot⟩ := hQ.2.1 v
    exact ⟨ds, hds, Q.subquotient.hasRealPlaceStandardConstituent_of_perm v hperm hquot⟩
  · intro v
    obtain ⟨ds, hds, ls, hperm, hquot⟩ := hQ.2.2 v
    exact ⟨ds, hds, Q.subquotient.hasComplexPlaceStandardConstituent_of_perm v hperm hquot⟩

end Langlands.Global
