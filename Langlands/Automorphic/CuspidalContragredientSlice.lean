import Langlands.Automorphic.CuspidalUnitaryCompactForm
import Langlands.Automorphic.OperatorRealizationCountable
import Langlands.Representation.Unitary.CountableDualAdmissible
import Langlands.Automorphic.CuspidalFiniteSlice
import Langlands.Automorphic.Contragredient
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

/-! # Irreducible admissible finite slices of supplied unitary cuspidal duals -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Cardinal Module Langlands.FiniteVectors

variable {F : Type uF} [Field F] [NumberField F]

local instance contragredientSliceGroup1 (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance contragredientSliceGroup2 (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance contragredientSliceGroup3 (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance contragredientSliceGroup4 (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance contragredientSliceGroup5 (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance contragredientSliceGroup6 (n : ℕ) (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance contragredientSliceGroup7 (n : ℕ) (S : FiniteRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Every open subgroup of the finite adelic matrix group contains a compact open one. -/
theorem finiteAdelicGL_exists_compact_le (n : ℕ) (U : OpenSubgroup (FiniteAdelicGL F n)) :
    ∃ U' : OpenSubgroup (FiniteAdelicGL F n), U' ≤ U ∧
      IsCompact (U' : Set (FiniteAdelicGL F n)) := by
  refine ⟨U ⊓ FiniteAdelicGL.standardIntegral F n, inf_le_left, ?_⟩
  refine (FiniteAdelicGL.isCompact_standardIntegral F n).of_isClosed_subset
    (U ⊓ FiniteAdelicGL.standardIntegral F n).isClosed ?_
  intro x hx
  exact (OpenSubgroup.mem_inf.mp hx).2

set_option maxHeartbeats 2000000 in
/-- A nonzero irreducible admissible subrepresentation of the finite action of a realization
gives an irreducible admissible finite slice of the corresponding cuspidal realization. -/
theorem CuspidalOperatorRealization.exists_finiteSlice_of_subrepresentation
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (S : CuspidalOperatorRealization F r)
    (A : Subrepresentation S.realization.finiteRepresentation) (hA : A ≠ ⊥)
    (hirr : A.toRepresentation.IsIrreducible) (hadm : IsAdmissible A.toRepresentation) :
    ∃ B : S.FiniteSlice, B.subspace.IsIrreducible ∧
      Langlands.IsAdmissible B.subspace.representation := by
  let ι : FiniteRealizationMap F (r + 1) A.toRepresentation :=
    { toLinearMap := S.realization.formInclusion.toLinearMap ∘ₗ A.toSubmodule.subtype
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        exact Representation.IntertwiningMap.isIntertwining _ _ S.realization.formInclusion g
          x.val }
  have hι : FiniteRealizationMap.IsInjective F (r + 1) ι :=
    S.realization.formInclusion_injective.comp Subtype.val_injective
  let e := finiteRealizationImageEquiv F (r + 1) ι hι
  let B : S.FiniteSlice :=
    { subspace := finiteRealizationImage F (r + 1) ι
      le_image := by
        rintro _ ⟨x, rfl⟩
        exact ⟨x.val, rfl⟩
      nonzero := by
        intro h
        apply hA
        apply Subrepresentation.ext
        change A.toSubmodule = ⊥
        rw [eq_bot_iff]
        intro v hv
        have hmem : ι ⟨v, hv⟩ ∈ finiteRealizationImage F (r + 1) ι := ⟨⟨v, hv⟩, rfl⟩
        rw [h] at hmem
        have h0 : ι ⟨v, hv⟩ = ι 0 := by rw [map_zero]; exact hmem
        exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val (hι h0)) }
  exact ⟨B, CountableDual.isIrreducible_of_equiv _ e hirr, Langlands.isAdmissible_of_equiv e hadm⟩

/-- Every space of smooth compact-finite functionals on `T` has countable dimension when
`T'` is an actual contragredient realization of `T`. -/
theorem OperatorRealization.rank_contragredientFunctionals_le {n : ℕ}
    (S S' : OperatorRealization F n) (hS' : S'.IsIrreducible)
    (B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ)
    (hsurj : ∀ l : Module.Dual ℂ S.Space, S.IsContragredientFunctional l → ∃ x, B.flip x = l)
    (L : Submodule ℂ (Module.Dual ℂ S.Space))
    (hL : ∀ l ∈ L, IsSmoothVector S.finiteRepresentation.dual l ∧
      IsFiniteVector S.compactRepresentation.dual l) :
    Module.rank ℂ L ≤ ℵ₀ := by
  have hle : L ≤ LinearMap.range B.flip := fun l hl => hsurj l (hL l hl)
  calc Module.rank ℂ L ≤ Module.rank ℂ (LinearMap.range B.flip) := Submodule.rank_mono hle
    _ ≤ Module.rank ℂ S'.Space := rank_range_le _
    _ ≤ ℵ₀ := S'.rank_le_aleph0 hS'

set_option maxHeartbeats 4000000 in
/-- Pairing against a fixed vector with a compact-invariant positive form is a contragredient
functional. -/
theorem OperatorRealization.isContragredientFunctional_conjFunctional {n : ℕ}
    (S : OperatorRealization F n) (b : InvariantPositiveForm S.finiteRepresentation)
    (hb : ∀ (k : standardInfiniteCompact F n) (f g : S.Space),
      b.inner (S.compactRepresentation k f) (S.compactRepresentation k g) = b.inner f g)
    (h : S.Space) :
    S.IsContragredientFunctional (CountableDual.conjFunctional b.toInnerProductCore h) := by
  constructor
  · obtain ⟨U, hU⟩ := S.finiteRepresentation_isSmooth h
    refine ⟨U, ?_⟩
    rw [fixedVectors, Representation.mem_invariants]
    intro u
    change S.finiteRepresentation.dual (u : FiniteAdelicGL F n)
      (CountableDual.conjFunctional b.toInnerProductCore h) = _
    rw [← CountableDual.conjFunctional_apply_rep]
    exact congrArg _ (hU u)
  · have hk : ∀ k, S.compactRepresentation.dual k
        (CountableDual.conjFunctional b.toInnerProductCore h) =
        CountableDual.conjFunctional b.toInnerProductCore (S.compactRepresentation k h) := by
      intro k
      apply LinearMap.ext
      intro y
      change b.inner h (S.compactRepresentation k⁻¹ y) = b.inner (S.compactRepresentation k h) y
      have := hb k h (S.compactRepresentation k⁻¹ y)
      rw [Representation.self_inv_apply] at this
      exact this.symm
    have hfin : (orbitSpan S.compactRepresentation h).FG :=
      Module.Finite.iff_fg.mp (S.compactRepresentation_isFiniteVector h)
    have hle : orbitSpan S.compactRepresentation.dual
        (CountableDual.conjFunctional b.toInnerProductCore h) ≤
        (orbitSpan S.compactRepresentation h).map
          (CountableDual.conjFunctional b.toInnerProductCore) := by
      rw [orbitSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hmem : CountableDual.conjFunctional b.toInnerProductCore
          (S.compactRepresentation k h) ∈ (orbitSpan S.compactRepresentation h).map
            (CountableDual.conjFunctional b.toInnerProductCore) :=
        ⟨_, action_mem_orbitSpan _ k h, rfl⟩
      rw [← hk k] at hmem
      exact hmem
    have : Module.Finite ℂ ((orbitSpan S.compactRepresentation h).map
        (CountableDual.conjFunctional b.toInnerProductCore)) :=
      Module.Finite.iff_fg.mpr (hfin.map _)
    exact Submodule.finiteDimensional_of_le hle

set_option maxHeartbeats 1000000 in
/-- **Irreducible admissible slices of supplied unitary cuspidal duals.** If `T` has unitary
central character and `T'` is an actual full-operator contragredient of `T`, then `T'`
contains a nonzero actual finite slice whose finite adelic action is irreducible and
admissible. -/
theorem CuspidalOperatorRealization.exists_irreducibleAdmissible_finiteSlice_of_contragredient
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (hdual : T'.realization.IsContragredientOf T.realization) :
    ∃ A : T'.FiniteSlice, A.subspace.IsIrreducible ∧
      Langlands.IsAdmissible A.subspace.representation := by
  obtain ⟨b, hb⟩ := T.exists_compactInvariantForm hT
  obtain ⟨B, hBinv, -, hinj, hsurj⟩ := hdual
  obtain ⟨A₀, hA₀, hirr, hadm⟩ := CountableDual.exists_irreducible_admissible
    T.realization.finiteRepresentation T.realization.finiteRepresentation_isSmooth
    T.realization.compactRepresentation
    (fun d k f => T.realization.finiteRepresentation_compactRepresentation d k f) b hb
    T.realization.compactRepresentation_isFiniteVector (finiteAdelicGL_exists_compact_le (r + 1))
    (T.realization.rank_contragredientFunctionals_le T'.realization T'.irreducible B hsurj)
  obtain ⟨A', hA'ne, hA'irr, hA'adm⟩ := CountableDual.exists_dual_subrepresentation
    T.realization.finiteRepresentation T'.realization.finiteRepresentation
    T'.realization.finiteRepresentation_isSmooth b B.flip hinj
    (fun d x => OperatorRealization.IsInvariantPairing.flip_finite hBinv d x)
    (fun h => hsurj _ (T.realization.isContragredientFunctional_conjFunctional b hb h))
    A₀ hA₀ hirr hadm
  exact T'.exists_finiteSlice_of_subrepresentation A' hA'ne hA'irr hA'adm

/-- A chosen nonzero actual finite slice of a supplied contragredient `T'` of a unitary
cuspidal realization `T`, on which the finite adelic action is irreducible and admissible. -/
noncomputable def CuspidalOperatorRealization.contragredientIrreducibleSlice
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (hdual : T'.realization.IsContragredientOf T.realization) : T'.FiniteSlice :=
  Classical.choose (T.exists_irreducibleAdmissible_finiteSlice_of_contragredient T' hT hdual)

theorem CuspidalOperatorRealization.contragredientIrreducibleSlice_isIrreducible
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (hdual : T'.realization.IsContragredientOf T.realization) :
    (T.contragredientIrreducibleSlice T' hT hdual).subspace.IsIrreducible :=
  (Classical.choose_spec
    (T.exists_irreducibleAdmissible_finiteSlice_of_contragredient T' hT hdual)).1

theorem CuspidalOperatorRealization.contragredientIrreducibleSlice_isAdmissible
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (hT : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (hdual : T'.realization.IsContragredientOf T.realization) :
    Langlands.IsAdmissible (T.contragredientIrreducibleSlice T' hT hdual).subspace.representation :=
  (Classical.choose_spec
    (T.exists_irreducibleAdmissible_finiteSlice_of_contragredient T' hT hdual)).2

end Langlands.Automorphic
