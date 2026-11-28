import Langlands.BaseChange.TwistedCharacter.InducedSupport
import Langlands.BaseChange.TwistedCharacter.UnramifiedTraceFamily
import Langlands.BaseChange.TwistedCharacter.EssentiallyTemperedDatum
import Langlands.BaseChange.TwistedCharacter.OrbitVisibility
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.Representation.Classification.SupercuspidalSupportCharacterTwist
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Category.UniverseLift

/-! # Selection of irreducibles by the unramified twist class of a supercuspidal support -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear HarmonicAnalysis PadicField.TopologicalData Classification

universe u v z

section Padic

variable {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p} (T : E.TopologicalData)

/-- The unramified field character `a ↦ c ^ ord(a)` as a smooth character. -/
def unramifiedFieldCharacter (c : ℂˣ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ E.Carrierˣ := by
  letI := T.topology
  exact ⟨T.unramifiedCharacter c, T.isOpen_ker_unramifiedCharacter c⟩

theorem isSmooth_universeLift_twist_determinantUnramified {n : ℕ} {W : Type z} [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GeneralLinear n E.Carrier) W)
    (hs : letI := T.topology; IsSmooth π) (c : ℂˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsSmooth (universeLiftRepresentation.{v} (twist (determinantUnramified E.Carrier n c) π)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (isSmooth_universeLift_iff _).mpr
    ((isSmooth_twist_iff _ _ (isOpen_ker_determinantUnramified E.Carrier n c)).mpr hs)

/-- An irreducible representation is selected when some unramified determinant twist has the
given supercuspidal support. -/
def supportTwistSelection (n : ℕ) (s : Multiset (CuspidalDatum.{z, v} T)) :
    ∀ (W : Type z) [AddCommGroup W] [Module ℂ W],
      Representation ℂ (GeneralLinear n E.Carrier) W → Prop := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro W _ _ π
  exact ∃ (hs : IsSmooth π) (c : ℂˣ), T.IsSupercuspidalSupport
    (SmoothRep.of (universeLiftRepresentation.{v} (twist (determinantUnramified E.Carrier n c) π))
      (isSmooth_universeLift_twist_determinantUnramified T π hs c)) s

set_option maxHeartbeats 800000 in
/-- The selection is invariant under equivalence. -/
theorem supportTwistSelection_of_equiv {n : ℕ} (s : Multiset (CuspidalDatum.{z, v} T))
    {W W' : Type z} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π : Representation ℂ (GeneralLinear n E.Carrier) W}
    {π' : Representation ℂ (GeneralLinear n E.Carrier) W'} (e : π.Equiv π')
    (h : supportTwistSelection T n s W π) : supportTwistSelection T n s W' π' := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨hs, c, hsupp⟩ := h
  have hs' : IsSmooth π' := isSmooth_of_injective e.symm.toIntertwiningMap e.symm.injective hs
  refine ⟨hs', c, hsupp.of_iso (SmoothRep.mkIso ?_)⟩
  exact ((universeLiftEquiv.{v} _).symm.trans (twistEquiv _ e)).trans (universeLiftEquiv.{v} _)

set_option maxHeartbeats 800000 in
/-- Invariant unramified twists of a representation with the given support are selected. -/
theorem supportTwistSelection_of_isUnramifiedTwistOf {n : ℕ} (hn : 0 < n)
    (s : Multiset (CuspidalDatum.{z, v} T)) {V : Type z} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear n E.Carrier) V) (hτs : letI := T.topology; IsSmooth τ)
    (hsτ : letI := T.topology; T.IsSupercuspidalSupport
      (SmoothRep.of (universeLiftRepresentation.{v} τ) ((isSmooth_universeLift_iff τ).mpr hτs)) s)
    (θ : GeneralLinear n E.Carrier ≃* GeneralLinear n E.Carrier)
    {W : Type z} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GeneralLinear n E.Carrier) W)
    (h : letI := T.topology; IsUnramifiedTwistOf θ τ π) :
    supportTwistSelection T n s W π := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  let := LocalFieldTopology.generalLinear_t2Space E.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
  obtain ⟨ψ, hψ, -, ⟨e⟩⟩ := h
  have hψeq : ψ = determinantUnramified E.Carrier n (ψ (Iwasawa.diagonalUnits
      (Pi.mulSingle (⟨0, hn⟩ : Fin n) (LocalFieldData.ofInstances E.Carrier).uniformizerUnit))) :=
    @eq_detOrderCharacter_of_isUnramified E.Carrier _ T.valuativeRel T.topology T.localField n
      ⟨0, hn⟩ ψ hψ
  set c₀ := ψ (Iwasawa.diagonalUnits
      (Pi.mulSingle (⟨0, hn⟩ : Fin n) (LocalFieldData.ofInstances E.Carrier).uniformizerUnit))
  have hτψ : IsSmooth (twist ψ τ) := (isSmooth_twist_iff _ _ hψ.isOpen_ker).mpr hτs
  have hs : IsSmooth π := isSmooth_of_injective e.toIntertwiningMap e.injective hτψ
  refine ⟨hs, c₀⁻¹, hsτ.of_iso (SmoothRep.mkIso ?_)⟩
  have heq : twist (determinantUnramified E.Carrier n c₀⁻¹) (twist ψ τ) = τ := by
    rw [hψeq, twist_twist, ← determinantUnramified_mul, inv_mul_cancel,
      determinantUnramified_one T n, twist_one]
  exact ((universeLiftEquiv.{v} τ).symm.trans (equivOfRepresentationEq heq.symm)).trans
    ((twistEquiv _ e.symm).trans (universeLiftEquiv.{v} _))

set_option maxHeartbeats 1600000 in
/-- A representation equivalent to an irreducible one with support `s'` is selected exactly when
some unramified character twist of `s'` is `s`. -/
theorem supportTwistSelection_iff {n : ℕ} (hn : 0 < n) (s s' : Multiset (CuspidalDatum.{z, v} T))
    (D : letI := T.topology; SmoothRep.{0, v, max v z} ℂ (GeneralLinear n E.Carrier))
    (hDirr : letI := T.topology; D.IsIrreducible) (hD : T.IsSupercuspidalSupport D s')
    {W : Type z} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GeneralLinear n E.Carrier) W)
    (e : letI := T.topology; π.Equiv D.representation) :
    supportTwistSelection T n s W π ↔
      ∃ c : ℂˣ, s'.map (CuspidalDatum.characterTwist (unramifiedFieldCharacter T c)) = s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  have hπs : IsSmooth π := isSmooth_of_injective e.toIntertwiningMap e.injective D.isSmooth
  have hiso (c : ℂˣ) : SmoothRep.of (universeLiftRepresentation.{v}
      (twist (determinantUnramified E.Carrier n c) π))
        (isSmooth_universeLift_twist_determinantUnramified T π hπs c) ≅
      D.twist ((unramifiedFieldCharacter T c).toMonoidHom.comp determinant)
        ((unramifiedFieldCharacter T c).isOpen_ker.preimage
          (T.generalLinearDeterminant n).continuous) :=
    SmoothRep.mkIso ((universeLiftEquiv.{v} _).symm.trans (twistEquiv _ e))
  have hirr (c : ℂˣ) : (SmoothRep.of (universeLiftRepresentation.{v}
      (twist (determinantUnramified E.Carrier n c) π))
        (isSmooth_universeLift_twist_determinantUnramified T π hπs c)).IsIrreducible :=
    (isIrreducible_iff_of_equiv (SmoothRep.equivOfIso (hiso c))).mpr
      ((SmoothRep.isIrreducible_twist_iff _ _ D).mpr hDirr)
  constructor
  · rintro ⟨hs, c, hsupp⟩
    refine ⟨c, (glSupercuspidalSupportUniqueness.{z, v} p E T n hn _ (hirr c) _ _ hsupp
      ((hD.characterTwist (unramifiedFieldCharacter T c)).of_iso (hiso c).symm)).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨hπs, c, ?_⟩
    rw [← hc]
    exact (hD.characterTwist (unramifiedFieldCharacter T c)).of_iso (hiso c).symm

section Covering

theorem sum_rank_of_ofFn_eq {k : ℕ} (g : Fin k → CuspidalDatum.{z, v} T)
    {s : Multiset (CuspidalDatum.{z, v} T)} (hg : (List.ofFn g : Multiset _) = s) :
    ∑ i, (g i).rank = (s.map CuspidalDatum.rank).sum := by
  rw [← hg, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  rfl

theorem mem_toFinset_of_ofFn_eq [DecidableEq (CuspidalDatum.{z, v} T)] {k : ℕ}
    (g : Fin k → CuspidalDatum.{z, v} T)
    {s : Multiset (CuspidalDatum.{z, v} T)} (hg : (List.ofFn g : Multiset _) = s) (i : Fin k) :
    g i ∈ s.toFinset := by
  rw [Multiset.mem_toFinset, ← hg]
  exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem cuspidalProductInduced_hasFiniteLength {k n : ℕ} (hn : 0 < n)
    (g : Fin k → CuspidalDatum.{z, v} T) (h : ∑ i, (g i).rank = n)
    (A : letI := T.topology; ∀ i, SupercuspidalRep.{v, z} (F := E.Carrier) (n := (g i).rank)) :
    letI := T.topology
    (T.cuspidalProductInduced g h A).HasFiniteLength :=
  irreducibleProductFiniteLength.{v, z} E T n hn (T.cuspidalShape g h) (fun i => (A i).obj)
    (fun i => (A i).property.1)

set_option maxHeartbeats 1600000 in
/-- Finitely many supercuspidal products of finite length contain every irreducible
representation with a given supercuspidal support as a subquotient. -/
theorem exists_finite_cuspidalProducts_covering {n : ℕ} (hn : 0 < n)
    (s : Multiset (CuspidalDatum.{z, v} T)) (hrank : (s.map CuspidalDatum.rank).sum = n) :
    letI := T.topology
    ∃ (ι : Type (max v (z + 1))) (_ : Fintype ι)
      (P : ι → SmoothRep.{0, v, max v z} ℂ (GeneralLinear n E.Carrier)),
      (∀ i, (P i).HasFiniteLength) ∧
      ∀ D : SmoothRep.{0, v, max v z} ℂ (GeneralLinear n E.Carrier),
        T.IsSupercuspidalSupport D s → ∃ i, D.IsIrreducible ∧ SmoothRep.IsSubquotient D (P i) := by
  classical
  let := T.topology
  let ι := {f : Fin (Multiset.card s) → s.toFinset //
    (List.ofFn (fun i => ((f i : s.toFinset) : CuspidalDatum.{z, v} T)) : Multiset _) = s}
  choose R hR using fun d : s.toFinset => Quotient.exists_rep d.1.cls
  have hsumf (f : ι) : ∑ i, ((f.1 i : s.toFinset) : CuspidalDatum.{z, v} T).rank = n :=
    (sum_rank_of_ofFn_eq T _ f.2).trans hrank
  refine ⟨ι, Fintype.ofFinite ι, fun f => T.cuspidalProductInduced
    (fun i => ((f.1 i : s.toFinset) : CuspidalDatum.{z, v} T)) (hsumf f) (fun i => R (f.1 i)),
    fun f => cuspidalProductInduced_hasFiniteLength T hn _ (hsumf f) _, fun D hD => ?_⟩
  obtain ⟨k', ρ, hρs, hcon⟩ := hD
  have hk : k' = Multiset.card s := by
    rw [← hρs]
    simp
  subst hk
  let f : ι := ⟨fun i => ⟨ρ i, mem_toFinset_of_ofFn_eq T ρ hρs i⟩, hρs⟩
  exact ⟨f, (isCuspidalConstituent_iff ρ D (hsumf f) (fun i => R (f.1 i))
    (fun i => hR (f.1 i))).mp hcon⟩

end Covering

section Visibility

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F E.Carrier]
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier) (σ : E.Carrier ≃ₐ[F] E.Carrier)

set_option maxHeartbeats 1600000 in
include hModule in
/-- Every irreducible representation selected by an unramified twist class of a supercuspidal
support has nonzero fixed vectors at one compact open level. -/
theorem exists_compact_fixed_of_supportTwistSelection {n : ℕ} (hn : 0 < n)
    (hθ : letI := T.topology; ∀ U : OpenSubgroup (GeneralLinear n E.Carrier),
      ∃ J : OpenSubgroup (GeneralLinear n E.Carrier), J ≤ U ∧
        IsCompact (J : Set (GeneralLinear n E.Carrier)) ∧ ∀ j ∈ J, (entrywiseAut σ n).symm j ∈ J)
    (s : Multiset (CuspidalDatum.{z, v} T)) (hrank : (s.map CuspidalDatum.rank).sum = n) :
    letI := T.topology
    ∃ J : OpenSubgroup (GeneralLinear n E.Carrier),
      IsCompact (J : Set (GeneralLinear n E.Carrier)) ∧
      ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear n E.Carrier) W),
        supportTwistSelection T n s W π → fixedVectors π J.toSubgroup ≠ ⊥ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  let := T.generalLinearTopologicalGroup n
  let := LocalFieldTopology.generalLinear_t2Space E.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
  obtain ⟨ι, _, P, hP, hcover⟩ := exists_finite_cuspidalProducts_covering T hn s hrank
  obtain ⟨J, hJc, -, hvis⟩ := exists_compact_open_fixed_constituentTwists (entrywiseAut σ n) hθ P hP
  refine ⟨J, hJc, fun W _ _ π hS => ?_⟩
  obtain ⟨hs, c, hsupp⟩ := hS
  obtain ⟨f, hDirr, hDsub⟩ := hcover _ hsupp
  have heq : twist (determinantUnramified E.Carrier n c⁻¹)
      (twist (determinantUnramified E.Carrier n c) π) = π := by
    rw [twist_twist, ← determinantUnramified_mul, inv_mul_cancel, determinantUnramified_one T n,
      twist_one]
  have htw : IsUnramifiedTwistOf (entrywiseAut σ n)
      (universeLiftRepresentation.{v} (twist (determinantUnramified E.Carrier n c) π))
      (universeLiftRepresentation.{v} π) :=
    ⟨determinantUnramified E.Carrier n c⁻¹, isUnramifiedCharacter_determinantUnramified E.Carrier n _,
      fun g => determinantUnramified_entrywiseAut E.Carrier σ n _ g,
      ⟨((universeLiftEquiv.{v} π).symm.trans (equivOfRepresentationEq heq.symm)).trans
        (twistEquiv _ (universeLiftEquiv.{v} _))⟩⟩
  have hfix := hvis f _ hDirr hDsub _ (universeLiftRepresentation.{v} π) htw
  exact (fixedVectors_ne_bot_iff_of_equiv (universeLiftEquiv.{v} π) J.toSubgroup).mpr hfix

end Visibility

end Padic

end Langlands.BaseChange
