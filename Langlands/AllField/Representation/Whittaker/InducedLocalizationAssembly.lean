import Langlands.Representation.Whittaker.InducedLocalizationAssembly
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.AllField.Representation.Geometric.WeylStatementSupplement
import Langlands.AllField.Representation.Whittaker.InducedLocalizationStatement
noncomputable section

open CategoryTheory

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding CompactLocalizationStatement UnipotentOrbitStatement inducedLocalization_of_prerequisites
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem
open Langlands.AllField.Geometric
open Langlands.Jacquet.Localization

universe uF uV

private theorem locallyConstant_of_open_kernel {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : G →* ℂˣ) (hθ : IsOpen (θ.ker : Set G)) :
    IsLocallyConstant (fun g => (θ g : ℂ)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨(fun x : G => g⁻¹ * x) ⁻¹' (θ.ker : Set G),
    hθ.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro x hx
    have hx' : θ (g⁻¹ * x) = 1 := hx
    have h : (θ g)⁻¹ * θ x = 1 := by
      simpa only [map_mul, map_inv] using hx'
    exact congrArg Units.val (inv_mul_eq_one.mp h).symm

private theorem limit_top_of_limit {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U) :
    IsLimitOfCompactSubgroups (⊤ : Subgroup U) := by
  intro C hC
  obtain ⟨K, hK, hCK⟩ :=
    hU (Subtype.val '' C) (hC.image continuous_subtype_val)
  refine ⟨K.comap (⊤ : Subgroup U).subtype, ?_, ?_⟩
  · exact (isClosed_univ.isClosedEmbedding_subtypeVal).isCompact_preimage hK
  · intro x hx
    exact hCK ⟨x, hx, rfl⟩

/-- Conditional assembly of the induced quotient equivalence from the four
separate geometric, compact-localization and filtration propositions. -/
theorem inducedLocalization_of_prerequisites
    (hOrbit : UnipotentOrbitStatement.{uF})
    (hWitness : NonOpenCharacterWitnessStatement.{uF})
    (hCompact : CompactLocalizationStatement.{uF, uV})
    (hCollapse : FiltrationCollapseStatement.{uF, max uF uV}) :
    InducedLocalizationStatement.{uF, uV} := by
  intro F _ _ _ _
  let := (⟨⟩ : LocalFieldData F).fieldT2
  intro n B
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  let := (⟨⟩ : LocalFieldData F).generalLinearNonarchimedean (n + 1)
  let := (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
  let := (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (n + 1)
  let := (⟨⟩ : LocalFieldData F).upperUnipotentNonarchimedean (n + 1)
  intro V _ _ π ψ hψc hψn hψu hπ _hfinite
  let P := B.parabolic F
  let U := upperUnipotent (n + 1) F
  let σ := (FiniteTensor.external π).comp (B.leviProjection F)
  have hσ : IsSmooth σ :=
    isSmooth_comp (B.leviProjection F)
      (B.leviProjectionContinuous F).continuous
      (FiniteTensor.isSmooth_external π (fun i => (hπ i).1))
  let A : SmoothRep.{0, uF, uV} ℂ P := SmoothRep.of σ hσ
  have hP : IsClosed (P : Set (Langlands.GeneralLinear (n + 1) F)) :=
    B.isClosed_parabolic F
  have hU : IsClosed (U : Set (Langlands.GeneralLinear (n + 1) F)) :=
    UpperUnipotent.isClosed
  have hθopen : IsOpen ((entrywiseCharacter ψ (n + 1)).ker : Set U) := by
    rw [entrywiseCharacter_eq_standardCharacter_ofComplex ψ hψc hψn hψu n]
    exact isOpen_ker_of_continuous_complex_character _
      (standardCharacterContinuous
        (HarmonicAnalysis.UnitaryAdditiveCharacter.ofComplex ψ hψc hψn hψu) n).continuous
  let θ : Induction.SmoothCharacter ℂ U :=
    ⟨entrywiseCharacter ψ (n + 1), hθopen⟩
  have hθloc : IsLocallyConstant (fun u => (θ.toMonoidHom u : ℂ)) :=
    locallyConstant_of_open_kernel θ.toMonoidHom θ.isOpen_ker
  have hlim : IsLimitOfCompactSubgroups (⊤ : Subgroup U) :=
    limit_top_of_limit U
      (upperUnipotent_isLimitOfCompactSubgroups F (⟨⟩ : LocalFieldData F) (n + 1))
  let : CompactSpace (Induction.LeftQuotient P) :=
    Langlands.AllField.Parabolic.parabolicQuotientCompact F (⟨⟩ : LocalFieldData F) B
  obtain ⟨_hbij, m, s, e, he⟩ := hOrbit F (⟨⟩ : LocalFieldData F) n B
  let vopen : MinimalRepresentatives B (BlockShape.singletons (n + 1)) :=
    ⟨B.reversePermutation.symm, reversePermutation_isMinimalRepresentative B⟩
  let j := e.symm vopen
  have hrep : s.representative j = (B.reverseMatrix F)⁻¹ := by
    rw [he j]
    change permutation (n + 1) F (e (e.symm vopen)).val = _
    rw [e.apply_symm_apply]
    exact (permutation_inv (n + 1) F B.reversePermutation).symm
  let T := restrictedCompactInduction (R := ℂ) P U
  let ambient := T.obj A
  let sf := s.supportFiltration (R := ℂ)
  let fs : ObjectRepFiltration ambient m :=
    ObjectRepFiltration.ofSubrepresentations (fun k => (sf.step k).obj A)
      (sf.monotone A) (sf.zero A) (sf.top A)
  let pieceσ (i : Fin m) :=
    σ.comp (stabilizerToInducing P U (s.representative i))
  have hsmooth (i : Fin m) : IsSmooth (pieceσ i) := by
    apply isSmooth_comp _ _ hσ
    exact ((continuous_const.mul
      (continuous_subtype_val.comp continuous_subtype_val)).mul
        continuous_const).subtype_mk _
  have qeq (i : Fin m) :
      Nonempty
        (Coinvariants (fs.gradedRepresentation i).ρ (⊤ : Subgroup U)
            (θ.toMonoidHom.comp (⊤ : Subgroup U).subtype) ≃ₗ[ℂ]
          Coinvariants (pieceσ i) (⊤ : Subgroup (orbitStabilizer P U (s.representative i)))
            ((θ.toMonoidHom.comp (orbitStabilizer P U (s.representative i)).subtype).comp
              (⊤ : Subgroup (orbitStabilizer P U (s.representative i))).subtype)) := by
    obtain ⟨eg⟩ := closedSubgroupMackeyFiltration
      (Langlands.GeneralLinear (n + 1) F) P U hP hU m s i
    let er := Representation.equivOfIso (eg.app A)
    obtain ⟨ec⟩ := hCompact F (⟨⟩ : LocalFieldData F) n
      (orbitStabilizer P U (s.representative i))
      (isClosed_orbitStabilizer P U (s.representative i) hP)
      (PiTensorProduct ℂ V) (pieceσ i) (hsmooth i) θ
    exact ⟨(representationEquiv (⊤ : Subgroup U)
      (θ.toMonoidHom.comp (⊤ : Subgroup U).subtype) er).trans ec⟩
  have hvanish (i : Fin m) (hi : i ≠ j) :
      Subsingleton (Coinvariants (fs.gradedRepresentation i).ρ
        (⊤ : Subgroup U) (θ.toMonoidHom.comp (⊤ : Subgroup U).subtype)) := by
    have hv : (e i).val ≠ B.reversePermutation.symm := by
      intro hv
      apply hi
      apply e.injective
      change e i = e (e.symm vopen)
      rw [e.apply_symm_apply]
      exact Subtype.ext hv
    have hw :
        ∃ q : orbitStabilizer P U (s.representative i),
          B.leviProjection F (stabilizerToInducing P U (s.representative i) q) = 1 ∧
            entrywiseCharacter ψ (n + 1) q.val ≠ 1 := by
      rw [he i]
      exact hWitness F n B ψ hψn (e i) hv
    obtain ⟨q, hq, hqθ⟩ := hw
    let qtop : (⊤ : Subgroup (orbitStabilizer P U (s.representative i))) := ⟨q, trivial⟩
    have := subsingleton_of_trivial_action (pieceσ i)
      (⊤ : Subgroup (orbitStabilizer P U (s.representative i)))
      ((θ.toMonoidHom.comp (orbitStabilizer P U (s.representative i)).subtype).comp
        (⊤ : Subgroup (orbitStabilizer P U (s.representative i))).subtype)
      qtop (fun v => by
        change FiniteTensor.external π
          (B.leviProjection F (stabilizerToInducing P U (s.representative i) q)) v = v
        rw [hq]
        simp) hqθ
    obtain ⟨eqi⟩ := qeq i
    exact ⟨fun a b => eqi.injective (Subsingleton.elim _ _)⟩
  have hambient : IsSmooth ambient.ρ :=
    isSmooth_comp U.subtype continuous_subtype_val (Induction.compactInduced_smooth P σ)
  obtain ⟨ecollapse⟩ := hCollapse U hlim θ.toMonoidHom hθloc ambient hambient m fs j hvanish
  obtain ⟨ej⟩ := qeq j
  have hopen (w : Langlands.GeneralLinear (n + 1) F)
      (hw : w = (B.reverseMatrix F)⁻¹) :
      Nonempty
        (Coinvariants (σ.comp (stabilizerToInducing P U w))
            (⊤ : Subgroup (orbitStabilizer P U w))
            ((θ.toMonoidHom.comp (orbitStabilizer P U w).subtype).comp
              (⊤ : Subgroup (orbitStabilizer P U w)).subtype) ≃ₗ[ℂ]
          PiTensorProduct ℂ (fun i =>
            Coinvariants (π i) (upperUnipotent (B.size i) F)
              (entrywiseCharacter ψ (B.size i)))) := by
    subst w
    exact ⟨openStabilizerLocalizationEquiv B F π ψ⟩
  obtain ⟨eo⟩ := hopen (s.representative j) hrep
  let ecomp := Representation.equivOfIso
    ((rawRestrictedCompactSmoothIso (R := ℂ) P U).app A.obj)
  let eambient :=
    (representationEquiv (⊤ : Subgroup U)
      (θ.toMonoidHom.comp (⊤ : Subgroup U).subtype) ecomp).trans
      (restrictionEquiv (Induction.smoothInduced P σ) U θ.toMonoidHom)
  exact ⟨eambient.symm.trans (ecollapse.trans (ej.trans eo))⟩

end Langlands.AllField.Whittaker
