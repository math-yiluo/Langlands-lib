import Langlands.Representation.Exponents.ActualUnitaryPieceFullness
import Langlands.Representation.Exponents.TemperedGeometricPiece
import Langlands.Representation.Geometric.SelfIntersectionLevi
import Langlands.Representation.Aubert.General.NormalizerRegularity
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Filtration.HomBounds

/-! # Multiplicity of the self-intersection unitary geometric pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Generic

variable {H : Type*} [Group H] [TopologicalSpace H]
  {X V W : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- A representation with an injective map into an irreducible representation
has at most a one-dimensional space of maps into an admissible irreducible
representation. -/
theorem rank_intertwiningMap_le_one_of_injective
    {ρ : Representation ℂ H X} {σ' : Representation ℂ H V} {σ : Representation ℂ H W}
    (hσ' : σ'.IsIrreducible) (hσ : σ.IsIrreducible) (hadm : IsAdmissible σ)
    (j : ρ.IntertwiningMap σ') (hj : Function.Injective j) :
    Module.rank ℂ (ρ.IntertwiningMap σ) ≤ 1 := by
  by_cases h : ∃ f : ρ.IntertwiningMap σ, f ≠ 0
  · obtain ⟨f, hf⟩ := h
    let := hσ'
    let := hσ
    have hj0 : j ≠ 0 := by
      intro hj0
      apply hf
      ext x
      have hx : x = 0 := hj (by
        rw [hj0, map_zero]
        rfl)
      change f x = 0
      rw [hx, map_zero]
    let J := j.ofBijective
      ⟨hj, (Representation.IsIrreducible.surjective_or_eq_zero j).resolve_right hj0⟩
    let g := f.comp J.symm.toIntertwiningMap
    have hg : g ≠ 0 := by
      intro hg
      apply hf
      ext x
      have hx := congrArg (fun t : σ'.IntertwiningMap σ => t (J x)) hg
      change f (J.symm (J x)) = 0 at hx
      change f x = 0
      simpa only [Representation.Equiv.symm_apply_apply] using hx
    let E := g.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero g).resolve_right hg)
    obtain ⟨e⟩ := admissibleSchur_homEquiv σ hadm hσ σ (Representation.Equiv.refl σ)
    let s : σ.IntertwiningMap ρ := J.symm.toIntertwiningMap.comp E.symm.toIntertwiningMap
    have hs : Function.Surjective s := by
      intro x
      refine ⟨E (J x), ?_⟩
      change J.symm (E.symm (E (J x))) = x
      rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply]
    let L : ρ.IntertwiningMap σ →ₗ[ℂ] ℂ := e.toLinearMap.comp (HomSpace.comap σ s)
    have hL : Function.Injective L := e.injective.comp (HomSpace.comap_injective σ s hs)
    simpa using LinearMap.lift_rank_le_of_injective L hL
  · push Not at h
    have : Subsingleton (ρ.IntertwiningMap σ) := ⟨fun a b => (h a).trans (h b).symm⟩
    rw [rank_subsingleton']
    exact zero_le_one

end Generic

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance selfUnitaryPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)} {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [T2Space k]
  [LocallyCompactSpace (rationalPoints G)] in
/-- A conjugacy of `σ` with itself by the inverse of `z` places `z` in the
literal Levi point image when `σ` is regular for its actual normalizer. -/
theorem FullPieceConjugacy.mem_pointImage_of_isNormalizerRegular
    {σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (C : FullPieceConjugacy (p := p) (l := l) (q := p) (lQ := l)
      (hl := hl) (hlQ := hl) (z := z) σ σ)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) :
    z ∈ pointImage (l ≫ p) := by
  let := leviPointTopology l hl
  let e' := leviPointsEquiv p l hp hl
  let ψ := rationalPoints.map C.leviIso.hom
  have hψ (m : rationalPoints M) :
      rationalPoints.map (l ≫ p) (ψ m) = z⁻¹ * rationalPoints.map (l ≫ p) m * z := by
    have h := congrArg (fun f => rationalPoints.map f m) C.conjugacy
    simp only [pointMap_comp_apply, rationalPoints_map_innerIso] at h
    simpa [pointMap_comp_apply, MulAut.conj_apply] using h
  have hψinv (m : rationalPoints M) : ψ (rationalPoints.map C.leviIso.inv m) = m := by
    change rationalPoints.map C.leviIso.hom (rationalPoints.map C.leviIso.inv m) = m
    rw [← pointMap_comp_apply, Iso.inv_hom_id]
    rfl
  have hz : z ∈ Subgroup.normalizer (pointImage (l ≫ p) : Set (rationalPoints G)) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨ψ m, hψ m⟩
    · rintro ⟨m, hm⟩
      refine ⟨rationalPoints.map C.leviIso.inv m, ?_⟩
      have h := hψ (rationalPoints.map C.leviIso.inv m)
      rw [hψinv, hm] at h
      calc rationalPoints.map (l ≫ p) (rationalPoints.map C.leviIso.inv m)
          = z * (z⁻¹ * rationalPoints.map (l ≫ p) (rationalPoints.map C.leviIso.inv m) * z) *
              z⁻¹ := by group
        _ = x := by rw [← h]; group
  by_contra hnot
  apply hreg ⟨z, hz⟩ hnot
  have hconj (y : pointImage (l ≫ p)) :
      e'.symm (normalizerConjugation ⟨z, hz⟩ y) = ψ (e'.symm y) := by
    apply e'.injective
    apply Subtype.ext
    rw [ContinuousMulEquiv.apply_symm_apply]
    change z⁻¹ * (y : rationalPoints G) * z = rationalPoints.map (l ≫ p) (ψ (e'.symm y))
    rw [hψ]
    congr 2
    exact congrArg Subtype.val (e'.apply_symm_apply y).symm
  refine ⟨Representation.Equiv.mk C.linearEquiv.symm fun y => ?_⟩
  ext x
  change C.linearEquiv.symm (σ.representation (e'.symm (normalizerConjugation ⟨z, hz⟩ y)) x) =
    σ.representation (e'.symm y) (C.linearEquiv.symm x)
  rw [hconj]
  apply C.linearEquiv.injective
  rw [LinearEquiv.apply_symm_apply, C.intertwines]
  exact congrArg _ (C.linearEquiv.apply_symm_apply x).symm

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
  {A' : CommGroupScheme (Spec (CommRingCat.of k))} {a' : A'.toGrp ⟶ D.M'}
  (ha' : IsSplitComponent a')
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))

set_option maxHeartbeats 800000 in
/-- If the first intersection parabolic of a self-intersection datum is full,
the actual unitary piece has at most a one-dimensional space of maps to an
admissible irreducible inducing representation. -/
theorem unitaryPieceHom_rank_le_one_of_isIso [IsIso D.p']
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hadm : letI := leviPointTopology l hl; IsAdmissible σ.representation) :
    letI := leviPointTopology l hl
    Module.rank ℂ ((D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation) ≤ 1 := by
  let := leviPointTopology l hl
  have := D.isIso_q'_of_isIso_p'
  let j := D.unitaryFullPieceEmbedding ha' σ
  exact rank_intertwiningMap_le_one_of_injective
    ((isIrreducible_comp_continuousMulEquiv_iff σ.representation
      D.fullLeviPointsEquiv.symm).mpr hσ) hσ hadm j.val j.property

variable
  (hσtemp : letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsNormalizedExponentTempered hl.isConnectedReductive σ)
  [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  [hBorelM : letI := leviPointTopology l hl
    BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  (haarM : MeasureTheory.Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
  [hhaarM : letI := leviPointTopology l hl; haarM.IsHaarMeasure]
  (hσsquare : letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsSquareIntegrableModCenter σ.representation haarM)
  (hcriterion : TemperedSquareIntegrableUnitaryPartStatement.{u, v})

include hσtemp haarM hσsquare hcriterion hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- For a tempered irreducible representation that is square-integrable
modulo the center, every self-intersection unitary piece has at most a
one-dimensional space of maps to it. A nonzero map makes the first
intersection parabolic full by the supplied square-integrability criterion. -/
theorem unitaryPieceHom_rank_le_one_of_squareIntegrable
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible) :
    letI := leviPointTopology l hl
    Module.rank ℂ ((D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation) ≤ 1 := by
  let := leviPointTopology l hl
  by_cases h : ∃ F : (D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation, F ≠ 0
  · obtain ⟨F, hF⟩ := h
    have : IsIso D.p' :=
      NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable
        (D := D) (ha' := ha') (σ := σ) (τ := σ) (F := ⟨F, hF⟩)
        (hσtemp := hσtemp) (haarM := haarM) (hσsquare := hσsquare)
        (hcriterionσ := hcriterion)
    exact D.unitaryPieceHom_rank_le_one_of_isIso ha' σ hσ hσsquare.1
  · push Not at h
    have : Subsingleton
        ((D.unitaryPieceRep ha' σ).ρ.IntertwiningMap σ.representation) :=
      ⟨fun a b => (h a).trans (h b).symm⟩
    rw [rank_subsingleton']
    exact zero_le_one

include hσtemp haarM hσsquare hcriterion hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- A nonzero map from a self-intersection unitary piece to the tempered
square-integrable irreducible inducing representation gives the actual
conjugacy of that representation with itself by the inverse of `z`. -/
def selfUnitaryPieceConjugacyOfNonzeroMap
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (F : D.NonzeroUnitaryPieceMap ha' σ σ) :
    FullPieceConjugacy (p := p) (l := l) (q := p) (lQ := l)
      (hl := hl) (hlQ := hl) (z := z) σ σ := by
  haveI : IsIso D.p' :=
    NonzeroUnitaryPieceMap.isIso_left_of_squareIntegrable
      (D := D) (ha' := ha') (σ := σ) (τ := σ) (F := F)
      (hσtemp := hσtemp) (haarM := haarM) (hσsquare := hσsquare)
      (hcriterionσ := hcriterion)
  haveI := D.isIso_q'_of_isIso_p'
  exact D.unitaryFullPieceConjugacyOfNonzeroMap ha' σ σ hσ hσ F.map F.nonzero

include hσtemp haarM hσsquare hcriterion hBorelM hhaarM in
set_option maxHeartbeats 800000 in
/-- For a regular tempered square-integrable irreducible representation, a
self-intersection unitary piece with a nonzero map to it has its double-coset
representative in the literal Levi point image. -/
theorem mem_pointImage_of_unitaryPieceHom_ne_zero
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
    (F : D.NonzeroUnitaryPieceMap ha' σ σ) :
    z ∈ pointImage (l ≫ p) :=
  (D.selfUnitaryPieceConjugacyOfNonzeroMap ha' σ hσtemp haarM hσsquare hcriterion hσ
    F).mem_pointImage_of_isNormalizerRegular hreg

section Selected

variable [Smooth G.X.hom] (hcompact : ArbitraryParabolicQuotientCompactStatement.{u})
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
  (hJac : haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ((jacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).IsAdmissible)

include ha' hσtemp haarM hσsquare hcriterion hBorelM hhaarM hcompact pres hJac in
set_option maxHeartbeats 800000 in
/-- The zero-real-part selected part, for the split component of `M`, of a
self-intersection geometric-lemma piece has Hom length at most one into the
tempered square-integrable irreducible inducing representation. -/
theorem selectedPieceHomLength_le_one
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible) :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    HomSpace.length
      (selectedWeightPart (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)
        ha.isCentralSplitTorus.isCentral.map_mem_center
        (fun χ => Plancherel.SplitTorus.normalizedRealPart
          ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation σ.representation ≤ 1 := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨e⟩ := D.nonempty_selectedWeightPart_pieceFunctor_equiv hcompact ha pres ha' σ
    hσtemp hJac
  rw [HomSpace.length_congr_left σ.representation e, HomSpace.length,
    Module.length_eq_rank]
  exact Cardinal.toENat_le_one.mpr
    (D.unitaryPieceHom_rank_le_one_of_squareIntegrable ha' σ hσtemp haarM hσsquare
      hcriterion hσ)

include ha' hσtemp haarM hσsquare hcriterion hBorelM hhaarM hcompact pres hJac in
set_option maxHeartbeats 800000 in
/-- For a regular tempered square-integrable irreducible inducing
representation, a self-intersection piece whose selected part has nonzero Hom
length into it has its double-coset representative in the literal Levi point
image. -/
theorem mem_pointImage_of_selectedPieceHomLength_ne_zero
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
    (hne : letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      HomSpace.length
        (selectedWeightPart (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)
          ha.isCentralSplitTorus.isCentral.map_mem_center
          (fun χ => Plancherel.SplitTorus.normalizedRealPart
            ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation σ.representation ≠ 0) :
    z ∈ pointImage (l ≫ p) := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  obtain ⟨e⟩ := D.nonempty_selectedWeightPart_pieceFunctor_equiv hcompact ha pres ha' σ
    hσtemp hJac
  rw [HomSpace.length_congr_left σ.representation e, HomSpace.length, Ne,
    Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial] at hne
  obtain ⟨F, hF⟩ := exists_ne (0 : (D.unitaryPieceRep ha' σ).ρ.IntertwiningMap
    σ.representation)
  exact D.mem_pointImage_of_unitaryPieceHom_ne_zero ha' σ hσtemp haarM hσsquare hcriterion
    hσ hreg ⟨F, hF⟩

include ha' hσtemp haarM hσsquare hcriterion hBorelM hhaarM hcompact pres hJac in
/-- The same conclusion in the parabolic point image. -/
theorem mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero
    (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
    (hreg : letI := leviPointTopology l hl
      IsNormalizerRegular (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ))
    (hne : letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      HomSpace.length
        (selectedWeightPart (D.pieceFunctor.obj σ).ρ (rationalPoints.map a)
          ha.isCentralSplitTorus.isCentral.map_mem_center
          (fun χ => Plancherel.SplitTorus.normalizedRealPart
            ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation σ.representation ≠ 0) :
    z ∈ pointImage p :=
  pointImage_comp_le p l (D.mem_pointImage_of_selectedPieceHomLength_ne_zero ha' σ hσtemp
    haarM hσsquare hcriterion hcompact ha pres hJac hσ hreg hne)

end Selected

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
