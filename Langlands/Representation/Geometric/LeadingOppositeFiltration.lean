import Langlands.Representation.Geometric.OppositeRefinedFiltration
import Langlands.Representation.Geometric.ReversedIdentityPiece
import Langlands.Representation.Geometric.RelativeLeadingCharacterExclusionStatement
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.Classification.MaximalConeExponents
import Langlands.Representation.Classification.MaximalConeAssembly
import Langlands.Representation.Classification.ProductLeviCentralCharacter

/-! Actual coarse opposite filtration and same-full-character grade adapters. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory OppositeCuspidalJacquetFiltration
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- Conditional actual coarse opposite filtration, with all raw representatives
and actual arbitrary intersection refinements retained. -/
structure LeadingOppositeFiltrationData
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) where
  sourceRefinement : MinimalRepresentatives B B.reverse → BlockRefinement B
  targetRefinement : MinimalRepresentatives B B.reverse → BlockRefinement B.reverse
  sourceIntersection : ∀ v, IsIntersectionRefinement (F := F.Carrier)
    B B.reverse v.val (sourceRefinement v)
  targetIntersection : ∀ v, IsIntersectionRefinement (F := F.Carrier)
    B.reverse B v.val⁻¹ (targetRefinement v)
  length : ℕ
  enumeration : Fin length ≃ MinimalRepresentatives B B.reverse
  filtration : letI := T.topology
    ObjectRepFiltration
      (CuspidalJacquetMultiplicity.oppositeJacquet T B
        (CuspidalJacquetMultiplicity.induced T B (Rep.of A.representation))) length
  gradeEquiv : letI := T.topology
    ∀ j, Nonempty (Representation.Equiv (filtration.gradedRepresentation j).ρ
      ((((geometricPieceFunctor T B B.reverse (enumeration j).val
        (sourceRefinement (enumeration j)) (targetRefinement (enumeration j))
        (sourceIntersection (enumeration j)).2.1
        (targetIntersection (enumeration j)).2.1).obj A).ρ).comp
          (leviReverseEquiv B).toMonoidHom))

set_option maxHeartbeats 3000000 in
/-- Evaluate the supplied upper geometric filtration and transport it through
actual normalized reversal. This proves no upper geometric lemma. -/
def leadingOppositeFiltrationOfUpper
    (hupper : GeometricLemmaTheorem.{uF, uV} T B B.reverse)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) :
    LeadingOppositeFiltrationData T B A := by
  letI := T.topology
  apply Classical.choice
  obtain ⟨P, Q, hP, hQ, m, e, δ, f, hf⟩ := hupper
  let I := CuspidalJacquetMultiplicity.induced T B (Rep.of A.representation)
  let s : ObjectRepFiltration (Rep.of (T.normalizedJacquet B.reverse I.ρ)) m :=
    ObjectRepFiltration.ofSubrepresentations (fun k => (f.step k).obj A)
      (f.monotone A) (f.zero A) (f.top A)
  refine ⟨⟨P, Q, hP, hQ, m, δ.trans e, oppositeFiltrationOfReverse T B I s, ?_⟩⟩
  intro j
  obtain ⟨ψ⟩ := hf j
  let g : (s.gradedRepresentation j).ρ.Equiv
      ((geometricPieceFunctor T B B.reverse (e (δ j)).val
        (P (e (δ j))) (Q (e (δ j)))
        (hP (e (δ j))).2.1 (hQ (e (δ j))).2.1).obj A).ρ :=
    Representation.equivOfIso (ψ.app A)
  exact ⟨(oppositeFiltrationOfReverseGradedEquiv T B I s j).symm.trans
    (FiniteTensorFiltration.compCongr g (leviReverseEquiv B).toMonoidHom)⟩

/-- The raw inverse reversal is a minimal representative from B to B.reverse. -/
def inverseReversalMinimal : MinimalRepresentatives B B.reverse :=
  ⟨B.reversePermutation.symm, by
    constructor
    · exact reversePermutation_symm_index_strictMono B
    · intro j a b hab
      change B.reversePermutation (B.reverse.index j a) <
        B.reversePermutation (B.reverse.index j b)
      have ha := B.reversePermutation_index (j : Fin B.length) a
      have hb := B.reversePermutation_index (j : Fin B.length) b
      erw [ha, hb]
      exact index_strictMono B j.rev hab⟩

/-- Reversal transports the full-center character restriction, with its exact
size-weighted real part. -/
theorem leadingRealPart_reverse
    (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ) (t : Fin B.length → ℝ)
    (hχ : T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
      (fun k => (B.size k : ℝ) * t k)) :
    T.IsRealPartOf
      (χ.comp ((B.blockScalarToCenter F.Carrier).comp
        (MaximalConeAssembly.precomp Fin.rev)))
      (fun j : Fin B.reverse.length => (B.reverse.size j : ℝ) * t j.rev) := by
  intro b
  calc
    _ = ∏ k : Fin B.length, T.normalizedAbs (b k.rev : F.Carrier) ^
        ((B.size k : ℝ) * t k) := hχ (b ∘ Fin.rev)
    _ = _ := by
      simpa only [BlockShape.reverse, Fin.revPerm_apply, Fin.rev_rev] using
        (Equiv.prod_comp Fin.revPerm (fun j : Fin B.length =>
          T.normalizedAbs (b j : F.Carrier) ^ ((B.size j.rev : ℝ) * t j.rev)))

set_option maxHeartbeats 1400000 in
/-- A full-center generalized character of the actual pulled-back piece gives
that SAME character restricted along reversed coarse scalars, and hence the
raw leading-piece conclusion. No full character is extended or changed. -/
theorem pulledPiece_leading_implies_inverseReversal
    (hexclusion : GLRelativeGeometricLeadingCharacterExclusionStatement.{uF, uV}) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ [MeasurableSpace
        (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [μ.IsHaarMeasure] (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsTemperedModCenter A.representation μ →
      ∀ t : Fin B.length → ℝ, StrictAnti t →
      ∀ (v : Equiv.Perm (Fin n)), IsMinimalRepresentative B B.reverse v →
      ∀ (S : BlockRefinement B) (R : BlockRefinement B.reverse)
        (hS : sourceLevi F.Carrier B B.reverse v = refinedLevi F.Carrier B S)
        (hR : sourceLevi F.Carrier B.reverse B v⁻¹ = refinedLevi F.Carrier B.reverse R),
      let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
        ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
      ∀ (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ),
      IsGeneralizedEigencharacter
        (((((geometricPieceFunctor T B B.reverse v S R hS hR).obj At).ρ).comp
          (leviReverseEquiv B).toMonoidHom).comp
            (Subgroup.center (B.Levi F.Carrier)).subtype) χ →
      T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
        (fun k => (B.size k : ℝ) * t k) →
      v = B.reversePermutation.symm := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro _ _ μ _ A hA t ht v hv S R hS hR
  dsimp only
  intro χ hχ hre
  let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
    ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
  let M := (geometricPieceFunctor T B B.reverse v S R hS hR).obj At
  let β := (B.blockScalarToCenter F.Carrier).comp (MaximalConeAssembly.precomp Fin.rev)
  let θ := (leviReverseEquiv (R := F.Carrier) B).toMonoidHom
  let χr := χ.comp β
  let e : Representation.Equiv
      (((M.ρ.comp θ).comp (Subgroup.center (B.Levi F.Carrier)).subtype).comp β)
      (M.ρ.comp (B.reverse.blockScalarLevi F.Carrier)) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ M) (fun b => by
      apply LinearMap.ext
      intro x
      change M.ρ (leviReverseEquiv B
        (B.blockScalarLevi F.Carrier (b ∘ Fin.rev))) x =
          M.ρ (B.reverse.blockScalarLevi F.Carrier b) x
      congr 2
      funext j
      change GeneralLinear.scalar (b j.rev.rev) = GeneralLinear.scalar (b j)
      rw [Fin.rev_rev])
  have hrestrict : IsGeneralizedEigencharacter
      (((M.ρ.comp θ).comp (Subgroup.center (B.Levi F.Carrier)).subtype).comp β) χr := by
    obtain ⟨m, x, hx₀, hx⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
    exact (isGeneralizedEigencharacter_iff _ _).mpr ⟨m, x, hx₀, fun b => hx (β b)⟩
  exact hexclusion p F T n B μ A hA t ht v hv S R hS hR χr
    ((isGeneralizedEigencharacter_iff_of_equiv e χr).mp hrestrict)
    (leadingRealPart_reverse T B χ t hre)

set_option maxHeartbeats 2200000 in
private def identityPieceAtEq (v : Equiv.Perm (Fin n))
    (hv : v = B.reversePermutation.symm)
    (S : BlockRefinement B) (R : BlockRefinement B.reverse)
    (hS : sourceLevi F.Carrier B B.reverse v = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier B.reverse B v⁻¹ = refinedLevi F.Carrier B.reverse R) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      Representation.Equiv
        ((((geometricPieceFunctor T B B.reverse v S R hS hR).obj A).ρ).comp
          (leviReverseEquiv B).toMonoidHom) A.representation := by
  subst v
  exact reversedIdentityGeometricPieceEquiv T B S R hS hR

/-- The unique enumerated index of the actual inverse-reversal piece. -/
def LeadingOppositeFiltrationData.identityIndex
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)}
    (D : LeadingOppositeFiltrationData T B A) : Fin D.length :=
  D.enumeration.symm (inverseReversalMinimal B)

set_option maxHeartbeats 3000000 in
/-- The actual distinguished grade is equivalent to the inducing representation,
for every intersection refinement supplied by the upper geometric lemma. -/
def LeadingOppositeFiltrationData.identityGradeEquiv
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)}
    (D : LeadingOppositeFiltrationData T B A) :
    letI := T.topology
    Representation.Equiv (D.filtration.gradedRepresentation (D.identityIndex T B)).ρ
      A.representation := by
  letI := T.topology
  let j := D.identityIndex T B
  let g := Classical.choice (D.gradeEquiv j)
  have hv : (D.enumeration j).val = B.reversePermutation.symm :=
    congrArg Subtype.val (D.enumeration.apply_symm_apply (inverseReversalMinimal B))
  exact g.trans (identityPieceAtEq T B (D.enumeration j).val hv
    (D.sourceRefinement (D.enumeration j)) (D.targetRefinement (D.enumeration j))
    (D.sourceIntersection (D.enumeration j)).2.1
    (D.targetIntersection (D.enumeration j)).2.1 A)

set_option maxHeartbeats 2600000 in
/-- The same full central character can occur in a leading-real grade only at
the unique identity index of the actual coarse opposite filtration. -/
theorem LeadingOppositeFiltrationData.leadingGrade_eq_identity
    (hexclusion : GLRelativeGeometricLeadingCharacterExclusionStatement.{uF, uV}) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [μ.IsHaarMeasure] (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsTemperedModCenter A.representation μ →
      ∀ t : Fin B.length → ℝ, StrictAnti t →
      let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
        ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
      ∀ (D : LeadingOppositeFiltrationData T B At) (j : Fin D.length)
        (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ),
        T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
          (fun k => (B.size k : ℝ) * t k) →
        IsGeneralizedEigencharacter
          ((D.filtration.gradedRepresentation j).ρ.comp
            (Subgroup.center (B.Levi F.Carrier)).subtype) χ →
        j = D.identityIndex T B := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro _ _ μ _ A hA t ht
  dsimp only
  intro D j χ hre hχ
  obtain ⟨g⟩ := D.gradeEquiv j
  have hχ' := (isGeneralizedEigencharacter_iff_of_equiv
    (FiniteTensorFiltration.compCongr g (Subgroup.center (B.Levi F.Carrier)).subtype) χ).mp hχ
  have hv := pulledPiece_leading_implies_inverseReversal T B hexclusion μ A hA t ht
    (D.enumeration j).val (D.enumeration j).property
    (D.sourceRefinement (D.enumeration j)) (D.targetRefinement (D.enumeration j))
    (D.sourceIntersection (D.enumeration j)).2.1
    (D.targetIntersection (D.enumeration j)).2.1 χ hχ' hre
  apply D.enumeration.injective
  exact (Subtype.ext hv).trans (D.enumeration.apply_symm_apply (inverseReversalMinimal B)).symm

end Langlands.Geometric
