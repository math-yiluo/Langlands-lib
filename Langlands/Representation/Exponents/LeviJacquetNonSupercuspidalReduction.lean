import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Exponents.LeviInductionNoSupercuspidalSubquotientStatement
import Langlands.Representation.Exponents.LeviJacquetInductionNoSupercuspidalStatement
import Langlands.Representation.Filtration.ActualGradedExtraction
import Langlands.Representation.Filtration.SingleSurvivingGrade
import Langlands.GroupScheme.Rational.FullParabolicLevi

/-! # Non-supercuspidal Jacquet subquotients from geometric pieces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The consumer deduction of VI.5.3(ii) from the represented geometric
lemma and the exact no-supercuspidal-subquotient assertion of VI.5.2. -/
def LeviJacquetInductionNoSupercuspidalReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    LeviInductionNoSupercuspidalSubquotientStatement.{u, v} →
      LeviJacquetInductionNoSupercuspidalStatement.{u, v}

/-- Conditional deduction of Renard VI.5.3(ii), retaining the full
represented geometric lemma and VI.5.2 as explicit premises. -/
theorem leviJacquetInductionNoSupercuspidal_of_geometricLemma
    (hgeom : RepresentedGeometricLemmaStatement.{u, v})
    (hind : LeviInductionNoSupercuspidalSubquotientStatement.{u, v}) :
    LeviJacquetInductionNoSupercuspidalStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hnone
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) :=
    leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
  have : LocallyCompactSpace (rationalPoints L) :=
    leviPoints_locallyCompactSpace q lQ hq hlQ
  have : NonarchimedeanGroup (rationalPoints L) :=
    leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro ρ hρ σ hσ hsub hσsc
  obtain ⟨m, c, z, hz, D, e, s, hs⟩ :=
    hgeom k G hG P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  obtain ⟨j, hj⟩ := (s.atObject ρ).exists_smoothGradedObject_subquotient hσ hsub
  let d := D (e j)
  have := d.hl'.isConnectedReductive.isAffineHom
  have := d.hlQ'.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints d.M') := leviPointTopology d.l' d.hl'
  let : TopologicalSpace (rationalPoints d.L') := leviPointTopology d.lQ' d.hlQ'
  let τ : SmoothRep.{0, u, v} ℂ (rationalPoints d.L') :=
    SmoothRep.pullback d.e
      ((leviJacquetFunctor d.p' d.l' d.r' d.hp' d.hr' d.hl' d.hmul').obj ρ)
  let B : SmoothRep.{0, u, max u v} ℂ (rationalPoints L) :=
    (leviInductionFunctor d.q' d.lQ' d.rQ' d.hq' d.hrQ' d.hlQ' d.hmulQ').obj τ
  obtain ⟨f⟩ := hs j
  have f' := f.app ρ
  dsimp only [Function.comp_apply, GeometricLemmaIntersectionDatum.pieceFunctor,
    Functor.comp_obj] at f'
  let β : (s.atObject ρ).smoothGradedObject j ≅ B := by
    apply ObjectProperty.isoMk
    change (s.graded j).obj ρ ≅ B.obj
    dsimp only [B, τ, d, SmoothRep.pullbackFunctor, SmoothRep.toRep,
      Function.comp_apply, Functor.comp_obj, ObjectProperty.ι_obj] at f' ⊢
    with_reducible exact f'
  have hpiece : SmoothRep.IsSubquotient σ B := hj.of_iso_right β
  by_cases hfullQ : IsIso d.q'
  · have hproper : ¬ IsIso d.p' := by
      intro hfullP
      have := hfullP
      have := hfullQ
      let isoML := rationalLeviConjugacyOfFullParabolics d.hl' d.hlQ'
        hl.isConnectedReductive hlQ.isConnectedReductive (l ≫ p) (lQ ≫ q)
        (G.innerIso (z (e j))) d.φ d.φ_comp
      apply hnone
      refine ⟨(z (e j))⁻¹, isoML.val, ?_⟩
      simpa only [Category.assoc, G.innerIso_inv_hom] using isoML.property
    have hJ := hρ d.P' d.M' d.N' d.p' d.l' d.r' d.hp' d.hl' d.hr' d.hmul' hproper
    have hB : Subsingleton B := by
      change Subsingleton (Induction.SmoothFunctions _ _)
      constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact funext (fun _ => hJ.elim _ _)
    let : σ.representation.IsIrreducible := hσ
    let : Nontrivial σ :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints L)) σ.representation.asModule
    obtain ⟨C, i, t, hi, ht⟩ := SmoothRep.isSubquotient_iff_exists.mp hpiece
    obtain ⟨a, b, hab⟩ := exists_pair_ne σ
    obtain ⟨a', rfl⟩ := ht a
    obtain ⟨b', rfl⟩ := ht b
    exact hab (congrArg (SmoothRep.hom t) (hi (hB.elim _ _)))
  · exact hind k L hlQ.isConnectedReductive d.Q' d.L' d.U'
      d.q' d.lQ' d.rQ' d.hq' d.hlQ' d.hrQ' d.hmulQ' hfullQ τ σ hσ hpiece hσsc

end Langlands.Aubert.General.RepresentedParabolic
