import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantPolarization
import Langlands.GroupScheme.RelativeLevi.ParabolicPolarizedDescent
import Langlands.GroupScheme.RelativeLevi.ParabolicModelCoproductPolarization

/-! # Reduction to finite parabolic types, determinant positivity and descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Finite local types and actual determinant positivity give an affine etale
neighbourhood with an ample restricted original determinant dual. -/
theorem exists_affineEtaleModel_determinantDual_isAmple
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u})
    (hG : IsReductive G) (s : S) :
    ∃ a : AffineEtaleModel hG s,
      (((parabolicLieDeterminantDualPresheafLineBundle G hG).baseChange a.baseMap).universal
        (SmoothProperModel.restrictedRepresentation a.baseMap a.model)).IsAmple := by
  obtain ⟨R, hR, f, hf, ⟨x, hx⟩, n, P, j, hj, htypes⟩ := hfin S G hG s
  let : CommRing R := hR
  let P' : ULift.{u} (Fin n) → GroupScheme (Spec (CommRingCat.of R)) :=
    fun a => P a.down
  let j' : ∀ a : ULift.{u} (Fin n), P' a ⟶ (GroupScheme.baseChange f).obj G :=
    fun a => j a.down
  have hj' (a : ULift.{u} (Fin n)) : IsRelativeParabolicSubgroup (j' a) := hj a.down
  have htypes' : HasUniformParabolicFieldTypes j' := by
    intro k _ z Q i hi
    obtain ⟨a, ha, hua⟩ := htypes k z Q i hi
    refine ⟨⟨a⟩, ha, ?_⟩
    intro b hb
    exact ULift.ext _ _ (hua b.down hb)
  let d := finiteAffineParabolicModel (hG.baseChange f) j' hj' htypes'
  refine ⟨⟨R, f, hf, x, hx, d⟩, ?_⟩
  exact (parabolicLieDeterminantDual_universalBaseChange_isAmple_iff
    f hG d.represents).mpr
      (finiteAffineParabolicDeterminantDual_universal_isAmple
        (hG.baseChange f) j' hj' htypes' hample)

/-- On a compact base, finitely many polarized affine etale neighbourhoods
assemble into one affine etale surjection with the same ample universal dual. -/
theorem exists_affineEtaleCoverModel_determinantDual_isAmple [CompactSpace S]
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u})
    (hG : IsReductive G) :
    ∃ c : AffineEtaleCoverModel hG,
      (((parabolicLieDeterminantDualPresheafLineBundle G hG).baseChange c.baseMap).universal
        (SmoothProperModel.restrictedRepresentation c.baseMap c.model)).IsAmple := by
  classical
  let a : ∀ s : S, AffineEtaleModel hG s :=
    fun s => (exists_affineEtaleModel_determinantDual_isAmple hfin hample hG s).choose
  have hL (s : S) :
      (((parabolicLieDeterminantDualPresheafLineBundle G hG).baseChange (a s).baseMap).universal
        (SmoothProperModel.restrictedRepresentation (a s).baseMap (a s).model)).IsAmple :=
    (exists_affineEtaleModel_determinantDual_isAmple hfin hample hG s).choose_spec
  have hopen (s : S) : IsOpen (Set.range (a s).baseMap) := by
    let : Etale (a s).baseMap := (a s).etale
    exact (a s).baseMap.isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun s : S => Set.range (a s).baseMap)
    (fun s => (hopen s).mem_nhds ⟨(a s).point, (a s).point_over⟩)
  let X : t → Scheme.{u} := fun s => Spec (CommRingCat.of (a s.val).ring)
  let f : ∀ s : t, X s ⟶ S := fun s => (a s.val).baseMap
  have hcover (s : S) : ∃ i : t, s ∈ Set.range (f i) := by
    have hs : s ∈ (⊤ : Set S) := trivial
    rw [← ht, Set.mem_iUnion] at hs
    rcases hs with ⟨y, _, ⟨hy, rfl⟩, hs⟩
    exact ⟨⟨y, hy⟩, hs⟩
  have hf (s : t) : Etale (f s) := (a s.val).etale
  let : ∀ s : t, IsAffine (X s) := fun s => inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (a s.val).ring)))
  have hsurj : Surjective (Sigma.desc f) := by
    constructor
    intro s
    obtain ⟨i, y, hy⟩ := hcover s
    exact ⟨Sigma.ι X i y, by simpa [← Scheme.Hom.comp_apply] using hy⟩
  let c : AffineEtaleCoverModel hG :=
    ⟨∐ X, inferInstance, Sigma.desc f,
      IsZariskiLocalAtSource.sigmaDesc hf, hsurj,
      SmoothProperModel.coproduct (hG := hG) X f (fun s => (a s.val).model)⟩
  refine ⟨c, ?_⟩
  exact SmoothProperModel.coproduct_universal_isAmple X f
    (fun s => (a s.val).model) (parabolicLieDeterminantDualPresheafLineBundle G hG)
    (fun s => hL s.val)

/-- These two geometric inputs supply exactly the polarization required by
the effective-descent interface, using the original coherent determinant dual. -/
theorem exists_affineEtaleCoverModel_polarization [CompactSpace S]
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u})
    (hG : IsReductive G) :
    ∃ c : AffineEtaleCoverModel hG, Nonempty c.Polarization := by
  obtain ⟨c, hc⟩ := exists_affineEtaleCoverModel_determinantDual_isAmple hfin hample hG
  exact ⟨c, ⟨⟨parabolicLieDeterminantDualPresheafLineBundle G hG, hc⟩⟩⟩

/-- Choose an affine etale covering model and polarize it with precisely the
original coherent determinant dual, using the two supplied geometric inputs. -/
def polarizedAffineEtaleCoverModel [CompactSpace S]
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u})
    (hG : IsReductive G) : Σ c : AffineEtaleCoverModel hG, c.Polarization :=
  let hc := exists_affineEtaleCoverModel_determinantDual_isAmple hfin hample hG
  ⟨hc.choose, ⟨parabolicLieDeterminantDualPresheafLineBundle G hG, hc.choose_spec⟩⟩

/-- Finite local types, positivity of the actual finite quotient-family
determinant dual, and effective polarized descent imply the unchanged target. -/
theorem relativeParabolicSchemeStatement_of_finiteTypes_determinantPositivity_descent
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hample : FiniteAffineParabolicDeterminantDualAmpleStatement.{u})
    (hdesc : PolarizedSmoothProperEtaleDescentStatement.{u, u + 1}) :
    RelativeParabolicSchemeStatement.{u} := by
  apply relativeParabolicSchemeStatement_of_affinePolarizedModels hdesc
  intro B H hH hB
  let : IsAffine B := hB
  exact exists_affineEtaleCoverModel_polarization hfin hample hH

end Langlands.GroupScheme.ParabolicSubgroupModuli
