import Langlands.Representation.CompactCoefficient.ProjectiveLifting
import Langlands.Representation.CompactCoefficient.TotalCompactness
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Projective lifting for all compact-coefficient smooth objects -/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

set_option maxHeartbeats 800000 in
/-- A semisimple smooth object is projective when each of its irreducible
actual subrepresentations is projective in the smooth category. -/
theorem projective_of_semisimple_of_projective_subrepresentations
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.representation.IsSemisimpleRepresentation)
    (hproj : ∀ S : Subrepresentation A.representation,
      (subrepresentation A S).IsIrreducible → Projective (subrepresentation A S)) :
    Projective A := by
  classical
  let R := MonoidAlgebra ℂ G
  have : IsSemisimpleModule R A.representation.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hA
  obtain ⟨s, e, -, hs⟩ :=
    IsSemisimpleModule.exists_linearEquiv_dfinsupp R A.representation.asModule
  let D (i : s) : SmoothRep.{0, uG, uV} ℂ G :=
    subrepresentation A (Subrepresentation.ofSubmodule' i.val)
  let j (i : s) : (D i).representation.asModule ≃ₗ[R] i.val :=
    LinearEquiv.ofBijective
      ((Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (hom (subtype A (Subrepresentation.ofSubmodule' i.val)))).codRestrict
          i.val (fun v => v.property))
      ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
        fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
  have hD (i : s) : (D i).IsIrreducible := by
    apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
    exact (j i).isSimpleModule_iff.mpr (hs i)
  have (i : s) : Projective (D i) := hproj _ (hD i)
  refine ⟨fun {X Y} f q hq => ?_⟩
  let fm : A.representation.asModule →ₗ[R] Y.representation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom f)
  let qm : X.representation.asModule →ₗ[R] Y.representation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom q)
  let fi (i : s) : D i ⟶ Y := ofHom
    ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
      (fm.comp (e.symm.toLinearMap.comp
        ((DirectSum.lof R s (fun i : s => i.val) i).comp (j i).toLinearMap))))
  let gi (i : s) : D i ⟶ X := Projective.factorThru (fi i) q
  let gm (i : s) : i.val →ₗ[R] X.representation.asModule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom (gi i))).comp
      (j i).symm.toLinearMap
  let t : (Π₀ i : s, i.val) →ₗ[R] X.representation.asModule :=
    DirectSum.toModule R s X.representation.asModule gm
  let g : A ⟶ X := ofHom
    ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
      (t.comp e.toLinearMap))
  have hgm (i : s) : qm.comp (gm i) =
      fm.comp (e.symm.toLinearMap.comp (DirectSum.lof R s (fun i : s => i.val) i)) := by
    ext v
    have h := congrArg (fun k => hom k ((j i).symm v))
      (Projective.factorThru_comp (fi i) q)
    change qm (gm i v) = fm (e.symm (DirectSum.lof R s (fun i : s => i.val) i v))
    change qm (gm i v) =
      fm (e.symm (DirectSum.lof R s (fun i : s => i.val) i ((j i) ((j i).symm v)))) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have ht : qm.comp t = fm.comp e.symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    ext v
    change qm (t (DirectSum.lof R s (fun i : s => i.val) i v)) =
      fm (e.symm (DirectSum.lof R s (fun i : s => i.val) i v))
    rw [show t (DirectSum.lof R s (fun i : s => i.val) i v) = gm i v from
      DirectSum.toModule_lof R (ι := s) (M := fun i : s => i.val)
        (N := X.representation.asModule) (φ := gm) i v]
    exact congrArg (fun k => k v) (hgm i)
  refine ⟨g, ?_⟩
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h := congrArg (fun k => k (e v)) ht
  change qm (t (e v)) = fm v
  change qm (t (e v)) = fm (e.symm (e v)) at h
  exact h.trans (congrArg fm (e.symm_apply_apply v))

end Langlands.SmoothRep

namespace Langlands.CompactCoefficient

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Every smooth complex object with compact smooth-dual coefficients is
projective, with independent group and carrier universes. -/
theorem projective_of_compactCoefficients
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (hc : HasCompactSmoothDualCoefficients A.representation) : Projective A := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have hA := CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
    (MeasureTheory.Measure.haar (G := G)) A.representation A.isSmooth hc
  apply SmoothRep.projective_of_semisimple_of_projective_subrepresentations A hA
  intro S hS
  apply projective_of_hasCompactSmoothDualCoefficients _ hS
  apply hasCompactSmoothDualCoefficients_subrepresentation _ A hc S
  intro K
  obtain ⟨L, hLK, hL, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
  exact ⟨L, hL, hLK⟩

/-- A chosen lift for an arbitrary compact-coefficient smooth source. -/
def allProjectiveLift (A : SmoothRep.{0, uG, uV} ℂ G)
    (hc : HasCompactSmoothDualCoefficients A.representation)
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ Y) (q : X ⟶ Y) [Epi q] : A ⟶ X :=
  letI := projective_of_compactCoefficients A hc
  Projective.factorThru f q

/-- The chosen lift composes to the prescribed morphism. -/
@[simp]
theorem allProjectiveLift_comp (A : SmoothRep.{0, uG, uV} ℂ G)
    (hc : HasCompactSmoothDualCoefficients A.representation)
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ Y) (q : X ⟶ Y) [Epi q] :
    allProjectiveLift A hc f q ≫ q = f := by
  have := projective_of_compactCoefficients A hc
  exact Projective.factorThru_comp f q

end Langlands.CompactCoefficient
