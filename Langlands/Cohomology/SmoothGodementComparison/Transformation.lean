import Langlands.Cohomology.AcyclicResolution.Comparison
import Langlands.Cohomology.SmoothGodementComparison.Statement
import Langlands.Cohomology.SmoothGodement.Statement

/-!
# The comparison transformation from smooth Godement cohomology to derived compact sections

Let `G` be a topological group acting on a topological space `X` with stable
neighbourhoods. The smooth Godement complex `Godement.smoothComplexFunctor R G X`, with the
augmentation `CokernelComplex.augmentationNat` built from the monic smooth coaugmentation,
is a functorial right resolution in the abelian category of smooth equivariant module
sheaves, provided every augmentation is a quasi-isomorphism. This module takes that
property as an explicit hypothesis `hK`, and derives it from the published
`CokernelResolutionStatement` (`quasiIso_augmentationMap`), which is not proved here.

* `comparisonTrans hK q` is the natural transformation from compactly supported smooth
  Godement cohomology `smoothGodementCompactCohomology R G X q` to derived compact sections
  `compactDerived R G X q`, namely `AcyclicResolution.comparisonNatTrans` for compact
  sections and the smooth Godement resolution.
* `comparisonTrans_app`: its component at `F` is Worker 3's `comparisonMap R G X I φ q` for
  every injective resolution `I` of `F` and every augmentation-compatible `φ`.
* `comparisonTrans_zero`: in degree zero it is the published identification of both sides
  with compact sections.
* `comparisonIso`: on a locally compact Hausdorff space, under the unproved published
  statements `AcyclicResolutionComparisonStatement` and
  `SmoothGodementCompactDerivedAcyclicStatement` as explicit hypotheses, the comparison
  transformation is a natural isomorphism.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothGodementComparison

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- The published `CokernelResolutionStatement` makes every smooth Godement augmentation a
quasi-isomorphism, because the smooth coaugmentation is a monomorphism. -/
theorem quasiIso_augmentationMap (h : CokernelResolutionStatement.{u + 1, u})
    (F : SmoothTopologicalSheaf R G X) :
    QuasiIso (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F) :=
  h _ _ _ (fun M => Godement.mono_smoothCoaugmentation_app R G X M) F

variable {R G X}
variable (hK : ∀ F : SmoothTopologicalSheaf R G X,
  QuasiIso (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
    (Godement.smoothCoaugmentation R G X) F))

/-- The degree-`q` comparison transformation from compactly supported smooth Godement
cohomology to derived compact sections, given that every smooth Godement augmentation is a
quasi-isomorphism. -/
def comparisonTrans (q : ℕ) :
    SmoothGodementCohomology.smoothGodementCompactCohomology R G X q ⟶
      SmoothSheafCohomology.compactDerived R G X q :=
  AcyclicResolution.comparisonNatTrans (smoothSheafCompactSections R G X)
    (Godement.smoothComplexFunctor R G X)
    (CokernelComplex.augmentationNat (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X)) hK q

/-- Each component of the comparison transformation is Worker 3's `comparisonMap` for every
injective resolution and every augmentation-compatible map to it. -/
theorem comparisonTrans_app (F : SmoothTopologicalSheaf R G X) (I : InjectiveResolution F)
    (φ : Godement.smoothComplex R G X F ⟶ I.cocomplex)
    (hφ : CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F ≫ φ = I.ι) (q : ℕ) :
    (comparisonTrans hK q).app F = comparisonMap R G X I φ q :=
  AcyclicResolution.comparisonNatTrans_app _ _ _ hK F I φ hφ q

omit hK in
/-- The generic degree-zero identification for the smooth Godement resolution is the
published degree-zero isomorphism of smooth Godement compact cohomology. -/
theorem homologyZeroIso_eq (F : SmoothTopologicalSheaf R G X)
    [QuasiIso (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F)] :
    AcyclicResolution.homologyZeroIso (smoothSheafCompactSections R G X)
        (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
          (Godement.smoothCoaugmentation R G X) F) =
      (SmoothGodementCohomology.smoothGodementCompactCohomologyZeroIso R G X).app F := by
  have hc : AcyclicResolution.cyclesZeroIso (smoothSheafCompactSections R G X)
      (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) F) =
      EquivariantGodementCohomology.cyclesIso (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) (smoothSheafCompactSections R G X) F := by
    apply Iso.ext
    rw [AcyclicResolution.cyclesZeroIso_hom, ← cancel_mono (HomologicalComplex.iCycles _ 0),
      AcyclicResolution.toCyclesZero_iCycles]
    refine (congrArg (fun g => (smoothSheafCompactSections R G X).map g)
      (CokernelComplex.augmentationMap_f_zero _ _ F)).trans ?_
    exact (EquivariantGodementCohomology.cyclesIso_hom_iCycles _ _ _ F).symm
  apply Iso.ext
  rw [AcyclicResolution.homologyZeroIso, hc]
  rfl

/-- In degree zero, the comparison transformation is the identification of compactly
supported smooth Godement cohomology with compact sections, followed by the inverse of the
identification of derived compact sections with compact sections. -/
theorem comparisonTrans_zero :
    comparisonTrans hK 0 =
      (SmoothGodementCohomology.smoothGodementCompactCohomologyZeroIso R G X).hom ≫
        (SmoothSheafCohomology.compactDerivedZeroIso R G X).inv := by
  refine NatTrans.ext (funext fun F => ?_)
  have := hK F
  have h := AcyclicResolution.comparison_zero (smoothSheafCompactSections R G X)
    (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F) (injectiveResolution F) _
    (AcyclicResolution.comp_lift_id _ _)
  rw [homologyZeroIso_eq F] at h
  exact h

/-- In degree zero, the comparison transformation is an isomorphism. -/
instance isIso_comparisonTrans_zero : IsIso (comparisonTrans hK 0) := by
  rw [comparisonTrans_zero]
  infer_instance

variable [T2Space X] [LocallyCompactSpace X]

/-- On a locally compact Hausdorff space, the comparison transformation is a natural
isomorphism, given the separate theorem obligations `AcyclicResolutionComparisonStatement`
and `SmoothGodementCompactDerivedAcyclicStatement` as hypotheses. Neither is proved here. -/
def comparisonIso (hcomp : AcyclicResolutionComparisonStatement.{u + 1, u, u + 1, u})
    (hacyc : SmoothGodement.SmoothGodementCompactDerivedAcyclicStatement R G X) (q : ℕ) :
    SmoothGodementCohomology.smoothGodementCompactCohomology R G X q ≅
      SmoothSheafCohomology.compactDerived R G X q :=
  AcyclicResolution.comparisonNatIso (smoothSheafCompactSections R G X)
    (Godement.smoothComplexFunctor R G X)
    (CokernelComplex.augmentationNat (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X)) hK hcomp (fun F i n => hacyc F i n) q

/-- The isomorphism `comparisonIso` is the comparison transformation. -/
@[simp]
lemma comparisonIso_hom (hcomp : AcyclicResolutionComparisonStatement.{u + 1, u, u + 1, u})
    (hacyc : SmoothGodement.SmoothGodementCompactDerivedAcyclicStatement R G X) (q : ℕ) :
    (comparisonIso hK hcomp hacyc q).hom = comparisonTrans hK q :=
  rfl

end Langlands.Cohomology.SmoothGodementComparison
