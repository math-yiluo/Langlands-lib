import Langlands.Cohomology.LeftExactHomology
import Langlands.Cohomology.SmoothGodementComparison.Transformation
import Langlands.Cohomology.DivisibleSystem.Invariants

/-!
# Smooth Godement comparison for left exact functors and invariants

Let `G` act on `X` with stable neighbourhoods, and assume that every smooth Godement
augmentation is a quasi-isomorphism (hypothesis `hK`, as in
`SmoothGodementComparison.comparisonTrans`).

* For an additive functor `T` from smooth equivariant module sheaves to an abelian category,
  `godementCohomology T q` is the cohomology of `T` applied to the smooth Godement complex,
  and `sheafComparisonTrans hK T q : godementCohomology T q ⟶ T.rightDerived q` is the
  comparison transformation of `AcyclicResolution`. For left exact `T` it is the degree-zero
  identification in degree zero (`sheafComparisonTrans_zero`), and it is an isomorphism under
  `AcyclicResolutionComparisonStatement` (proved as `acyclicResolutionComparisonStatement` in
  `AcyclicResolution.ComparisonProof`, not imported here) and `T`-acyclicity of the Godement
  terms (`sheafComparisonIso`). `comparisonTrans` is the case of compact sections.
* `invariantComparisonTrans hK q`: the case of invariant compact sections, from
  `smoothGodementInvariantCompactCohomology` to `invariantCompactDerived`.
* For a left exact functor `Φ` on smooth representations, `godementEdge Φ q` and
  `derivedEdge Φ q` compare the cohomology of `Φ` applied to compact sections of the
  Godement complex and the derived functors of compact sections followed by `Φ` with `Φ` of
  the compactly supported Godement cohomology and of derived compact sections.
  `sheafComparisonTrans_comp_derivedEdge`: these maps form a commutative square with the
  comparison transformations.
* `smoothInvariants`, `smoothSubgroupInvariants K` and the published
  `smoothQuotientInvariants H` (invariants under all of `G`, under a subgroup `K`, and under
  a normal subgroup `H` as a representation of `G ⧸ H`) are left exact functors to which
  this applies. `invariantCompactSections` is compact sections followed by
  `smoothInvariants`.
-/

noncomputable section

namespace Langlands.Cohomology.SmoothGodementComparison

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u v' u'

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]
variable (hK : ∀ F : SmoothTopologicalSheaf R G X,
  QuasiIso (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
    (Godement.smoothCoaugmentation R G X) F))

section Sheaf

variable {B : Type u'} [Category.{v'} B] [Abelian B] (T : SmoothTopologicalSheaf R G X ⥤ B)
  [T.Additive]

/-- The degree-`q` cohomology of `T` applied termwise to the smooth Godement complex. -/
def godementCohomology (q : ℕ) : SmoothTopologicalSheaf R G X ⥤ B :=
  Godement.smoothComplexFunctor R G X ⋙ T.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) q

/-- The comparison transformation from the cohomology of `T` applied to the smooth Godement
complex to the right derived functors of `T`. -/
def sheafComparisonTrans (q : ℕ) : godementCohomology T q ⟶ T.rightDerived q :=
  AcyclicResolution.comparisonNatTrans T (Godement.smoothComplexFunctor R G X)
    (CokernelComplex.augmentationNat (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X)) hK q

/-- Each component of `sheafComparisonTrans hK T q` is the comparison map for every injective
resolution and every augmentation-compatible map to it. -/
theorem sheafComparisonTrans_app (F : SmoothTopologicalSheaf R G X) (I : InjectiveResolution F)
    (φ : (Godement.smoothComplexFunctor R G X).obj F ⟶ I.cocomplex)
    (hφ : CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F ≫ φ = I.ι) (q : ℕ) :
    (sheafComparisonTrans hK T q).app F = AcyclicResolution.comparison T I φ q :=
  AcyclicResolution.comparisonNatTrans_app _ _ _ hK F I φ hφ q

/-- The comparison transformation of compact sections is `comparisonTrans`. -/
theorem sheafComparisonTrans_compactSections (q : ℕ) :
    sheafComparisonTrans hK (smoothSheafCompactSections R G X) q = comparisonTrans hK q :=
  rfl

variable [PreservesFiniteLimits T]

omit hK in
/-- For left exact `T`, the degree-zero identification of `AcyclicResolution` for the smooth
Godement augmentation is the published degree-zero isomorphism of
`EquivariantGodementCohomology`. -/
theorem homologyZeroIso_eq_app (F : SmoothTopologicalSheaf R G X)
    [QuasiIso (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F)] :
    AcyclicResolution.homologyZeroIso T
        (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
          (Godement.smoothCoaugmentation R G X) F) =
      (EquivariantGodementCohomology.homologyZeroIso (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) T).app F := by
  have hc : AcyclicResolution.cyclesZeroIso T
      (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) F) =
      EquivariantGodementCohomology.cyclesIso (Godement.smoothZeroFunctor R G X)
        (Godement.smoothCoaugmentation R G X) T F := by
    apply Iso.ext
    rw [AcyclicResolution.cyclesZeroIso_hom, ← cancel_mono (HomologicalComplex.iCycles _ 0),
      AcyclicResolution.toCyclesZero_iCycles]
    refine (congrArg (fun g => T.map g)
      (CokernelComplex.augmentationMap_f_zero _ _ F)).trans ?_
    exact (EquivariantGodementCohomology.cyclesIso_hom_iCycles _ _ _ F).symm
  apply Iso.ext
  rw [AcyclicResolution.homologyZeroIso, hc]
  rfl

/-- For left exact `T`, in degree zero the comparison transformation is the identification of
the degree-zero cohomology of `T` applied to the smooth Godement complex with `T`, followed by
the inverse of the identification of `R⁰T` with `T`. -/
theorem sheafComparisonTrans_zero :
    sheafComparisonTrans hK T 0 =
      (EquivariantGodementCohomology.homologyZeroIso (Godement.smoothZeroFunctor R G X)
          (Godement.smoothCoaugmentation R G X) T).hom ≫ T.rightDerivedZeroIsoSelf.inv := by
  refine NatTrans.ext (funext fun F => ?_)
  have := hK F
  have h := AcyclicResolution.comparison_zero T
    (CokernelComplex.augmentationMap (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X) F) (injectiveResolution F) _
    (AcyclicResolution.comp_lift_id _ _)
  rw [homologyZeroIso_eq_app T F] at h
  exact h

/-- For left exact `T`, the comparison transformation is an isomorphism in degree zero. -/
instance isIso_sheafComparisonTrans_zero : IsIso (sheafComparisonTrans hK T 0) :=
  AcyclicResolution.isIso_comparisonNatTrans_zero T (Godement.smoothComplexFunctor R G X)
    (CokernelComplex.augmentationNat (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X)) hK

/-- For left exact `T`, the comparison transformation is a natural isomorphism, given
`AcyclicResolutionComparisonStatement` and the `T`-acyclicity of every term of every smooth
Godement complex as hypotheses. Neither is proved here. -/
def sheafComparisonIso (hcomp : AcyclicResolutionComparisonStatement.{u + 1, u, u', v'})
    (hacyc : ∀ (F : SmoothTopologicalSheaf R G X) (i n : ℕ),
      IsZero ((T.rightDerived (n + 1)).obj (((Godement.smoothComplexFunctor R G X).obj F).X i)))
    (q : ℕ) : godementCohomology T q ≅ T.rightDerived q :=
  AcyclicResolution.comparisonNatIso T (Godement.smoothComplexFunctor R G X)
    (CokernelComplex.augmentationNat (Godement.smoothZeroFunctor R G X)
      (Godement.smoothCoaugmentation R G X)) hK hcomp hacyc q

/-- The isomorphism `sheafComparisonIso` is the comparison transformation. -/
@[simp]
lemma sheafComparisonIso_hom (hcomp : AcyclicResolutionComparisonStatement.{u + 1, u, u', v'})
    (hacyc : ∀ (F : SmoothTopologicalSheaf R G X) (i n : ℕ),
      IsZero ((T.rightDerived (n + 1)).obj (((Godement.smoothComplexFunctor R G X).obj F).X i)))
    (q : ℕ) : (sheafComparisonIso hK T hcomp hacyc q).hom = sheafComparisonTrans hK T q :=
  rfl

end Sheaf

section InvariantCompactSections

/-- The comparison transformation from invariant compactly supported smooth Godement
cohomology to derived invariant compact sections. -/
def invariantComparisonTrans (q : ℕ) :
    SmoothGodementCohomology.smoothGodementInvariantCompactCohomology R G X q ⟶
      SmoothSheafCohomology.invariantCompactDerived R G X q :=
  sheafComparisonTrans hK (SmoothSheafCohomology.invariantCompactSections R G X) q

/-- In degree zero, `invariantComparisonTrans` is the identification of invariant compactly
supported smooth Godement cohomology with invariant compact sections, followed by the inverse
of the identification of derived invariant compact sections with invariant compact
sections. -/
theorem invariantComparisonTrans_zero :
    invariantComparisonTrans hK 0 =
      (SmoothGodementCohomology.smoothGodementInvariantCompactCohomologyZeroIso R G X).hom ≫
        (SmoothSheafCohomology.invariantCompactDerivedZeroIso R G X).inv :=
  sheafComparisonTrans_zero hK _

/-- In degree zero, `invariantComparisonTrans` is an isomorphism. -/
instance isIso_invariantComparisonTrans_zero : IsIso (invariantComparisonTrans hK 0) :=
  isIso_sheafComparisonTrans_zero hK _

end InvariantCompactSections

section LeftExact

variable {E : Type u'} [Category.{v'} E] [Abelian E] (Φ : SmoothRep.{u, u, u} R G ⥤ E)
  [Φ.Additive] [PreservesFiniteLimits Φ]

/-- The map from the cohomology of `Φ` applied to compact sections of the smooth Godement
complex to `Φ` of compactly supported smooth Godement cohomology. -/
def godementEdge (q : ℕ) :
    godementCohomology (smoothSheafCompactSections R G X ⋙ Φ) q ⟶
      SmoothGodementCohomology.smoothGodementCompactCohomology R G X q ⋙ Φ :=
  Functor.whiskerLeft (SmoothGodementCohomology.smoothGodementCompactComplex R G X)
    (LeftExactHomology.homologyNatTrans Φ (ComplexShape.up ℕ) q)

/-- The map from the right derived functors of compact sections followed by `Φ` to `Φ` of
derived compact sections. -/
def derivedEdge (q : ℕ) :
    (smoothSheafCompactSections R G X ⋙ Φ).rightDerived q ⟶
      SmoothSheafCohomology.compactDerived R G X q ⋙ Φ :=
  LeftExactHomology.derivedNatTrans Φ (smoothSheafCompactSections R G X) q

/-- The comparison transformation for compact sections followed by `Φ`, followed by
`derivedEdge`, is `godementEdge` followed by `Φ` of the comparison transformation for compact
sections. -/
theorem sheafComparisonTrans_comp_derivedEdge (q : ℕ) :
    sheafComparisonTrans hK (smoothSheafCompactSections R G X ⋙ Φ) q ≫ derivedEdge Φ q =
      godementEdge Φ q ≫ Functor.whiskerRight (comparisonTrans hK q) Φ :=
  LeftExactHomology.comparisonNatTrans_comp_derivedNatTrans Φ _ _ _ hK q

/-- In degree zero, `godementEdge` is an isomorphism. -/
instance isIso_godementEdge_zero : IsIso (godementEdge (X := X) Φ 0) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

/-- In degree zero, `derivedEdge` is an isomorphism. -/
instance isIso_derivedEdge_zero : IsIso (derivedEdge (X := X) Φ 0) :=
  inferInstanceAs (IsIso (LeftExactHomology.derivedNatTrans _ _ 0))

/-- If `Φ` preserves homology, `godementEdge` is an isomorphism. -/
instance isIso_godementEdge [Φ.PreservesHomology] (q : ℕ) :
    IsIso (godementEdge (X := X) Φ q) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft _ _))

/-- If `Φ` preserves homology, `derivedEdge` is an isomorphism. -/
instance isIso_derivedEdge [Φ.PreservesHomology] (q : ℕ) :
    IsIso (derivedEdge (X := X) Φ q) :=
  inferInstanceAs (IsIso (LeftExactHomology.derivedNatTrans _ _ q))

end LeftExact

section Invariants

variable (R G)

/-- The invariants of a smooth representation under all of `G`. -/
abbrev smoothInvariants : SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  SmoothRep.toRep ⋙ Rep.invariantsFunctor R G

/-- The invariants of a smooth representation of `G` under a subgroup `K`; for compact open
`K`, the level-`K` invariants. -/
abbrev smoothSubgroupInvariants (K : Subgroup G) : SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  SmoothRep.toRep ⋙ Rep.resFunctor K.subtype ⋙ Rep.invariantsFunctor R K

variable (X)

omit [IsTopologicalGroup G] [HasStableNeighbourhoods G X] in
/-- Invariant compact sections are compact sections followed by `smoothInvariants`. -/
theorem invariantCompactSections_eq :
    SmoothSheafCohomology.invariantCompactSections R G X =
      smoothSheafCompactSections R G X ⋙ smoothInvariants R G :=
  rfl

variable {R G X}

/-- `invariantComparisonTrans` followed by `derivedEdge` for `smoothInvariants` is
`godementEdge` followed by the invariants of the comparison transformation for compact
sections. -/
theorem invariantComparisonTrans_comp_derivedEdge (q : ℕ) :
    invariantComparisonTrans hK q ≫ derivedEdge (smoothInvariants R G) q =
      godementEdge (smoothInvariants R G) q ≫
        Functor.whiskerRight (comparisonTrans hK q) (smoothInvariants R G) :=
  sheafComparisonTrans_comp_derivedEdge hK (smoothInvariants R G) q

/-- The square of `sheafComparisonTrans_comp_derivedEdge` for the invariants under a
subgroup `K`. -/
theorem subgroupInvariants_comparisonTrans_comp_derivedEdge (K : Subgroup G) (q : ℕ) :
    sheafComparisonTrans hK (smoothSheafCompactSections R G X ⋙ smoothSubgroupInvariants R G K)
        q ≫ derivedEdge (smoothSubgroupInvariants R G K) q =
      godementEdge (smoothSubgroupInvariants R G K) q ≫
        Functor.whiskerRight (comparisonTrans hK q) (smoothSubgroupInvariants R G K) :=
  sheafComparisonTrans_comp_derivedEdge hK _ q

/-- The square of `sheafComparisonTrans_comp_derivedEdge` for the invariants under a normal
subgroup `H`, as representations of `G ⧸ H`. -/
theorem quotientInvariants_comparisonTrans_comp_derivedEdge (H : Subgroup G) [H.Normal]
    (q : ℕ) :
    sheafComparisonTrans hK (smoothSheafCompactSections R G X ⋙
        smoothQuotientInvariants.{u, u, u} R H) q ≫ derivedEdge (smoothQuotientInvariants R H) q =
      godementEdge (smoothQuotientInvariants R H) q ≫
        Functor.whiskerRight (comparisonTrans hK q) (smoothQuotientInvariants R H) :=
  sheafComparisonTrans_comp_derivedEdge hK _ q

end Invariants

end Langlands.Cohomology.SmoothGodementComparison
