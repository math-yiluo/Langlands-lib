import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenGluing
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.Geometry.RingedSpace.SheafedSpace

/-! # Completed-residue evaluation of actual open sections and topological germs -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- The actual bounded evaluation of a rational quotient in the completed
residue field of a point of its locus. -/
def completedResidueEvaluation (d : RationalChart K A) (x : BanachSpectrum A)
    (hx : x ∈ d.locus) : BoundedAlgHom K d.algebra (CompletedResidueField K x) :=
  RationalPresentation.liftFromBase K A d.radii d.denominator d.numerators
    (CompletedResidueField K x) (completedResidueMap K x)
    (RationalPresentation.residueFractions K A d.denominator d.numerators x)
    (RationalPresentation.residueFractions_bounded K A d.radii d.denominator
      d.numerators d.generates x hx)
    (RationalPresentation.residueFractions_equations K A d.radii d.denominator
      d.numerators d.generates x hx)

@[simp]
theorem completedResidueEvaluation_comp_baseMap (d : RationalChart K A)
    (x : BanachSpectrum A) (hx : x ∈ d.locus) :
    (completedResidueEvaluation d x hx).comp d.baseMap = completedResidueMap K x :=
  RationalPresentation.liftFromBase_comp_baseMap K A d.radii d.denominator
    d.numerators _ _ _ _ _

@[simp]
theorem completedResidueEvaluation_baseMap (d : RationalChart K A)
    (x : BanachSpectrum A) (hx : x ∈ d.locus) (a : A) :
    completedResidueEvaluation d x hx (d.baseMap a) = completedResidueMap K x a :=
  congrArg (fun f : BoundedAlgHom K A (CompletedResidueField K x) => f a)
    (completedResidueEvaluation_comp_baseMap d x hx)

/-- Actual restrictions commute with completed-residue evaluation, including
at boundary points of the closed rational loci. -/
theorem completedResidueEvaluation_restriction {d e : RationalChart K A}
    (f : d ⟶ e) (x : BanachSpectrum A) (hx : x ∈ d.locus) :
    (completedResidueEvaluation d x hx).comp f.restriction =
      completedResidueEvaluation e x (f.subset hx) := by
  apply RationalPresentation.hom_ext_base K A e.radii e.denominator e.numerators
    (CompletedResidueField K x) e.generates
  change (completedResidueEvaluation d x hx).comp (f.restriction.comp e.baseMap) =
    (completedResidueEvaluation e x (f.subset hx)).comp e.baseMap
  rw [f.comp_baseMap]
  exact (completedResidueEvaluation_comp_baseMap d x hx).trans
    (completedResidueEvaluation_comp_baseMap e x (f.subset hx)).symm

/-- The norm of the constructed evaluation is the original chart seminorm
over the chosen base point. -/
theorem norm_completedResidueEvaluation (d : RationalChart K A)
    (x : BanachSpectrum A) (hx : x ∈ d.locus) (a : d.algebra) :
    ‖completedResidueEvaluation d x hx a‖ = d.locusHomeomorph.symm ⟨x, hx⟩ a := by
  have h : BanachSpectrum.comap
      (completedResidueEvaluation d x hx).toBoundedRingHom
        (fieldPoint (CompletedResidueField K x)) = d.locusHomeomorph.symm ⟨x, hx⟩ := by
    apply d.locusHomeomorph.injective
    apply Subtype.ext
    exact (RationalPresentation.spectrumMap_pointLift K A d.radii d.denominator
      d.numerators d.generates x hx).trans
      (congrArg Subtype.val (d.locusHomeomorph.apply_symm_apply ⟨x, hx⟩)).symm
  exact congrArg (fun y : BanachSpectrum d.algebra => y a) h

namespace OpenSections

/-- A chosen actual rational neighborhood wholly contained in an open. -/
def pointChart (U : Opens (BanachSpectrum A)) (x : BanachSpectrum A) (hx : x ∈ U) :
    ChartIn (U : Set (BanachSpectrum A)) :=
  ⟨(exists_rational_neighborhood x U (U.isOpen.mem_nhds hx)).choose,
    (exists_rational_neighborhood x U (U.isOpen.mem_nhds hx)).choose_spec.2⟩

theorem pointChart_mem_nhds (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) :
    (pointChart U x hx).val.locus ∈ 𝓝 x :=
  (exists_rational_neighborhood x U (U.isOpen.mem_nhds hx)).choose_spec.1

theorem mem_pointChart (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) : x ∈ (pointChart U x hx).val.locus :=
  mem_of_mem_nhds (pointChart_mem_nhds U x hx)

variable [CompleteSpace K]

/-- Evaluate an actual compatible quotient family in the completed residue
field through a rational neighborhood. -/
def pointEvaluation (U : Opens (BanachSpectrum A)) (x : BanachSpectrum A)
    (hx : x ∈ U) : Sections (U : Set (BanachSpectrum A)) →ₐ[K] CompletedResidueField K x :=
  (completedResidueEvaluation (pointChart U x hx).val x (mem_pointChart U x hx)).toAlgHom.comp
    (OpenSections.evaluation (U : Set (BanachSpectrum A)) (pointChart U x hx))

/-- Every contained rational chart through the point computes the same
evaluation, whether or not the point is in that chart's interior. -/
theorem pointEvaluation_eq_chart (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) (d : ChartIn (U : Set (BanachSpectrum A)))
    (hd : x ∈ d.val.locus) (s : Sections (U : Set (BanachSpectrum A))) :
    pointEvaluation U x hx s = completedResidueEvaluation d.val x hd (s.val d) := by
  let e := pointChart U x hx
  let w := e.val.inter d.val
  have hw : x ∈ w.locus := by
    rw [locus_inter]
    exact ⟨mem_pointChart U x hx, hd⟩
  have hsub : w.locus ⊆ U := (interLeft e.val d.val).subset.trans e.property
  have hl := congrArg
    (fun f : BoundedAlgHom K e.val.algebra (CompletedResidueField K x) => f (s.val e))
    (completedResidueEvaluation_restriction (interLeft e.val d.val) x hw)
  have hr := congrArg
    (fun f : BoundedAlgHom K d.val.algebra (CompletedResidueField K x) => f (s.val d))
    (completedResidueEvaluation_restriction (interRight e.val d.val) x hw)
  change completedResidueEvaluation e.val x (mem_pointChart U x hx) (s.val e) = _
  exact hl.symm.trans ((congrArg (completedResidueEvaluation w x hw)
    ((s.property ⟨w, hsub⟩ e (interLeft e.val d.val)).trans
      (s.property ⟨w, hsub⟩ d (interRight e.val d.val)).symm)).trans hr)

omit [CompleteSpace K] in
@[simp]
theorem pointEvaluation_fromBase (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) (a : A) :
    pointEvaluation U x hx (fromBase U a) = completedResidueMap K x a :=
  completedResidueEvaluation_baseMap (pointChart U x hx).val x (mem_pointChart U x hx) a

@[simp]
theorem pointEvaluation_restriction {U V : Opens (BanachSpectrum A)}
    (h : U ≤ V) (x : BanachSpectrum A) (hx : x ∈ U)
    (s : Sections (V : Set (BanachSpectrum A))) :
    pointEvaluation U x hx (restriction h s) = pointEvaluation V x (h hx) s := by
  exact (pointEvaluation_eq_chart V x (h hx)
    ⟨(pointChart U x hx).val, (pointChart U x hx).property.trans h⟩
    (mem_pointChart U x hx) s).symm

end OpenSections

variable [CompleteSpace K]

/-- The actual spectrum equipped with the concrete sheaf of rational
quotient-algebra section families. -/
def algebraSheafedSpace (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    AlgebraicGeometry.SheafedSpace (CommAlgCat K) where
  carrier := TopCat.of (BanachSpectrum A)
  presheaf := openAlgebraPresheaf K A
  IsSheaf := openAlgebraPresheaf_isSheaf

/-- The genuine topological stalk, formed over ordinary open neighborhoods. -/
abbrev openStalk (x : BanachSpectrum A) : CommAlgCat K :=
  TopCat.Presheaf.stalk (X := TopCat.of (BanachSpectrum A)) (openAlgebraPresheaf K A) x

/-- The original open-section germ map, retaining its algebra structure. -/
abbrev openGerm (U : Opens (BanachSpectrum A)) (x : BanachSpectrum A) (hx : x ∈ U) :
    CommAlgCat.of K (OpenSections.Sections (U : Set (BanachSpectrum A))) ⟶ openStalk x :=
  TopCat.Presheaf.germ (X := TopCat.of (BanachSpectrum A)) (openAlgebraPresheaf K A) U x hx

/-- The ordinary open interior of the full closed rational locus. -/
def interiorOpen (d : RationalChart K A) : Opens (BanachSpectrum A) :=
  ⟨interior d.locus, isOpen_interior⟩

/-- An actual rational quotient element gives its compatible section family
on the open interior by the original bounded restriction maps. -/
def chartInteriorSection (d : RationalChart K A) :
    d.algebra →ₐ[K] OpenSections.Sections (interiorOpen d : Set (BanachSpectrum A)) :=
  (OpenSections.restriction interior_subset).comp (OpenSections.fromChart d)

/-- The topological germ of a rational quotient element, requiring an actual
neighborhood rather than mere membership in its closed locus. -/
def chartOpenGerm (d : RationalChart K A) (x : BanachSpectrum A)
    (hx : x ∈ interior d.locus) : d.algebra →ₐ[K] openStalk x :=
  (openGerm (interiorOpen d) x hx).hom.comp (chartInteriorSection d)

/-- Every element of the actual topological stalk has an actual rational
neighborhood representative. -/
theorem exists_chartOpenGerm (x : BanachSpectrum A) (t : openStalk x) :
    ∃ (d : RationalChart K A) (hx : x ∈ interior d.locus) (a : d.algebra),
      chartOpenGerm d x hx a = t := by
  have : PreservesFilteredColimits (forget (CommAlgCat K)) := {
    preserves_filtered_colimits J _ _ := by
      have : IsConnected J := IsFiltered.isConnected J
      change PreservesColimitsOfShape J ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
        Under.forget _ ⋙ forget CommRingCat)
      infer_instance }
  obtain ⟨U, hx, s, hs⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of (BanachSpectrum A)) (openAlgebraPresheaf K A) t
  let d := OpenSections.pointChart U x hx
  have hxi : x ∈ interior d.val.locus :=
    mem_interior_iff_mem_nhds.mpr (OpenSections.pointChart_mem_nhds U x hx)
  have hsub : interiorOpen d.val ≤ U := interior_subset.trans d.property
  have heq : OpenSections.restriction hsub s = chartInteriorSection d.val (s.val d) := by
    apply OpenSections.ext
    intro e
    exact (s.property ⟨e.val, e.property.trans hsub⟩ d
      (restrictionOfSubset e.val d.val (e.property.trans interior_subset))).symm
  refine ⟨d.val, hxi, s.val d, ?_⟩
  change openGerm (interiorOpen d.val) x hxi (chartInteriorSection d.val (s.val d)) = t
  rw [← heq]
  exact (TopCat.Presheaf.germ_res_apply (X := TopCat.of (BanachSpectrum A))
    (openAlgebraPresheaf K A) (homOfLE hsub) x hxi s).trans hs

/-- The compatible concrete evaluations form a cocone on the actual
open-neighborhood diagram. -/
def openResidueCocone (x : BanachSpectrum A) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of (BanachSpectrum A)) x).op ⋙
      openAlgebraPresheaf K A) where
  pt := CommAlgCat.of K (CompletedResidueField K x)
  ι.app U := CommAlgCat.ofHom (OpenSections.pointEvaluation U.unop.1 x U.unop.2)
  ι.naturality U V f := by
    ext s
    exact OpenSections.pointEvaluation_restriction f.unop.le x V.unop.2 s

/-- Evaluate topological germs in the actual completed residue field, using
the colimit universal property and the proved concrete restriction equations. -/
def openStalkResidue (x : BanachSpectrum A) :
    openStalk x ⟶ CommAlgCat.of K (CompletedResidueField K x) :=
  colimit.desc _ (openResidueCocone x)

@[reassoc (attr := simp)]
theorem openGerm_openStalkResidue (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) :
    openGerm U x hx ≫ openStalkResidue x =
      CommAlgCat.ofHom (OpenSections.pointEvaluation U x hx) :=
  colimit.ι_desc _ _

@[simp]
theorem openStalkResidue_openGerm (U : Opens (BanachSpectrum A))
    (x : BanachSpectrum A) (hx : x ∈ U) (s : OpenSections.Sections (U : Set (BanachSpectrum A))) :
    openStalkResidue x (openGerm U x hx s) = OpenSections.pointEvaluation U x hx s :=
  ConcreteCategory.congr_hom (openGerm_openStalkResidue U x hx) s

@[simp]
theorem openStalkResidue_chartOpenGerm (d : RationalChart K A) (x : BanachSpectrum A)
    (hx : x ∈ interior d.locus) (a : d.algebra) :
    openStalkResidue x (chartOpenGerm d x hx a) =
      completedResidueEvaluation d x (interior_subset hx) a := by
  change openStalkResidue x (openGerm (interiorOpen d) x hx (chartInteriorSection d a)) = _
  refine (openStalkResidue_openGerm (interiorOpen d) x hx _).trans ?_
  let e := OpenSections.pointChart (interiorOpen d) x hx
  let f := restrictionOfSubset e.val d (e.property.trans interior_subset)
  change completedResidueEvaluation e.val x (OpenSections.mem_pointChart _ _ hx)
    (f.restriction a) = _
  exact congrArg (fun g : BoundedAlgHom K d.algebra (CompletedResidueField K x) => g a)
    (completedResidueEvaluation_restriction f x (OpenSections.mem_pointChart _ _ hx))

/-- Structural germs of actual elements of the original affinoid algebra. -/
def baseOpenGerm (x : BanachSpectrum A) : A →ₐ[K] openStalk x :=
  (openGerm ⊤ x (by trivial)).hom.comp (OpenSections.fromBase Set.univ)

@[simp]
theorem openStalkResidue_baseOpenGerm (x : BanachSpectrum A) (a : A) :
    openStalkResidue x (baseOpenGerm x a) = completedResidueMap K x a := by
  exact (openStalkResidue_openGerm ⊤ x (by trivial) _).trans
    (OpenSections.pointEvaluation_fromBase ⊤ x (by trivial) a)

/-- The evaluation kernel contracts to the original seminorm kernel of A. -/
theorem baseOpenGerm_residue_eq_zero (x : BanachSpectrum A) (a : A) :
    openStalkResidue x (baseOpenGerm x a) = 0 ↔ a ∈ x.kernel := by
  rw [openStalkResidue_baseOpenGerm, completedResidueMap_eq_zero]

/-- The actual ideal of topological germs vanishing under completed-residue
evaluation. Locality or maximality is not assumed. -/
def openStalkResidueKernel (x : BanachSpectrum A) : Ideal (openStalk x) :=
  RingHom.ker (openStalkResidue x).hom.toRingHom

instance openStalkResidueKernel_isPrime (x : BanachSpectrum A) :
    (openStalkResidueKernel x).IsPrime :=
  RingHom.ker_isPrime _

/-- The actual residue-evaluation ideal contracts to the original point
kernel in the base affinoid algebra. -/
theorem comap_openStalkResidueKernel (x : BanachSpectrum A) :
    (openStalkResidueKernel x).comap (baseOpenGerm x).toRingHom = x.kernel := by
  ext a
  exact baseOpenGerm_residue_eq_zero x a

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
