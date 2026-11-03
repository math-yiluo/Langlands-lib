import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraSheafIso
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenGluing

/-! # Full-domain algebras and compatible rational subset sections -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits Opposite RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Restrict a stored domain element to every ambient rational chart contained
in its locus, using the actual bounded restrictions over the base. -/
def toLocusSections (U : Domain K A) :
    U.algebra →ₐ[K] OpenSections.Sections U.locus where
  toFun a := ⟨fun d => (inclusionOfSubset d.val.toDomain U d.property).restriction a, by
    intro d e f
    exact congrArg (fun g : Inclusion d.val.toDomain U => g.restriction a)
      (@Subsingleton.elim (Inclusion d.val.toDomain U) inferInstance
        ((toDomainFunctor K A).map f ≫ inclusionOfSubset e.val.toDomain U e.property)
        (inclusionOfSubset d.val.toDomain U d.property))⟩
  map_zero' := by
    apply OpenSections.ext
    intro d
    exact map_zero (inclusionOfSubset d.val.toDomain U d.property).restriction.toAlgHom
  map_one' := by
    apply OpenSections.ext
    intro d
    exact map_one (inclusionOfSubset d.val.toDomain U d.property).restriction.toAlgHom
  map_add' a b := by
    apply OpenSections.ext
    intro d
    exact map_add (inclusionOfSubset d.val.toDomain U d.property).restriction.toAlgHom a b
  map_mul' a b := by
    apply OpenSections.ext
    intro d
    exact map_mul (inclusionOfSubset d.val.toDomain U d.property).restriction.toAlgHom a b
  commutes' a := by
    apply OpenSections.ext
    intro d
    exact (inclusionOfSubset d.val.toDomain U d.property).restriction.toAlgHom.commutes a

@[simp]
theorem toLocusSections_apply (U : Domain K A) (a : U.algebra)
    (d : OpenSections.ChartIn U.locus) :
    (toLocusSections U a).val d =
      (inclusionOfSubset d.val.toDomain U d.property).restriction a := rfl

/-- A compatible subset section gives a point of the actual finite
rational multiequalizer defining the domain's descent algebra. -/
def locusSectionsToExtension (U : Domain K A) :
    CommAlgCat.of K (OpenSections.Sections U.locus) ⟶
      (algebraSheafExtension K A).obj.obj (op U) :=
  Multiequalizer.lift _ _
    (fun i => CommAlgCat.ofHom (OpenSections.evaluation U.locus
      ⟨(finiteRationalCoverData U).chart i, ((finiteRationalCoverData U).map i).subset⟩))
    (by
      rintro ⟨⟨i, j⟩, t⟩
      ext s
      let c := finiteRationalCoverData U
      let d : OpenSections.ChartIn U.locus :=
        ⟨(c.chart i).inter (c.chart j),
          (interLeft (c.chart i) (c.chart j)).subset.trans (c.map i).subset⟩
      exact (s.property d ⟨c.chart i, (c.map i).subset⟩
        (interLeft (c.chart i) (c.chart j))).trans
        (s.property d ⟨c.chart j, (c.map j).subset⟩
          (interRight (c.chart i) (c.chart j))).symm)

@[reassoc (attr := simp)]
theorem locusSectionsToExtension_projection (U : Domain K A)
    (i : Fin (finiteRationalCoverData U).size) :
    locusSectionsToExtension U ≫ sectionProjection K A U i =
      CommAlgCat.ofHom (OpenSections.evaluation U.locus
        ⟨(finiteRationalCoverData U).chart i,
          ((finiteRationalCoverData U).map i).subset⟩) :=
  Multiequalizer.lift_ι _ _ _ _ _

/-- Recover the stored domain element through the inverse of the proved
canonical finite-rational-descent isomorphism. -/
def fromLocusSections (U : Domain K A) :
    OpenSections.Sections U.locus →ₐ[K] U.algebra :=
  (algebraSectionEquiv K A U).symm.toAlgHom.comp (locusSectionsToExtension U).hom

theorem fromLocusSections_projection (U : Domain K A)
    (s : OpenSections.Sections U.locus) (i : Fin (finiteRationalCoverData U).size) :
    ((finiteRationalCoverData U).map i).restriction (fromLocusSections U s) =
      s.val ⟨(finiteRationalCoverData U).chart i,
        ((finiteRationalCoverData U).map i).subset⟩ := by
  have h := (algebraSectionEquiv K A U).apply_symm_apply (locusSectionsToExtension U s)
  change (algebraSectionIso K A U).hom (fromLocusSections U s) =
    locusSectionsToExtension U s at h
  calc
    _ = sectionProjection K A U i
        ((algebraSectionIso K A U).hom (fromLocusSections U s)) :=
      (congrArg (fun f => f (fromLocusSections U s))
        (algebraSectionIso_hom_projection K A U i)).symm
    _ = sectionProjection K A U i (locusSectionsToExtension U s) := congrArg _ h
    _ = _ := congrArg (fun f => f s) (locusSectionsToExtension_projection U i)

/-- Recovery agrees with the original section on every contained rational
chart, by restricting to intersections with the finite rational cover. -/
theorem fromLocusSections_chart (U : Domain K A)
    (s : OpenSections.Sections U.locus) (d : OpenSections.ChartIn U.locus) :
    (inclusionOfSubset d.val.toDomain U d.property).restriction
        (fromLocusSections U s) = s.val d := by
  let c := finiteRationalCoverData U
  let r : FiniteCover d.val.toDomain := {
    size := c.size
    obj i := (d.val.inter (c.chart i)).toDomain
    map i := (toDomainFunctor K A).map (interLeft d.val (c.chart i))
    covers := by
      intro x hx
      obtain ⟨i, hi⟩ := c.covers x (d.property hx)
      exact ⟨i, by
        change x ∈ (d.val.inter (c.chart i)).locus
        rw [locus_inter]
        exact ⟨hx, hi⟩⟩ }
  apply r.algebra_ext_of_restrict_eq
  intro i
  let e : OpenSections.ChartIn U.locus :=
    ⟨d.val.inter (c.chart i), (interLeft d.val (c.chart i)).subset.trans d.property⟩
  change (interLeft d.val (c.chart i)).restriction
      ((inclusionOfSubset d.val.toDomain U d.property).restriction
        (fromLocusSections U s)) =
    (interLeft d.val (c.chart i)).restriction (s.val d)
  have hroute :
      (interLeft d.val (c.chart i)).restriction
          ((inclusionOfSubset d.val.toDomain U d.property).restriction
            (fromLocusSections U s)) =
        (interRight d.val (c.chart i)).restriction
          ((c.map i).restriction (fromLocusSections U s)) :=
    congrArg (fun f : Inclusion (d.val.inter (c.chart i)).toDomain U =>
      f.restriction (fromLocusSections U s))
      (@Subsingleton.elim (Inclusion (d.val.inter (c.chart i)).toDomain U)
        inferInstance
        ((toDomainFunctor K A).map (interLeft d.val (c.chart i)) ≫
          inclusionOfSubset d.val.toDomain U d.property)
        ((toDomainFunctor K A).map (interRight d.val (c.chart i)) ≫ c.map i))
  refine hroute.trans ?_
  change (interRight d.val (c.chart i)).restriction
      (((finiteRationalCoverData U).map i).restriction (fromLocusSections U s)) = _
  rw [fromLocusSections_projection]
  exact (s.property e ⟨c.chart i, (c.map i).subset⟩
    (interRight d.val (c.chart i))).trans
    (s.property e d (interLeft d.val (c.chart i))).symm

@[simp]
theorem toLocusSections_fromLocusSections (U : Domain K A)
    (s : OpenSections.Sections U.locus) :
    toLocusSections U (fromLocusSections U s) = s :=
  OpenSections.ext (fromLocusSections_chart U s)

@[simp]
theorem fromLocusSections_toLocusSections (U : Domain K A) (a : U.algebra) :
    fromLocusSections U (toLocusSections U a) = a := by
  apply (finiteRationalCoverData U).toFiniteCover.algebra_ext_of_restrict_eq
  intro i
  calc
    _ = (inclusionOfSubset ((finiteRationalCoverData U).chart i).toDomain U
        ((finiteRationalCoverData U).map i).subset).restriction a :=
      fromLocusSections_projection U (toLocusSections U a) i
    _ = _ := congrArg (fun f : Inclusion
        ((finiteRationalCoverData U).chart i).toDomain U => f.restriction a)
      (@Subsingleton.elim (Inclusion ((finiteRationalCoverData U).chart i).toDomain U)
        inferInstance _ _)

/-- The canonical algebra equivalence retains every actual rational quotient
component, including its nilpotents. -/
def locusSectionsEquiv (U : Domain K A) :
    U.algebra ≃ₐ[K] OpenSections.Sections U.locus :=
  AlgEquiv.ofAlgHom (toLocusSections U) (fromLocusSections U)
    (by
      apply AlgHom.ext
      intro s
      exact toLocusSections_fromLocusSections U s)
    (by
      apply AlgHom.ext
      intro a
      exact fromLocusSections_toLocusSections U a)

@[simp]
theorem locusSectionsEquiv_apply (U : Domain K A) (a : U.algebra)
    (d : OpenSections.ChartIn U.locus) :
    (locusSectionsEquiv U a).val d =
      (inclusionOfSubset d.val.toDomain U d.property).restriction a := rfl

@[simp]
theorem locusSectionsEquiv_symm_apply (U : Domain K A)
    (s : OpenSections.Sections U.locus) :
    (locusSectionsEquiv U).symm s = fromLocusSections U s := rfl

/-- The comparison retains the original structural map from the base algebra. -/
@[simp]
theorem toLocusSections_baseMap (U : Domain K A) (a : A) :
    toLocusSections U (U.baseMap a) = OpenSections.fromBase U.locus a := by
  apply OpenSections.ext
  intro d
  exact congrArg (fun f : BoundedAlgHom K A d.val.algebra => f a)
    (inclusionOfSubset d.val.toDomain U d.property).comp_baseMap

/-- The canonical comparison commutes with every actual domain restriction. -/
theorem toLocusSections_restriction {U V : Domain K A} (f : U ⟶ V)
    (a : V.algebra) :
    toLocusSections U (f.restriction a) =
      OpenSections.restriction f.subset (toLocusSections V a) := by
  apply OpenSections.ext
  intro d
  exact congrArg (fun g : Inclusion d.val.toDomain V => g.restriction a)
    (@Subsingleton.elim (Inclusion d.val.toDomain V) inferInstance
      (inclusionOfSubset d.val.toDomain U d.property ≫ f)
      (inclusionOfSubset d.val.toDomain V (d.property.trans f.subset)))

/-- Recovery from compatible sections commutes with the same restrictions. -/
theorem fromLocusSections_restriction {U V : Domain K A} (f : U ⟶ V)
    (s : OpenSections.Sections V.locus) :
    f.restriction (fromLocusSections V s) =
      fromLocusSections U (OpenSections.restriction f.subset s) := by
  apply (locusSectionsEquiv U).injective
  change toLocusSections U (f.restriction (fromLocusSections V s)) =
    toLocusSections U (fromLocusSections U (OpenSections.restriction f.subset s))
  rw [toLocusSections_restriction, toLocusSections_fromLocusSections,
    toLocusSections_fromLocusSections]

/-- On an actual rational image the canonical full-domain comparison is
exactly the existing rational-chart comparison. -/
theorem locusSectionsEquiv_rational (d : RationalChart K A) :
    locusSectionsEquiv d.toDomain = OpenSections.chartEquiv d := by
  apply AlgEquiv.ext
  intro a
  apply OpenSections.ext
  intro e
  rfl

variable (K A)

/-- Compatible ambient rational quotient sections on full-domain loci,
with restriction by forgetting components. -/
def locusSectionPresheaf : (Domain K A)ᵒᵖ ⥤ CommAlgCat K where
  obj U := CommAlgCat.of K (OpenSections.Sections U.unop.locus)
  map f := CommAlgCat.ofHom (OpenSections.restriction f.unop.subset)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem locusSectionPresheaf_map_apply {U V : Domain K A} (f : U ⟶ V)
    (s : OpenSections.Sections V.locus) (d : OpenSections.ChartIn U.locus) :
    ((locusSectionPresheaf K A).map f.op s).val d =
      s.val ⟨d.val, d.property.trans f.subset⟩ := rfl

/-- The valuewise canonical comparisons identify the entire retained
algebra presheaf with compatible rational subset sections. -/
def locusSectionPresheafIso :
    algebraPresheaf K A ≅ locusSectionPresheaf K A :=
  NatIso.ofComponents (fun U => CommAlgCat.isoMk (locusSectionsEquiv U.unop))
    (by
      intro U V f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      exact toLocusSections_restriction f.unop a)

@[simp]
theorem locusSectionPresheafIso_hom_app_apply (U : Domain K A) (a : U.algebra) :
    (locusSectionPresheafIso K A).hom.app (op U) a = toLocusSections U a := rfl

@[simp]
theorem locusSectionPresheafIso_inv_app_apply (U : Domain K A)
    (s : OpenSections.Sections U.locus) :
    (locusSectionPresheafIso K A).inv.app (op U) s = fromLocusSections U s := rfl

/-- Compatible rational subset sections satisfy the actual finite full-domain
site sheaf law, transported through the canonical algebra presheaf isomorphism. -/
theorem locusSectionPresheaf_isSheaf :
    Presheaf.IsSheaf (finiteDomainTopology K A) (locusSectionPresheaf K A) :=
  (Presheaf.isSheaf_of_iso_iff (locusSectionPresheafIso K A)).1
    (algebraPresheaf_isSheaf K A)

/-- The full-domain site sheaf of actual compatible rational subset sections. -/
def locusSectionSheaf : Sheaf (finiteDomainTopology K A) (CommAlgCat K) :=
  ⟨locusSectionPresheaf K A, locusSectionPresheaf_isSheaf K A⟩

/-- The actual stored-algebra sheaf and compatible subset-section sheaf are
canonically isomorphic, using their original restriction maps. -/
def locusSectionSheafIso :
    algebraSheaf K A ≅ locusSectionSheaf K A :=
  ObjectProperty.isoMk _ (locusSectionPresheafIso K A)

/-- When the full-domain locus is open, its stored algebra is the value of
the actual ordinary-open algebra sheaf on that very open subset. -/
def openLocusSectionIso (U : Domain K A) (hU : IsOpen U.locus) :
    CommAlgCat.of K U.algebra ≅
      (openAlgebraSheaf K A).obj.obj (op ⟨U.locus, hU⟩) :=
  CommAlgCat.isoMk (locusSectionsEquiv U)

@[simp]
theorem openLocusSectionIso_hom_apply (U : Domain K A) (hU : IsOpen U.locus)
    (a : U.algebra) (d : OpenSections.ChartIn U.locus) :
    ((openLocusSectionIso K A U hU).hom a).val d =
      (inclusionOfSubset d.val.toDomain U d.property).restriction a := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
