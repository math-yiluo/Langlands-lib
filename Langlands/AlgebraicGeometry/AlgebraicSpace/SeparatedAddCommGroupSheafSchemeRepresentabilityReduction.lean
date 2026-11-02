import Langlands.AlgebraicGeometry.AlgebraicSpace.GroupLocalCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.ClosedPointChartRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedAddCommGroupSheafSchemeRepresentabilityStatement
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenProof

/-! # Scheme representability of separated commutative group spaces, conditionally

The separated commutative group space statement follows from the published statement of
Stacks 03BM on affine quotients by finite locally free equivalence relations. It uses the proof
of finite-set Stacks 03JE in `FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenProof` and
the invariance of the finite locus of an etale equivalence relation proved in
`FiniteLocusInvariant`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The separated commutative group space statement, assuming the statement of Stacks 03BM. -/
theorem separatedAddCommGroupSheafSchemeRepresentability_of
    (h03BM : FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u}) :
    SeparatedAddCommGroupSheafSchemeRepresentabilityStatement.{u} := by
  have hS1 := separatedDenseAffineOpenLFT_of h03BM
    finiteLocallyFreeEquivalenceRelationInvariantAffineOpen FiniteLocus.finiteLocus_invariant
  intro k _ H G ⟨e⟩ _ hd ⟨U, a, ha, hs, hU⟩
  have : LocallyOfFiniteType U.hom := hU
  let F := G ⋙ forget AddCommGrpCat
  have hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology _) F :=
    (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mpr H.property
  have hdF : IsClosedImmersion (Limits.diag F) := isClosedImmersion_diag_of_iso e hd
  let a' := a ≫ e.inv
  have ha' : IsEtale a' := ha.comp_iso e.symm
  refine separated_lft_representableBy_of_closed_point_lft_charts (F := H) hd a ha hs ?_
  intro x hx
  let K := U.left.residueField x
  let := FieldSchemePoints.residueFieldAlgebra U.hom x
  have : FiniteDimensional k K := FieldSchemePoints.residueField_finiteDimensional U.hom x hx
  have hw : U.left.fromSpecResidueField x ≫ U.hom = (specOver k K).hom := by
    change U.left.fromSpecResidueField x ≫ U.hom = Spec.map (CommRingCat.ofHom
      (Spec.preimage (U.left.fromSpecResidueField x ≫ U.hom)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let t : specOver k K ⟶ U := Over.homMk (U.left.fromSpecResidueField x) hw
  obtain ⟨V, b, hVlft, hb, ⟨v, hv⟩⟩ :=
    exists_open_chart_of_field_point hS1 h03BM G hF hdF a' ha' K t
  refine ⟨V, b ≫ e.hom, hb.comp_iso e, hVlft, ?_⟩
  let ε : OpenSubfunctorPoints.residueFieldTest U x ⟶ specOver k K :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hw.symm)
  have hε : ε ≫ t = OpenSubfunctorPoints.residueFieldPoint U x := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have hval : (b ≫ e.hom).app _ v = H.obj.map t.op (uliftYonedaEquiv a) := by
    change e.hom.app _ (b.app _ v) = _
    rw [hv]
    change e.hom.app _ (F.map t.op (e.inv.app _ (uliftYonedaEquiv a))) = _
    rw [← NatTrans.naturality_apply e.inv t.op]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id _) _
  refine ⟨((schemeYoneda _).obj V).map ε.op v, ?_⟩
  rw [NatTrans.naturality_apply, hval, ← hε, op_comp, Functor.map_comp_apply]
