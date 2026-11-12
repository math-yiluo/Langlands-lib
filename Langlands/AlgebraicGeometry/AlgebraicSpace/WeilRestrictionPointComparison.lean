import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs

/-!
# Weil restriction point comparison under the finite dimensional vector topology

Scheme-map adjunction gives forward continuity. The inverse is continuous when
both fields are henselian, the restricted space is quasi-separated and locally
of finite type, and the extension has the module topology over the base.
Representability and the module-topology hypothesis remain explicit inputs.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringBaseChange ringPointBaseChangeEquiv schemePointTopology
    IsHenselianValuedField weilRestrictionBaseTestIso)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

section Adjunction

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']
variable (Y' : AlgebraicSpace (Spec (CommRingCat.of R')))
variable {U : Over (Spec (CommRingCat.of R))}

/-- The adjoint of a map from a scheme to a Weil restriction, obtained by Yoneda. -/
def ringWeilRestrictionSchemeAdjoint
    (a : (schemeYoneda _).obj U ⟶ ((ringWeilRestriction R R').obj Y'.toSheaf).obj) :
    (schemeYoneda _).obj (ringBaseChange R R' U) ⟶ Y'.presheaf :=
  uliftYonedaEquiv.{u + 1}.symm
    (uliftYonedaEquiv.{u + 1} (F := ((ringWeilRestriction R R').obj Y'.toSheaf).obj) a)

theorem ringWeilRestrictionSchemeAdjoint_apply
    (a : (schemeYoneda _).obj U ⟶ ((ringWeilRestriction R R').obj Y'.toSheaf).obj)
    (T : Over (Spec (CommRingCat.of R))) (p : T ⟶ U) :
    (ringWeilRestrictionSchemeAdjoint R R' Y' a).app (op (ringBaseChange R R' T))
      (ULift.up ((Over.pullback (Spec.algebraMap R R')).map p)) =
        a.app (op T) (ULift.up p) := by
  change Y'.presheaf.map (((Over.pullback (Spec.algebraMap R R')).map p).op)
    (uliftYonedaEquiv (F := ((ringWeilRestriction R R').obj Y'.toSheaf).obj) a) = _
  exact congrArg (fun f => f.app (op T) (ULift.up p))
    (uliftYonedaEquiv.{u + 1}.symm_apply_apply a)

/-- Extension of a rational scheme point is the base-changed point, precomposed with
 the canonical identification of the base-changed test scheme. -/
theorem ringPointBaseChangeEquiv_basePoint
    (p : RingPoint R U R) :
    ringPointBaseChangeEquiv R R' R' U
      (RingPoint.changeRing (Algebra.ofId R R') p) =
      (weilRestrictionBaseTestIso R R').hom ≫
        (Over.pullback (Spec.algebraMap R R')).map p := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [PointTopology.ringPointBaseChangeEquiv_left_fst, Over.comp_left,
      Over.pullback_map_left, Category.assoc, pullback.lift_fst,
      weilRestrictionBaseTestIso, Iso.trans_hom, Iso.symm_hom,
      PointTopology.weilRestrictionTensorUnitTestIso,
      PointTopology.ringTest, Over.mk_hom]
    rw [← Category.assoc (PointTopology.ringBaseChangeSpectrumIso R R' R).inv.left
      (pullback.fst (Spec.algebraMap R R) (Spec.algebraMap R R')) p.left,
      PointTopology.ringBaseChangeSpectrumIso_inv_fst R R' R]
    change (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ p.left =
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.rid R R' R').toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : R →ₐ[R] R' ⊗[R] R).toRingHom) ≫ p.left
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    simp [Algebra.smul_def]
  · rw [PointTopology.ringPointBaseChangeEquiv_left_snd]
    exact (Over.w ((weilRestrictionBaseTestIso R R').hom ≫
      (Over.pullback (Spec.algebraMap R R')).map p)).symm

/-- The canonical base-point identification commutes with adjunction on scheme maps. -/
theorem ringWeilRestrictionBasePointsEquiv_schemePointsMap
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj Y'.toSheaf))
    (a : (schemeYoneda _).obj U ⟶ ((ringWeilRestriction R R').obj Y'.toSheaf).obj)
    (p : RingPoint R U R) :
    ringWeilRestrictionBasePointsEquiv R R' Y' h
        (a.app (op (ringTest R R)) (ULift.up p)) =
      (ringWeilRestrictionSchemeAdjoint R R' Y' a).app (op (ringTest R' R'))
        (ULift.up (ringPointBaseChangeEquiv R R' R' U
          (RingPoint.changeRing (Algebra.ofId R R') p))) := by
  rw [ringPointBaseChangeEquiv_basePoint]
  change Y'.presheaf.map (PointTopology.weilRestrictionTensorUnitTestIso R R').hom.op
    (Y'.presheaf.map (PointTopology.ringBaseChangeSpectrumIso R R' R).inv.op
      (a.app (op (ringTest R R)) (ULift.up p))) = _
  rw [← types_comp_apply, ← Functor.map_comp]
  change Y'.presheaf.map (weilRestrictionBaseTestIso R R').hom.op
    (a.app (op (ringTest R R)) (ULift.up p)) = _
  rw [← ringWeilRestrictionSchemeAdjoint_apply R R' Y' a]
  change Y'.presheaf.map (weilRestrictionBaseTestIso R R').hom.op
    (Y'.presheaf.map (((Over.pullback (Spec.algebraMap R R')).map p).op)
      (uliftYonedaEquiv (F := ((ringWeilRestriction R R').obj Y'.toSheaf).obj) a)) =
    Y'.presheaf.map (((weilRestrictionBaseTestIso R R').hom ≫
      (Over.pullback (Spec.algebraMap R R')).map p).op) _
  rw [op_comp, Functor.map_comp]
  rfl

variable [Module.Finite R R'] [Module.Projective R R']

/-- Restrict a map from an affine scheme by applying it to the universal Weil point. -/
def ringWeilRestrictionAffineSchemeMap
    (U' : Over (Spec (CommRingCat.of R'))) [IsAffine U'.left]
    [LocallyOfFiniteType U'.hom] (a : (schemeYoneda _).obj U' ⟶ Y'.presheaf) :
    (schemeYoneda _).obj (PointTopology.affineWeilRestriction R R' U') ⟶
      ((ringWeilRestriction R R').obj Y'.toSheaf).obj :=
  uliftYonedaEquiv.{u + 1}.symm
    (a.app (op (ringBaseChange R R' (PointTopology.affineWeilRestriction R R' U')))
      (ULift.up (PointTopology.affineWeilRestrictionCounit R R' U')))

variable [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace R'] [IsTopologicalRing R'] [IsModuleTopology R R']

/-- On base points, restricting an affine scheme map commutes with the affine point
 homeomorphism and the canonical space point identification. -/
theorem ringWeilRestrictionBasePointsEquiv_affineSchemeMap
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj Y'.toSheaf))
    (U' : Over (Spec (CommRingCat.of R'))) [IsAffine U'.left]
    [LocallyOfFiniteType U'.hom] (a : (schemeYoneda _).obj U' ⟶ Y'.presheaf)
    (p : RingPoint R (PointTopology.affineWeilRestriction R R' U') R) :
    ringWeilRestrictionBasePointsEquiv R R' Y' h
        ((ringWeilRestrictionAffineSchemeMap R R' Y' U' a).app (op (ringTest R R))
          (ULift.up p)) =
      a.app (op (ringTest R' R'))
        (ULift.up (PointTopology.affineWeilRestrictionPointHomeomorph R R' U' p)) := by
  change Y'.presheaf.map (PointTopology.weilRestrictionTensorUnitTestIso R R').hom.op
    (Y'.presheaf.map (PointTopology.ringBaseChangeSpectrumIso R R' R).inv.op
      (Y'.presheaf.map (((Over.pullback (Spec.algebraMap R R')).map p).op)
        (a.app _ (ULift.up (PointTopology.affineWeilRestrictionCounit R R' U'))))) = _
  rw [← types_comp_apply, ← Functor.map_comp]
  change Y'.presheaf.map (weilRestrictionBaseTestIso R R').hom.op
    (Y'.presheaf.map (((Over.pullback (Spec.algebraMap R R')).map p).op)
      (a.app _ (ULift.up (PointTopology.affineWeilRestrictionCounit R R' U')))) = _
  rw [← a.naturality_apply]
  change Y'.presheaf.map (weilRestrictionBaseTestIso R R').hom.op
    (a.app _ (ULift.up ((Over.pullback (Spec.algebraMap R R')).map p ≫
      PointTopology.affineWeilRestrictionCounit R R' U'))) = _
  rw [← a.naturality_apply]
  change a.app _ (ULift.up ((weilRestrictionBaseTestIso R R').hom ≫
    ((Over.pullback (Spec.algebraMap R R')).map p ≫
      PointTopology.affineWeilRestrictionCounit R R' U'))) = _
  exact congrArg (fun q : RingPoint R' U' R' => a.app _ (ULift.up q))
    (PointTopology.affineWeilRestrictionComparison_basePoint R R' U' p)

end Adjunction

section Continuity

variable (K K' : Type u) [NontriviallyNormedField K] [NontriviallyNormedField K']
  [Algebra K K'] [ContinuousSMul K K']
variable (Y' : AlgebraicSpace (Spec (CommRingCat.of K')))

/-- Forward continuity of the Weil restriction identification needs henselianity only
 over the larger field, and is tested on charts by the scheme-map adjunction. -/
theorem continuous_ringWeilRestrictionBasePointsEquiv
    (hK' : IsHenselianValuedField K')
    (hY' : IsQuasiSeparatedLocallyFiniteType K' Y')
    (h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf)) :
    Continuous[etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h),
      etaleChartTopology K' Y'] (ringWeilRestrictionBasePointsEquiv K K' Y' h) := by
  let : TopologicalSpace (RingPoints K' Y' K') := etaleChartTopology K' Y'
  rw [etaleChartTopology_continuous_iff]
  intro c
  have := c.locallyOfFiniteType
  have : LocallyOfFiniteType (ringBaseChange K K' c.scheme).hom := by
    change LocallyOfFiniteType (pullback.snd c.scheme.hom (Spec.algebraMap K K'))
    infer_instance
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
  let : TopologicalSpace (RingPoint K c.scheme K') := schemePointTopology K c.scheme K'
  let : TopologicalSpace (RingPoint K' (ringBaseChange K K' c.scheme) K') :=
    schemePointTopology K' (ringBaseChange K K' c.scheme) K'
  have heq : ringWeilRestrictionBasePointsEquiv K K' Y' h ∘ c.pointMap =
      schemePointsMap (ringWeilRestrictionSchemeAdjoint K K' Y' (hom c.hom)) ∘
        ringPointBaseChangeEquiv K K' K' c.scheme ∘
          RingPoint.changeRing (Algebra.ofId K K') := by
    funext p
    exact ringWeilRestrictionBasePointsEquiv_schemePointsMap K K' Y' h (hom c.hom) p
  rw [heq]
  exact (continuous_schemePointsMap hK' hY'.exists_chart _).comp
    ((PointTopology.schemeBaseChangeTopology_proof K K' K' c.scheme).continuous.comp
      (PointTopology.schemeCoefficientContinuity_proof K K K' c.scheme
        (Algebra.ofId K K') (continuous_algebraMap K K')))

variable [FiniteDimensional K K'] [IsModuleTopology K K']

omit [ContinuousSMul K K'] in
/-- Inverse continuity follows from open affine charts when the larger field carries
 the finite dimensional vector topology over the smaller field. -/
theorem continuous_ringWeilRestrictionBasePointsEquiv_symm
    (hK : IsHenselianValuedField K) (hK' : IsHenselianValuedField K')
    (hY' : IsQuasiSeparatedLocallyFiniteType K' Y')
    (h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf))
    (hY : IsQuasiSeparatedLocallyFiniteType K (ringWeilRestrictionSpace K K' Y' h)) :
    Continuous[etaleChartTopology K' Y',
      etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)]
      (ringWeilRestrictionBasePointsEquiv K K' Y' h).symm := by
  let : TopologicalSpace (RingPoints K' Y' K') := etaleChartTopology K' Y'
  let : TopologicalSpace (RingPoints K (ringWeilRestrictionSpace K K' Y' h) K) :=
    etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)
  let C := {c : EtaleFiniteTypeChart K' Y' // IsAffine c.scheme.left}
  let E := ringWeilRestrictionBasePointsEquiv K K' Y' h
  have hc : ∀ c : C, Continuous[schemePointTopology K' c.val.scheme K', _]
      (E.symm ∘ c.val.pointMap) := by
    intro c
    have := c.val.locallyOfFiniteType
    have := c.property
    let W := PointTopology.affineWeilRestriction K K' c.val.scheme
    rw [PointTopology.schemePointTopology_eq_affine]
    have heq : E.symm ∘ c.val.pointMap =
        schemePointsMap (ringWeilRestrictionAffineSchemeMap K K' Y' c.val.scheme
          (hom c.val.hom)) ∘
            (PointTopology.affineWeilRestrictionPointHomeomorph K K' c.val.scheme).symm := by
      funext p
      apply E.injective
      dsimp only [Function.comp_apply]
      rw [Equiv.apply_symm_apply]
      change c.val.pointMap p = E
        ((ringWeilRestrictionAffineSchemeMap K K' Y' c.val.scheme (hom c.val.hom)).app _
          (ULift.up ((PointTopology.affineWeilRestrictionPointHomeomorph K K'
            c.val.scheme).symm p)))
      rw [ringWeilRestrictionBasePointsEquiv_affineSchemeMap,
        Homeomorph.apply_symm_apply]
      rfl
    rw [heq]
    have hcont := continuous_schemePointsMap hK hY.exists_chart
      (ringWeilRestrictionAffineSchemeMap K K' Y' c.val.scheme (hom c.val.hom))
    rw [PointTopology.schemePointTopology_eq_affine] at hcont
    exact hcont.comp
      (PointTopology.affineWeilRestrictionPointHomeomorph K K' c.val.scheme).symm.continuous
  have hcov : ∀ y : RingPoints K' Y' K',
      ∃ (c : C) (p : RingPoint K' c.val.scheme K'), c.val.pointMap p = y := by
    intro y
    obtain ⟨c, p, ha, hp⟩ := exists_affine_chart_pointMap_eq hY'.1 hY'.2 y
    exact ⟨⟨c, ha⟩, p, hp⟩
  refine ⟨?_⟩
  intro V hV
  have heq : E.symm ⁻¹' V = ⋃ c : C, c.val.pointMap ''
      ((E.symm ∘ c.val.pointMap) ⁻¹' V) := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, p, rfl⟩ := hcov y
      exact Set.mem_iUnion.2 ⟨c, p, hy, rfl⟩
    · intro hy
      obtain ⟨c, p, hp, rfl⟩ := Set.mem_iUnion.1 hy
      exact hp
  rw [heq]
  apply isOpen_iUnion
  intro c
  let : TopologicalSpace (RingPoint K' c.val.scheme K') :=
    schemePointTopology K' c.val.scheme K'
  exact c.val.isOpenMap_pointMap hK' _ ((hc c).isOpen_preimage V hV)

/-- The canonical Weil restriction point equivalence as a homeomorphism, with the
 vector-topology and geometric hypotheses explicit. -/
def ringWeilRestrictionPointHomeomorph
    (hK : IsHenselianValuedField K) (hK' : IsHenselianValuedField K')
    (hY' : IsQuasiSeparatedLocallyFiniteType K' Y')
    (h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf))
    (hY : IsQuasiSeparatedLocallyFiniteType K (ringWeilRestrictionSpace K K' Y' h)) :
    @Homeomorph (RingPoints K (ringWeilRestrictionSpace K K' Y' h) K)
      (RingPoints K' Y' K')
      (etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)) (etaleChartTopology K' Y') := by
  let : TopologicalSpace (RingPoints K' Y' K') := etaleChartTopology K' Y'
  let : TopologicalSpace (RingPoints K (ringWeilRestrictionSpace K K' Y' h) K) :=
    etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)
  exact Homeomorph.mk (ringWeilRestrictionBasePointsEquiv K K' Y' h)
    (continuous_ringWeilRestrictionBasePointsEquiv K K' Y' hK' hY' h)
    (continuous_ringWeilRestrictionBasePointsEquiv_symm K K' Y' hK hK' hY' h hY)

/-- The complete topological comparison, conditional on representability, finite type
 and the vector topology on the valued extension. -/
theorem isHomeomorph_ringWeilRestrictionBasePointsEquiv
    (hK : IsHenselianValuedField K) (hK' : IsHenselianValuedField K')
    (hY' : IsQuasiSeparatedLocallyFiniteType K' Y')
    (h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf))
    (hY : IsQuasiSeparatedLocallyFiniteType K (ringWeilRestrictionSpace K K' Y' h)) :
    @IsHomeomorph _ _ (etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h))
      (etaleChartTopology K' Y') (ringWeilRestrictionBasePointsEquiv K K' Y' h) := by
  let : TopologicalSpace (RingPoints K' Y' K') := etaleChartTopology K' Y'
  let : TopologicalSpace (RingPoints K (ringWeilRestrictionSpace K K' Y' h) K) :=
    etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h)
  exact (ringWeilRestrictionPointHomeomorph K K' Y' hK hK' hY' h hY).isHomeomorph

end Continuity

end Langlands.AlgebraicGeometry.AlgebraicSpace
