import Langlands.GroupScheme.RelativeLevi.FiniteFaceCoverGroups
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Langlands.GroupScheme.RelativeUnipotent.LinearQuotientComparison

/-! # Geometric properties of the actual finite-cover filtration -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A property local on the target can be checked after restricting a group
homomorphism to an open cover of its base. -/
theorem homProperty_of_base_openCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {S : Scheme.{u}} (𝒰 : S.OpenCover) {G H : GroupScheme S} (f : G ⟶ H)
    (hf : ∀ a, P ((baseChange (𝒰.f a)).map f).hom.hom.left) :
    P f.hom.hom.left := by
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (𝒰.pullback₁ H.X.hom)
  intro a
  have h := hf a
  have hp := (baseChange_map_isPullback (𝒰.f a) f).flip
  rw [← hp.isoPullback_hom_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := P)] at h
  exact h

/-- Actual source and target isomorphisms transport an underlying morphism
property through a commuting square. -/
theorem homProperty_of_compatible_isos
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S : Scheme.{u}} {G H G' H' : GroupScheme S}
    (f : G ⟶ H) (f' : G' ⟶ H') (eG : G ≅ G') (eH : H ≅ H')
    (he : f ≫ eH.hom = eG.hom ≫ f')
    (hf' : P f'.hom.hom.left) : P f.hom.hom.left := by
  have h : f = eG.hom ≫ f' ≫ eH.inv := by
    apply (cancel_mono eH.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he
  let : IsIso eG.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eG)).hom)
  let : IsIso eH.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eH)).inv)
  rw [h]
  change P (eG.hom.hom.hom.left ≫ f'.hom.hom.left ≫ eH.inv.hom.hom.left)
  rw [MorphismProperty.cancel_left_of_respectsIso (P := P),
    MorphismProperty.cancel_right_of_respectsIso (P := P)]
  exact hf'

/-- A commuting square of actual source and quotient isomorphisms identifies
the full kernel on every scheme test. -/
theorem kernelRange_comap_of_compatible_isos
    {S : Scheme.{u}} {G Q G' Q' : GroupScheme S}
    (q : G ⟶ Q) (q' : G' ⟶ Q') (eG : G ≅ G') (eQ : Q ≅ Q')
    (he : q ≫ eQ.hom = eG.hom ≫ q') :
    SubgroupFunctor.range (kernelι q) =
      (SubgroupFunctor.range (kernelι q')).comap eG.hom := by
  have hs : q.hom.hom ≫ eQ.hom.hom.hom = eG.hom.hom.hom ≫ q'.hom.hom :=
    congrArg (fun f => f.hom.hom) he
  ext T x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_comap, mem_range_kernelι_iff]
  rw [Category.assoc, ← hs, ← Category.assoc]
  exact (isoPointsEquiv eQ T).map_eq_one_iff.symm

namespace RelativeLevi

open LocalSplitCell

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom] {p : H ⟶ G}

local instance {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace AffineParabolicFaceChart

variable {s : S} (C : AffineParabolicFaceChart p s)

local instance : Fintype C.coordinateType := C.coordinateFintype
local instance : Fintype C.rootType := C.rootFintype
local instance geometryChartAmbientAffine : IsAffine ((baseChange C.projection).obj G).X.left :=
  isAffine_of_isAffineHom ((baseChange C.projection).obj G).X.hom

/-- The original chart term is smooth over its actual coefficient ring. -/
theorem smooth_termGroup (d : ℕ) : Smooth (C.termGroup d).X.hom :=
  C.chart.weights.smooth_groupScheme d

/-- The exact-weight vector group is smooth, including in rank zero. -/
theorem smooth_layerGroup (d : ℕ) : Smooth (C.layerGroup d).X.hom := by
  change Smooth (VectorGroup.groupScheme (CommRingCat.of C.ring)
    (Nat.card (C.chart.weights.exactSupport d))).X.hom
  apply Corepresented.smooth_groupScheme_iff.mpr
  infer_instance

/-- Each original term is closed in the original pulled-back ambient group. -/
theorem isClosedSubgroup_termInclusion (d : ℕ) : IsClosedSubgroup (C.termInclusion d) := by
  have h₁ := C.chart.weights.isClosedSubgroup_inclusion d
  have h₂ := Dynamic.Affine.isClosedSubgroup_unipotentHom
    (AffineRegularBorel.cocharacter C.torus C.chart.cocharacter)
  change IsClosedImmersion
    ((C.chart.weights.inclusion d).hom.hom.left ≫
      (Dynamic.Affine.unipotentHom
        (AffineRegularBorel.cocharacter C.torus C.chart.cocharacter)).hom.hom.left)
  exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsClosedImmersion)
    _ _ h₁ h₂

/-- The original consecutive-term map is a closed subgroup inclusion. -/
theorem isClosedSubgroup_termStep (d : ℕ) : IsClosedSubgroup (C.termStep d) :=
  C.chart.weights.isClosedSubgroup_step d

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
/-- The original chart projection is a full fppf quotient by the next term. -/
theorem isFppfQuotient_layerProjection (d : ℕ) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (C.termStep d))
      (C.layerProjection d) :=
  C.chart.weights.isFppfQuotient_quotientMap d
end

end AffineParabolicFaceChart

namespace FiniteParabolicFaceCover

variable (D : FiniteParabolicFaceCover p)

/-- The component open cover of the actual assembled-group base. -/
def groupsOpenCover : D.groupsSpace.OpenCover :=
  sigmaOpenCover (fun a : D.Index => Spec (D.charts a.down).2.ring)

/-- The assembled original terms are smooth over the finite affine cover. -/
theorem smooth_termGroup (d : ℕ) : Smooth (D.termGroup d).X.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth) D.groupsOpenCover
  intro a
  let e := D.termComponentIso d a
  let : Smooth ((D.charts a.down).2.termGroup d).X.hom :=
    (D.charts a.down).2.smooth_termGroup d
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  change Smooth ((baseChange (D.componentMap a)).obj (D.termGroup d)).X.hom
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- The assembled actual vector layers are smooth over the cover base. -/
theorem smooth_layerGroup (d : ℕ) : Smooth (D.layerGroup d).X.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth) D.groupsOpenCover
  intro a
  let e := D.layerComponentIso d a
  let : Smooth ((D.charts a.down).2.layerGroup d).X.hom :=
    (D.charts a.down).2.smooth_layerGroup d
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  change Smooth ((baseChange (D.componentMap a)).obj (D.layerGroup d)).X.hom
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- The assembled term retains its closed ORIGINAL ambient inclusion. -/
theorem isClosedSubgroup_termInclusion (d : ℕ) : IsClosedSubgroup (D.termInclusion d) := by
  apply homProperty_of_base_openCover (@IsClosedImmersion) D.groupsOpenCover
  intro a
  exact homProperty_of_compatible_isos (@IsClosedImmersion) _ _
    (D.termComponentIso d a) (D.ambientComponentIso a)
    (D.termInclusion_component d a) ((D.charts a.down).2.isClosedSubgroup_termInclusion d)

/-- The original assembled consecutive-term inclusion is closed. -/
theorem isClosedSubgroup_termStep (d : ℕ) : IsClosedSubgroup (D.termStep d) := by
  apply homProperty_of_base_openCover (@IsClosedImmersion) D.groupsOpenCover
  intro a
  exact homProperty_of_compatible_isos (@IsClosedImmersion) _ _
    (D.termComponentIso (d + 1) a) (D.termComponentIso d a)
    (D.termStep_component d a) ((D.charts a.down).2.isClosedSubgroup_termStep d)

/-- Flatness of the actual assembled quotient map follows on its components. -/
theorem flat_layerProjection (d : ℕ) : Flat (D.layerProjection d).hom.hom.left := by
  apply homProperty_of_base_openCover (@Flat) D.groupsOpenCover
  intro a
  exact homProperty_of_compatible_isos (@Flat) _ _
    (D.termComponentIso d a) (D.layerComponentIso d a)
    (D.layerProjection_component d a) ((D.charts a.down).2.isFppfQuotient_layerProjection d).1

/-- Surjectivity of the actual quotient is preserved by the finite assembly. -/
theorem surjective_layerProjection (d : ℕ) :
    Surjective (D.layerProjection d).hom.hom.left := by
  apply homProperty_of_base_openCover (@Surjective) D.groupsOpenCover
  intro a
  exact homProperty_of_compatible_isos (@Surjective) _ _
    (D.termComponentIso d a) (D.layerComponentIso d a)
    (D.layerProjection_component d a) ((D.charts a.down).2.isFppfQuotient_layerProjection d).2.1

/-- The actual assembled quotient is locally of finite presentation. -/
theorem locallyOfFinitePresentation_layerProjection (d : ℕ) :
    LocallyOfFinitePresentation (D.layerProjection d).hom.hom.left := by
  apply homProperty_of_base_openCover (@LocallyOfFinitePresentation) D.groupsOpenCover
  intro a
  exact homProperty_of_compatible_isos (@LocallyOfFinitePresentation) _ _
    (D.termComponentIso d a) (D.layerComponentIso d a)
    (D.layerProjection_component d a)
    ((D.charts a.down).2.isFppfQuotient_layerProjection d).2.2.1

/-- The full scheme-theoretic kernel of the assembled quotient is the next
actual term on all tests over the cover base. -/
theorem range_kernelι_layerProjection (d : ℕ) :
    SubgroupFunctor.range (kernelι (D.layerProjection d)) =
      SubgroupFunctor.range (D.termStep d) := by
  have : IsClosedImmersion (D.termStep d).hom.hom.left := D.isClosedSubgroup_termStep d
  let : Mono (D.termStep d).hom.hom := Over.mono_of_mono_left _
  apply (SubgroupFunctor.range_eq_iff_baseChange_openCover D.groupsOpenCover _ _).mpr
  intro a
  rw [← kernel_range_baseChange, ← SubgroupFunctor.range_baseChangeHom]
  change SubgroupFunctor.range (kernelι ((baseChange (D.componentMap a)).map
      (D.layerProjection d))) =
    SubgroupFunctor.range ((baseChange (D.componentMap a)).map (D.termStep d))
  rw [kernelRange_comap_of_compatible_isos _ _
    (D.termComponentIso d a) (D.layerComponentIso d a) (D.layerProjection_component d a),
    ((D.charts a.down).2.isFppfQuotient_layerProjection d).2.2.2,
    FppfQuotientComparison.range_comap_of_compatible_isos _ _
      (D.termComponentIso d a) (D.termComponentIso (d + 1) a) (D.termStep_component d a)]

/-- The original assembled projection is a represented fppf quotient by the
actual next term, with no replacement of its map or its kernel. -/
theorem isFppfQuotient_layerProjection (d : ℕ) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (D.termStep d))
      (D.layerProjection d) :=
  ⟨D.flat_layerProjection d, D.surjective_layerProjection d,
    D.locallyOfFinitePresentation_layerProjection d, D.range_kernelι_layerProjection d⟩

/-- The actual next term is normal in the preceding assembled term. -/
theorem isNormal_range_termStep (d : ℕ) :
    (SubgroupFunctor.range (D.termStep d)).IsNormal := by
  rw [← D.range_kernelι_layerProjection d]
  intro T g x _ hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx,
    mul_one, mul_inv_cancel]

end FiniteParabolicFaceCover
end RelativeLevi
end Langlands.GroupScheme
