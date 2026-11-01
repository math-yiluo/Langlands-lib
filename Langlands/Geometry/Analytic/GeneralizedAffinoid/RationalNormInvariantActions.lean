import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormContinuousLocus

/-! # Continuous equivariant diagrams of weighted rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

/-- Actual weighted rational charts whose loci are preserved by the common
open subgroup, with no extra condition on their bounded restriction maps. -/
def normInvariantChartProperty (H : OpenSubgroup G) :
    ObjectProperty (RationalChart K A) :=
  fun d => H ≤ normOpenStabilizer ρ hρ d

/-- The full category of rational charts preserved by the common subgroup. -/
abbrev NormInvariantChart (H : OpenSubgroup G) :=
  (normInvariantChartProperty ρ hρ H).FullSubcategory

/-- The derived simultaneous stabilizer makes every chart in the finite
family an object of the same invariant category. -/
def finiteNormInvariantChart (s : Finset (RationalChart K A))
    (U : OpenSubgroup G) (d : s) :
    NormInvariantChart ρ hρ (finiteNormOpenStabilizer ρ hρ s U) :=
  ⟨d.val, fun g hg => (mem_normOpenStabilizer ρ hρ d.val g).mpr
    (((mem_finiteNormOpenStabilizer ρ hρ s U g).mp hg).2 d.val d.property)⟩

/-- The common group includes continuously into each full local stabilizer,
with the original subgroup topologies and the same ambient group element. -/
def normInvariantStabilizerInclusion (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    H →ₜ* normOpenStabilizer ρ hρ d.obj where
  toFun g := ⟨g.val, d.property g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem normInvariantStabilizerInclusion_coe (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (g : H) :
    (normInvariantStabilizerInclusion ρ hρ H d g).val = g.val := rfl

/-- Restrict the already constructed jointly continuous action on the actual
weighted rational locus to the common open subgroup. -/
def normInvariantLocusAction (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) : ContAction TopCat.{u} H :=
  (ContAction.res TopCat (normInvariantStabilizerInclusion ρ hρ H d)).obj
    (normLocusContinuousAction ρ hρ d.obj)

@[simp]
theorem normInvariantLocusAction_apply_coe (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (g : H) (x : d.obj.locus) :
    ((show d.obj.locus from
      ConcreteCategory.hom ((normInvariantLocusAction ρ hρ H d).obj.ρ g) x) :
        BanachSpectrum A) = ρ g.val • x.val := rfl

/-- All actual bounded restrictions give equivariant continuous locus
inclusions for the common subgroup. -/
def normInvariantLocusFunctor (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ ContAction TopCat.{u} H where
  obj d := normInvariantLocusAction ρ hρ H d
  map f := ObjectProperty.homMk
    { hom := TopCat.ofHom f.hom.locusMap
      comm := fun _ => by
        apply TopCat.ext
        intro x
        rfl }
  map_id _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    rfl

@[simp]
theorem normInvariantLocusFunctor_map_apply (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e) (x : d.obj.locus) :
    ((normInvariantLocusFunctor ρ hρ H).map f).hom.hom x =
      f.hom.locusMap x := rfl

/-- Forgetting the continuous action gives exactly the existing locus diagram. -/
@[simp]
theorem normInvariantLocusFunctor_forget (H : OpenSubgroup G) :
    normInvariantLocusFunctor ρ hρ H ⋙ forget₂ _ TopCat.{u} =
      (normInvariantChartProperty ρ hρ H).ι ⋙ locusFunctor K A := rfl

variable [CompleteSpace K]

/-- Restrict the constructed quotient-norm continuous section action, keeping
the entire original weighted rational quotient and its bounded operators. -/
def normInvariantSectionAction (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) : NormContinuousAction K H :=
  (NormContinuousAction.restrict (normInvariantStabilizerInclusion ρ hρ H d)).obj
    (normContinuousSectionAction ρ hρ d.obj)

@[simp]
theorem normInvariantSectionAction_algebra (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    (normInvariantSectionAction ρ hρ H d).obj.V = d.obj.algebra := rfl

/-- The full automorphism homomorphism is precisely the restricted actual
bounded section action, including its inverse maps. -/
@[simp]
theorem normInvariantSectionAction_actionAut (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) :
    (normInvariantSectionAction ρ hρ H d).actionAut =
      (normSectionAction ρ hρ d.obj).comp
        (normInvariantStabilizerInclusion ρ hρ H d).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  rfl

@[simp]
theorem normInvariantSectionAction_baseMap (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (g : H) (a : A) :
    ((normInvariantSectionAction ρ hρ H d).obj.ρ g).toAlgHom (d.obj.baseMap a) =
      d.obj.baseMap ((ρ g.val).hom.toAlgHom a) :=
  normSectionAction_baseMap ρ hρ d.obj
    (normInvariantStabilizerInclusion ρ hρ H d g) a

/-- Actual rational restrictions commute with the bounded common-group
operators as equalities of full bounded algebra maps. -/
theorem normInvariantSectionAction_restriction (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e) (g : H) :
    f.hom.restriction.comp ((normInvariantSectionAction ρ hρ H e).obj.ρ g) =
      ((normInvariantSectionAction ρ hρ H d).obj.ρ g).comp f.hom.restriction :=
  (normSectionAction_restriction ρ hρ f.hom g.val
    (d.property g.property) (e.property g.property)).symm

/-- The actual bounded rational section presheaf now takes values in
norm-continuous common-group actions; no equivariance is imposed on arrows. -/
def normInvariantBoundedPresheaf (H : OpenSubgroup G) :
    (NormInvariantChart ρ hρ H)ᵒᵖ ⥤ NormContinuousAction K H where
  obj d := normInvariantSectionAction ρ hρ H d.unop
  map f := NormContinuousAction.homMk f.unop.hom.restriction
    (normInvariantSectionAction_restriction ρ hρ H f.unop)
  map_id _ := by
    apply NormContinuousAction.hom_ext
    rfl
  map_comp _ _ := by
    apply NormContinuousAction.hom_ext
    rfl

@[simp]
theorem normInvariantBoundedPresheaf_forget (H : OpenSubgroup G) :
    normInvariantBoundedPresheaf ρ hρ H ⋙ NormContinuousAction.forget =
      (normInvariantChartProperty ρ hρ H).ι.op ⋙ boundedPresheaf K A := rfl

/-- The structural bounded base maps are equivariant for the common group. -/
def normInvariantBaseMapNat (H : OpenSubgroup G) :
    (Functor.const (NormInvariantChart ρ hρ H)ᵒᵖ).obj
      ((NormContinuousAction.restrict
        { toMonoidHom := H.toSubgroup.subtype
          continuous_toFun := continuous_subtype_val }).obj
        (NormContinuousAction.ofAut A ρ hρ)) ⟶
      normInvariantBoundedPresheaf ρ hρ H where
  app d := NormContinuousAction.homMk d.unop.obj.baseMap
    (fun g => BoundedAlgHom.ext
      (fun a => (normInvariantSectionAction_baseMap ρ hρ H d.unop g a).symm))
  naturality _ _ f := by
    apply NormContinuousAction.hom_ext
    exact f.unop.hom.comp_baseMap.symm

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- Jointly continuous point actions follow functorially from the constructed
norm-continuous section presheaf, with inverse bounded seminorm pullbacks. -/
def normInvariantSpectrumFunctor (H : OpenSubgroup G) :
    NormInvariantChart ρ hρ H ⥤ ContAction TopCat.{u} H :=
  (normInvariantBoundedPresheaf ρ hρ H).rightOp ⋙ NormContinuousAction.spectrumFunctor

@[simp]
theorem normInvariantSpectrumFunctor_obj_apply (H : OpenSubgroup G)
    (d : NormInvariantChart ρ hρ H) (g : H)
    (x : BanachSpectrum d.obj.algebra) (b : d.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (((normInvariantSpectrumFunctor ρ hρ H).obj d).obj.ρ g) x) b =
        x ((normSectionAction ρ hρ d.obj
          (normInvariantStabilizerInclusion ρ hρ H d g)).inv.toAlgHom b) := by
  change x (((normInvariantSectionAction ρ hρ H d).actionAut g).inv.toAlgHom b) = _
  rw [normInvariantSectionAction_actionAut]
  rfl

@[simp]
theorem normInvariantSpectrumFunctor_map_apply (H : OpenSubgroup G)
    {d e : NormInvariantChart ρ hρ H} (f : d ⟶ e)
    (x : BanachSpectrum d.obj.algebra) (b : e.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (((normInvariantSpectrumFunctor ρ hρ H).map f).hom.hom x) b =
        x (f.hom.restriction b) := rfl

/-- Forgetting the continuous point action retains the exact actual rational
spectrum diagram, including its original bounded pullback maps. -/
@[simp]
theorem normInvariantSpectrumFunctor_forget (H : OpenSubgroup G) :
    normInvariantSpectrumFunctor ρ hρ H ⋙ forget₂ _ TopCat.{u} =
      (normInvariantChartProperty ρ hρ H).ι ⋙ toTopologicalSpace K A := rfl

/-- The proved rational spectrum homeomorphism is an isomorphism of continuous
actions for the unchanged common open subgroup. -/
def normInvariantSpectrumLocusIso (H : OpenSubgroup G) :
    normInvariantSpectrumFunctor ρ hρ H ≅ normInvariantLocusFunctor ρ hρ H :=
  NatIso.ofComponents (fun d => ObjectProperty.isoMk _
    (Action.mkIso (TopCat.isoOfHomeo d.obj.locusHomeomorph)
      (fun g => by
        apply TopCat.ext
        intro x
        change d.obj.locusHomeomorph
          (BanachSpectrum.comap
            ((normInvariantSectionAction ρ hρ H d).actionAut g).inv.toBoundedRingHom x) =
            normLocusOperator ρ hρ d.obj
              (normInvariantStabilizerInclusion ρ hρ H d g) (d.obj.locusHomeomorph x)
        rw [normInvariantSectionAction_actionAut]
        exact normSectionAction_locusHomeomorph ρ hρ d.obj
          (normInvariantStabilizerInclusion ρ hρ H d g) x)))
    (fun f => by
      apply ObjectProperty.hom_ext _
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      exact f.hom.locusHomeomorph_naturality x)

@[simp]
theorem normInvariantSpectrumLocusIso_forget (H : OpenSubgroup G) :
    Functor.isoWhiskerRight (normInvariantSpectrumLocusIso ρ hρ H) (forget₂ _ TopCat.{u}) =
      Functor.isoWhiskerLeft (normInvariantChartProperty ρ hρ H).ι
        (spectrumLocusIso K A) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
