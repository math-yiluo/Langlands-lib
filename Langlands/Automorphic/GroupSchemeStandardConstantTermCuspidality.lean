import Langlands.Global.ArthurTruncationCuspidal
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Global.AdelicCompactConstantTermCovariance
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Derived.RelativeMaximalTorusProduct
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof

/-! # Cuspidality from the proper standard constant terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.GroupScheme Langlands.Global AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Proper standard constant terms detect cuspidality for continuous rational-invariant
functions on the actual adelic group. -/
def StandardConstantTermCuspidalityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (f : ContinuousRationalFunctions F G),
    (∀ I : StandardIndex F G fam.i fam.ν, I ≠ fam.top →
      subgroupConstantTerm F (fam.iU I ≫ fam.p I) (evaluate F G f) = 0) →
    ArthurTruncation.HasCuspidalConstantTerms (evaluate F G f)

omit [NumberField F] in
/-- The all-test image of the full standard parabolic is the ambient group. -/
theorem standardParabolicFamily_range_top (fam : StandardParabolicFamily F G) :
    SubgroupFunctor.range (fam.p fam.top) = ⊤ :=
  (fam.isCompatible fam.top).parabolic_eq.trans
    (standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
      fam.ν fam.generic).2.2.1

/-- For a continuous rational-invariant function, vanishing along the radicals of the
proper standard parabolics implies vanishing along the radicals of all proper parabolics. -/
theorem hasCuspidalConstantTerms_of_standard : StandardConstantTermCuspidalityStatement.{u} := by
  intro F _ _ G _ _ _ fam f hf P U p j _ _ hp hj hproper
  obtain ⟨ζ, hpζ⟩ := (parabolicDynamic F G fam.connectedReductive P p hp.isClosedSubgroup).mp hp
  obtain ⟨I, ⟨g, hζ⟩, -⟩ :=
    (standardParabolicClassification F G fam.connectedReductive fam.T fam.i fam.maximalSplit
      fam.ν fam.generic).2 ζ
  let e := G.innerIso g
  have hpI : SubgroupFunctor.range p = (SubgroupFunctor.range (fam.p I)).comap e.hom := by
    rw [(fam.isCompatible I).parabolic_eq, hpζ]
    exact hζ
  have hI : I ≠ fam.top := by
    intro heq
    apply hproper
    rw [hpI, heq, standardParabolicFamily_range_top, SubgroupFunctor.comap_top]
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsClosedImmersion (fam.p I).hom.hom.left := (fam.isCompatible I).parabolic.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let : Mono (fam.p I).hom.hom := Over.mono_of_mono_left _
  let : Mono (p ≫ e.hom).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hpIso : SubgroupFunctor.range (p ≫ e.hom) = SubgroupFunctor.range (fam.p I) := by
    rw [SubgroupFunctor.range_comp_iso, hpI, SubgroupFunctor.comap_iso_hom_inv]
  let hrep : (SubgroupFunctor.range (fam.p I)).IsRepresentedBy (p ≫ e.hom) :=
    ⟨inferInstance, hpIso⟩
  let hrepI : (SubgroupFunctor.range (fam.p I)).IsRepresentedBy (fam.p I) :=
    ⟨inferInstance, rfl⟩
  let eP := hrep.isoOfIsRepresentedBy hrepI
  have heP : eP.hom ≫ fam.p I = p ≫ e.hom := hrep.isoOfIsRepresentedBy_hom_comp hrepI
  have hjI : SubgroupFunctor.range (j ≫ eP.hom) = SubgroupFunctor.range (fam.iU I) :=
    (hj.comp_iso eP).1.range_eq (fam.isUnipotentRadical I).1
  have hjp : SubgroupFunctor.range (j ≫ p) =
      (SubgroupFunctor.range (fam.iU I ≫ fam.p I)).comap e.hom := by
    apply (SubgroupFunctor.eq_comap_iso_iff e).mpr
    rw [← SubgroupFunctor.range_comp_iso]
    simpa only [Category.assoc, heP] using
      SubgroupFunctor.range_comp_eq_of_range_eq _ _ (fam.p I) hjI
  let V := SubgroupFunctor.range (fam.iU I ≫ fam.p I)
  let U' := SubgroupFunctor.range (j ≫ p)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU I ≫ fam.p I)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G U' : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (j ≫ p)
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) :=
    fam.compactSpace_radicalRationalQuotient I
  funext y
  rw [subgroupConstantTerm_eq_continuousConstantTerm (j ≫ p) f]
  refine (forall_constantTerm_eq_zero_comap_innerIso_iff F G g V U' hjp f).mp (fun x => ?_) y
  change constantTerm F G (SubgroupFunctor.range (fam.iU I ≫ fam.p I))
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) f x = 0
  rw [← subgroupConstantTerm_eq_continuousConstantTerm (fam.iU I ≫ fam.p I) f]
  exact congrFun (hf I hI) x

end Langlands.Automorphic.GroupSchemeFunctions
