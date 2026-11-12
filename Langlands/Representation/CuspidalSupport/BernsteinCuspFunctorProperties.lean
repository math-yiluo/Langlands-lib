import Langlands.Representation.CuspidalSupport.BernsteinCuspAdjunction
import Langlands.Representation.Induction.Faithful
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RationalSupportInduction
import Langlands.Representation.Category.ExactInclusion
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Actual Bernstein functors and their independent properties -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace Langlands.CuspidalSupport

universe uI uC vC uD vD

/-- A coproduct of faithful component functors is faithful in a category with
zero morphisms: each coproduct injection is a split monomorphism. -/
theorem piCoproductFunctor_faithful
    {ι : Type uI} {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
    [HasColimitsOfShape (Discrete ι) C]
    {D : ι → Type uD} [∀ j, Category.{vD} (D j)]
    (K : ∀ j, D j ⥤ C) [∀ j, (K j).Faithful] :
    (Functor.pi K ⋙ (piEquivalenceFunctorDiscrete ι C).functor ⋙ colim).Faithful where
  map_injective {X Y} f g hfg := by
    funext j
    apply (K j).map_injective
    apply (cancel_mono (Sigma.ι (fun j => (K j).obj (Y j)) j)).mp
    have h := congrArg
      (fun t => Sigma.ι (fun j => (K j).obj (X j)) j ≫ t) hfg
    simpa [Functor.pi, piEquivalenceFunctorDiscrete] using h

universe uR uG uW

section ConcreteExactness

variable {R : Type uR} [CommRing R] {H : Type uG} [Group H] [TopologicalSpace H]

/-- Concrete short exactness agrees with categorical short exactness in the
published category of smooth representations. -/
theorem smoothShortComplex_shortExact_iff
    (S : ShortComplex (SmoothRep.{uR, uG, uW} R H)) :
    S.ShortExact ↔ SmoothRep.IsShortExact (SmoothRep.hom S.f) (SmoothRep.hom S.g) := by
  let U : SmoothRep.{uR, uG, uW} R H ⥤ ModuleCat.{uW} R :=
    SmoothRep.toRep ⋙ forget₂ (Rep.{uW} R H) (ModuleCat.{uW} R)
  constructor
  · intro hS
    have h := hS.map_of_exact U
    exact ⟨h.moduleCat_injective_f, h.moduleCat_surjective_g,
      h.exact.moduleCat_range_eq_ker⟩
  · rintro ⟨hf, hg, hex⟩
    have : Mono S.f := (SmoothRep.mono_iff_injective _).mpr hf
    have : Epi S.g := (SmoothRep.epi_iff_surjective _).mpr hg
    refine ⟨U.reflects_exact_of_faithful S ?_⟩
    exact (S.map U).moduleCat_exact_iff_range_eq_ker.mpr hex

/-- A pair of concrete short exact intertwiners has zero composite. -/
theorem smooth_comp_eq_zero_of_isShortExact
    {A B C : SmoothRep.{uR, uG, uW} R H} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g)) :
    f ≫ g = 0 := by
  ext x
  have hx : SmoothRep.hom f x ∈ (SmoothRep.hom g).toLinearMap.ker := by
    rw [← hfg.2.2]
    exact ⟨x, rfl⟩
  exact hx

end ConcreteExactness

/-- Short exactness of functor diagrams can be tested at every object. -/
theorem shortComplex_shortExact_of_evaluation
    {J : Type uI} [Category J] {C : Type uC} [Category.{vC} C] [Abelian C]
    (S : ShortComplex (J ⥤ C))
    (hS : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have : ∀ j, Mono (S.f.app j) := fun j => (hS j).mono_f
  have : ∀ j, Epi (S.g.app j) := fun j => (hS j).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app _
  have : Epi S.g := NatTrans.epi_of_epi_app _
  refine ⟨S.exact_of_f_is_kernel ?_⟩
  apply evaluationJointlyReflectsLimits
  intro j
  exact (KernelFork.isLimitMapConeEquiv _ _).symm (hS j).fIsKernel

/-- Finite coproducts preserve actual short exact sequences of smooth
representations, including an empty coproduct. -/
theorem finiteCoproduct_map_isShortExact
    {ι : Type uI} [Finite ι]
    {R : Type uR} [CommRing R] {H : Type uG} [Group H] [TopologicalSpace H]
    {A B C : Discrete ι ⥤ SmoothRep.{uR, uG, uW} R H}
    (f : A ⟶ B) (g : B ⟶ C)
    (hfg : ∀ j, SmoothRep.IsShortExact
      (SmoothRep.hom (f.app j)) (SmoothRep.hom (g.app j))) :
    SmoothRep.IsShortExact (SmoothRep.hom (colim.map f)) (SmoothRep.hom (colim.map g)) := by
  have : HasFiniteBiproducts (SmoothRep.{uR, uG, uW} R H) := Abelian.hasFiniteBiproducts
  have : PreservesFiniteLimits
      (colim : (Discrete ι ⥤ SmoothRep.{uR, uG, uW} R H) ⥤ _) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  let S := ShortComplex.mk f g (by
    apply NatTrans.ext
    funext j
    exact smooth_comp_eq_zero_of_isShortExact _ _ (hfg j))
  have hS : S.ShortExact := shortComplex_shortExact_of_evaluation S
    (fun j => (smoothShortComplex_shortExact_iff _).mpr (hfg j))
  exact (smoothShortComplex_shortExact_iff _).mp (hS.map_of_exact colim)

universe uF uV

open _root_.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

section StandardFamily

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance : TopologicalSpace (rationalPoints G) := pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The actual standard normalized Jacquet functor, on the carrier universe of
the closed second-Lemma statement. -/
abbrev bernsteinJacquetFunctor (J : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) :=
  normalizedJacquetFunctor (unipotent i ν J) (levi i ν J)
    (family.closedUnipotent J) (family.decomposition J).levi_le_normalizer

/-- The literal finite-coproduct induction functor `I` of the target. -/
def bernsteinInductionFunctor :
    (∀ J : Finset (SimpleRoot i ν),
      (bernsteinLeviCuspidalProperty.{uV, uF} i ν family J).FullSubcategory) ⥤
        SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  have : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
  Functor.pi (fun J => (bernsteinLeviCuspidalProperty i ν family J).ι ⋙
      normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)) ⋙
    (piEquivalenceFunctorDiscrete (Finset (SimpleRoot i ν))
      (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))).functor ⋙ colim

/-- The literal tuple of normalized Jacquet functors followed by the supplied
cuspidal-part functors. No existence of the latter is asserted here. -/
def bernsteinRestrictionFunctor
    (sc : ∀ J : Finset (SimpleRoot i ν),
      SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤
        (bernsteinLeviCuspidalProperty.{uV, uF} i ν family J).FullSubcategory) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
      (∀ J : Finset (SimpleRoot i ν),
        (bernsteinLeviCuspidalProperty.{uV, uF} i ν family J).FullSubcategory) :=
  Functor.pi' fun J => bernsteinJacquetFunctor i ν family J ⋙ sc J

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Actual standard induction is faithful, independently of cuspidal
reflector existence and of the exactness assertions. -/
theorem bernsteinInductionFunctor_faithful :
    (bernsteinInductionFunctor.{uF, uV} i ν family).Faithful := by
  have : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
  have (J : Finset (SimpleRoot i ν)) :
      (normalizedInductionFunctor.{uF, max uF uV}
        (family.decomposition J) (family.closedUnipotent J)).Faithful :=
    normalizedInductionFunctor_faithful _ _
      (continuous_standard_projection i ν standardCocharacter
        family.connectedReductive family.maximalSplitTorus family.genericCocharacter J)
  exact piCoproductFunctor_faithful _

/-- The literal finite-coproduct induction functor sends every componentwise
short exact sequence to a short exact sequence. -/
theorem bernsteinInductionFunctor_map_isShortExact
    {X Y Z : ∀ J : Finset (SimpleRoot i ν),
      (bernsteinLeviCuspidalProperty.{uV, uF} i ν family J).FullSubcategory}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : ∀ J, SmoothRep.IsShortExact (SmoothRep.hom (f J).hom)
      (SmoothRep.hom (g J).hom)) :
    SmoothRep.IsShortExact
      (SmoothRep.hom ((bernsteinInductionFunctor.{uF, uV} i ν family).map f))
      (SmoothRep.hom ((bernsteinInductionFunctor.{uF, uV} i ν family).map g)) := by
  have : Finite (SimpleRoot i ν) := family.finiteSimpleRoots
  have : T2Space F := BruhatTits.localField_t2Space F
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  apply finiteCoproduct_map_isShortExact
  rintro ⟨J⟩
  exact normalizedInductionFunctor_map_isShortExact
    (compactOpenCofinal_of_nonarchimedean _) (family.decomposition J)
    (family.closedUnipotent J)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter J)
    (continuous_standard_projection i ν standardCocharacter
      family.connectedReductive family.maximalSplitTorus family.genericCocharacter J)
    (f J).hom (g J).hom (hfg J)

/-- Each actual Jacquet component preserves every short exact sequence. All
unipotent compact-containment hypotheses are discharged by published results. -/
theorem bernsteinJacquetFunctor_map_isShortExact
    (J : Finset (SimpleRoot i ν))
    {A B C : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (f : A ⟶ B) (g : B ⟶ C)
    (hfg : SmoothRep.IsShortExact (SmoothRep.hom f) (SmoothRep.hom g)) :
    SmoothRep.IsShortExact (SmoothRep.hom ((bernsteinJacquetFunctor i ν family J).map f))
      (SmoothRep.hom ((bernsteinJacquetFunctor i ν family J).map g)) :=
  jacquetFunctor_map_isShortExact (family.decomposition J) (family.closedUnipotent J)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter family.connectedReductive family.maximalSplitTorus
        family.genericCocharacter J) f g hfg

end StandardFamily

end Langlands.CuspidalSupport
