/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.HomTensorTotal
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.RingedHomRestrictionComposition
import WeilConjectures.Algebra.Homology.RingedHomRestrictionOrdinary
import WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import WeilConjectures.Algebra.Homology.RingedInternalHomCovariantExact
import WeilConjectures.CategoryTheory.SiteRelocalizationKInjective

/-!
# Internal derived Hom calculus on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JB and 08JC
(auxiliary; not a blueprint node).

The tensor functor is specified by its natural total-tensor comparison on K-flat
representatives. Restriction uses Mathlib's slice functors and their induced functors
on unbounded derived categories. The opposite triangulated structure reverses shifts.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem ringedSite_pushforward_limits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem ringedSite_pushforward_colimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K] [G.IsCocontinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  have : PreservesColimitsOfSize.{u, u} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{u} J K).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} S
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- The overFunctor slice restriction is additive.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(auxiliary; not a blueprint node).

Proof: Restriction evaluates a sectionwise linear natural transformation on the slice site.
    Addition of such transformations is sectionwise, so restriction preserves addition. -/
@[instance]
theorem ringedSite_overFunctor_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) U).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- The overFunctor slice restriction preserves finite limits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(auxiliary; not a blueprint node).

Proof: Kernels and finite products of module sheaves are computed sectionwise. Evaluation along
    the forgetful functor from the slice preserves these constructions. The ring transport in
    overMap is the canonical identity on sections. -/
@[instance]
theorem ringedSite_overFunctor_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  exact ringedSite_pushforward_limits (𝟙 _)

/-- The overFunctor slice restriction preserves finite colimits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(auxiliary; not a blueprint node).

Proof: Finite sums are sectionwise and cokernels are sheafified sectionwise cokernels. Coverings
    of an object of a slice are exactly coverings of its domain with the given structural arrow.
    Thus restriction commutes with sheafification and with these cokernels. The same argument
    applies to overMap. -/
@[instance]
theorem ringedSite_overFunctor_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteColimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  exact ringedSite_pushforward_colimits (𝟙 _)

/-- The overMap slice restriction is additive.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(auxiliary; not a blueprint node).

Proof: Restriction evaluates a sectionwise linear natural transformation on the slice site.
    Addition of such transformations is sectionwise, so restriction preserves addition. -/
@[instance]
theorem ringedSite_overMap_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- The overMap slice restriction preserves finite limits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(auxiliary; not a blueprint node).

Proof: Kernels and finite products of module sheaves are computed sectionwise. Evaluation along
    the forgetful functor from the slice preserves these constructions. The ring transport in
    overMap is the canonical identity on sections. -/
@[instance]
theorem ringedSite_overMap_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteLimits (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f) := by
  exact ringedSite_pushforward_limits (Sheaf.pushforwardOverMapIso _ f).inv

/-- The overMap slice restriction preserves finite colimits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(auxiliary; not a blueprint node).

Proof: Finite sums are sectionwise and cokernels are sheafified sectionwise cokernels. Coverings
    of an object of a slice are exactly coverings of its domain with the given structural arrow.
    Thus restriction commutes with sheafification and with these cokernels. The same argument
    applies to overMap. -/
@[instance]
theorem ringedSite_overMap_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteColimits (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f) := by
  exact ringedSite_pushforward_colimits (Sheaf.pushforwardOverMapIso _ f).inv

attribute [local irreducible] derivedInternalHom homComplexFunctor

local instance {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [h : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))] (U : C) :
    HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
  h U

/-- Derived internal Hom commutes naturally with slice restriction, compatibly
with successive restrictions. The comparison for V to U, followed by transport
along the canonical derived overFunctorMap, equals direct restriction to V.

Source: Stacks Project, Tag 08JB (lemma-restriction-RHom-to-U).
(auxiliary; not a blueprint node).

Proof: Represent M by a K-injective I and L by A. The sections of Hom(A,I) restricted to U, over
    each arrow W to U, are the same families of local maps as the sections of Hom(A restricted to
    U, I restricted to U); their differentials coincide. Restriction preserves K-injectivity
    (lem-pur-kinjective-restrict-localized), so these complexes compute derived internal Hom. The
    same construction for Over.map f gives s. On every object mapping to V both successive and
    direct comparisons are identity on these families, after the canonical overFunctorMap
    transport. This proves the displayed equation; pre- and postcomposition give naturality.
    Independence of representatives follows from lem-pur-rhom-well-defined. -/
theorem ringedInternalHom_restriction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] [hDCU : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))] :
    ∃ (e : ∀ U : C, (derivedInternalHom.{u, w} J R) ⋙ (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory ≅
    ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
    R) U).mapDerivedCategory.op.prod (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over U) inferInstance (J.over U) (R.over U) (hDCU U)))
    (s : ∀ (U V : C) (f : V ⟶ U), (@derivedInternalHom.{u, w} (Over U) inferInstance (J.over U)
    (R.over U) (hDCU U)) ⋙ (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory ≅
    ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.op.prod (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over V) inferInstance (J.over V) (R.over V) (hDCU V))),
    ∀ (U V : C) (f : V ⟶ U) (L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.map ((e U).hom.app (op L, M)) ≫
    (s U V f).hom.app (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L),
    (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    U).mapDerivedCategory.obj M) ≫
    (@derivedInternalHom.{u, w} (Over V) inferInstance (J.over V) (R.over V) (hDCU V)).map
    (X := (op ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose
    J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L)),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj M)))
    (Y := (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) V).mapDerivedCategory.obj L), (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V).mapDerivedCategory.obj M))
    (((((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)) ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).inv.app L).op, (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)) ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f))).hom.app M) =
    (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f)) ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).hom.app ((derivedInternalHom.{u, w} J R).obj (op L, M)) ≫
    (e V).hom.app (op L, M) := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    let F (U : C) : RingedHomRestriction.Modules R ⥤
        RingedHomRestriction.Modules (R.over U) :=
      SheafOfModules.overFunctor.{u} (RingedHomRestriction.Rings R) U
    let G (U V : C) (f : V ⟶ U) : RingedHomRestriction.Modules (R.over U) ⥤
        RingedHomRestriction.Modules (R.over V) :=
      SheafOfModules.overMap.{u} (RingedHomRestriction.Rings R) f
    let (U : C) : HasDerivedCategory.{w} (RingedHomRestriction.Modules (R.over U)) := hDCU U
    let (U : C) : (F U).Additive :=
      ringedSite_overFunctor_additive J R U
    let (U V : C) (f : V ⟶ U) :
        (G U V f).Additive :=
      ringedSite_overMap_additive J R f
    let (U : C) : PreservesFiniteLimits
        (F U) :=
      ringedSite_overFunctor_limits J R U
    let (U : C) : PreservesFiniteColimits
        (F U) :=
      ringedSite_overFunctor_colimits J R U
    let (U V : C) (f : V ⟶ U) : PreservesFiniteLimits
        (G U V f) :=
      ringedSite_overMap_limits J R f
    let (U V : C) (f : V ⟶ U) : PreservesFiniteColimits
        (G U V f) :=
      ringedSite_overMap_colimits J R f
    obtain ⟨a, b, hab⟩ := RingedHomRestriction.ordinary_comparisons J R
    have hk (U : C) (I : RingedHomRestriction.Complex R) (hI : I.IsKInjective) :
        CochainComplex.IsKInjective
          ((Functor.mapHomologicalComplex
            (F U) (.up ℤ)).obj I) := by
      exact isKInjective_restrict_localized (RingedHomRestriction.Rings R) U inferInstance I
    have hs (U V : C) (f : V ⟶ U)
        (I : RingedHomRestriction.Complex (R.over U)) (hI : I.IsKInjective) :
        CochainComplex.IsKInjective
          ((Functor.mapHomologicalComplex
            (G U V f) (.up ℤ)).obj I) := by
      let : (G U V f).PreservesKInjectiveComplexes :=
        SheafOfModules.overMap_preservesKInjectiveComplexes_ofUniverses.{u, u, u}
          (RingedHomRestriction.Rings R) f
      exact Functor.PreservesKInjectiveComplexes.isKInjective_map I
    have he (U : C) := RingedHomRestriction.comparison_exists R (R.over U)
      (F U) (hk U) (a U)
    choose e he using he
    have hs' (U V : C) (f : V ⟶ U) :=
      RingedHomRestriction.comparison_exists (R.over U) (R.over V)
        (G U V f) (hs U V f) (b U V f)
    choose s hs' using hs'
    refine ⟨e, s, ?_⟩
    intro U V f
    let c : F U ⋙ G U V f ≅ F V :=
      SheafOfModules.overFunctorMap (RingedHomRestriction.Rings R) f
    have hn := RingedHomRestriction.composite_normalized R (R.over U) (R.over V)
      (F U) (G U V f) (F V) c (hk U) (a U) (b U V f) (e U) (s U V f) (he U) (hs' U V f)
    have hc : RingedHomRestriction.composite
        (Functor.mapHomologicalComplexCompIso c (.up ℤ)) (a U) (b U V f) = a V :=
      (RingedHomRestriction.compatible_iff _ _ _ _ _ _ _ _ _ _).mp (hab U V f)
    rw [hc] at hn
    have h := RingedHomRestriction.comparison_unique R (R.over V) (F V) (a V)
      _ (e V) hn (he V)
    exact (RingedHomRestriction.compatible_iff _ _ _ _ _ _ _ _ _ _).mpr h

/-- Internal derived Hom preserves distinguished triangles in each variable
and commutes with shifts. The first variable is a functor from the opposite
triangulated category, whose shift by m is the original shift by -m.

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(auxiliary; not a blueprint node).

Proof: For the first variable fix a K-injective I representing M. The graded splitting of the cone
    gives Hom(C(f),I) as Hom(B,I) plus Hom(A[1],I). Put X=Hom(B,I), Y=Hom(A,I), h=f*. In degree n
    its differential is (d_X x, d_Y y+(-1)^(n+1)h(x)); (x,y) maps to ((-1)^(n-1)y,x) in C(h)[-1].
    Rotation gives the reversed distinguished triangle. For the second variable choose K-injective
    representatives J,I; lem-weil-pbc-kinjective-hom-derived represents the morphism by a chain
    map g. TR3 and lem-sf-triangle-morphism-iso identify its cone triangle with the given
    triangle. Its cone is K-injective: Hom from any acyclic test complex is the cone of two
    acyclic ordinary Hom complexes, hence acyclic. Then Hom(A,C(g)) is the cone of Hom(A,g), with
    differential (dx+Hom(A,g)y,-dy). These cone calculations descend by
    lem-pur-homotopy-category-triangulated and lem-pur-rhom-well-defined. The natural shift
    identifications from lem-pur-derived-internal-hom-shift-left and
    lem-pur-derived-internal-hom-shift-right give H(P[m],Q)=H(P,Q)[-m] and H(P,Q[n])=H(P,Q)[n].
    The cone signs give the required triangulated structures. Only finite splittings occur, so no
    boundedness or finite-generation hypothesis is used. -/
theorem ringedInternalHom_exact
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] :
    (∀ L : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op
    L)).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op L)).IsTriangulated) ∧
    (∀ M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj
    M).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj M).IsTriangulated) := by
  exact ⟨ringedInternalHom_covariant_exact J R, ringedInternalHom_contravariant_exact J R⟩

end CategoryTheory
