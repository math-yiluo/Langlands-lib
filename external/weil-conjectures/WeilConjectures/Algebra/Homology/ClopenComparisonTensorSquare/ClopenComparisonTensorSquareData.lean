/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Tensor squares for the normalized clopen comparison

Source: Stacks 0F7B, 07A4, 0GL1 and 04TS; the seven-step tensor refinement
(blueprint: def-sf-clopen-comparison-tensor-data).

The composite presentations `J_s ⋙ J_b` and `P_q ⋙ P_s` are used for `J_k`
and `P_r`. Their adjunctions fix the canonical compositors. All ringed-site
operations are the existing ordinary unbounded localizations, also in systems mode.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ClopenComparisonTensorSquare

/-- The Cartesian open square inside the proper/open square. The ring map is
written in its adjoint direct-image form, exactly as in `Input`.
Source: Stacks 0F7B, 03D7 (blueprint: def-sf-clopen-comparison-tensor-data). -/
def input (m : Mode) {B C D : Scheme.{u}} (p : B ⟶ D) (i : C ⟶ D)
    [IsOpenImmersion i] (R : Sheaf (topology m D) CommRingCat.{u + 1})
    (S : Sheaf (topology m B) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m p).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m D) (topology m B)).obj S) : Input m where
  U := C
  U' := CategoryTheory.Limits.pullback p i
  X := D
  X' := B
  gU := pullback.snd p i
  j' := pullback.fst p i
  j := i
  g := p
  square :=
    { w := pullback.condition.symm
      isoPullback := pullbackSymmetry p i
      hom_fst := pullbackSymmetry_hom_comp_fst p i
      hom_snd := pullbackSymmetry_hom_comp_snd p i
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  R := R
  S := S
  coefficient := c

/-- A presentation of the canonical 07A4 comparison for a possibly nonexact
ringed pullback. Its ordinary unit formula fixes pure tensors. The representative
square uses the published signed ProjectionRestriction.total map and the actual left-derived counit;
it does not assume the ordinary pullback exact.
Source: Stacks 03EL, 07A4 (blueprint: def-sf-clopen-comparison-tensor-data). -/
structure PullTensor (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology m Y) CommRingCat.{u + 1})
    (S : Sheaf (topology m X) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S)
    (p : Pullback R S (direct m f R S c)) (a : TensorModel R) (b : TensorModel S) where
  ordinary : ∀ M N : ProjectionRestriction.Mod R,
    p.ordinary.obj (((ProjectionRestriction.tensor R).obj M).obj N) ≅
    ((ProjectionRestriction.tensor S).obj (p.ordinary.obj M)).obj (p.ordinary.obj N)
  pure_unit : ∀ (M N : ProjectionRestriction.Mod R) (W : (Site m Y)ᵒᵖ)
      (x : M.val.obj W) (y : N.val.obj W),
    ((direct m f R S c).map (ordinary M N).hom).val.app W
        ((p.adjunction.unit.app (((ProjectionRestriction.tensor R).obj M).obj N)).val.app W
          (ProjectionRestriction.pure R M N W x y)) =
      ProjectionRestriction.pure S (p.ordinary.obj M) (p.ordinary.obj N) ((baseChange m f).op.obj W)
        ((p.adjunction.unit.app M).val.app W x)
        ((p.adjunction.unit.app N).val.app W y)
  preserves : ∀ P, ProjectionRestriction.resolving R P →
    ProjectionRestriction.resolving S ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  comparison : a.functor ⋙ p.derived ≅ (p.derived.prod p.derived) ⋙ b.functor
  comm : ∀ (P Q : CochainComplex (ProjectionRestriction.Mod R) ℤ) (n l : ℤ),
    ProjectionRestriction.totalComponent a b p.ordinary ordinary P Q n ≫
        p.ordinary.map (((ProjectionRestriction.total R).obj (P, Q)).d n l) =
      ((ProjectionRestriction.total S).obj ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
        (p.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)).d n l ≫
          ProjectionRestriction.totalComponent a b p.ordinary ordinary P Q l
  representative : ∀ (P Q : CochainComplex (ProjectionRestriction.Mod R) ℤ)
      (hp : ProjectionRestriction.resolving R P) (hq : ProjectionRestriction.resolving R Q),
    p.derived.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
        comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        b.functor.map (Prod.mkHom
          (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P)
          (derivedPullbackComplexComparison p.ordinary p.derived p.epsilon Q)) ≫
        b.representative.inv.app
          (⟨(p.ordinary.mapHomologicalComplex (.up ℤ)).obj P, preserves P hp⟩,
            ⟨(p.ordinary.mapHomologicalComplex (.up ℤ)).obj Q, preserves Q hq⟩) ≫
        DerivedCategory.Q.map (ProjectionRestriction.totalMap a b p.ordinary ordinary comm P Q) =
      derivedPullbackComplexComparison p.ordinary p.derived p.epsilon
        ((ProjectionRestriction.total R).obj (P, Q))

/-- The remaining open tensor data, with the extension fixed in advance.
The ordinary comparison retains the literal restriction of ProjectionRestriction.pure sections;
`TensorComparison` pins its derived map on all flat K-flat representatives.
The inverse transpose is precisely the open-unit normalization.
Source: Stacks 0GL1, 07A4 (blueprint: def-sf-clopen-comparison-tensor-data). -/
structure OpenTensor (m : Mode) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology m X) CommRingCat.{u + 1})
    (e : OpenExtension m j R) (a : TensorModel R)
    (b : TensorModel (restrictRing m j R)) where
  ordinary : ∀ M N : ProjectionRestriction.Mod R,
    (OpenTensorNormalization.restrict m j R).obj (((ProjectionRestriction.tensor R).obj M).obj N) ≅
      ((ProjectionRestriction.tensor (restrictRing m j R)).obj
        ((OpenTensorNormalization.restrict m j R).obj M)).obj
        ((OpenTensorNormalization.restrict m j R).obj N)
  pure_sections : ∀ (M N : ProjectionRestriction.Mod R) (W : (Site m U)ᵒᵖ)
      (x : M.val.obj ((openInclusion m j).op.obj W))
      (y : N.val.obj ((openInclusion m j).op.obj W)),
    (ordinary M N).hom.val.app W
        (ProjectionRestriction.pure R M N ((openInclusion m j).op.obj W) x y) =
      ProjectionRestriction.pure (restrictRing m j R)
        ((OpenTensorNormalization.restrict m j R).obj M)
        ((OpenTensorNormalization.restrict m j R).obj N) W x y
  tensorComparison : TensorComparison (OpenTensorNormalization.restrict m j R)
    (restrictionModel j R) a b ordinary
  delta : e.ordinary.mapDerivedCategory.prod (𝟭 _) ⋙ a.functor ≅
    (𝟭 _).prod (OpenTensorNormalization.restrict m j R).mapDerivedCategory ⋙ b.functor ⋙
      e.ordinary.mapDerivedCategory
  inverse_transpose : ∀ M N,
    (exactDerivedAdjunction e.adjunction).homEquiv _ _ (delta.inv.app (M, N)) =
      b.functor.map (Prod.mkHom ((exactDerivedAdjunction e.adjunction).unit.app M) (𝟙 _)) ≫
        tensorComparison.comparison.inv.app (e.ordinary.mapDerivedCategory.obj M, N)

/-- Simultaneous canonical data needed by the three squares. This is a conclusion
of the theorem, not an extra hypothesis on rings or derived objects. The reverse
clopen adjunction has the inverse open unit as its counit; hence its localized unit
is exactly the first-factor projection `(1,0)`. The composite-open tensor map has
its own prescribed transpose, independently of the composite-open equality below.
Source: Stacks 04TS, 0GL1 (blueprint: def-sf-clopen-comparison-tensor-data). -/
structure Data {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) {A : Scheme.{u}} (s : A ⟶ d.U') [IsOpenImmersion s] where
  tensorP : PullTensor m d.g d.R d.S d.coefficient o.gPull o.tensorX o.tensorX'
  tensorQ : PullTensor m d.gU (restrictRing m d.j d.R) (restrictRing m d.j' d.S)
    (cornerCoefficient t) o.gUPull o.tensorU o.tensorU'
  tensorB : OpenTensor m d.j' d.S o.opens.extension' o.tensorX' o.tensorU'
  extensionS : OpenExtension m s (restrictRing m d.j' d.S)
  tensorA : TensorModel (restrictRing m s (restrictRing m d.j' d.S))
  tensorS : OpenTensor m s (restrictRing m d.j' d.S) extensionS o.tensorU' tensorA
  rightAdjunction : restrict m s (restrictRing m d.j' d.S) ⊣ extensionS.ordinary
  counit_normalization : ∀ M,
    extensionS.adjunction.unit.app M ≫ rightAdjunction.counit.app M = 𝟙 M
  deltaK : (extensionS.ordinary.mapDerivedCategory ⋙ o.opens.jShriek').prod (𝟭 _) ⋙
      o.tensorX'.functor ≅
    (𝟭 _).prod (o.opens.jStar' ⋙
      (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory) ⋙
        tensorA.functor ⋙ (extensionS.ordinary.mapDerivedCategory ⋙ o.opens.jShriek')
  inverse_transposeK : ∀ M N,
    ((exactDerivedAdjunction extensionS.adjunction).comp o.opens.adj').homEquiv _ _
        (deltaK.inv.app (M, N)) =
      tensorA.functor.map
          (Prod.mkHom
            (((exactDerivedAdjunction extensionS.adjunction).comp o.opens.adj').unit.app M)
            (𝟙 _)) ≫
        tensorS.tensorComparison.comparison.inv.app
          (o.opens.jStar'.obj (o.opens.jShriek'.obj
            (extensionS.ordinary.mapDerivedCategory.obj M)), o.opens.jStar'.obj N) ≫
        (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
          (tensorB.tensorComparison.comparison.inv.app
            (o.opens.jShriek'.obj (extensionS.ordinary.mapDerivedCategory.obj M), N))

/-- The actual localized clopen projection, given by the exact reverse adjunction.
Source: Stacks 04TS (blueprint: def-sf-clopen-comparison-tensor-data). -/
def Data.rho {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} {A : Scheme.{u}} {s : A ⟶ d.U'} [IsOpenImmersion s]
    (v : Data o s) : 𝟭 (ProjectionRestriction.Der (restrictRing m d.j' d.S)) ⟶
      (OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory ⋙
        v.extensionS.ordinary.mapDerivedCategory :=
  (exactDerivedAdjunction v.rightAdjunction).unit

/-- The comparison is beta followed by the first-factor projection, with `k_!`
presented by the composite open extension and `P_r` by the composite pullback.
Source: Stacks 0F7B (blueprint: def-sf-clopen-comparison-tensor-data). -/
def alpha {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s)
    (H : ProjectionRestriction.Der (restrictRing m d.j d.R)) :
    o.gPull.derived.obj (o.opens.jShriek.obj H) ⟶
      o.opens.jShriek'.obj (v.extensionS.ordinary.mapDerivedCategory.obj
        ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj
          (o.gUPull.derived.obj H))) :=
  a.beta.hom.app H ≫ o.opens.jShriek'.map (v.rho.app (o.gUPull.derived.obj H))

/-- The three tensor identities and the composite-open normalization, as equalities
of morphisms on the whole ringed-site derived category, naturally in all inputs.
The theta factors write out `P_q P_i = P_b P_p`; no equality after evaluation is used.
Source: Stacks 07A4, 0GL1 and the node's tensor refinement
(blueprint: def-sf-clopen-comparison-tensor-data). -/
def Equations {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    {o : Operations d t} (a : Assertion o) {A : Scheme.{u}}
    {s : A ⟶ d.U'} [IsOpenImmersion s] (v : Data o s) : Prop :=
  (∀ (H : ProjectionRestriction.Der (restrictRing m d.j d.R)) (N : ProjectionRestriction.Der d.R),
    o.gPull.derived.map (a.gamma.hom.app (H, N)) ≫
        a.beta.hom.app (o.tensorU.functor.obj (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (o.tensorU'.functor.map
          (Prod.mkHom (𝟙 _) (o.theta.inv.app N))) =
      v.tensorP.comparison.hom.app (o.opens.jShriek.obj H, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (a.beta.hom.app H) (𝟙 _)) ≫
        v.tensorB.delta.hom.app (o.gUPull.derived.obj H, o.gPull.derived.obj N)) ∧
  (∀ (F V : ProjectionRestriction.Der (restrictRing m d.j' d.S)),
    v.rho.app (o.tensorU'.functor.obj (F, V)) ≫
        v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorS.tensorComparison.comparison.hom.app (F, V)) =
      o.tensorU'.functor.map (Prod.mkHom (v.rho.app F) (𝟙 V)) ≫
        v.tensorS.delta.hom.app
          ((OpenTensorNormalization.restrict m s
            (restrictRing m d.j' d.S)).mapDerivedCategory.obj F, V)) ∧
  (∀ (M : ProjectionRestriction.Der (restrictRing m s (restrictRing m d.j' d.S)))
      (N : ProjectionRestriction.Der d.S),
    v.tensorB.delta.hom.app (v.extensionS.ordinary.mapDerivedCategory.obj M, N) ≫
        o.opens.jShriek'.map (v.tensorS.delta.hom.app (M, o.opens.jStar'.obj N)) =
      v.deltaK.hom.app (M, N)) ∧
  (∀ (H : ProjectionRestriction.Der (restrictRing m d.j d.R)) (N : ProjectionRestriction.Der d.R),
    o.gPull.derived.map (a.gamma.hom.app (H, N)) ≫
        alpha a v (o.tensorU.functor.obj (H, o.opens.jStar.obj N)) ≫
        o.opens.jShriek'.map (v.extensionS.ordinary.mapDerivedCategory.map
          ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
            (v.tensorQ.comparison.hom.app (H, o.opens.jStar.obj N)) ≫
          v.tensorS.tensorComparison.comparison.hom.app
            (o.gUPull.derived.obj H, o.gUPull.derived.obj (o.opens.jStar.obj N)))) =
      v.tensorP.comparison.hom.app (o.opens.jShriek.obj H, N) ≫
        o.tensorX'.functor.map (Prod.mkHom (alpha a v H) (𝟙 _)) ≫
        v.deltaK.hom.app
          ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.obj
            (o.gUPull.derived.obj H), o.gPull.derived.obj N) ≫
        o.opens.jShriek'.map (v.extensionS.ordinary.mapDerivedCategory.map
          (v.tensorA.functor.map (Prod.mkHom (𝟙 _)
            ((OpenTensorNormalization.restrict m s (restrictRing m d.j' d.S)).mapDerivedCategory.map
              (o.theta.hom.app N))))))

end SheafOfModules.ClopenComparisonTensorSquare
