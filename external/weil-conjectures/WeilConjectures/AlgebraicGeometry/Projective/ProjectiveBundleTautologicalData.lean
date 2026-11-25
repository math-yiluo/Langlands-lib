/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra

/-! # Data for finite locally free projective bundles

The symmetric-algebra realization, its normalized twist, frame charts, and base-change
comparisons.

## Implementation details

These definitions are factored out so their construction lemmas can be proved separately
without an import cycle.

## References

* Stacks Project, Tags 0095, 0096, 01C5, 01MN, 01NR, 01O3, 01OB, 01OE
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback

/-- The unit-normalized comparison from the tensor pullback to Mathlib's pullback of modules,
given by uniqueness of left adjoints. -/
noncomputable def projectiveBundleTensorPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.Modules.tensorPullback g ≅ Scheme.Modules.pullback g :=
  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)

/-- Tensor-pullback identity, transported by the unit-normalized adjoint comparison. -/
noncomputable def projectiveBundlePullbackId (X : Scheme.{u}) :
    Scheme.Modules.tensorPullback (𝟙 X) ≅ 𝟭 X.Modules :=
  projectiveBundleTensorPullbackIso (𝟙 X) ≪≫ Scheme.Modules.pullbackId X

/-- Tensor-pullback composition, using the canonical adjoint comparison. -/
noncomputable def projectiveBundlePullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
  Functor.isoWhiskerRight (projectiveBundleTensorPullbackIso g) (Scheme.Modules.tensorPullback f) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback g) (projectiveBundleTensorPullbackIso f) ≪≫
    Scheme.Modules.pullbackComp f g ≪≫ (projectiveBundleTensorPullbackIso (f ≫ g)).symm

/-- Transport of tensor pullback along equality of the underlying scheme maps. -/
noncomputable def projectiveBundlePullbackCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) : Scheme.Modules.tensorPullback f ≅ Scheme.Modules.tensorPullback g :=
  eqToIso (congrArg Scheme.Modules.tensorPullback h)

/-- The specified tensor-pullback adjunction; its universal property fixes the unit. -/
noncomputable def projectiveBundlePullbackAdjunction {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g :=
  Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)

/-- Pulling back the unit module by tensor product gives the unit module. -/
noncomputable def projectiveBundlePullbackUnitIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Scheme.Modules.tensorPullback g).obj (Scheme.Modules.unit Y) ≅ Scheme.Modules.unit X :=
  (projectiveBundleTensorPullbackIso g).app (Scheme.Modules.unit Y) ≪≫
    Scheme.Modules.pullbackObjUnitIso g

/-- The actual pullback of a section, defined by the tensor-pullback adjunction unit. -/
noncomputable def projectiveBundlePullbackSection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {U : Y.Opens} (m : Γ(M, U)) :
    Γ((Scheme.Modules.tensorPullback g).obj M, g ⁻¹ᵁ U) :=
  ((projectiveBundlePullbackAdjunction g).unit.app M).app U m

attribute [local irreducible] projectiveBundleTensorPullbackIso
  projectiveBundlePullbackId projectiveBundlePullbackComp projectiveBundlePullbackCongr
  projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

namespace Scheme

/-- The symmetric-degree submodule: products of exactly `d` degree-one generators. -/
def symmetricDegree (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (d : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  Submodule.span R {x | ∃ v : Fin d → M,
    x = ∏ i, SymmetricAlgebra.ι R M (v i)}

/-- An actual frame, rather than merely the proposition that one exists. -/
def ModuleFrame (B : Scheme.{u}) (F : B.Modules) (U : B.Opens) (r : ℕ) : Type u :=
  (Modules.tensorPullback U.ι).obj F ≅
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The symmetric algebra presented on the affine basis, with its actual symmetric grading,
algebra structure and canonical restriction maps. -/
structure SymmetricGradedAlgebraData (B : Scheme.{u}) (F : B.Modules) where
  data : B.GradedAlgebraData
  sectionEquiv : ∀ U : B.affineOpens,
    SymmetricAlgebra (B.presheaf.obj (op U.1)) (F.val.obj (op U.1)) ≃ₐ[
      B.presheaf.obj (op U.1)] data.obj U
  sectionEquiv_grade : ∀ (U : B.affineOpens) (d : ℕ) (x : SymmetricAlgebra
      (B.presheaf.obj (op U.1)) (F.val.obj (op U.1))),
    x ∈ symmetricDegree (B.presheaf.obj (op U.1)) (F.val.obj (op U.1)) d ↔
      sectionEquiv U x ∈ data.grading U d
  sectionEquiv_restriction : ∀ {U V : B.affineOpens} (h : U ≤ V) (x :
      SymmetricAlgebra (B.presheaf.obj (op V.1)) (F.val.obj (op V.1))),
    data.res h (sectionEquiv V x) =
      sectionEquiv U (SymmetricAlgebraSheaf.restriction F (homOfLE h).op x)

end Scheme

/-- Transport of the restriction of a global module across nested affine Proj charts. -/
noncomputable def tautologicalTransport
    (B : Scheme.{u}) (A : B.GradedAlgebraData) (L : A.relProj.Modules)
    {U V : B.affineOpens} (h : U ≤ V) :
    (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
        ((Scheme.Modules.tensorPullback (A.relProjι V)).obj L) ≅
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L :=
  (projectiveBundlePullbackComp (A.relProjFunctor.map (homOfLE h))
    (A.relProjι V)).app L ≪≫
    (projectiveBundlePullbackCongr (A.relProjFunctor_map_relProjι (homOfLE h))).app L

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Compatible affine twist charts. The restriction isomorphisms are normalized on every
homogeneous degree-one section, so they are the homogeneous-localization maps. -/
structure TautologicalTwistData (B : Scheme.{u}) (A : B.GradedAlgebraData)
    (L : A.relProj.Modules) where
  chart : ∀ U : B.affineOpens,
    (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅ Proj.twist (A.grading U) 1
  twistRestriction : ∀ {U V : B.affineOpens} (h : U ≤ V),
    (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
        (Proj.twist (A.grading V) 1) ≅ Proj.twist (A.grading U) 1
  restriction_generator : ∀ {U V : B.affineOpens} (h : U ≤ V)
      (x : A.obj V) (hx : x ∈ A.grading V 1),
    (twistRestriction h).hom.app
        ((A.relProjFunctor.map (homOfLE h)) ⁻¹ᵁ ⊤)
        (projectiveBundlePullbackSection (A.relProjFunctor.map (homOfLE h))
          (Scheme.Modules.Hom.app (Proj.unitToTwist hx) ⊤ (1 : Γ(Proj (A.grading V), ⊤)))) =
      Scheme.Modules.Hom.app (Proj.unitToTwist ((A.res h).map_mem hx))
        ((A.relProjFunctor.map (homOfLE h)) ⁻¹ᵁ ⊤)
        (1 : Γ(Proj (A.grading U), (A.relProjFunctor.map (homOfLE h)) ⁻¹ᵁ ⊤))
  chart_overlap : ∀ {U V : B.affineOpens} (h : U ≤ V),
    tautologicalTransport B A L h ≪≫ chart U =
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).mapIso
        (chart V) ≪≫ twistRestriction h

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A projectivization of the actual symmetric algebra with its normalized tautological
quotient and compatible degree-one twist charts. -/
structure ProjectiveBundleRealization (B : Scheme.{u}) (F : B.Modules) where
  A : B.SymmetricGradedAlgebraData F
  L : A.data.relProj.Modules
  quotient : (Scheme.Modules.tensorPullback A.data.relProjHom).obj F ⟶ L
  twists : TautologicalTwistData B A.data L
  quotient_generator : ∀ (U : B.affineOpens) (x : F.val.obj (op U.1))
      (hx : A.sectionEquiv U (SymmetricAlgebra.ι _ _ x) ∈ A.data.grading U 1),
    (twists.chart U).hom.app
        (A.data.relProjι U ⁻¹ᵁ (A.data.relProjHom ⁻¹ᵁ U.1))
        (projectiveBundlePullbackSection (A.data.relProjι U)
          (((projectiveBundlePullbackAdjunction A.data.relProjHom).homEquiv
            F L quotient).app U.1 x)) =
      Scheme.Modules.Hom.app (Proj.unitToTwist hx)
        (A.data.relProjι U ⁻¹ᵁ (A.data.relProjHom ⁻¹ᵁ U.1))
        (1 : Γ(Proj (A.data.grading U),
          A.data.relProjι U ⁻¹ᵁ (A.data.relProjHom ⁻¹ᵁ U.1)))

/-- Transport of a frame vector to the pullback of the module on the inverse-image open.
Naming this morphism keeps the canonical pullback comparisons shared in section formulas. -/
@[no_expose]
noncomputable def projectiveBundleFrameVector
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1))) :
    Scheme.Modules.unit (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ⟶
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F) :=
  (projectiveBundlePullbackUnitIso (D.A.data.relProjHom ∣_ U)).inv ≫
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ∣_ U)).map
      (SheafOfModules.ιFree i ≫ e.inv) ≫
    ((projectiveBundlePullbackComp (D.A.data.relProjHom ∣_ U) U.ι).app F).hom ≫
    (projectiveBundlePullbackCongr (morphismRestrict_ι _ _)).hom.app F ≫
    ((projectiveBundlePullbackComp (D.A.data.relProjHom ⁻¹ᵁ U).ι
      D.A.data.relProjHom).app F).inv

attribute [irreducible] projectiveBundleFrameVector

/-- The quotient section associated to the `i`th vector of a specified frame, on `p⁻¹U`. -/
@[no_expose]
noncomputable def projectiveBundleFrameSection
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (n : ℕ) (U : B.Opens) (e : B.ModuleFrame F U (n + 1)) (i : ULift.{u} (Fin (n + 1))) :
    Scheme.Modules.unit (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ⟶
      (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L :=
  projectiveBundleFrameVector D n U e i ≫
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).map D.quotient

attribute [irreducible] projectiveBundleFrameSection

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The frame determines a chart over `U`, its comparison with the polynomial projective
space, and the twist isomorphism carrying the ordered homogeneous coordinates to that frame. -/
structure ProjectiveBundleFrameChart {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (n : ℕ) (U : B.Opens)
    (e : B.ModuleFrame F U (n + 1)) where
  relativeChart : (D.A.data.relProjHom ⁻¹ᵁ U).toScheme ≅
    RelativeProjectiveSpace.scheme U.toScheme n
  relativeChart_over : relativeChart.hom ≫ RelativeProjectiveSpace.π U.toScheme n =
    D.A.data.relProjHom ∣_ U
  polynomialChart : RelativeProjectiveSpace.scheme U.toScheme n ≅
    ℙ(ULift.{u} (Fin (n + 1)); U.toScheme)
  polynomialChart_over : polynomialChart.hom ≫
    (ℙ(ULift.{u} (Fin (n + 1)); U.toScheme) ↘ U.toScheme) =
      RelativeProjectiveSpace.π U.toScheme n
  twist : (Scheme.Modules.tensorPullback (relativeChart.hom ≫ polynomialChart.hom)).obj
      (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) U.toScheme 1) ≅
    (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
  coordinate : ∀ i : ULift.{u} (Fin (n + 1)),
    (projectiveBundlePullbackUnitIso (relativeChart.hom ≫ polynomialChart.hom)).inv ≫
      (Scheme.Modules.tensorPullback (relativeChart.hom ≫ polynomialChart.hom)).map
        (ProjectiveSpace.coordinateSection (ULift.{u} (Fin (n + 1))) U.toScheme i) ≫
      twist.hom = projectiveBundleFrameSection D n U e i

  generator : ∀ i : ULift.{u} (Fin (n + 1)),
    let φ := relativeChart.hom ≫ polynomialChart.hom
    let M := (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
    let W := φ ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) U.toScheme i
    Scheme.Modules.IsFreeGenerator
      (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (Scheme.Modules.Hom.app (projectiveBundleFrameSection D n U e i) ⊤
          (1 : Γ((D.A.data.relProjHom ⁻¹ᵁ U).toScheme, ⊤))))
  transition : ∀ i j : ULift.{u} (Fin (n + 1)),
    let φ := relativeChart.hom ≫ polynomialChart.hom
    let M := (Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).obj D.L
    let W := φ ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) U.toScheme j
    M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (Scheme.Modules.Hom.app (projectiveBundleFrameSection D n U e i) ⊤
          (1 : Γ((D.A.data.relProjHom ⁻¹ᵁ U).toScheme, ⊤))) =
      φ.app (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) U.toScheme j)
          (ProjectiveSpace.coordRatio (ULift.{u} (Fin (n + 1))) U.toScheme j i) •
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
          (Scheme.Modules.Hom.app (projectiveBundleFrameSection D n U e j) ⊤
            (1 : Γ((D.A.data.relProjHom ⁻¹ᵁ U).toScheme, ⊤)))

/-- The universal quotient square defining the degree-one Stacks base-change theta.
Naming this equation prevents repeated expansion in the dependent record projections. -/
def projectiveBundleThetaQuotientLaw
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (r : D'.A.data.relProj ⟶ D.A.data.relProj)
    (h : r ≫ D.A.data.relProjHom = D'.A.data.relProjHom ≫ g)
    (θ : (Scheme.Modules.tensorPullback r).obj D.L ≅ D'.L) : Prop :=
  (Scheme.Modules.tensorPullback r).map D.quotient ≫ θ.hom =
    ((projectiveBundlePullbackComp r D.A.data.relProjHom).app F).hom ≫
    (projectiveBundlePullbackCongr h).hom.app F ≫
    ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
    (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The canonical base-change comparison. Its coefficient maps are fixed on degree-one
vectors, and its actual theta is fixed by the universal quotient square (the degree-one
part of Stacks 01O3). No arbitrary invertible module is introduced. -/
structure ProjectiveBundleBaseChangeDatum
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F) where
  comparison : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data
  generator : ∀ {U : B.affineOpens} {U' : B'.affineOpens}
      (h : U'.1 ≤ g ⁻¹ᵁ U.1) (x : F.val.obj (op U.1)),
    comparison.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
      D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
        (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
          (projectiveBundlePullbackSection g x))))
  map : D'.A.data.relProj ⟶ D.A.data.relProj
  map_eq : map = comparison.relProjComparison
  over : map ≫ D.A.data.relProjHom = D'.A.data.relProjHom ≫ g
  theta : (Scheme.Modules.tensorPullback map).obj D.L ≅ D'.L
  theta_quotient : projectiveBundleThetaQuotientLaw D D' g e map over theta

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The existing fixed-rank predicate, with the base explicit to avoid re-inferring the
site and its sheafification instances at every dependent occurrence. This is only an alias. -/
def projectiveBundleRank (B : Scheme.{u}) (n : ℕ) (F : B.Modules) : Prop :=
  F.IsFiniteLocallyFreeOfRank (n + 1)

end AlgebraicGeometry
