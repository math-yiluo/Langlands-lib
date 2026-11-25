/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.DerivedHomPushforwardKFlatModel
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology

/-! # Closed-immersion self-Ext on fixed resolution representatives

Source: Stacks Project, Tags 08DH, 08I3, 06YS, 079P and 08KS.
(blueprint: lem-pc-self-ext-pushforward-homology). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The self-Ext sheaf is the pushforward of the Hom-complex homology, for any
K-flat resolution of the pushed-forward structure sheaf and any K-injective
resolution of the structure sheaf on the closed subscheme.

Source: Stacks Project, cohomology.tex, Tags 08DH and 08I3; modules.tex,
Tag 08KS; Tags 06YS and 079P for the resolution representatives.
(blueprint: lem-pc-self-ext-pushforward-homology).

Proof: Work first in standard derived localizations on Z and Y. The augmentation a
identifies Q(P) with B[0]. The K-flat representative comparison for derived pullback
identifies Li*(B[0]) with Q(T), where T is the termwise tensor pullback of P. The
augmentation b identifies Q(J) with O_Z[0]. Closed-immersion direct image is exact:
forget to abelian sheaves, identify Z with the closed image in Y, apply exactness of
closed-subset pushforward, and use reflection of exactness by the forgetful functor.
Consequently Ri*(O_Z[0]) is B[0], and homology of Ri* is ordinary pushforward of
homology. Apply the internal-Hom pullback adjunction to B[0] and O_Z[0], obtaining
RHom_Y(B[0],B[0]) isomorphic to Ri*RHom_Z(Li*(B[0]),O_Z[0]). Use the representative
isomorphisms and the K-injectivity of J to identify the latter internal Hom with
Q(Hom(T,J)). Apply degree-k homology and the exact-pushforward comparison. Finally
transport through the localization equivalence on Y to the supplied universe w;
the localization comparisons for internal Hom and homology identify precisely the
objects below. No derived-category choice on Z is required in the final statement.
For the identity immersion this is the ordinary resolution computation; zero objects
and empty schemes are covered by the same functorial isomorphisms. -/
theorem nonempty_selfExt_pushforward_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
      (SheafOfModules.unit Z.ringCatSheaf) ⟶ J)
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (hb : QuasiIso b) (hJ : J.IsKInjective) (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj
        (H.obj (op (S.obj B), S.obj B))) ≅
      (Scheme.Modules.pushforward i).obj ((homComplex (R := Z.sheaf) T J).homology k))
    := by
  let Q := DerivedCategory.Q (C :=
    SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let F := Scheme.Modules.pushforward i
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let B := F.obj (SheafOfModules.unit Z.ringCatSheaf)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
  let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  let C : CochainComplex Z.Modules ℤ := homComplex (R := Z.sheaf) T J
  let : F.PreservesHomology := closed_modulePushforward_preservesHomology i
  let : QuasiIso a := hP.1
  let : QuasiIso b := hb
  have ha : IsIso (Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) a).2 inferInstance
  have hf : IsIso (Q.map (Fc.map b)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (Fc.map b)).2 inferInstance
  let ea : Q.obj P ≅ S.obj B := asIso (Q.map a)
  let eb : S.obj B ≅ Q.obj (Fc.obj J) :=
    (Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app
        (SheafOfModules.unit Z.ringCatSheaf))).symm ≪≫
      asIso (Q.map (Fc.map b))
  obtain ⟨e⟩ := nonempty_derivedHom_pushforward_kFlat_model i P J hP.2 hJ
  let h := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k
  exact ⟨h.mapIso (H.mapIso (ea.op.prod eb) ≪≫ e) ≪≫
    (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).app
      (Fc.obj (homComplex (R := Z.sheaf) T J)) ≪≫
    (C.sc k).mapHomologyIso F⟩

end AlgebraicGeometry
