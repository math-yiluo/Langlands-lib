/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Transport of tensor base change to a specified cartesian square

Source: Stacks Project, Tag 0A1D, displayed cartesian-square comparison.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPullback_iso_equivalence {Y Y' : Scheme.{u}} (i : Y' ≅ Y) :
    (Scheme.Modules.tensorPullback i.hom).IsEquivalence := by
  obtain ⟨c₁⟩ := Scheme.Modules.nonempty_tensorPullbackComp i.inv i.hom
  obtain ⟨c₂⟩ := Scheme.Modules.nonempty_tensorPullbackComp i.hom i.inv
  obtain ⟨u₁⟩ := Scheme.Modules.nonempty_tensorPullbackId Y
  obtain ⟨u₂⟩ := Scheme.Modules.nonempty_tensorPullbackId Y'
  let a := c₁.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback i.inv_hom_id) ≪≫ u₁
  let b := c₂.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback i.hom_inv_id) ≪≫ u₂
  exact (CategoryTheory.Equivalence.mk (Scheme.Modules.tensorPullback i.hom)
    (Scheme.Modules.tensorPullback i.inv) a.symm b).isEquivalence_functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem iso_pullback_computes {Y Y' : Scheme.{u}} (i : Y' ≅ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    Nonempty ((derivedPullback i.hom).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback i.hom).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y'.toRingedSpace) :=
    Scheme.Modules.tensorPullback i.hom
  have : T.IsEquivalence := tensorPullback_iso_equivalence i
  have : T.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨_, _, _, _, _, _, _, F, hF, hFmap, _, ε, hL, _, _⟩ :=
    (derivedPullback_spec i.hom)
  have h : F = T := CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFmap a)
  subst F
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback i.hom).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let compute := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback i.hom) ε
    T.mapDerivedCategoryFactorsh.hom W
  exact ⟨compute.app (DerivedCategory.Q.obj K) ≪≫ T.mapDerivedCategoryFactors.app K⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Tensor base change in a specified cartesian square, with identified tensor factors.
Source: Stacks Project, Tag 0A1D, displayed cartesian square and its isomorphism.
Proof: the cartesian square identifies X' with the canonical pullback of f and p.
Apply relativelyFlat_tensor_baseChange_iso to f, p, E and G. Transport its right side
along this scheme isomorphism, using composition of derived pullbacks and of derived
direct images and the identity comparisons; pushforward along a scheme isomorphism
is inverse to pullback. The given degreewise isomorphisms e commute with differentials,
so define an isomorphism of complexes from the ordinary tensor pullback of G to G'.
Apply DerivedCategory.Q to this complex isomorphism. Tensor it with the given derived
identification of E, and apply the direct-image functor. Composing gives the displayed
isomorphism. Only ordinary pullback is used on G; relative flatness, rather than
O_X-flatness, is exactly the assumption of Tag 0A1D. There are no support, finite
presentation, perfectness or Noetherian assumptions. Empty schemes and zero complexes
are included by the same categorical construction.
(blueprint: lem-pc-cartesian-tensor-data-comparison). -/
theorem cartesian_tensor_data_comparison
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S X' T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (p : T ⟶ S) (g : X' ⟶ X) (f' : X' ⟶ T) (sq : IsPullback g f' f p)
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (G.X n))
    (hGqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (E' : schemeDerivedCategory X')
    (hEE' : Nonempty ((derivedPullback g).obj E ≅ E'))
    (G' : CochainComplex X'.Modules ℤ)
    (e : ∀ n : ℤ, Scheme.Modules.tensorPullbackObj g (G.X n) ≅ G'.X n)
    (he : ∀ n m : ℤ, Scheme.Modules.tensorPullbackMap g (G.d n m) ≫ (e m).hom =
      (e n).hom ≫ G'.d n m) :
    Nonempty ((derivedPullback p).obj
        ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
      (schemeDerivedDirectImage f').obj (E' ⊗ DerivedCategory.Q.obj G')) := by
  classical
  obtain ⟨bc⟩ := relativelyFlat_tensor_baseChange_iso f p E hE G hGb hGqc hGflat
  let i := sq.isoPullback
  obtain ⟨_, _, _, c, _, j, _⟩ := exists_derivedPullbackComposition
  let d₁ := c i.inv i.hom ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) i.inv_hom_id) ≪≫ j (pullback f p)
  let d₂ := c i.hom i.inv ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) i.hom_inv_id) ≪≫ j X'
  let di := CategoryTheory.Equivalence.mk
    (derivedPullback i.hom) (derivedPullback i.inv) d₁.symm d₂
  have : (derivedPullback i.hom).IsEquivalence := di.isEquivalence_functor
  obtain ⟨adj⟩ := nonempty_derivedPullbackAdjunction i.hom
  obtain ⟨m, _⟩ := exists_derivedPullbackMonoidalModel i.hom
  let F := Scheme.Modules.tensorPullback (pullback.fst f p)
  let C := (F.mapHomologicalComplex (.up ℤ)).obj G
  let A := (derivedPullback (pullback.fst f p)).obj E
  let B : schemeDerivedCategory (pullback f p) := DerivedCategory.Q.obj C
  obtain ⟨second⟩ := iso_pullback_computes i C
  obtain ⟨cc⟩ := Scheme.Modules.nonempty_tensorPullbackComp i.hom (pullback.fst f p)
  let complexComp := (Functor.mapHomologicalComplexCompIso cc.symm (.up ℤ)).app G
  let first := (c i.hom (pullback.fst f p)).app E
  let factors := (m.μIso A B).symm ≪≫
    tensorIso first (second ≪≫ DerivedCategory.Q.mapIso complexComp)
  let push := (schemeDerivedDirectImage (pullback.snd f p)).mapIso
    ((asIso adj.unit).app (A ⊗ B))
  obtain ⟨dc⟩ := derivedDirectImageComposition i.hom (pullback.snd f p)
  let transported := push ≪≫
    (dc.app ((derivedPullback i.hom).obj (A ⊗ B))).symm ≪≫
    (schemeDerivedDirectImage (i.hom ≫ pullback.snd f p)).mapIso factors
  have hf : i.hom ≫ pullback.snd f p = f' := sq.isoPullback_hom_snd
  have hg : i.hom ≫ pullback.fst f p = g := sq.isoPullback_hom_fst
  rw [hf, hg] at transported
  let complexIso : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj G ≅
      G' := HomologicalComplex.Hom.isoOfComponents e (fun n m _ ↦ (he n m).symm)
  obtain ⟨ee⟩ := hEE'
  exact ⟨bc ≪≫ transported ≪≫ (schemeDerivedDirectImage f').mapIso
    (tensorIso ee (DerivedCategory.Q.mapIso complexIso))⟩

end AlgebraicGeometry
