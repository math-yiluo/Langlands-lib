/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # Descent coherence of the explicit chart tensor-pullback comparisons

Source: Stacks Project, Tags 0095 and 0096, and Mathlib descent naturality. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- There is a unique isomorphism between the pulled canonical descent datum
and the canonical datum of tensor pullback with the prescribed chart maps.
Source: Stacks Project, Tags 0095 and 0096; Mathlib
`DescentData.toDescentDataCompPullFunctorIso` and pseudofunctor composition.
(blueprint: lem-pc-open-cover-tensor-descent-comparison-coherence).

Proof: Compose toDescentDataCompPullFunctorIso with the image, under the
canonical descent functor, of the unique left-adjoint comparison between
ordinary pullback and tensor pullback. This gives an isomorphism between the
two displayed descent data. Its component at a chart x is the inverse of
isoMapOfCommSq for the chart pullback square, followed by restriction of the
left-adjoint comparison. The formula isoMapOfCommSq_eq, followed by
modulesPseudofunctor_mapComp'_hom_app_eq and
modulesPseudofunctor_mapComp'_inv_app_eq, identifies the first factor with
pullbackComp for the chart projection, pullbackCongr for its commutativity
identity, and inverse pullbackComp for q followed by the pulled chart.
The remaining factor is exactly the whiskered left-adjoint comparison in
openCoverTensorPullbackComparison. Thus its hom chart components are the
prescribed ones. Cancel each invertible hom component to obtain the prescribed
inverse components. For uniqueness, two such isomorphisms have equal hom chart
components, hence equal hom morphisms by descent Hom extensionality, and then
are equal by Iso.ext. The specified chart maps determine all data uniquely. The proof
requires no assumptions on q or the modules, and includes empty overlaps and
zero modules. All isomorphism data are specified canonical constructions. -/
theorem openCoverTensorDescentComparison_existsUnique
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (q : Y ⟶ X) (M : X.Modules) :
    let D := (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
      (f := U.f) (f' := fun x ↦ pullback.fst q (U.f x)) (p := q) (α := id)
      (p' := fun x ↦ U.pullbackHom q x) (fun x ↦ U.pullbackHom_map q x)).obj
      ((modulesPseudofunctor.toDescentData U.f).obj M)
    let E := (modulesPseudofunctor.toDescentData
      (fun x ↦ pullback.fst q (U.f x))).obj ((Scheme.Modules.tensorPullback q).obj M)
    ∃! e : D ≅ E, ∀ a : U.I₀,
      e.hom.hom a = (Scheme.Modules.openCoverTensorPullbackComparison q U a).hom.app M ∧
      e.inv.hom a = (Scheme.Modules.openCoverTensorPullbackComparison q U a).inv.app M := by
  classical
  dsimp only
  let T := modulesPseudofunctor.toDescentData (fun x ↦ pullback.fst q (U.f x))
  let c := (Adjunction.leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q))
    (Scheme.Modules.pullbackPushforwardAdjunction q)).symm
  let e := (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    modulesPseudofunctor (f := U.f) (f' := fun x ↦ pullback.fst q (U.f x))
    (p := q) (α := id) (p' := fun x ↦ U.pullbackHom q x)
    (fun x ↦ U.pullbackHom_map q x)).app M ≪≫ T.mapIso (c.app M)
  have he (a : U.I₀) : e.hom.hom a =
      (Scheme.Modules.openCoverTensorPullbackComparison q U a).hom.app M := by
    change (modulesPseudofunctor.isoMapOfCommSq
      (CommSq.mk (U.pullbackHom_map q a)).op.toLoc).inv.toNatTrans.app M ≫
        (Scheme.Modules.pullback ((U.pullback₁ q).f a)).map (c.hom.app M) = _
    have hsq := modulesPseudofunctor.isoMapOfCommSq_eq
      (CommSq.mk (U.pullbackHom_map q a)).op.toLoc
      ((U.pullback₁ q).f a ≫ q).op.toLoc (by rfl)
    rw [hsq]
    simp only [Iso.trans_inv, Iso.symm_inv]
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app]
    rw [modulesPseudofunctor_mapComp'_inv_app_eq (U.f a) (U.pullbackHom q a)
        ((U.pullback₁ q).f a ≫ q) (U.pullbackHom_map q a) M,
      modulesPseudofunctor_mapComp'_hom_app_eq q ((U.pullback₁ q).f a)
        ((U.pullback₁ q).f a ≫ q) rfl M]
    simp only [pullbackCompOfEq, Iso.trans_hom, Iso.trans_inv]
    unfold Scheme.Modules.openCoverTensorPullbackComparison
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
    have hid : ((Scheme.Modules.pullbackCongr
        (rfl : (U.pullback₁ q).f a ≫ q = (U.pullback₁ q).f a ≫ q)).app M).inv = 𝟙 _ := by
      simp [Scheme.Modules.pullbackCongr]
    simp only [hid]
    rfl
  refine ⟨e, fun a ↦ ⟨he a, ?_⟩, ?_⟩
  · have hi := congrArg (fun φ ↦ φ.hom a) e.hom_inv_id
    change e.hom.hom a ≫ e.inv.hom a = 𝟙 _ at hi
    rw [he a] at hi
    apply (cancel_epi ((Scheme.Modules.openCoverTensorPullbackComparison q U a).hom.app M)).mp
    rw [hi]
    exact ((Scheme.Modules.openCoverTensorPullbackComparison q U a).hom_inv_id_app M).symm
  · intro e' he'
    apply Iso.ext
    ext a
    exact (he' a).1.trans (he a).symm

end AlgebraicGeometry
