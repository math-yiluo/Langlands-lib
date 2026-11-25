/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.PerfectHomStageColimit
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh

/-! # Representing the stage pullback Hom functors on the original scheme

Source: Stacks Project, Tags 079W, 0D5S and 09RE.
(blueprint: lem-pc-perfect-hom-push-pull-cocone).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
  {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
  [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- A representable stage Hom cocone, natural in the testing object. Naturality in
all testing objects is essential: it pins the representing maps by Yoneda, including
what their open restrictions do. This is data about derived objects, not triangles
or colimits of groups.
Source: Stacks Project, Tags 079W and 0D5S.
(blueprint: lem-pc-perfect-hom-push-pull-cocone). -/
structure PerfectHomPushPullData (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F) where
  stageQCoh : ∀ j, schemeDerivedQCohProperty Y (F.obj j)
  limitQCoh : schemeDerivedQCohProperty Y d.pt
  stageEquiv : ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y), (M ⟶ F.obj j) ≃
    ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
     (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q)
  limitEquiv : ∀ M : schemeDerivedCategory Y, (M ⟶ d.pt) ≃
    ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj M ⟶
     (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)
  stageNatural : ∀ (j : Set.Ici i) (M N : schemeDerivedCategory Y)
    (g : M ⟶ N) (f : N ⟶ F.obj j),
    stageEquiv j M (g ≫ f) =
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).map g ≫
        stageEquiv j N f
  limitNatural : ∀ (M N : schemeDerivedCategory Y) (g : M ⟶ N) (f : N ⟶ d.pt),
    limitEquiv M (g ≫ f) =
      (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).map g ≫ limitEquiv N f
  stageMap : ∀ (j k : Set.Ici i) (hjk : j ≤ k) (M : schemeDerivedCategory Y)
    (f : M ⟶ F.obj j),
    stageEquiv k M (f ≫ F.map (homOfLE hjk)) =
      perfectStageMap R s j.property hjk (stageEquiv j M f)
  limitMap : ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
    limitEquiv M (f ≫ d.ι.app j) =
      perfectLimitMap R c s j.property (stageEquiv j M f)

private theorem transport_natural {X S : Scheme.{u}} (q : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {M N K : schemeDerivedCategory X}
    (a : M ⟶ N)
    (f : (derivedPullback (pullback.fst q T.hom)).obj N ⟶
      (derivedPullback (pullback.fst q T.hom)).obj K) :
    perfectHomMap q g ((derivedPullback (pullback.fst q T.hom)).map a ≫ f) =
      (derivedPullback (pullback.fst q T'.hom)).map a ≫ perfectHomMap q g f := by
  unfold perfectHomMap
  rw [CategoryTheory.Functor.map_comp]
  have hn := (perfectHomComparison q g).hom.naturality a
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc ((perfectHomComparison q g).hom.app M), ← hn]
  simp only [Category.assoc]

private theorem stage_natural (j k : Set.Ici i) (hjk : j ≤ k)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj N ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q) :
    perfectStageMap R s j.property hjk
      ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).map g ≫ f) =
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE k.property))))).map g ≫
      perfectStageMap R s j.property hjk f := by
  unfold perfectStageMap
  exact transport_natural s
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (Spec.map (R.map (homOfLE k.property)))) _ g f

private theorem limit_natural (j : Set.Ici i)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj N ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q) :
    perfectLimitMap R c s j.property
      ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).map g ≫ f) =
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).map g ≫
      perfectLimitMap R c s j.property f := by
  unfold perfectLimitMap
  exact transport_natural s
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (Spec.map (c.ι.app i))) _ g f

private theorem stage_identity (j : Set.Ici i) (M Q : schemeDerivedCategory Y)
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q) :
    perfectStageMap R s j.property le_rfl f = f := by
  obtain ⟨H, d, _, e, ht⟩ := perfect_hom_stage_colimit R i Y s M Q
  have hh := ht j j le_rfl ((e j).symm f)
  have hid : (homOfLE (le_refl j) : j ⟶ j) = 𝟙 j := rfl
  rw [hid, H.map_id] at hh
  simpa using hh.symm

private theorem stage_composition (j k l : Set.Ici i) (hjk : j ≤ k) (hkl : k ≤ l)
    {M Q : schemeDerivedCategory Y}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj M ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q) :
    perfectStageMap R s k.property hkl (perfectStageMap R s j.property hjk f) =
      perfectStageMap R s j.property (hjk.trans hkl) f := by
  unfold perfectStageMap
  rw [perfectHomMap_trans]
  congr 1
  ext
  change Spec.map (R.map (homOfLE hkl)) ≫ Spec.map (R.map (homOfLE hjk)) =
    Spec.map (R.map (homOfLE (hjk.trans hkl)))
  rw [← Spec.map_comp, ← R.map_comp]
  rfl

/-- The stage pullback Hom functors admit a coherent representing cocone of
quasi-coherent derived objects on Y. No Mayer--Vietoris triangles, cover, perfect
source object, or group-colimit comparisons are asserted.

Source: Stacks Project, Tags 079W, 0D5S and 09RE.
(blueprint: lem-pc-perfect-hom-push-pull-cocone).

Proof: Write pi_j for the projection of Y_j = Y x Spec(R_j) to Y, and pi_inf
for the limit projection. Represent Hom(Lpi_j* M,Lpi_j* Q) by
Rpi_j* Lpi_j* Q, using the derived pullback/direct-image adjunction of Tag 079W.
Use its Hom equivalence for every M; its left naturality gives stageNatural.
For j <= k, transport on these Hom functors is perfectStageMap, which is natural
in M by the naturality of the counit-pinned pullback composition comparison.
Conjugate transport by the adjunction equivalences to obtain a natural map
mu_M : Hom(M,B_j) -> Hom(M,B_k). Evaluate mu at M = B_j and id to define the
representing arrow. Naturality with respect to f : M -> B_j says
f followed by this arrow equals mu_M(f); this is the elementary Yoneda argument.
The identity law is read from perfect_hom_stage_colimit at the identity arrow.
The composition law follows from perfectHomMap_trans. Applying the injective
adjunction equivalence proves both functor laws. Construct the cocone legs by the
same evaluation at id, now using perfectLimitMap. Its stage compatibility proves
the cocone laws. These evaluation identities give stageMap and limitMap.
Perfectness of Q implies quasi-coherent cohomology. Derived pullback preserves it,
and the projections are affine, hence qcqs, so their derived direct images also
have quasi-coherent cohomology. This gives stageQCoh and limitQCoh. No finiteness,
directedness or ring-colimit witness is needed. The objects are constructed as
these specific derived direct images; no arbitrary existence witness is selected.
The argument also works for Q = 0 and empty Y. -/
theorem perfect_hom_pushPull_cocone
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (Q : schemeDerivedCategory Y) (hQ : Y.IsPerfect Q) :
    ∃ (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F),
      Nonempty (PerfectHomPushPullData R c s Q F d) := by
  classical
  let π (j : Set.Ici i) := pullback.fst s (Spec.map (R.map (homOfLE j.property)))
  let piLimit := pullback.fst s (Spec.map (c.ι.app i))
  let L (j : Set.Ici i) := derivedPullback (π j)
  let pullLimit := derivedPullback piLimit
  let B (j : Set.Ici i) := (schemeDerivedDirectImage (π j)).obj ((L j).obj Q)
  let objLimit := (schemeDerivedDirectImage piLimit).obj (pullLimit.obj Q)
  let adj (j : Set.Ici i) := Classical.choice (nonempty_derivedPullbackAdjunction (π j))
  let adjLimit := Classical.choice (nonempty_derivedPullbackAdjunction piLimit)
  let e (j : Set.Ici i) (M : schemeDerivedCategory Y) :=
    (adj j |>.homEquiv M ((L j).obj Q)).symm
  let b (M : schemeDerivedCategory Y) := (adjLimit.homEquiv M (pullLimit.obj Q)).symm
  have en (j : Set.Ici i) (M N : schemeDerivedCategory Y) (g : M ⟶ N) (f : N ⟶ B j) :
      e j M (g ≫ f) = (L j).map g ≫ e j N f :=
    (adj j).homEquiv_naturality_left_symm g f
  have bn (M N : schemeDerivedCategory Y) (g : M ⟶ N) (f : N ⟶ objLimit) :
      b M (g ≫ f) = pullLimit.map g ≫ b N f :=
    adjLimit.homEquiv_naturality_left_symm g f
  let μ (j k : Set.Ici i) (hjk : j ≤ k) (M : schemeDerivedCategory Y)
      (f : M ⟶ B j) : M ⟶ B k :=
    (e k M).symm (perfectStageMap R s j.property hjk (e j M f))
  let ν (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ B j) : M ⟶ objLimit :=
    (b M).symm (perfectLimitMap R c s j.property (e j M f))
  have μn (j k : Set.Ici i) (hjk : j ≤ k) (M N : schemeDerivedCategory Y)
      (g : M ⟶ N) (f : N ⟶ B j) : μ j k hjk M (g ≫ f) = g ≫ μ j k hjk N f := by
    apply (e k M).injective
    simp only [μ, Equiv.apply_symm_apply, en]
    exact stage_natural R s j k hjk g (e j N f)
  have νn (j : Set.Ici i) (M N : schemeDerivedCategory Y)
      (g : M ⟶ N) (f : N ⟶ B j) : ν j M (g ≫ f) = g ≫ ν j N f := by
    apply (b M).injective
    simp only [ν, Equiv.apply_symm_apply, en, bn]
    exact limit_natural R c s j g (e j N f)
  have μspec (j k : Set.Ici i) (hjk : j ≤ k) (M : schemeDerivedCategory Y)
      (f : M ⟶ B j) :
      e k M (f ≫ μ j k hjk (B j) (𝟙 _)) =
        perfectStageMap R s j.property hjk (e j M f) := by
    rw [← μn, Category.comp_id]
    exact (e k M).apply_symm_apply _
  have νspec (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ B j) :
      b M (f ≫ ν j (B j) (𝟙 _)) = perfectLimitMap R c s j.property (e j M f) := by
    rw [← νn, Category.comp_id]
    exact (b M).apply_symm_apply _
  let F : Set.Ici i ⥤ schemeDerivedCategory Y :=
    { obj := B
      map := fun {j k} f ↦ μ j k (leOfHom f) (B j) (𝟙 _)
      map_id := by
        intro j
        apply (e j (B j)).injective
        change e j (B j) (μ j j le_rfl (B j) (𝟙 _)) = e j (B j) (𝟙 _)
        exact (e j (B j)).apply_symm_apply _ |>.trans
          (stage_identity R s j (B j) Q (e j (B j) (𝟙 _)))
      map_comp := by
        intro j k l f g
        apply (e l (B j)).injective
        change e l (B j) (μ j l _ (B j) (𝟙 _)) =
          e l (B j) (μ j k _ (B j) (𝟙 _) ≫ μ k l _ (B k) (𝟙 _))
        rw [μspec]
        simp only [μ, Equiv.apply_symm_apply]
        exact (stage_composition R s j k l (leOfHom f) (leOfHom g)
          (e j (B j) (𝟙 _))).symm }
  let d : Cocone F :=
    { pt := objLimit
      ι :=
        { app j := ν j (B j) (𝟙 _)
          naturality := by
            intro j k f
            change μ j k (leOfHom f) (B j) (𝟙 _) ≫ ν k (B k) (𝟙 _) =
              ν j (B j) (𝟙 _) ≫ 𝟙 _
            rw [Category.comp_id]
            apply (b (B j)).injective
            rw [νspec]
            simp only [μ, ν, Equiv.apply_symm_apply]
            exact perfectLimitMap_stage R c s j.property (leOfHom f)
              (e j (B j) (𝟙 _)) } }
  have hQQ := schemeDerivedQCohProperty_of_isPerfect Y Q hQ
  refine ⟨F, d, ⟨{
    stageQCoh := ?_
    limitQCoh := ?_
    stageEquiv := e
    limitEquiv := b
    stageNatural := en
    limitNatural := bn
    stageMap := ?_
    limitMap := ?_ }⟩⟩
  · intro j
    exact schemeDerivedDirectImage_preserves_QCoh (π j) _
      ((derivedPullback_tensor_preserve_QCoh (π j)).1 Q hQQ)
  · exact schemeDerivedDirectImage_preserves_QCoh piLimit _
      ((derivedPullback_tensor_preserve_QCoh piLimit).1 Q hQQ)
  · intro j k hjk M f
    exact μspec j k hjk M f
  · intro j M f
    exact νspec j M f

end AlgebraicGeometry
