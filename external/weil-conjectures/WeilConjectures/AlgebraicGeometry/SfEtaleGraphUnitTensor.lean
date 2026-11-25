/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphExchangeTensor

/-! # Tensor identity for the specified compactification graph unit

This is the geometric unit calculation preceding the adjunction calculation of the
etale projection square. Source: the proof of
`lem-sf-etale-graph-projection-arbitrary-base`, steps 2--6; blueprint
`sec-six-functors-basics/sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`, paragraph 3;
Stacks Tag 0GKF.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem transfer_unit_tensor
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {T : C ⥤ C ⥤ C} {T' : D ⥤ D ⥤ D}
    (φ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T')
    (M J : C) (H HJ : D) (t : F.obj M ⟶ H)
    (tJ : F.obj ((T.obj M).obj J) ⟶ HJ)
    (d : (T'.obj H).obj (F.obj J) ⟶ HJ)
    (ht : tJ = (φ.app M).app J ≫ (T'.map t).app (F.obj J) ≫ d) :
    adj.unit.app _ ≫ G.map tJ =
      (T.map (adj.unit.app M ≫ G.map t)).app J ≫
        ((adj.rightAdjointProjectionMap φ).app H).app J ≫ G.map d := by
  rw [ht, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    adj.unit_app_comp_map_rightAdjointProjectionMap, Category.assoc]
  have hn := NatTrans.congr_app ((adj.rightAdjointProjectionMap φ).naturality t) J
  dsimp at hn
  rw [← reassoc_of% hn]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem unit_tensor_assembly
    {C : Type*} [Category* C] (T : C ⥤ C)
    {M U UJ E EJ R RJ Y S : C}
    (u : M ⟶ U) (uJ : T.obj M ⟶ UJ) (a : U ≅ E) (aJ : UJ ≅ EJ)
    (b : U ≅ R) (bJ : UJ ≅ RJ) (μ : T.obj E ⟶ Y) (P : Y ⟶ EJ)
    (π : T.obj R ⟶ S) (d : S ⟶ RJ) (v : M ⟶ R) (vJ : T.obj M ⟶ RJ)
    (hf : u ≫ b.hom = v) (hfJ : uJ ≫ bJ.hom = vJ)
    (ht : vJ = T.map v ≫ π ≫ d)
    (he : μ ≫ P ≫ aJ.inv ≫ bJ.hom = T.map (a.inv ≫ b.hom) ≫ π ≫ d) :
    uJ ≫ aJ.hom = T.map (u ≫ a.hom) ≫ μ ≫ P := by
  apply (cancel_mono (aJ.inv ≫ bJ.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hfJ, ht, he]
  rw [← T.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, hf]

private theorem graph_unit_fac
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] (c : Compactification e)
    (M : DerivedCategoryModule A V) :
    (compactificationEtaleUnit A e c).app M ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (CategoryTheory.IsPullback.of_hasPullback c.g e).toCommSq).app
          (D((c.i)_!open[ModuleCat.{u + 1} A]).obj M) =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (CategoryTheory.Limits.pullback.snd c.g e)).unit.app M ≫
      R((CategoryTheory.Limits.pullback.snd c.g e)_*[ModuleCat.{u + 1} A]).map
        ((compactificationEtaleGraphMap A e c).app M) := by
  simp [compactificationEtaleUnit]

/-- The graph unit respects the specified proper/open projection, in the exact
inverse-image model. This statement concerns the graph unit before transposition;
it neither asserts invertibility nor mentions etale sum extension.

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3, and the accepted
proof of `lem-sf-etale-graph-projection-arbitrary-base`, steps 2--6; Stacks Tag 0GKF
(auxiliary; not a blueprint node).

Proof in words. Write F = Rr_*Dj_!, E = D(e^*), and J = EK. The graph sigma in
Z times_W V is clopen: it is a section of a separated proper morphism, and is an
etale monomorphism. Restriction to the graph and its open complement identifies
derived morphisms with pairs of morphisms, since the clopen sheaf equivalence is
exact and descends degreewise to the unbounded derived categories. Graph transfer
is the pair consisting of the specified restricted morphism and zero.
Consequently transfer commutes with tensor: the transfer t at M tensor J is
the pullback of the open tensor map composed with t_M tensor identity and the
pullback tensor comparison. The normalization on the graph is the open adjunction
unit and the open projection/exchange equation; on the complement both maps vanish.
For Q = Lq^* and R = Rq_*, the counit definition of the projection pi gives
R(tau) pi (eta_M tensor identity) = eta_(M tensor J): transpose under Q adjoint R
and use the triangle identity. Apply R to the transfer tensor equation and use
naturality of pi. Exchange/projection compatibility for (r,q,e,q_Z) then turns
this equation into the displayed identity. Proper exchange is invertible because
A is finite, hence additively torsion; cancel it. Finally insert the canonical
Le^* to D(e^*) comparison in both tensor inputs and the tensor output. Its
naturality and the monoidal composition comparisons give exactly the factors
shown below. This argument also covers the zero ring, empty graph and arbitrary
unbounded complexes; it uses no quasi-compactness of the open immersion. -/
theorem sfEtaleGraphUnitTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] [IsSeparated e] (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    (compactificationEtaleUnit A e c).app
          (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
            (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app _ =
      ((derivedTensor (ModuleCat.{u + 1} A) V).map
        ((compactificationEtaleUnit A e c).app M ≫
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app _)).app
            (D((e)^*[ModuleCat.{u + 1} A]).obj K) ≫
        (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) e
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) K).inv ≫
        D((e)^*[ModuleCat.{u + 1} A]).map
          (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
              (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
                ((leftDerivedUpperStarIsoMapDerivedCategory
                  (ModuleCat.{u + 1} A) e).hom.app K))) := by
  let J := D((e)^*[ModuleCat.{u + 1} A]).obj K
  let MK := ((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj J
  let H := D((c.i)_!open[ModuleCat.{u + 1} A])
  let R := R((CategoryTheory.Limits.pullback.snd c.g e)_*[ModuleCat.{u + 1} A])
  let η := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (CategoryTheory.Limits.pullback.snd c.g e)).unit
  let t := compactificationEtaleGraphMap A e c
  let Ex := asIso (derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (CategoryTheory.IsPullback.of_hasPullback c.g e).toCommSq)
  exact unit_tensor_assembly
    ((CategoryTheory.Functor.flip (derivedTensor (ModuleCat.{u + 1} A) V)).obj J)
    ((compactificationEtaleUnit A e c).app M)
    ((compactificationEtaleUnit A e c).app MK)
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).app _)
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).app _)
    (Ex.app (H.obj M)) (Ex.app (H.obj MK))
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) e
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) K).inv
    (D((e)^*[ModuleCat.{u + 1} A]).map
      (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) e).hom.app K))))
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      (CategoryTheory.Limits.pullback.snd c.g e)).app _).app J)
    (R.map (sfEtaleGraphTensorMap A e c M K))
    (η.app M ≫ R.map (t.app M)) (η.app MK ≫ R.map (t.app MK))
    (graph_unit_fac A e c M) (graph_unit_fac A e c MK)
    (transfer_unit_tensor
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (CategoryTheory.Limits.pullback.snd c.g e))
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A)
        (CategoryTheory.Limits.pullback.snd c.g e))
      M J _ _ (t.app M) (t.app MK) (sfEtaleGraphTensorMap A e c M K)
      (sfEtaleGraphTransferTensor A e c M K))
    (sfEtaleGraphExchangeTensor A e c M K)

end AlgebraicGeometry.Etale
