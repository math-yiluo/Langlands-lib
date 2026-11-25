/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.FiniteCoproductCohomologyAssembly
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Product coordinates for constant-coefficient base change

Source: blueprint theorem-cohomology-curves--6, first step, and Stacks Tag 0A5B,
first paragraph of the proof (finite disjoint unions).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

private noncomputable def cohomologyIsoEquiv {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (q : ℕ) : Sheaf.H F q ≃ Sheaf.H G q where
  toFun := Sheaf.H.map e.hom q
  invFun := Sheaf.H.map e.inv q
  left_inv x := by
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]

private theorem cohomologyMap_congr {X Y : Scheme.{u}} (s t : X ⟶ Y) (h : s = t)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H F q) :
    Sheaf.H.map (eqToHom (congrArg (fun r ↦ (upperStar AddCommGrpCat.{u + 1} r).obj F)
      h)) q (cohomologyMap s F q x) = cohomologyMap t F q x := by
  subst t
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The target product coordinates for finite-coproduct base change commute with
the normalized constant-coefficient restriction maps on the source.
Source: blueprint theorem-cohomology-curves--6, first step; Stacks Tag 0A5B,
first paragraph of the proof, and cohomology functoriality (Tag 01F7).
(blueprint: lem-sc-finite-coproduct-constant-base-change-square)

Proof: Inverse image of the constant Z/n sheaf is canonically the constant Z/n sheaf
on each D i. Normalize each restriction by the cohomology equivalence induced
by that sheaf isomorphism, giving the source restriction maps in the formula.
Base change preserves the disjoint coproduct: coprojections are clopen immersions
whose disjoint images cover C,
and their inverse images have those same properties after base change. Apply
finiteCoproductCohomologyAssembly on the base change of C to its pulled-back
coprojections. The pullback square identifies the restriction of the pulled-back
coefficient sheaf with the pullback of the component constant sheaf, using
upperStarComp and the constant-sheaf isomorphisms. This gives eK. Functoriality
of cohomology pullback for the commuting square, together with naturality in
the coefficient sheaf and coherence of the constant-sheaf identifications,
gives the displayed equality in each coordinate. This proves no bijectivity
of any field-extension comparison: it only diagonalizes the given map.
The empty family gives singleton products on both sides. The construction uses
no invertibility, and includes n=0, n=1 and q=0. -/
theorem finiteCoproductConstantBaseChangeSquare
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {I : Type u} [Finite I] {C : Scheme.{u}} (D : I → Scheme.{u})
    (f : C ⟶ Spec (.of k)) (g : ∀ i, D i ⟶ Spec (.of k))
    (ι : ∀ i, D i ⟶ C) (hw : ∀ i, ι i ≫ f = g i)
    (hc : IsColimit (Cofan.mk C ι)) (n q : ℕ) :
    ∃ eK : Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          (C.constantZMod n)) q ≃
      ∀ i, Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst (g i) (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
            ((D i).constantZMod n)) q,
    ∀ (x : Sheaf.H (C.constantZMod n) q) (i : I),
      eK (cohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (C.constantZMod n) q x) i =
      cohomologyMap
        (pullback.fst (g i) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        ((D i).constantZMod n) q
        (Sheaf.H.map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (ι i)).hom.app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) q
          (cohomologyMap (ι i) (C.constantZMod n) q x)) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst f b
  let pi (i : I) := pullback.fst (g i) b
  let a (i : I) : pullback (g i) b ⟶ pullback f b :=
    pullback.lift (pi i ≫ ι i) (pullback.snd (g i) b) (by
      dsimp [pi]
      rw [Category.assoc, hw i, pullback.condition])
  have ha (i : I) : a i ≫ p = pi i ≫ ι i := by simp [a, p]
  have hpb (i : I) : IsPullback (a i) (pi i) p (ι i) := by
    apply IsPullback.of_right _ (ha i) (IsPullback.of_hasPullback f b).flip
    simpa [a, pi, hw i] using (IsPullback.of_hasPullback (g i) b).flip
  have hcK : Nonempty (IsColimit (Cofan.mk (pullback f b) a)) := by
    apply FinitaryPreExtensive.isUniversal_finiteCoproducts hc
      (Cofan.mk (pullback f b) a) (Discrete.natTrans fun i ↦ pi i.as) p
    · ext i
      exact (ha i.as).symm
    · exact NatTrans.Equifibered.of_discrete _
    · intro i
      exact hpb i.as
  let F := C.constantZMod n
  let e (i : I) :
      (upperStar AddCommGrpCat.{u + 1} (a i)).obj
        ((upperStar AddCommGrpCat.{u + 1} p).obj F) ≅
      (upperStar AddCommGrpCat.{u + 1} (pi i)).obj ((D i).constantZMod n) :=
    ((upperStarComp AddCommGrpCat.{u + 1} (a i) p).app F).symm ≪≫
      eqToIso (congrArg (fun r ↦ (upperStar AddCommGrpCat.{u + 1} r).obj F) (ha i)) ≪≫
      (upperStarComp AddCommGrpCat.{u + 1} (pi i) (ι i)).app F ≪≫
      (upperStar AddCommGrpCat.{u + 1} (pi i)).mapIso
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (ι i)).app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))
  let E := Equiv.ofBijective _
    (finiteCoproductCohomologyAssembly (fun i ↦ pullback (g i) b)
      (pullback f b) a hcK.some ((upperStar AddCommGrpCat.{u + 1} p).obj F) q)
  refine ⟨E.trans (Equiv.piCongrRight fun i ↦ cohomologyIsoEquiv (e i) q), ?_⟩
  intro x i
  change Sheaf.H.map (e i).hom q
    (cohomologyMap (a i) ((upperStar AddCommGrpCat.{u + 1} p).obj F) q
      (cohomologyMap p F q x)) = _
  rw [(cohomologyPullbackFunctorial (a i) p F q).2.1]
  have hcomp := Sheaf.H.map_comp_apply
    ((upperStarComp AddCommGrpCat.{u + 1} (a i) p).hom.app F) (e i).hom
    (cohomologyMap (a i ≫ p) F q x)
  refine hcomp.symm.trans ?_
  simp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, eqToIso.hom, Iso.hom_inv_id_app_assoc]
  rw [Sheaf.H.map_comp_apply]
  rw [cohomologyMap_congr (a i ≫ p) (pi i ≫ ι i) (ha i)]
  rw [Sheaf.H.map_comp_apply,
    ← (cohomologyPullbackFunctorial (pi i) (ι i) F q).2.1]
  exact (cohomologyMap_map (pi i) q
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (ι i)).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))
    (cohomologyMap (ι i) F q x)).symm

end AlgebraicGeometry.Etale
