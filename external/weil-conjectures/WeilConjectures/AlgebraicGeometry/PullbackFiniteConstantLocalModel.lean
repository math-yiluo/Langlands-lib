/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility

/-! # Pullback of a finite constant local model

the base-changed covering argument.
(auxiliary; not a blueprint node)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def pullback_point_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPoint Y).mapMod Λ ⋙ CondensedRing.upperStar Λ f ≅
      (upperStarFromPoint X).mapMod Λ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapModCompIso (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
        (upperStarFromPointComp f).hom Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
        (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm) ≪≫
    Functor.rightUnitor _

/-- Pulling back the given pro-etale cover preserves its finite constant models.
proof.md,
"Constructible complexes".
(auxiliary; not a blueprint node)

Proof. Choose a witnessing cover U of Y. Its base change U.pullback₂ g covers X.
On its i-th member W = U_i ×_Y X, the two inverse images of M are isomorphic by
upperStarComp and pullback.condition. Pull back the given model on U_i along
W → U_i. The original finitely presented condensed module P_i is unchanged.
The point-pullback composition isomorphism upperStarFromPointComp identifies
pullback of its constant model with the same constant model on W; on modules
this follows from mapModCompIso and extendScalarsIsoComapInv, since the coefficient
comparison is invertible. Compose these isomorphisms to witness the definition.
No nonemptiness of X, Y, a cover member, or a coefficient ring is required. -/
theorem pullback_finiteConstantLocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : HasFiniteConstantLocalModel Λ Y M) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ g).obj M) := by
  obtain ⟨U, hU⟩ := hM
  let V : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    { I₀ := U.I₀
      X := fun i ↦ pullback (U.f i) g
      f := fun i ↦ pullback.snd (U.f i) g
      mem₀ := (U.pullback₂ g).mem₀ }
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hU i
  let q : V.X i ⟶ U.X i := pullback.fst (U.f i) g
  have comm : q ≫ U.f i = V.f i ≫ g := pullback.condition
  refine ⟨P, hP, ⟨?_⟩⟩
  exact ((CondensedRing.upperStarComp Λ (V.f i) g).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M)
      comm.symm) ≪≫
    (CondensedRing.upperStarComp Λ q (U.f i)).app M ≪≫
    (CondensedRing.upperStar Λ q).mapIso e ≪≫
    (pullback_point_iso Λ q).app P

end AlgebraicGeometry.ProEtale
