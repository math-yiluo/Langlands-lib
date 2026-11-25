/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforward
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

/-- Adjacent compatibility of termwise pushforward identifications assembles to an
isomorphism of inverse systems.  The construction uses `NatTrans.ofOpSequence` and
its componentwise inverse identities.
Source: Stacks, Remark 088F and equation 0880.
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting-assembly). -/
theorem thickeningSystemPushforward_assemble
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (R : CoherentThickeningSystem T i)
    (H : CoherentFormalModule X J)
    (e : ∀ n, ((thickeningSystemPushforward j hi ai).obj R).obj (op n) ≅
      H.obj.obj (op n))
    (he : ∀ n, ((thickeningSystemPushforward j hi ai).obj R).map
        (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ H.obj.map (homOfLE (Nat.le_succ n)).op) :
    Nonempty ((thickeningSystemPushforward j hi ai).obj R ≅ H.obj) := by
  let F := (thickeningSystemPushforward j hi ai).obj R
  let hom : F ⟶ H.obj := NatTrans.ofOpSequence (fun n ↦ (e n).hom) he
  let inv : H.obj ⟶ F := NatTrans.ofOpSequence (fun n ↦ (e n).inv) (by
    intro n
    refine (cancel_mono (e n).hom).mp ?_
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he]
    simp only [Iso.inv_hom_id_assoc])
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply NatTrans.ext
    funext n
    dsimp [hom, inv]
    exact (e n.unop).hom_inv_id
  · apply NatTrans.ext
    funext n
    dsimp [hom, inv]
    exact (e n.unop).inv_hom_id

end
end AlgebraicGeometry
