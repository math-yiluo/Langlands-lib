/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ThickeningSystemsDictionary
import WeilConjectures.AlgebraicGeometry.ThickeningSystemHomTransport

/-! # Morphisms of completions as compatible restriction families

Source: Stacks Project, Remark 088F, equation 0880 and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-completion-hom-dictionary).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The Hom part of the thickening dictionary for two completed coherent modules.
This identifies formal morphisms with compatible restriction families; it makes no
assertion that either kind of morphism lifts to an uncompleted morphism.
Source: Stacks, Remark 088F, equation 0880 and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-completion-hom-dictionary).

Proof:
1. Apply `thickeningSystems_dictionary` with the tensor-pullback adjunctions. It gives
   a restriction functor R, an equivalence Φ, evaluation comparisons r_n and a natural
   comparison ρ between completion and R followed by Φ.
2. Full faithfulness of Φ and conjugation by ρ identify formal Hom with Hom(R G,R F).
   CoherentFormalModule is a full subcategory, so its arrows are precisely the natural
   transformations between the two formalCompletionSystem functors.
3. Conjugating each component by r_n identifies these system arrows with families
   between the actual tensor pullbacks. The transition equation for r_n carries the
   compatibility equation to the one using the dictionary's comparison c'_n.
4. This remains the same family condition for the comparison c_n in the statement.
   For each closed immersion j_n its right adjoint is fully faithful (087T). The
   counit and the pulled-back unit are invertible by the adjunction triangle identities.
   Naturality against the unit shows that any natural automorphism of j_n^* acts
   centrally on maps between its values: conjugate its component on j_{n,*}M by the
   counit to get a natural automorphism of M, and use the unit to identify this with
   its component on j_n^*F. Hence c_n(c'_n)^{-1} commutes with
   every v_n. Cancel it to identify the two compatibility equations.
5. These componentwise operations are inverse bijections, since each r_n is invertible
   and Φ is fully faithful. Naturality of ρ and r_n sends the completion of w to the
   componentwise pullback of w, giving the displayed equation. Empty schemes, zero
   modules and I=0 impose no exception; no completeness or properness is used. -/
theorem thickeningSystems_completion_hom_equiv
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∃ e : (formalCompletionSystem ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) G ⟶
      formalCompletionSystem ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F) ≃
        {v : ∀ n : ℕ,
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ⟶
        (Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1))))))).obj F |
          ∀ n : ℕ, (c n).hom.app G ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F},
      ∀ w : G ⟶ F,
        e (formalCompletionMap ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) w) =
          ⟨fun n ↦ (Scheme.Modules.tensorPullback (pullback.fst f
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map w,
            fun n ↦ ((c n).hom.naturality w).symm⟩ := by
  classical
  let K := ((Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
  let ai := fun n ↦ Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction (i n))
  let aj := fun n ↦ Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction
    (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))))
  obtain ⟨hX, hj, Φ, β, hΦ, hβ, d, R, r, ρ, hd, hr, hρ, hb, hm, rest⟩ :=
    thickeningSystems_dictionary f I i hi hp ai aj
  let : IsNoetherian X := hX
  let F' : CoherentModules X := ⟨F, hF⟩
  let G' : CoherentModules X := ⟨G, hG⟩
  obtain ⟨eR, heR⟩ := thickeningSystem_hom_transport (i := i)
    (fun n ↦ pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))) (fun n ↦ (hj n).1) c d R r hr F' G'
  let b : (R.obj G' ⟶ R.obj F') ≃
      ((completion X K).obj G' ⟶ (completion X K).obj F') :=
    Equiv.ofBijective (fun v ↦ (ρ.hom.app G') ≫ Φ.map v ≫ (ρ.inv.app F')) (hb F' G')
  let q : ((completion X K).obj G' ⟶ (completion X K).obj F') ≃
      (formalCompletionSystem K G ⟶ formalCompletionSystem K F) :=
    { toFun := fun v ↦ v.hom
      invFun := fun v ↦ ObjectProperty.homMk v
      left_inv := fun v ↦ by cases v; rfl
      right_inv := fun v ↦ rfl }
  refine ⟨q.symm.trans (b.symm.trans eR), ?_⟩
  intro w
  have hw : b (R.map (ObjectProperty.homMk w : G' ⟶ F')) =
      (completion X K).map (ObjectProperty.homMk w : G' ⟶ F') := hm F' G' _
  change eR (b.symm (q.symm (formalCompletionMap K w))) = _
  have hq : q.symm (formalCompletionMap K w) =
      (completion X K).map (ObjectProperty.homMk w : G' ⟶ F') := rfl
  rw [hq, ← hw, b.symm_apply_apply]
  exact heR (ObjectProperty.homMk w)

end AlgebraicGeometry
