/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSubsheafSupportOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Geometric stalks of the open support of a subterminal étale sheaf -/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The open support of a subterminal étale sheaf is detected by geometric stalks.
Source: Stacks Project, Étale Cohomology, Tag 04HV, lemma-support-subsheaf-final.
(blueprint: lem-weil-pbc-etale-subsheaf-final-open-parts-stalk)

Proof: An element of the stalk is represented by a section on a pointed étale neighbourhood.
The factorization property puts the image point in W. Conversely, if the point belongs to
W, the geometric morphism lifts through the open immersion W → S. This makes W a pointed
étale neighbourhood. The identity factorization of W gives its unique section, whose image
in the stalk proves nonemptiness. The factorization hypothesis already makes every
inhabited section set a singleton: a section rules out the emptiness alternative, hence
implies factorization and uniqueness. Any two stalk elements have representatives on a
common pointed neighbourhood, where they agree by this uniqueness. Therefore a nonempty
stalk is a singleton; the converse follows
from its distinguished element. -/
theorem etale_subsheaf_final_stalk_criterion (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] (W : S.Opens)
    (hW : etaleSubsheafFactorization S H W) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
      (x default ∈ W ↔ Nonempty ((pointSmallEtale x).sheafFiber.obj H)) ∧
      (Nonempty ((pointSmallEtale x).sheafFiber.obj H) ↔
        Nonempty (Unique ((pointSmallEtale x).sheafFiber.obj H))) := by
  classical
  intro Ω _ _ x
  have hsections (U : S.Etale) (z : H.obj.obj (op U)) :
      Nonempty (Unique (H.obj.obj (op U))) := by
    apply (hW U).1.mpr
    by_contra hn
    exact ((hW U).2 hn).false z
  have hsub : Subsingleton ((pointSmallEtale x).sheafFiber.obj H) := by
    constructor
    intro a b
    obtain ⟨U, y, za, zb, ha, hb⟩ :=
      (pointSmallEtale x).toPresheafFiber_jointly_surjective₂ (P := H.obj) a b
    obtain ⟨hU⟩ := hsections U za
    have hz : za = zb := (hU.uniq za).trans (hU.uniq zb).symm
    exact ha.symm.trans ((congrArg _ hz).trans hb)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hx
    have hrange : Set.range x ⊆ Set.range W.ι := by
      rw [W.range_ι]
      rintro _ ⟨a, rfl⟩
      have ha : a = default := Subsingleton.elim _ _
      subst a
      exact hx
    let l := IsOpenImmersion.lift W.ι x hrange
    have hl : l ≫ W.ι = x := IsOpenImmersion.lift_fac W.ι x hrange
    let U : S.Etale := Etale.mk W.ι
    obtain ⟨hU⟩ := (hW U).1.mpr ⟨𝟙 _, by simp [U]⟩
    exact ⟨(pointSmallEtale x).toPresheafFiber U (Over.homMk l hl) H.obj hU.default⟩
  · rintro ⟨a⟩
    obtain ⟨U, y, z, _⟩ := (pointSmallEtale x).toPresheafFiber_jointly_surjective (P := H.obj) a
    obtain ⟨f, hf⟩ := (hW U).1.mp (hsections U z)
    have hcomp : y.left ≫ U.hom = x := Over.w y
    have hpoint : W.ι (f (y.left (default : Spec (.of Ω)))) = x default := by
      calc
        W.ι (f (y.left (default : Spec (.of Ω)))) =
            (y.left ≫ f ≫ W.ι) (default : Spec (.of Ω)) := rfl
        _ = x default := congrArg (fun g : Spec (.of Ω) ⟶ S ↦ g default) (by
          rw [hf]
          exact hcomp)
    rw [← hpoint]
    exact (f (y.left (default : Spec (.of Ω)))).property
  · constructor
    · rintro ⟨a⟩
      exact ⟨{ default := a, uniq := fun b ↦ hsub.elim b a }⟩
    · rintro ⟨h⟩
      exact ⟨h.default⟩

end AlgebraicGeometry.Scheme
