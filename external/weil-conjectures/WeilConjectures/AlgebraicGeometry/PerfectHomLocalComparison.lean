/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityOn
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Recognition of local filtered Hom comparisons

Source: Stacks Project, Tag 09RE, the local continuity step in the
Mayer--Vietoris argument. (blueprint: lem-pc-perfect-hom-local-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable {I : Type u} [Preorder I]
  (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
  (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
  [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- A map presented by the filtered Hom comparison on an open. All data are
existential, and the two equivalences and transition equation pin the comparison;
this predicate asserts neither injectivity nor surjectivity.
Source: Stacks Project, Tag 09RE.
(blueprint: def-pc-perfect-hom-local-comparison). -/
def PerfectHomLocalComparison (W : X.Opens)
    {α β : Type (max u w)} (m : α → β) : Prop :=
  ∃ (Y : Scheme.{u}) (t : Y ⟶ X) (_ : IsOpenImmersion t),
    t.opensRange = W ∧
    ∃ (s : Y ⟶ Spec (R.obj i)), s = t ≫ s₀ ∧
    ∃ (_ : LocallyOfFinitePresentation s) (_ : QuasiCompact s) (_ : QuasiSeparated s)
      (_ : ∀ T : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over T)))
      (P Q : schemeDerivedCategory Y), Y.IsPerfect P ∧ Y.IsPerfect Q ∧
    ∃ (H : Set.Ici i ⥤ Type (max u w)) (d : Cocone H) (_ : IsColimit d)
      (ident : ∀ j : Set.Ici i, H.obj j ≃
        ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj P ⟶
         (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.property))))).obj Q)),
      (∀ (j k : Set.Ici i) (hjk : j ≤ k) (f : H.obj j),
        ident k (H.map (homOfLE hjk) f) =
          perfectStageMap R s j.property hjk (ident j f)) ∧
      ∃ (a : α ≃ d.pt)
        (b : β ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        ∀ (j : Set.Ici i) (f : H.obj j),
          b (m (a.symm (d.ι.app j f))) = perfectLimitMap R c s j.property (ident j f)

/-- Finite products of local comparisons, transported through equivalences.
In a Mayer--Vietoris row the two-open terms use `prod`, while the intersection
terms use `basic`. Empty opens and zero groups need no additional constructor.
Source: Stacks Project, Tag 09RE.
(blueprint: def-pc-perfect-hom-local-map). -/
inductive PerfectHomLocalMap (U V : X.Opens) :
    {α β : Type (max u w)} → (α → β) → Prop
  | basic {α β : Type (max u w)} {m : α → β} (W : X.Opens)
      (hW : W = U ∨ W = V ∨ W = U ⊓ V)
      (h : PerfectHomLocalComparison R c i X s₀ W m) :
      PerfectHomLocalMap U V m
  | prod {α β γ δ : Type (max u w)} {m : α → β} {n : γ → δ}
      (hm : PerfectHomLocalMap U V m) (hn : PerfectHomLocalMap U V n) :
      PerfectHomLocalMap U V (fun x : α × γ ↦ (m x.1, n x.2))
  | equiv {α β γ δ : Type (max u w)} {m : α → β}
      (hm : PerfectHomLocalMap U V m) (a : γ ≃ α) (b : β ≃ δ) :
      PerfectHomLocalMap U V (fun x ↦ b (m (a x)))

private theorem local_bijective [IsDirected I (· ≤ ·)] (W : X.Opens)
    {α β : Type (max u w)} (m : α → β)
    (hm : PerfectHomLocalComparison R c i X s₀ W m)
    (hcont : PerfectHomContinuityOn R c i X s₀ W) : Function.Bijective m := by
  obtain ⟨Y, t, htI, ht, s, hs, hsL, hsC, hsQ, hD, P, Q, hP, hQ,
    H, d, hd, ident, htrans, a, b, hpin⟩ := hm
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  obtain ⟨hsurj, hinj⟩ := hcont Y t ht s hs P Q hP hQ
  constructor
  · intro x y hxy
    obtain ⟨j, f, hf⟩ := Types.jointly_surjective_of_isColimit hd (a x)
    obtain ⟨k, g, hg⟩ := Types.jointly_surjective_of_isColimit hd (a y)
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    let f' := H.map (homOfLE hjl) f
    let g' := H.map (homOfLE hkl) g
    have hf' : d.ι.app l f' = a x :=
      (ConcreteCategory.congr_hom (d.w (homOfLE hjl)) f).trans hf
    have hg' : d.ι.app l g' = a y :=
      (ConcreteCategory.congr_hom (d.w (homOfLE hkl)) g).trans hg
    have hp : perfectLimitMap R c s l.property (ident l f') =
        perfectLimitMap R c s l.property (ident l g') := by
      rw [← hpin, ← hpin, hf', hg', Equiv.symm_apply_apply, Equiv.symm_apply_apply, hxy]
    obtain ⟨n, hln, hn⟩ := hinj l.val l.property (ident l f') (ident l g') hp
    let n' : Set.Ici i := ⟨n, l.property.trans hln⟩
    have he : H.map (homOfLE hln : l ⟶ n') f' =
        H.map (homOfLE hln : l ⟶ n') g' := by
      apply (ident n').injective
      simpa only [htrans] using hn n le_rfl
    apply a.injective
    rw [← hf', ← hg']
    calc
      d.ι.app l f' = d.ι.app n' (H.map (homOfLE hln) f') :=
        (ConcreteCategory.congr_hom (d.w (homOfLE hln)) f').symm
      _ = d.ι.app n' (H.map (homOfLE hln) g') := congrArg (d.ι.app n') he
      _ = d.ι.app l g' := ConcreteCategory.congr_hom (d.w (homOfLE hln)) g'
  · intro y
    obtain ⟨j, hij, f, hf⟩ := hsurj i le_rfl (b y)
    let j' : Set.Ici i := ⟨j, hij⟩
    refine ⟨a.symm (d.ι.app j' ((ident j').symm f)), b.injective ?_⟩
    simpa only [hpin, Equiv.apply_symm_apply] using hf

/-- Open-local continuity makes every finite product of pinned local filtered Hom
comparisons bijective.

Source: Stacks Project, Tag 09RE, Mayer--Vietoris induction step.
(blueprint: lem-pc-perfect-hom-local-comparison).

Proof: For one comparison, every element of the source colimit has a stage
representative. Move two representatives to a common stage. If their limit images
agree, the eventual equality clause of continuity makes them equal at a later
stage, hence equal in the colimit. The representative clause gives surjectivity.
The two pinning equivalences transport this bijection to the given map. Products
of bijections and conjugation by equivalences preserve bijectivity. -/
theorem PerfectHomLocalMap.bijective [IsDirected I (· ≤ ·)] (U V : X.Opens)
    {α β : Type (max u w)} {m : α → β}
    (hm : PerfectHomLocalMap R c i X s₀ U V m)
    (hU : PerfectHomContinuityOn R c i X s₀ U)
    (hV : PerfectHomContinuityOn R c i X s₀ V)
    (hUV : PerfectHomContinuityOn R c i X s₀ (U ⊓ V)) : Function.Bijective m := by
  induction hm with
  | basic W hW h =>
    apply local_bijective R c i X s₀ W _ h
    rcases hW with rfl | rfl | rfl
    · exact hU
    · exact hV
    · exact hUV
  | prod hm hn ihm ihn =>
    constructor
    · intro x y h
      exact Prod.ext (ihm.injective (congrArg Prod.fst h))
        (ihn.injective (congrArg Prod.snd h))
    · intro y
      obtain ⟨x₁, hx₁⟩ := ihm.surjective y.1
      obtain ⟨x₂, hx₂⟩ := ihn.surjective y.2
      exact ⟨(x₁, x₂), Prod.ext hx₁ hx₂⟩
  | equiv hm a b ih => exact b.bijective.comp (ih.comp a.bijective)

end AlgebraicGeometry
