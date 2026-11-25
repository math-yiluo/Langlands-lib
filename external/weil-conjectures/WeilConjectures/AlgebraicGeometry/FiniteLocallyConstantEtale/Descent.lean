/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descending a representing finite étale scheme along an affine étale cover

Let `E` be a sheaf of sets on the small étale site of a scheme `T`, let `s : S ⟶ T` be étale
with `S` affine, and let `p : X ⟶ S` be a surjective étale morphism from an affine scheme.
Suppose that the restriction of `E` to étale `X`-schemes is represented by a finite étale
`X`-scheme `v : V ⟶ X`, with universal section `ξ ∈ E(V)`
(`AlgebraicGeometry.Scheme.IsUniversalSection`). Then the restriction of `E` to étale
`S`-schemes is represented by a finite étale `S`-scheme
(`AlgebraicGeometry.Scheme.IsUniversalSection.exists_isUniversalSection_of_isAffine`).

This is the descent step in the proof that finite locally constant sheaves are represented by
finite étale schemes (blueprint `lemma-weil-pbc-finite-locally-constant-etale-equivalence`): the
two pullbacks of `ξ` to `V ×_S X` give, by universality, the descent isomorphism
`γ : V ×_S X ⟶ V` (the transport of the first projection to the second), which satisfies the
counit and cocycle identities because both sides pull `ξ` back to the same section. Affine flat
descent in coaction form (`AlgebraicGeometry.exists_isPullback_of_coaction`, Stacks 023N)
produces `N` over `S` with `V ≅ N ×_S X`; `N` is finite étale by fpqc descent of these
properties, `ξ` descends to `ξ₀ ∈ E(N)` by the sheaf property along `V ⟶ N`, and `ξ₀` is
universal, by descending morphisms along the effective epimorphism `W ×_S X ⟶ W`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} {E : T.Etaleᵒᵖ ⥤ Type w} {S : Scheme.{u}} {s : S ⟶ T}
  [AlgebraicGeometry.Etale s] {X : Scheme.{u}} {p : X ⟶ S} [AlgebraicGeometry.Etale p]
  {V : Scheme.{u}} {v : V ⟶ X} [AlgebraicGeometry.Etale v]
  {ξ : E.obj (op (Etale.mk (v ≫ p ≫ s)))}

namespace IsUniversalSection

variable (s p v) in
/-- The fibre product `V ×_S X`, an étale `T`-scheme through the second projection. -/
noncomputable abbrev coactObj : T.Etale := Etale.mk (pullback.snd (v ≫ p) p ≫ p ≫ s)

variable (s p v) in
/-- The first projection `V ×_S X ⟶ V`, a morphism of étale `T`-schemes. -/
noncomputable abbrev coactFst : coactObj s p v ⟶ Etale.mk (v ≫ p ≫ s) :=
  Over.homMk (pullback.fst (v ≫ p) p) (by
    change pullback.fst (v ≫ p) p ≫ v ≫ p ≫ s = pullback.snd (v ≫ p) p ≫ p ≫ s
    rw [← pullback.condition_assoc, Category.assoc])

/-- A `T`-morphism `a : W ⟶ V` together with a morphism `x : W ⟶ X` agreeing with `a` over `S`
gives a `T`-morphism `W ⟶ V ×_S X`. -/
noncomputable abbrev coactLift {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p ≫ s)) (x : W.left ⟶ X)
    (hx : a.left ≫ v ≫ p = x ≫ p) : W ⟶ coactObj s p v :=
  Over.homMk (pullback.lift a.left x hx) (by
    change pullback.lift _ _ _ ≫ pullback.snd (v ≫ p) p ≫ p ≫ s = _
    rw [pullback.lift_snd_assoc, ← reassoc_of% hx]
    exact Over.w a)

/-- The lift `W ⟶ V ×_S X` of `(a, x)` followed by the first projection is `a`. -/
lemma coactLift_fst {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p ≫ s)) (x : W.left ⟶ X)
    (hx : a.left ≫ v ≫ p = x ≫ p) : coactLift a x hx ≫ coactFst s p v = a :=
  Over.Hom.ext (by
    change pullback.lift a.left x _ ≫ pullback.fst (v ≫ p) p = a.left
    exact pullback.lift_fst _ _ _)

/-- The lift `W ⟶ V ×_S X` of `(a, x)` followed by the second projection is `x`. -/
lemma coactLift_left_snd {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p ≫ s)) (x : W.left ⟶ X)
    (hx : a.left ≫ v ≫ p = x ≫ p) :
    (coactLift a x hx).left ≫ pullback.snd (v ≫ p) p = x := by
  change pullback.lift a.left x _ ≫ pullback.snd (v ≫ p) p = x
  exact pullback.lift_snd _ _ _

variable (h : IsUniversalSection E (p ≫ s) (Etale.mk (v ≫ p ≫ s)) v ξ)

/-- The descent isomorphism of a universal section: the morphism `γ : V ×_S X ⟶ V` over the
second projection which pulls `ξ` back to the pullback of `ξ` along the first projection. -/
noncomputable def coact : coactObj s p v ⟶ Etale.mk (v ≫ p ≫ s) :=
  (h.exists_hom (W := coactObj s p v) (pullback.snd (v ≫ p) p) rfl
    (E.map (coactFst s p v).op ξ)).choose

/-- The descent isomorphism `γ` lies over the second projection `V ×_S X ⟶ X`. -/
lemma coact_left_comp : (h.coact).left ≫ v = pullback.snd (v ≫ p) p :=
  (h.exists_hom (W := coactObj s p v) (pullback.snd (v ≫ p) p) rfl
    (E.map (coactFst s p v).op ξ)).choose_spec.1

/-- The descent isomorphism `γ` pulls `ξ` back to the pullback of `ξ` along the first projection.
-/
lemma map_coact : E.map h.coact.op ξ = E.map (coactFst s p v).op ξ :=
  (h.exists_hom (W := coactObj s p v) (pullback.snd (v ≫ p) p) rfl
    (E.map (coactFst s p v).op ξ)).choose_spec.2

/-- **The key identity**: for a `T`-morphism `a : W ⟶ V` and a morphism `x : W ⟶ X` over `S`,
the transport `(a, x) ≫ γ` of `a` to `x` is the unique `X`-morphism `b : W ⟶ V` over `x` with
`b^* ξ = a^* ξ`. -/
lemma coactLift_coact {W : T.Etale} (a : W ⟶ Etale.mk (v ≫ p ≫ s)) (x : W.left ⟶ X)
    (hx : a.left ≫ v ≫ p = x ≫ p) (b : W ⟶ Etale.mk (v ≫ p ≫ s)) (hb : b.left ≫ v = x)
    (hab : E.map b.op ξ = E.map a.op ξ) : coactLift a x hx ≫ h.coact = b := by
  refine h.hom_ext ?_ ?_ ?_
  · rw [Etale.comp_left_eq, Category.assoc, coact_left_comp, hb, coactLift_left_snd]
  · rw [Etale.comp_left_eq, Category.assoc, Category.assoc, reassoc_of% (coact_left_comp h)]
    exact Over.w (coactLift a x hx)
  · rw [op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp,
      coactLift_fst, hab]

/-- The counit identity `γ (v, v(x)) = x` for the descent isomorphism. -/
lemma coact_counit :
    coactionUnit p v ≫ (h.coact).left = 𝟙 V := by
  have := h.coactLift_coact (W := Etale.mk (v ≫ p ≫ s)) (𝟙 _) v (Category.id_comp _) (𝟙 _)
    (Category.id_comp _) rfl
  have e : coactionUnit p v =
      (coactLift (𝟙 (Etale.mk (v ≫ p ≫ s))) v (Category.id_comp _)).left :=
    pullback.hom_ext (by simp; rfl) (by simp)
  rw [e]
  exact congrArg (fun f ↦ f.left) this

/-- The cocycle identity for the descent isomorphism: transporting from the first to the second and
then to the third factor is transporting from the first to the third factor. -/
lemma coact_coassoc :
    coactionMap p v (h.coact).left (h.coact_left_comp) ≫ (h.coact).left =
      coactionForget p v ≫ (h.coact).left := by
  -- the scheme `(V ×_S X) ×_S X`, as an étale `T`-scheme through the last projection
  let Z₂ : T.Etale := Etale.mk (pullback.snd (pullback.snd (v ≫ p) p ≫ p) p ≫ p ≫ s)
  let fst₂ : Z₂ ⟶ coactObj s p v := Over.homMk (pullback.fst _ _) (by
    change pullback.fst _ _ ≫ pullback.snd (v ≫ p) p ≫ p ≫ s = pullback.snd _ _ ≫ p ≫ s
    rw [← Category.assoc (pullback.snd (v ≫ p) p) p s, pullback.condition_assoc])
  let Fe : Z₂ ⟶ coactObj s p v := Over.homMk (coactionForget p v) (by
    change coactionForget p v ≫ pullback.snd (v ≫ p) p ≫ p ≫ s = pullback.snd _ _ ≫ p ≫ s
    simp)
  let m : Z₂ ⟶ Etale.mk (v ≫ p ≫ s) := fst₂ ≫ h.coact
  have hmx : m.left ≫ v ≫ p = pullback.snd _ _ ≫ p := by
    change (pullback.fst _ _ ≫ h.coact.left) ≫ v ≫ p = _
    rw [Category.assoc, reassoc_of% (coact_left_comp h), pullback.condition]
  have hm : E.map m.op ξ = E.map (fst₂ ≫ coactFst s p v).op ξ := by
    rw [op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp]
  have h₁ := h.coactLift_coact (W := Z₂) m (pullback.snd _ _) hmx (Fe ≫ h.coact)
    (by
      change coactionForget p v ≫ h.coact.left ≫ v = _
      rw [coact_left_comp]
      simp)
    (by
      have hF : Fe ≫ coactFst s p v = fst₂ ≫ coactFst s p v := Over.Hom.ext (by
        change coactionForget p v ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _
        simp)
      rw [hm, op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp,
        hF])
  have e : coactionMap p v (h.coact).left h.coact_left_comp =
      (coactLift m (pullback.snd _ _) hmx).left := by
    apply pullback.hom_ext
    · change _ = pullback.lift (pullback.fst _ _ ≫ h.coact.left) _ _ ≫ pullback.fst _ _
      simp
    · change _ = pullback.lift (pullback.fst _ _ ≫ h.coact.left) _ _ ≫ pullback.snd _ _
      simp
  rw [e]
  exact congrArg (fun f ↦ f.left) h₁

include h in
/-- **Descent of a representing finite étale scheme along an affine étale cover.** Let `E` be a
sheaf of sets on the small étale site of `T`, `s : S ⟶ T` étale with `S` affine, `p : X ⟶ S`
surjective étale with `X` affine, and `ξ` a universal section of `E` relative to `p ≫ s` along
a finite étale `v : V ⟶ X`. Then the restriction of `E` to étale `S`-schemes is represented by a
finite étale `S`-scheme `n : N ⟶ S`, with a universal section `ξ₀` whose pullback to
`V = N ×_S X` is `ξ`. (blueprint: `lemma-weil-pbc-finite-locally-constant-etale-equivalence`) -/
theorem exists_isUniversalSection_of_isAffine [IsAffine X] [IsAffine S]
    [AlgebraicGeometry.Surjective p] [IsFinite v] (hE : Presheaf.IsSheaf T.smallEtaleTopology E) :
    ∃ (N : Scheme.{u}) (n : N ⟶ S) (_ : AlgebraicGeometry.Etale n) (_ : IsFinite n)
      (ξ₀ : E.obj (op (Etale.mk (n ≫ s)))), IsUniversalSection E s (Etale.mk (n ≫ s)) n ξ₀ := by
  have : IsAffine V := isAffine_of_isAffineHom v
  obtain ⟨N, -, n, q, hq, hγq⟩ := exists_isPullback_of_coaction p v h.coact.left h.coact_left_comp
    h.coact_counit h.coact_coassoc
  have hpq : (@AlgebraicGeometry.Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) p :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hn : AlgebraicGeometry.Etale n :=
    of_isPullback_of_descendsAlong (P := @AlgebraicGeometry.Etale) hq.flip hpq
      (inferInstanceAs (AlgebraicGeometry.Etale v))
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hnf : IsFinite n :=
    of_isPullback_of_descendsAlong (P := @IsFinite) hq.flip hpq (inferInstanceAs (IsFinite v))
  have : AlgebraicGeometry.Surjective q := MorphismProperty.of_isPullback hq.flip ‹_›
  let NE : T.Etale := Etale.mk (n ≫ s)
  let qE : Etale.mk (v ≫ p ≫ s) ⟶ NE := Over.homMk q (by
    change q ≫ n ≫ s = v ≫ p ≫ s
    rw [reassoc_of% hq.w])
  -- the section `ξ` descends along `q : V ⟶ N`
  obtain ⟨ξ₀, hξ₀⟩ := Etale.exists_map_eq_of_surjective hE qE q.surjective ξ (by
    intro Z p₁ p₂ hp
    have hp' : p₁.left ≫ q = p₂.left ≫ q := congrArg (fun f ↦ f.left) hp
    have hx : p₁.left ≫ v ≫ p = (p₂.left ≫ v) ≫ p := by
      rw [Category.assoc, ← hq.w, reassoc_of% hp']
    let ℓ := coactLift p₁ (p₂.left ≫ v) hx
    have hℓ : ℓ ≫ h.coact = p₂ := by
      refine Over.Hom.ext (hq.hom_ext ?_ ?_)
      · change (ℓ.left ≫ h.coact.left) ≫ q = p₂.left ≫ q
        rw [Category.assoc, hγq, ← hp', ← Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · change (ℓ.left ≫ h.coact.left) ≫ v = p₂.left ≫ v
        rw [Category.assoc, coact_left_comp, coactLift_left_snd]
    rw [← hℓ, op_comp, Functor.map_comp_apply, map_coact, ← Functor.map_comp_apply, ← op_comp,
      coactLift_fst])
  refine ⟨N, n, hn, hnf, ξ₀, fun W w hw ↦ ?_⟩
  -- the base change `W' = W ×_S X ⟶ W`, a surjective étale cover
  have : AlgebraicGeometry.Etale w := etale_of_comp_eq (V := W) hw
  let W' : T.Etale := Etale.mk (pullback.snd w p ≫ p ≫ s)
  let π : W' ⟶ W := Over.homMk (pullback.fst w p) (by
    change pullback.fst w p ≫ W.hom = pullback.snd w p ≫ p ≫ s
    rw [← hw, pullback.condition_assoc])
  have hπ : Function.Surjective π.left := (pullback.fst w p).surjective
  have : LocallyOfFinitePresentation (pullback.fst w p) := inferInstance
  have : Flat (pullback.fst w p) := inferInstance
  have : EffectiveEpi π.left := inferInstanceAs (EffectiveEpi (pullback.fst w p))
  -- the lift `W' ⟶ V` of a morphism `W ⟶ N` over `S`
  let lift (a : {a : W ⟶ NE // a.left ≫ n = w}) : W' ⟶ Etale.mk (v ≫ p ≫ s) :=
    Over.homMk (hq.lift (pullback.fst w p ≫ a.1.left) (pullback.snd w p) (by
      rw [Category.assoc, a.2]
      exact pullback.condition)) (by
      change hq.lift _ _ _ ≫ v ≫ p ≫ s = pullback.snd w p ≫ p ≫ s
      rw [hq.lift_snd_assoc])
  have lift_v (a : {a : W ⟶ NE // a.left ≫ n = w}) : (lift a).left ≫ v = pullback.snd w p :=
    hq.lift_snd _ _ _
  have lift_q (a : {a : W ⟶ NE // a.left ≫ n = w}) : lift a ≫ qE = π ≫ a.1 :=
    Over.Hom.ext (hq.lift_fst _ _ _)
  have map_lift (a : {a : W ⟶ NE // a.left ≫ n = w}) :
      E.map (lift a).op ξ = E.map π.op (E.map a.1.op ξ₀) := by
    rw [← hξ₀, ← Functor.map_comp_apply, ← op_comp, lift_q, op_comp, Functor.map_comp_apply]
  refine ⟨fun a b hab ↦ ?_, fun e ↦ ?_⟩
  · have hab' : lift a = lift b := h.hom_ext ((lift_v a).trans (lift_v b).symm)
      (by rw [lift_v]; rfl) (by
        rw [map_lift, map_lift]
        exact congrArg _ hab)
    have : π ≫ a.1 = π ≫ b.1 := by rw [← lift_q, ← lift_q, hab']
    exact Subtype.ext (Over.Hom.ext ((cancel_epi (pullback.fst w p)).1
      (congrArg (fun f ↦ f.left) this)))
  · obtain ⟨a', ha'v, ha'ξ⟩ := h.exists_hom (W := W') (pullback.snd w p) rfl (E.map π.op e)
    -- the kernel pair of `π`, as an étale `T`-scheme
    let K : T.Etale := Etale.mk (pullback.fst π.left π.left ≫ W'.hom)
    let k₁ : K ⟶ W' := Over.homMk (pullback.fst π.left π.left) rfl
    let k₂ : K ⟶ W' := Over.homMk (pullback.snd π.left π.left) (by
      change pullback.snd π.left π.left ≫ W'.hom = pullback.fst π.left π.left ≫ W'.hom
      rw [← Over.w π, pullback.condition_assoc])
    have hk : k₁ ≫ π = k₂ ≫ π := Over.Hom.ext pullback.condition
    have hkq : pullback.fst π.left π.left ≫ a'.left ≫ q =
        pullback.snd π.left π.left ≫ a'.left ≫ q := by
      have hx : (k₁ ≫ a').left ≫ v ≫ p = (k₂.left ≫ pullback.snd w p) ≫ p := by
        change (k₁.left ≫ a'.left) ≫ v ≫ p = (k₂.left ≫ pullback.snd w p) ≫ p
        rw [Category.assoc, reassoc_of% ha'v, Category.assoc, ← pullback.condition,
          ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ w) (congrArg (fun f ↦ f.left) hk)
      let ℓ := coactLift (k₁ ≫ a') (k₂.left ≫ pullback.snd w p) hx
      have hℓ : ℓ ≫ h.coact = k₂ ≫ a' := by
        refine h.coactLift_coact _ _ _ _ ?_ ?_
        · rw [Etale.comp_left_eq, Category.assoc, ha'v]
        · rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ha'ξ,
            ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hk]
      have h1 : ℓ.left ≫ pullback.fst (v ≫ p) p = k₁.left ≫ a'.left :=
        congrArg (fun f : K ⟶ Etale.mk (v ≫ p ≫ s) ↦ f.left) (coactLift_fst (k₁ ≫ a') _ _)
      have h2 := congrArg (fun f ↦ f.left ≫ q) hℓ
      change (ℓ.left ≫ h.coact.left) ≫ q = (k₂.left ≫ a'.left) ≫ q at h2
      rw [Category.assoc, hγq, ← Category.assoc, h1, Category.assoc, Category.assoc] at h2
      exact h2
    let aL : W.left ⟶ N := EffectiveEpi.desc π.left (a'.left ≫ q) (fun {Z} g₁ g₂ hg ↦ by
      calc g₁ ≫ a'.left ≫ q = pullback.lift g₁ g₂ hg ≫ pullback.fst π.left π.left ≫ a'.left ≫ q :=
            (pullback.lift_fst_assoc _ _ _ _).symm
        _ = pullback.lift g₁ g₂ hg ≫ pullback.snd π.left π.left ≫ a'.left ≫ q := by rw [hkq]
        _ = g₂ ≫ a'.left ≫ q := pullback.lift_snd_assoc _ _ _ _)
    have haL : π.left ≫ aL = a'.left ≫ q := EffectiveEpi.fac _ _ _
    have haLn : aL ≫ n = w := by
      rw [← cancel_epi π.left, reassoc_of% haL, hq.w, reassoc_of% ha'v]
      exact pullback.condition.symm
    let a : W ⟶ NE := Over.homMk aL (by
      change aL ≫ n ≫ s = W.hom
      rw [reassoc_of% haLn, hw])
    refine ⟨⟨a, haLn⟩, Etale.map_injective_of_surjective hE π hπ ?_⟩
    have hπa : π ≫ a = a' ≫ qE := Over.Hom.ext haL
    change E.map π.op (E.map a.op ξ₀) = E.map π.op e
    rw [← Functor.map_comp_apply, ← op_comp, ← ha'ξ, ← hξ₀, ← Functor.map_comp_apply, ← op_comp,
      hπa]

end IsUniversalSection

end AlgebraicGeometry.Scheme
