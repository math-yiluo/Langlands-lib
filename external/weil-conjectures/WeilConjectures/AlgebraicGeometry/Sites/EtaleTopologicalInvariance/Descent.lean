/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Descent of quasi-affine étale schemes along an étale cover

Let `f : X ⟶ Y` be a universal homeomorphism, `g : U ⟶ X` an affine étale morphism and
`p : W ⟶ Y` an étale surjection from an affine scheme, where `Y` is quasi-affine (embedded
into an affine scheme `S` by an open immersion `ι`). Suppose that after base change along
`p` the étale `X`-scheme `U` descends: there is a quasi-affine étale `W`-scheme `V''` with
`V'' ×_W W_X ≅ U ×_X W_X` over `W_X = W ×_Y X`. Then `U` descends to `Y`: there is a
quasi-affine étale `Y`-scheme `V` with `V ×_Y X ≅ U` over `X`.

## Proof sketch

Full faithfulness of base change along the universal homeomorphism `W_X ⟶ W` yields a
canonical "coaction" `γ : V'' ×_S W ⟶ V''` over `W` (the descent datum of `V''` relative to
`W/Y`, in coalgebra form), satisfying a counit and a coassociativity identity, both proved by
faithfulness after base change to `W_X`, where they reduce to identities between projections.

Taking global sections and using flat base change of global sections
(`AlgebraicGeometry.isPushout_appTop_of_flat`), `γ` induces a descent datum on the ring
`E = Γ(V'')` in the sense of `Algebra.DescentDatum`, relative to `Γ(S) → Γ(W)`. Flat descent
of algebras (`Algebra.DescentDatum.descendedEquiv`) produces a `Γ(S)`-algebra `D` with
`Γ(W) ⊗ D ≅ E`, i.e. an affine `S`-scheme `N = Spec D` with `N ×_S W ≅ Spec E`. The open
subscheme `V'' ⊆ Spec E` is stable under the descent datum, hence is the preimage of an open
`V ⊆ N`, and `V ×_Y W ≅ V''`. Étaleness of `V ⟶ Y` descends along the fpqc cover `p`, and the
isomorphism `V ×_Y X ≅ U` is obtained by descending the given isomorphism along the fpqc
cover `W_X ⟶ X`, using that surjective flat quasi-compact morphisms are effective
epimorphisms.
-/

@[expose] public section

universe u

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

namespace Scheme.Hom.EtaleDescent

variable {S Y W X U : Scheme.{u}} [IsAffine S] (ι : Y ⟶ S) [IsOpenImmersion ι] [IsAffine W]
  (p : W ⟶ Y) [AlgebraicGeometry.Etale p] [Surjective p] (f : X ⟶ Y) [IsUniversalHomeomorphism f]
  (g : U ⟶ X) [AlgebraicGeometry.Etale g] (V'' : W.Etale) [V''.left.IsQuasiAffine]
  (e : (pullback.fst p f).Etale.obj V'' ≅ Etale.mk (pullback.fst (pullback.snd p f) g))

/-! ### The schemes and morphisms involved -/

/-- `W_X = W ×_Y X`. -/
abbrev WX : Scheme.{u} := pullback p f

/-- The universal homeomorphism `W_X ⟶ W`. -/
abbrev f₀ : WX p f ⟶ W := pullback.fst p f

/-- The étale surjection `W_X ⟶ X`. -/
abbrev π₀ : WX p f ⟶ X := pullback.snd p f

/-- The underlying scheme of `V''`. -/
abbrev V : Scheme.{u} := V''.left

/-- The structure morphism of `V''`. -/
abbrev v : V V'' ⟶ W := V''.hom

/-- The composite `W ⟶ Y ⟶ S`. -/
abbrev pS : W ⟶ S := p ≫ ι

/-- The composite `V'' ⟶ W ⟶ S`. -/
abbrev vS : V V'' ⟶ S := v V'' ≫ pS ι p

/-- `P = V'' ×_S W = V'' ×_Y W`. -/
abbrev P : Scheme.{u} := pullback (vS ι p V'') (pS ι p)

/-- The first projection `P ⟶ V''`. -/
abbrev pr₁ : P ι p V'' ⟶ V V'' := pullback.fst _ _

/-- The second projection `P ⟶ W`. -/
abbrev pr₂ : P ι p V'' ⟶ W := pullback.snd _ _

/-- `PT = P ×_W W_X`. -/
abbrev PT : Scheme.{u} := pullback (pr₂ ι p V'') (f₀ p f)

/-- The projection `PT ⟶ P`. -/
abbrev pT : PT ι p f V'' ⟶ P ι p V'' := pullback.fst _ _

/-- The projection `PT ⟶ W_X`. -/
abbrev qT : PT ι p f V'' ⟶ WX p f := pullback.snd _ _

/-- `PV = V'' ×_W W_X`, the base change of `V''` to `W_X`. -/
abbrev PV : Scheme.{u} := pullback (v V'') (f₀ p f)

/-- `U' = U ×_X W_X`. -/
abbrev U' : Scheme.{u} := pullback (π₀ p f) g

instance : AlgebraicGeometry.Etale (pS ι p) := inferInstance
instance : Flat (pS ι p) := inferInstance
instance : CompactSpace (V V'') := inferInstance
instance : QuasiSeparatedSpace (V V'') := inferInstance

instance : QuasiSeparatedSpace (P ι p V'') :=
  quasiSeparatedSpace_of_quasiSeparated (pr₁ ι p V'')

instance : CompactSpace (P ι p V'') := inferInstance

/-- `P₂ = P ×_S W = V'' ×_S W ×_S W`. -/
abbrev P₂ : Scheme.{u} := pullback (pr₂ ι p V'' ≫ pS ι p) (pS ι p)

/-- The projection `P₂ ⟶ P` forgetting the middle factor. -/
abbrev π₁ : P₂ ι p V'' ⟶ P ι p V'' :=
  pullback.map _ _ _ _ (pr₁ ι p V'') (𝟙 W) (𝟙 S) (by simp [pullback.condition]) (by simp)

@[reassoc]
lemma pr₁_pr₂_p : pullback.fst (pr₂ ι p V'' ≫ pS ι p) (pS ι p) ≫ pr₂ ι p V'' ≫ p =
    pullback.snd (pr₂ ι p V'' ≫ pS ι p) (pS ι p) ≫ p := by
  rw [← cancel_mono ι]
  simpa [pS] using pullback.condition (f := pr₂ ι p V'' ≫ pS ι p) (g := pS ι p)

/-- `PT₂ = P₂ ×_W W_X`. -/
abbrev PT₂ : Scheme.{u} := pullback (pullback.snd (pr₂ ι p V'' ≫ pS ι p) (pS ι p)) (f₀ p f)

/-- The projection `PT₂ ⟶ P₂`. -/
abbrev pT₂ : PT₂ ι p f V'' ⟶ P₂ ι p V'' := pullback.fst _ _

/-- The projection `PT₂ ⟶ W_X`. -/
abbrev qT₂ : PT₂ ι p f V'' ⟶ WX p f := pullback.snd _ _

lemma pT₂_cond : pT₂ ι p f V'' ≫ pullback.snd _ _ = qT₂ ι p f V'' ≫ f₀ p f := pullback.condition

lemma pT₂_fst_pr₂_p :
    (pT₂ ι p f V'' ≫ pullback.fst _ _ ≫ pr₂ ι p V'') ≫ p = (qT₂ ι p f V'' ≫ π₀ p f) ≫ f := by
  simp only [Category.assoc]
  rw [pr₁_pr₂_p, ← Category.assoc, pT₂_cond, Category.assoc, pullback.condition]
variable {p f g V''}

/-- The `U`-coordinate of a point of `V'' ×_W W_X`, via the isomorphism `e`. -/
abbrev Ũ : PV p f V'' ⟶ U := e.hom.left ≫ pullback.snd (π₀ p f) g

lemma vS_comp_eq : pr₁ ι p V'' ≫ v V'' ≫ p = pr₂ ι p V'' ≫ p := by
  have := pullback.condition (f := vS ι p V'') (g := pS ι p)
  simp only [vS, pS, Category.assoc] at this
  rw [← cancel_mono ι]
  simpa using this

/-- The `W_X`-coordinate of the map `a : PT ⟶ PV`. -/
def x'' : PT ι p f V'' ⟶ WX p f :=
  pullback.lift (pT ι p f V'' ≫ pr₁ ι p V'' ≫ v V'') (qT ι p f V'' ≫ π₀ p f) (by
    rw [Category.assoc, Category.assoc, vS_comp_eq, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc, pullback.condition])

/-- The map `PT ⟶ PV` sending `(π, x')` to `(pr₁ π, x'')`. -/
def m₁ : PT ι p f V'' ⟶ PV p f V'' :=
  pullback.lift (pT ι p f V'' ≫ pr₁ ι p V'') (x'' ι) (by simp [x''])

@[reassoc]
lemma m₁_snd : m₁ ι ≫ pullback.snd (v V'') (f₀ p f) = x'' ι := by
  simp [m₁]

@[reassoc]
lemma e_hom_left_fst : e.hom.left ≫ pullback.fst (π₀ p f) g = pullback.snd (v V'') (f₀ p f) :=
  MorphismProperty.Over.w e.hom

@[reassoc]
lemma e_inv_left_snd : e.inv.left ≫ pullback.snd (v V'') (f₀ p f) = pullback.fst (π₀ p f) g :=
  MorphismProperty.Over.w e.inv

@[reassoc (attr := simp)]
lemma e_inv_left_hom_left : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← MorphismProperty.Comma.comp_left, e.inv_hom_id]
  rfl

@[reassoc (attr := simp)]
lemma e_hom_left_inv_left : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← MorphismProperty.Comma.comp_left, e.hom_inv_id]
  rfl

/-- The `U`-coordinate. -/
def u : PT ι p f V'' ⟶ U := m₁ ι ≫ Ũ e

lemma u_g : u ι e ≫ g = qT ι p f V'' ≫ π₀ p f := by
  have h1 : pullback.snd (π₀ p f) g ≫ g = pullback.fst (π₀ p f) g ≫ π₀ p f :=
    pullback.condition.symm
  rw [u, Ũ]
  simp only [Category.assoc]
  rw [h1, e_hom_left_fst_assoc, m₁_snd_assoc, x'', pullback.lift_snd]

/-- The map `PT ⟶ U'` sending `(π, x')` to `(x', u)`. -/
def m₂ : PT ι p f V'' ⟶ U' p f g :=
  pullback.lift (qT ι p f V'') (u ι e) (u_g ι e).symm

/-- The morphism `a : PT ⟶ PV` which is the base change of the coaction. -/
def a : PT ι p f V'' ⟶ PV p f V'' := m₂ ι e ≫ e.inv.left

lemma a_def : a ι e = m₂ ι e ≫ e.inv.left := rfl

lemma a_snd : a ι e ≫ pullback.snd (v V'') (f₀ p f) = qT ι p f V'' := by
  rw [a, Category.assoc, e_inv_left_snd, m₂, pullback.lift_fst]

/-- The coaction `γ : P = V'' ×_S W ⟶ V''`, a morphism over `W`, characterized by its base change
to `W_X`. -/
def γ : P ι p V'' ⟶ V V'' :=
  (Scheme.Hom.existsUnique_of_isPullback (f₀ p f) (pr₂ ι p V'') (v V'')
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _) (a ι e) (a_snd ι e)).choose

lemma γ_spec :
    γ ι e ≫ v V'' = pr₂ ι p V'' ∧
      pT ι p f V'' ≫ γ ι e = a ι e ≫ pullback.fst (v V'') (f₀ p f) :=
  (Scheme.Hom.existsUnique_of_isPullback (f₀ p f) (pr₂ ι p V'') (v V'')
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _) (a ι e)
    (a_snd ι e)).choose_spec.1

@[reassoc (attr := simp)]
lemma γ_v : γ ι e ≫ v V'' = pr₂ ι p V'' := (γ_spec ι e).1

lemma pT_γ : pT ι p f V'' ≫ γ ι e = a ι e ≫ pullback.fst (v V'') (f₀ p f) := (γ_spec ι e).2

lemma a_eq : a ι e = pullback.lift (pT ι p f V'' ≫ γ ι e) (qT ι p f V'') (by
    rw [Category.assoc, γ_v, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, pT_γ]
  · rw [pullback.lift_snd, a_snd]

/-- Uniqueness of `W`-morphisms `T ⟶ V''` with given base change to `W_X`. -/
lemma hom_ext_of_pullback {T : Scheme.{u}} (t : T ⟶ W) {g₁ g₂ : T ⟶ V V''}
    (h₁ : g₁ ≫ v V'' = t) (h₂ : g₂ ≫ v V'' = t)
    (H : pullback.fst t (f₀ p f) ≫ g₁ = pullback.fst t (f₀ p f) ≫ g₂) : g₁ = g₂ :=
  Scheme.Hom.ext_of_surjective_of_formallyUnramified (pullback.fst t (f₀ p f)) (v V'')
    (h₁.trans h₂.symm) H

section Coaction

variable {Z : Scheme.{u}} (θ : Z ⟶ P ι p V'') (ζ : Z ⟶ WX p f)
  (hθζ : θ ≫ pr₂ ι p V'' = ζ ≫ f₀ p f)

/-- The `W_X`-coordinate `(v (pr₁ θ), π₀ ζ)`. -/
abbrev liftWX : Z ⟶ WX p f :=
  pullback.lift (θ ≫ pr₁ ι p V'' ≫ v V'') (ζ ≫ π₀ p f) (by
    rw [Category.assoc, Category.assoc, vS_comp_eq, ← Category.assoc, hθζ, Category.assoc,
      pullback.condition, Category.assoc])

/-- The map `Z ⟶ PV`, `z ↦ (pr₁ (θ z), liftWX z)`. -/
abbrev liftPV : Z ⟶ PV p f V'' :=
  pullback.lift (θ ≫ pr₁ ι p V'') (liftWX ι θ ζ hθζ) (by simp)

lemma lift_m₁ : pullback.lift θ ζ hθζ ≫ m₁ ι = liftPV ι θ ζ hθζ := by
  apply pullback.hom_ext
  · simp [m₁]
  · rw [Category.assoc, m₁_snd, pullback.lift_snd, x'']
    apply pullback.hom_ext <;> simp

lemma lift_u : pullback.lift θ ζ hθζ ≫ u ι e = liftPV ι θ ζ hθζ ≫ Ũ e := by
  rw [u, ← Category.assoc, lift_m₁]

lemma lift_a :
    pullback.lift θ ζ hθζ ≫ a ι e =
      pullback.lift (θ ≫ γ ι e) ζ (by rw [Category.assoc, γ_v, hθζ]) := by
  rw [a_eq]
  apply pullback.hom_ext <;> simp

/-- The key computation: the `U`-coordinate of `(γ θ, ζ)` equals that of `(pr₁ θ, liftWX)`. -/
lemma lift_γ_Ũ :
    pullback.lift (θ ≫ γ ι e) ζ (by rw [Category.assoc, γ_v, hθζ]) ≫ Ũ e =
      liftPV ι θ ζ hθζ ≫ Ũ e := by
  rw [← lift_a, ← lift_m₁, Category.assoc, Category.assoc, a, Ũ, Category.assoc,
    ← Category.assoc e.inv.left, e_inv_left_hom_left, Category.id_comp, m₂, pullback.lift_snd]
  rfl

lemma lift_m₂ :
    pullback.lift θ ζ hθζ ≫ m₂ ι e = pullback.lift ζ (liftPV ι θ ζ hθζ ≫ Ũ e) (by
        rw [← lift_u, Category.assoc, u_g, pullback.lift_snd_assoc]) := by
  apply pullback.hom_ext
  · simp [m₂]
  · rw [Category.assoc, m₂, pullback.lift_snd, pullback.lift_snd, lift_u]

/-- The "unit" `V'' ⟶ P`, `x ↦ (x, v x)`. -/
abbrev d : V V'' ⟶ P ι p V'' := pullback.lift (𝟙 _) (v V'') (by simp)

/-- The counit identity for the coaction `γ`. -/
lemma d_γ : d ι ≫ γ ι e = 𝟙 _ := by
  apply hom_ext_of_pullback (p := p) (f := f) (v V'') (by simp) (by simp)
  have hθζ : (pullback.fst (v V'') (f₀ p f) ≫ d ι) ≫ pr₂ ι p V'' =
      pullback.snd (v V'') (f₀ p f) ≫ f₀ p f := by
    simp [pullback.condition]
  have h₁ : liftPV ι (pullback.fst (v V'') (f₀ p f) ≫ d ι) (pullback.snd _ _) hθζ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst_assoc, Category.id_comp]
        exact pullback.condition
      · rw [pullback.lift_snd]
  have h₂' : pullback.lift (pullback.fst (v V'') (f₀ p f) ≫ d ι) (pullback.snd _ _) hθζ ≫
      m₂ ι e = e.hom.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, m₂, pullback.lift_fst, pullback.lift_snd, e_hom_left_fst]
    · rw [Category.assoc, m₂, pullback.lift_snd, lift_u, h₁, Category.id_comp]
  have h₂ : pullback.lift (pullback.fst (v V'') (f₀ p f) ≫ d ι) (pullback.snd _ _) hθζ ≫
      a ι e = 𝟙 _ := by
    rw [a, ← Category.assoc, h₂', e_hom_left_inv_left]
    rfl
  have := congr($h₂ ≫ pullback.fst (v V'') (f₀ p f))
  rw [Category.assoc, ← pT_γ, Category.id_comp, pullback.lift_fst_assoc] at this
  simpa using this

/-- The map `P₂ ⟶ P` applying `γ` to the first two factors. -/
abbrev γ₁ : P₂ ι p V'' ⟶ P ι p V'' :=
  pullback.map (pr₂ ι p V'' ≫ pS ι p) (pS ι p) (vS ι p V'') (pS ι p) (γ ι e) (𝟙 W) (𝟙 S)
    (by simp) (by simp)

/-- The coassociativity identity for the coaction `γ`. -/
lemma γ₁_γ : γ₁ ι e ≫ γ ι e = π₁ ι p V'' ≫ γ ι e := by
  apply hom_ext_of_pullback (p := p) (f := f) (pullback.snd _ _) (by simp) (by simp)
  have h₁ : (pT₂ ι p f V'' ≫ π₁ ι p V'') ≫ pr₂ ι p V'' = qT₂ ι p f V'' ≫ f₀ p f := by
    rw [Category.assoc, pullback.lift_snd, Category.comp_id, pT₂_cond]
  have h₂ : (pT₂ ι p f V'' ≫ γ₁ ι e) ≫ pr₂ ι p V'' = qT₂ ι p f V'' ≫ f₀ p f := by
    rw [Category.assoc, pullback.lift_snd, Category.comp_id, pT₂_cond]
  -- reduce to the `U`-coordinates
  suffices h : liftPV ι (pT₂ ι p f V'' ≫ γ₁ ι e) (qT₂ ι p f V'') h₂ ≫ Ũ e =
      liftPV ι (pT₂ ι p f V'' ≫ π₁ ι p V'') (qT₂ ι p f V'') h₁ ≫ Ũ e by
    have e₃ : pullback.lift (pT₂ ι p f V'' ≫ γ₁ ι e) (qT₂ ι p f V'') h₂ ≫ m₂ ι e =
        pullback.lift (pT₂ ι p f V'' ≫ π₁ ι p V'') (qT₂ ι p f V'') h₁ ≫ m₂ ι e := by
      rw [lift_m₂, lift_m₂]
      congr 1
    have e₄ := congr($e₃ ≫ e.inv.left ≫ pullback.fst (v V'') (f₀ p f))
    simp only [Category.assoc] at e₄
    rw [← Category.assoc (m₂ ι e), ← a_def, ← pT_γ, pullback.lift_fst_assoc,
      pullback.lift_fst_assoc] at e₄
    simpa only [Category.assoc] using e₄
  -- the `W_X`-coordinate `(pr₂ (pr₁ z), π₀ (qT₂ z))`
  let ζ' : PT₂ ι p f V'' ⟶ WX p f :=
    pullback.lift (pT₂ ι p f V'' ≫ pullback.fst _ _ ≫ pr₂ ι p V'') (qT₂ ι p f V'' ≫ π₀ p f)
      (pT₂_fst_pr₂_p ι p f V'')
  have hθ : (pT₂ ι p f V'' ≫ pullback.fst _ _) ≫ pr₂ ι p V'' = ζ' ≫ f₀ p f := by
    simp [ζ']
  have k := lift_γ_Ũ ι e (pT₂ ι p f V'' ≫ pullback.fst _ _) ζ' hθ
  have e₃ : liftPV ι (pT₂ ι p f V'' ≫ γ₁ ι e) (qT₂ ι p f V'') h₂ =
      pullback.lift ((pT₂ ι p f V'' ≫ pullback.fst _ _) ≫ γ ι e) ζ'
        (by rw [Category.assoc, γ_v, hθ]) := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext <;> simp [ζ']
  have e₄ : liftPV ι (pT₂ ι p f V'' ≫ pullback.fst _ _) ζ' hθ =
      liftPV ι (pT₂ ι p f V'' ≫ π₁ ι p V'') (qT₂ ι p f V'') h₁ := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext <;> simp [ζ']
  rw [e₃, k, e₄]

end Coaction

section AffineDescent

/-- The affine part of the descent: the global sections `E = Γ(V'')` descend to a `Γ(S)`-algebra
`D₀`, giving an affine `S`-scheme `N = Spec D₀` with `N ×_S W ≅ Spec E`, compatibly with the
coaction `γ`. -/
theorem exists_affine_descent :
    ∃ (N : Scheme.{u}) (_ : IsAffine N) (nS : N ⟶ S) (q : Spec Γ(V V'', ⊤) ⟶ N)
      (w : Spec Γ(V V'', ⊤) ⟶ W), IsPullback w q (pS ι p) nS ∧
      (V V'').toSpecΓ ≫ w = v V'' ∧
      γ ι e ≫ (V V'').toSpecΓ ≫ q = pr₁ ι p V'' ≫ (V V'').toSpecΓ ≫ q := by
  -- the rings and their algebra structures
  let R : CommRingCat.{u} := Γ(S, ⊤)
  let A' : CommRingCat.{u} := Γ(W, ⊤)
  let E : CommRingCat.{u} := Γ(V V'', ⊤)
  let _ : Algebra R A' := (pS ι p).appTop.hom.toAlgebra
  let _ : Algebra A' E := (v V'').appTop.hom.toAlgebra
  let _ : Algebra R E := (vS ι p V'').appTop.hom.toAlgebra
  have : IsScalarTower R A' E := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  have hflat : Module.Flat R A' := (pS ι p).flat_appTop
  -- flat base change of global sections for `P = V'' ×_S W`
  have hP := isPushout_appTop_of_flat (pS ι p) (vS ι p V'')
  let ξ : A' ⊗[R] E ≃+* Γ(P ι p V'', ⊤) := hP.tensorEquiv rfl rfl
  have ξ_tmul : ∀ (a : A') (x : E),
      ξ (a ⊗ₜ x) = (pr₂ ι p V'').appTop a * (pr₁ ι p V'').appTop x :=
    hP.tensorEquiv_tmul rfl rfl
  -- the coaction on `E`
  let δ₀ : E →+* A' ⊗[R] E := ξ.symm.toRingHom.comp (γ ι e).appTop.hom
  have δ₀_apply : ∀ x, ξ (δ₀ x) = (γ ι e).appTop x := fun x ↦ by
    change ξ (ξ.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hγv : ∀ a, (γ ι e).appTop ((v V'').appTop a) = (pr₂ ι p V'').appTop a := fun a ↦
    congr(((Scheme.Hom.appTop $(γ_v ι e)).hom) a)
  let δ : E →ₐ[A'] A' ⊗[R] E :=
    { δ₀ with
      commutes' := fun a ↦ by
        change δ₀ (algebraMap A' E a) = algebraMap A' (A' ⊗[R] E) a
        apply ξ.injective
        rw [δ₀_apply, Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        exact hγv a }
  have δ_apply : ∀ x, ξ (δ x) = (γ ι e).appTop x := δ₀_apply
  -- the counit condition
  have hd₁ : d ι ≫ pr₁ ι p V'' = 𝟙 _ := pullback.lift_fst _ _ _
  have hd₂ : d ι ≫ pr₂ ι p V'' = v V'' := pullback.lift_snd _ _ _
  have hmul : ∀ t : A' ⊗[R] E, Algebra.TensorProduct.mulMap R A' E t = (d ι).appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [ξ_tmul, map_mul, Algebra.TensorProduct.mulMap_tmul, Algebra.smul_def]
      have h1 : (d ι).appTop ((pr₂ ι p V'').appTop a) = (v V'').appTop a :=
        congr(((Scheme.Hom.appTop $hd₂).hom) a)
      have h2 : (d ι).appTop ((pr₁ ι p V'').appTop x) = x :=
        congr(((Scheme.Hom.appTop $hd₁).hom) x)
      rw [h1, h2]
      rfl
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcounit : ∀ x, Algebra.TensorProduct.mulMap R A' E (δ x) = x := fun x ↦ by
    rw [hmul, δ_apply]
    exact congr(((Scheme.Hom.appTop $(d_γ ι e)).hom) x)
  -- the coassociativity condition, via `P₂ = P ×_S W`
  let _ : Algebra R Γ(P ι p V'', ⊤) := (pr₂ ι p V'' ≫ pS ι p).appTop.hom.toAlgebra
  have hP₂ := isPushout_appTop_of_flat (pS ι p) (pr₂ ι p V'' ≫ pS ι p)
  let ξ₂ : A' ⊗[R] Γ(P ι p V'', ⊤) ≃+* Γ(P₂ ι p V'', ⊤) := hP₂.tensorEquiv rfl rfl
  have ξ₂_tmul : ∀ (a : A') (y : Γ(P ι p V'', ⊤)), ξ₂ (a ⊗ₜ y) =
      (pullback.snd (pr₂ ι p V'' ≫ pS ι p) (pS ι p)).appTop a *
        (pullback.fst (pr₂ ι p V'' ≫ pS ι p) (pS ι p)).appTop y :=
    hP₂.tensorEquiv_tmul rfl rfl
  let ξₐ : A' ⊗[R] E ≃ₐ[R] Γ(P ι p V'', ⊤) :=
    { ξ with
      commutes' := fun r ↦ by
        change ξ (algebraMap R (A' ⊗[R] E) r) = algebraMap R Γ(P ι p V'', ⊤) r
        rw [Algebra.TensorProduct.algebraMap_apply, ξ_tmul, map_one, mul_one]
        rfl }
  have ξₐ_apply : ∀ t, ξₐ t = ξ t := fun _ ↦ rfl
  let Θ : A' ⊗[R] (A' ⊗[R] E) →+* Γ(P₂ ι p V'', ⊤) :=
    ξ₂.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id R A') ξₐ.toAlgHom).toRingHom
  have Θ_inj : Function.Injective Θ := by
    have : ⇑Θ = ξ₂ ∘ (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ) := by
      ext t
      simp [Θ, Algebra.TensorProduct.congr_apply]
    rw [this]
    exact ξ₂.injective.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A')) ξₐ).injective
  have Θ_tmul : ∀ (a : A') (t : A' ⊗[R] E), Θ (a ⊗ₜ t) =
      (pullback.snd (pr₂ ι p V'' ≫ pS ι p) (pS ι p)).appTop a *
        (pullback.fst (pr₂ ι p V'' ≫ pS ι p) (pS ι p)).appTop (ξ t) := by
    intro a t
    simp [Θ, ξ₂_tmul, ξₐ_apply]
  have hγ₁₂ : γ₁ ι e ≫ pr₂ ι p V'' = pullback.snd (pr₂ ι p V'' ≫ pS ι p) (pS ι p) := by simp
  have hγ₁₁ : γ₁ ι e ≫ pr₁ ι p V'' = pullback.fst _ _ ≫ γ ι e := by simp
  have hπ₁₂ : π₁ ι p V'' ≫ pr₂ ι p V'' = pullback.snd (pr₂ ι p V'' ≫ pS ι p) (pS ι p) := by simp
  have hπ₁₁ : π₁ ι p V'' ≫ pr₁ ι p V'' = pullback.fst _ _ ≫ pr₁ ι p V'' := by simp
  have hΘδ : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) t) =
      (γ₁ ι e).appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply, Θ_tmul,
        ξ_tmul, map_mul, δ_apply]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hγ₁₂).hom) a)).symm
      · exact (congr(((Scheme.Hom.appTop $hγ₁₁).hom) x)).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hΘinc : ∀ t, Θ (Algebra.TensorProduct.map (AlgHom.id R A')
      (Algebra.TensorProduct.includeRight (R := R) (A := A') (B := E)) t) =
      (π₁ ι p V'').appTop (ξ t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
        Θ_tmul, ξ_tmul, ξ_tmul, map_one, one_mul, map_mul]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hπ₁₂).hom) a)).symm
      · exact (congr(((Scheme.Hom.appTop $hπ₁₁).hom) x)).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hcoassoc : ∀ x, Algebra.TensorProduct.map (AlgHom.id R A') (δ.restrictScalars R) (δ x) =
      Algebra.TensorProduct.map (AlgHom.id R A') Algebra.TensorProduct.includeRight (δ x) := by
    intro x
    apply Θ_inj
    rw [hΘδ, hΘinc, δ_apply]
    exact congr(((Scheme.Hom.appTop $(γ₁_γ ι e)).hom) x)
  -- the descent datum and the descended algebra
  let D : Algebra.DescentDatum R A' E := ⟨δ, hcounit, hcoassoc⟩
  let D₀ : Subalgebra R E := D.descended
  let ε : A' ⊗[R] D₀ ≃ₐ[A'] E := D.descendedEquiv
  have ε_tmul : ∀ (a : A') (x : D₀), ε (a ⊗ₜ x) = a • (x : E) := fun a x ↦ by
    change D.descendedEquiv (a ⊗ₜ x) = _
    rw [D.descendedEquiv_apply, D.descendedMap_tmul]
  -- the affine scheme `N = Spec D₀` and the pullback square `Spec E = N ×_S W`
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap R A'))
      (CommRingCat.ofHom (algebraMap R D₀)) (CommRingCat.ofHom (algebraMap A' E))
      (CommRingCat.ofHom (algebraMap D₀ E)) := by
    refine (CommRingCat.isPushout_tensorProduct R A' D₀).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ε.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext a
      simp [ε_tmul, Algebra.smul_def]
    · ext x
      simp [ε_tmul]
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hiso : IsPullback W.isoSpec.inv (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      (pS ι p) S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality (pS ι p)).symm⟩
  have hQ := hsq.paste_horiz hiso
  have hjw : (V V'').toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ W.isoSpec.inv =
      v V'' := by
    rw [← Category.assoc]
    change (V V'').toSpecΓ ≫ Spec.map (v V'').appTop ≫ W.isoSpec.inv = v V''
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨Spec (.of D₀), inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap R D₀)) ≫ S.isoSpec.inv,
    Spec.map (CommRingCat.ofHom (algebraMap D₀ E)),
    Spec.map (CommRingCat.ofHom (algebraMap A' E)) ≫ W.isoSpec.inv, hQ, hjw, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc (pr₁ ι p V''),
    Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  have hx := D.δ_of_mem_descended x.2
  have := δ_apply x
  rw [hx, ξ_tmul, map_one, one_mul] at this
  exact this.symm

end AffineDescent

section Final

variable {N : Scheme.{u}} {nS : N ⟶ S} {q : Spec Γ(V V'', ⊤) ⟶ N} {w : Spec Γ(V V'', ⊤) ⟶ W}

include ι in
lemma quasiSeparatedSpace_Y : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated ι

/-- Descent of the open `V'' ⊆ Spec Γ(V'')`: it is the preimage of its image in `N`. -/
lemma mem_range_toSpecΓ_of_eq (hQ : IsPullback w q (pS ι p) nS)
    (hjw : (V V'').toSpecΓ ≫ w = v V'')
    (hstar : γ ι e ≫ (V V'').toSpecΓ ≫ q = pr₁ ι p V'' ≫ (V V'').toSpecΓ ≫ q)
    (z : Spec Γ(V V'', ⊤)) (x : V V'') (h : q z = q ((V V'').toSpecΓ x)) :
    z ∈ Set.range (V V'').toSpecΓ := by
  set j := (V V'').toSpecΓ
  -- a point of the kernel pair of `q` over `(j x, z)`
  obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := q) (j x) z h.symm
  -- `P̂ = Spec E ×_S W`, with the two maps to `Spec E`
  have hwq : w ≫ pS ι p = q ≫ nS := hQ.w
  let φ' : pullback q q ⟶ pullback (w ≫ pS ι p) (pS ι p) :=
    pullback.lift (pullback.fst q q) (pullback.snd q q ≫ w) (by
      rw [hwq, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hwq])
  let t : pullback (w ≫ pS ι p) (pS ι p) ⟶ Spec Γ(V V'', ⊤) :=
    hQ.lift (pullback.snd _ _) (pullback.fst _ _ ≫ q) (by
      rw [Category.assoc, ← hwq, ← Category.assoc, pullback.condition])
  have ht₁ : t ≫ w = pullback.snd _ _ := hQ.lift_fst _ _ _
  have ht₂ : t ≫ q = pullback.fst _ _ ≫ q := hQ.lift_snd _ _ _
  have hφt : φ' ≫ t = pullback.snd q q := by
    apply hQ.hom_ext
    · rw [Category.assoc, ht₁, pullback.lift_snd]
    · rw [Category.assoc, ht₂, pullback.lift_fst_assoc, pullback.condition]
  -- the open immersion `P ⟶ P̂`
  let j' : P ι p V'' ⟶ pullback (w ≫ pS ι p) (pS ι p) :=
    pullback.map _ _ _ _ j (𝟙 W) (𝟙 S) (by simp [vS, ← hjw]) (by simp)
  have hj't : j' ≫ t = γ ι e ≫ j := by
    apply hQ.hom_ext
    · rw [Category.assoc, ht₁, Category.assoc, hjw, γ_v]
      simp [j']
    · rw [Category.assoc, ht₂, Category.assoc, hstar]
      simp [j']
  have hrange : Set.range j' = pullback.fst (w ≫ pS ι p) (pS ι p) ⁻¹' Set.range j := by
    rw [Scheme.Pullback.range_map]
    simp
  have hmem : φ' y ∈ Set.range j' := by
    rw [hrange, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, hy₁]
    exact ⟨x, rfl⟩
  obtain ⟨y₀, hy₀⟩ := hmem
  refine ⟨γ ι e y₀, ?_⟩
  rw [← hy₂, ← hφt, Scheme.Hom.comp_apply, ← hy₀]
  change (γ ι e ≫ j) y₀ = (j' ≫ t) y₀
  rw [hj't]

/-- From the affine descent data, produce the descended quasi-affine étale `Y`-scheme. -/
theorem exists_of_affine_descent [IsAffine N] (hQ : IsPullback w q (pS ι p) nS)
    (hjw : (V V'').toSpecΓ ≫ w = v V'')
    (hstar : γ ι e ≫ (V V'').toSpecΓ ≫ q = pr₁ ι p V'' ≫ (V V'').toSpecΓ ≫ q) :
    ∃ V₀ : Y.Etale, V₀.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V₀ ≅ Etale.mk g) := by
  have := quasiSeparatedSpace_Y ι
  set j := (V V'').toSpecΓ with hj
  have hq : AlgebraicGeometry.Etale q := MorphismProperty.of_isPullback hQ inferInstance
  -- the open `V₀ = q(V'') ⊆ N`
  let V₀ : N.Opens := ⟨q.base '' Set.range j.base, q.isOpenMap _ j.isOpenEmbedding.isOpen_range⟩
  have hpre : ((q ⁻¹ᵁ V₀ : (Spec Γ(V V'', ⊤)).Opens) : Set (Spec Γ(V V'', ⊤))) =
      Set.range j.base := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hz⟩
      exact mem_range_toSpecΓ_of_eq ι e hQ hjw hstar z x hz.symm
    · rintro ⟨x, rfl⟩
      exact ⟨j x, ⟨x, rfl⟩, rfl⟩
  let e₀ : V V'' ≅ (q ⁻¹ᵁ V₀).toScheme :=
    IsOpenImmersion.isoOfRangeEq j (q ⁻¹ᵁ V₀).ι (by rw [Scheme.Opens.range_ι, hpre])
  have he₀ : e₀.hom ≫ (q ⁻¹ᵁ V₀).ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let j₀ : V V'' ⟶ V₀.toScheme := e₀.hom ≫ q ∣_ V₀
  have hj₀ : j₀ ≫ V₀.ι = j ≫ q := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he₀]
  -- the pullback square `V'' = V₀ ×_S W`
  have hsqS : IsPullback (v V'') j₀ (pS ι p) (V₀.ι ≫ nS) := by
    have h₁ := (isPullback_morphismRestrict q V₀).paste_vert hQ.flip
    refine (h₁.of_iso e₀.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_).flip
    · simp [j₀]
    · simp [← hjw, ← he₀]
    · simp
    · simp
  -- the structure map `V₀ ⟶ Y`
  have hrange : Set.range (V₀.ι ≫ nS).base ⊆ Set.range ι.base := by
    rintro _ ⟨y₀, rfl⟩
    obtain ⟨_, ⟨x, rfl⟩, hy₀⟩ := y₀.2
    refine ⟨p (v V'' x), ?_⟩
    have h1 : (j ≫ q) x = V₀.ι y₀ := by rw [Scheme.Hom.comp_apply, hy₀]; rfl
    have h2 : (j ≫ q) ≫ nS = v V'' ≫ p ≫ ι := by
      rw [Category.assoc, ← hQ.w, ← Category.assoc, hjw]
    rw [Scheme.Hom.comp_apply, ← h1]
    change (v V'' ≫ p ≫ ι) x = ((j ≫ q) ≫ nS) x
    rw [h2]
  let vY : V₀.toScheme ⟶ Y := IsOpenImmersion.lift ι (V₀.ι ≫ nS) hrange
  have hvY : vY ≫ ι = V₀.ι ≫ nS := IsOpenImmersion.lift_fac _ _ _
  have hcomm : v V'' ≫ p = j₀ ≫ vY := by
    rw [← cancel_mono ι, Category.assoc, Category.assoc, hvY]
    exact hsqS.w
  -- the pullback square `V'' = V₀ ×_Y W`
  have hsqY : IsPullback (v V'') j₀ p vY := by
    refine IsPullback.of_bot (v₂₁ := 𝟙 _) (v₂₂ := ι) (h₃₁ := V₀.ι ≫ nS) ?_ hcomm
      (IsPullback.of_vert_isIso_mono ⟨by rw [hvY, Category.id_comp]⟩)
    simpa using hsqS
  -- `vY` is étale by fpqc descent along `p`
  have hetale : AlgebraicGeometry.Etale vY :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @AlgebraicGeometry.Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsqY
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      inferInstance
  have hcpt : CompactSpace V₀.toScheme :=
    isCompact_iff_compactSpace.mp ((isCompact_range j.continuous).image q.continuous)
  have hqa : V₀.toScheme.IsQuasiAffine := IsQuasiAffine.of_isImmersion V₀.ι
  let V₀' : Y.Etale := Etale.mk vY
  refine ⟨V₀', hqa, ⟨?_⟩⟩
  -- the isomorphism `V₀ ×_Y X ≅ U`, by descent along `W_X ⟶ X`
  let Z : Scheme.{u} := pullback vY f
  have hγj₀ : γ ι e ≫ j₀ = pr₁ ι p V'' ≫ j₀ := by
    have := hstar
    rw [← hj₀] at this
    rw [← cancel_mono V₀.ι, Category.assoc, Category.assoc]
    exact this
  have hcond : pullback.fst (π₀ p f) g ≫ π₀ p f = pullback.snd (π₀ p f) g ≫ g :=
    pullback.condition
  -- name the inverse isomorphism to avoid transparency issues
  let ê : U' p f g ⟶ PV p f V'' := e.inv.left
  let eh : PV p f V'' ⟶ U' p f g := e.hom.left
  have hê₁ : ê ≫ pullback.snd (v V'') (f₀ p f) = pullback.fst (π₀ p f) g := e_inv_left_snd e
  have hê₂ : ê ≫ eh = 𝟙 _ := e_inv_left_hom_left e
  have hê₃ : eh ≫ ê = 𝟙 _ := e_hom_left_inv_left e
  have hŨ : Ũ e = eh ≫ pullback.snd (π₀ p f) g := rfl
  have ha : a ι e = m₂ ι e ≫ ê := rfl
  clear_value ê eh
  let ψ₁ : U' p f g ⟶ V₀.toScheme := ê ≫ pullback.fst (v V'') (f₀ p f) ≫ j₀
  have hψ : ψ₁ ≫ vY = (pullback.fst (π₀ p f) g ≫ π₀ p f) ≫ f := by
    simp only [ψ₁, Category.assoc]
    rw [← hcomm, pullback.condition_assoc, ← Category.assoc ê, hê₁,
      pullback.condition (f := p) (g := f)]
  let ψ : U' p f g ⟶ Z := pullback.lift ψ₁ (pullback.fst (π₀ p f) g ≫ π₀ p f) hψ
  -- compatibility with the kernel pair of `U' ⟶ U`
  have hcompat : ∀ {T : Scheme.{u}} (g₁ g₂ : T ⟶ U' p f g),
      g₁ ≫ pullback.snd (π₀ p f) g = g₂ ≫ pullback.snd (π₀ p f) g → g₁ ≫ ψ = g₂ ≫ ψ := by
    intro T g₁ g₂ hg
    have hfst : g₁ ≫ pullback.fst (π₀ p f) g ≫ π₀ p f =
        g₂ ≫ pullback.fst (π₀ p f) g ≫ π₀ p f := by
      rw [hcond, ← Category.assoc, hg, Category.assoc]
    have hfst' := reassoc_of% hfst
    apply pullback.hom_ext
    · simp only [ψ, Category.assoc, pullback.lift_fst, ψ₁]
      -- the two `V`-coordinates are related by the coaction
      have hα : g₁ ≫ ê ≫ pullback.fst (v V'') (f₀ p f) ≫ v V'' =
          g₁ ≫ pullback.fst (π₀ p f) g ≫ f₀ p f := by
        rw [pullback.condition, ← Category.assoc ê, hê₁]
      have hα' := reassoc_of% hα
      have hθ : (g₁ ≫ ê ≫ pullback.fst (v V'') (f₀ p f)) ≫ vS ι p V'' =
          (g₂ ≫ pullback.fst (π₀ p f) g ≫ f₀ p f) ≫ pS ι p := by
        simp only [vS, pS, Category.assoc]
        rw [hα', pullback.condition_assoc (f := p) (g := f), hfst']
      let θ : T ⟶ P ι p V'' := pullback.lift _ _ hθ
      have hθζ : θ ≫ pr₂ ι p V'' = (g₂ ≫ pullback.fst (π₀ p f) g) ≫ f₀ p f := by
        simp [θ]
      have h₁ : liftPV ι θ (g₂ ≫ pullback.fst (π₀ p f) g) hθζ = g₁ ≫ ê := by
        apply pullback.hom_ext
        · simp [θ]
        · rw [pullback.lift_snd, Category.assoc, hê₁]
          apply pullback.hom_ext
          · simp only [pullback.lift_fst, Category.assoc, θ, pullback.lift_fst_assoc]
            exact hα
          · simp only [pullback.lift_snd, Category.assoc]
            exact hfst.symm
      have h₂ : pullback.lift θ (g₂ ≫ pullback.fst (π₀ p f) g) hθζ ≫ m₂ ι e = g₂ := by
        rw [lift_m₂ ι e θ _ hθζ]
        apply pullback.hom_ext
        · simp
        · rw [pullback.lift_snd, h₁, Category.assoc, hŨ, ← Category.assoc ê, hê₂,
            Category.id_comp, hg]
      have h₃ : pullback.lift (θ ≫ γ ι e) (g₂ ≫ pullback.fst (π₀ p f) g)
          (by rw [Category.assoc, γ_v, hθζ]) = g₂ ≫ ê := by
        rw [← lift_a ι e θ _ hθζ, ha, ← Category.assoc, h₂]
      have h₄ : θ ≫ γ ι e = g₂ ≫ ê ≫ pullback.fst (v V'') (f₀ p f) := by
        rw [← Category.assoc, ← h₃, pullback.lift_fst]
      rw [← reassoc_of% h₄, hγj₀]
      simp [θ]
    · simp only [ψ, Category.assoc, pullback.lift_snd]
      exact hfst
  -- descend `ψ` along the effective epimorphism `U' ⟶ U`
  have : QuasiCompact (π₀ p f) := inferInstance
  have : Surjective (π₀ p f) := inferInstance
  have : Flat (π₀ p f) := inferInstance
  let φ : U ⟶ Z := EffectiveEpi.desc (pullback.snd (π₀ p f) g) ψ hcompat
  have hφψ : pullback.snd (π₀ p f) g ≫ φ = ψ := EffectiveEpi.fac _ _ _
  have hφ : φ ≫ pullback.snd vY f = g := by
    rw [← cancel_epi (pullback.snd (π₀ p f) g), ← Category.assoc, hφψ]
    simp only [ψ, pullback.lift_snd]
    exact hcond
  -- `φ` is an isomorphism, by fpqc descent along `W_X ⟶ X`
  let ρ : PV p f V'' ⟶ Z := pullback.lift (pullback.fst (v V'') (f₀ p f) ≫ j₀)
    (pullback.snd (v V'') (f₀ p f) ≫ π₀ p f) (by
      rw [Category.assoc, ← hcomm, pullback.condition_assoc, Category.assoc,
        pullback.condition (f := p) (g := f)])
  have hρ : IsPullback ρ (pullback.snd (v V'') (f₀ p f)) (pullback.snd vY f) (π₀ p f) := by
    have h₁ := ((IsPullback.of_hasPullback (v V'') (f₀ p f)).flip.paste_vert hsqY).flip
    rw [pullback.condition (f := p) (g := f)] at h₁
    have h₂ : ρ ≫ pullback.fst vY f = pullback.fst (v V'') (f₀ p f) ≫ j₀ :=
      pullback.lift_fst _ _ _
    rw [← h₂] at h₁
    exact IsPullback.of_right h₁ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback vY f)
  have hQρ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) ρ :=
    MorphismProperty.of_isPullback hρ.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsq' : IsPullback ê (pullback.snd (π₀ p f) g) ρ φ := by
    refine IsPullback.of_right ?_ ?_ hρ.flip
    · rw [hê₁, hφ]
      exact IsPullback.of_hasPullback _ _
    · rw [hφψ]
      apply pullback.hom_ext
      · simp [ρ, ψ, ψ₁]
      · simp only [ρ, ψ, Category.assoc, pullback.lift_snd]
        rw [← Category.assoc, hê₁]
  have hφiso : IsIso φ :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq' hQρ
      (show IsIso ê from ⟨eh, hê₂, hê₃⟩)
  exact (MorphismProperty.Over.isoMk (asIso φ) hφ).symm

end Final

/-- **Descent along an étale cover** of quasi-affine étale schemes, with the canonical descent
datum coming from a universal homeomorphism: if `U ×_X W_X` is the base change of a quasi-affine
étale `W`-scheme, then `U` is the base change of a quasi-affine étale `Y`-scheme. Here `Y` is
embedded into the affine scheme `S` by the open immersion `ι`. -/
theorem exists_isQuasiAffine_etale_obj_iso (ι : Y ⟶ S) [IsOpenImmersion ι]
    (e : (pullback.fst p f).Etale.obj V'' ≅ Etale.mk (pullback.fst (pullback.snd p f) g)) :
    ∃ V₀ : Y.Etale, V₀.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V₀ ≅ Etale.mk g) := by
  obtain ⟨N, _, nS, q, w, hQ, hjw, hstar⟩ := exists_affine_descent ι e
  exact exists_of_affine_descent ι e hQ hjw hstar

end Scheme.Hom.EtaleDescent

/-- **Descent along an étale cover** of quasi-affine étale schemes, with the canonical descent
datum coming from a universal homeomorphism `f : X ⟶ Y`. Let `Y` be quasi-affine, `p : W ⟶ Y` an
étale surjection from an affine scheme, `g : U ⟶ X` étale, and `V''` a quasi-affine
étale `W`-scheme with `V'' ×_W W_X ≅ U ×_X W_X` over `W_X = W ×_Y X`. Then there is a
quasi-affine étale `Y`-scheme `V` with `V ×_Y X ≅ U` over `X`. -/
theorem Scheme.Hom.exists_isQuasiAffine_etale_obj_iso_of_etale_cover
    {Y W X U : Scheme.{u}} [IsAffine W] [Y.IsQuasiAffine]
    (p : W ⟶ Y) [AlgebraicGeometry.Etale p] [Surjective p] (f : X ⟶ Y)
    [IsUniversalHomeomorphism f] (g : U ⟶ X) [AlgebraicGeometry.Etale g]
    (V'' : W.Etale) [V''.left.IsQuasiAffine]
    (e : (pullback.fst p f).Etale.obj V'' ≅ Etale.mk (pullback.fst (pullback.snd p f) g)) :
    ∃ V : Y.Etale, V.left.IsQuasiAffine ∧ Nonempty (f.Etale.obj V ≅ Etale.mk g) :=
  Scheme.Hom.EtaleDescent.exists_isQuasiAffine_etale_obj_iso Y.toSpecΓ e

end AlgebraicGeometry

end
