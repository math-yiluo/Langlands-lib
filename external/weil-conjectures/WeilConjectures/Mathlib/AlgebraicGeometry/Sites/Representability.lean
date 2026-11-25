/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Representability of sheaves on `Sch/S` is a local property

Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` shows that a
`Type u`-valued Zariski sheaf on `Scheme.{u}` which is covered by relatively representable open
immersions `yoneda.obj (X i) ⟶ F` is representable (Stacks, Lemma 01JJ). This file proves the
relative version over a base scheme `S`: for a Zariski sheaf `P` on `Over S` with values in an
arbitrary universe, but with `u`-small values.

The proof reduces to Mathlib's statement. To `P` we attach the presheaf of `Type u` on
`Scheme.{u}`
`sigmaOver P : T ↦ Σ s : T ⟶ S, P(T, s)`,
show that it is a Zariski sheaf, that the elements `ξ i ∈ P(X i)` give relatively representable
open immersions `yoneda.obj (X i).left ⟶ sigmaOver P` which are jointly locally surjective, and
that a scheme representing `sigmaOver P` gives an `S`-scheme representing `P`.

## Main definitions

- `AlgebraicGeometry.Scheme.LocalRepresentability.sigmaOver`: the presheaf
  `T ↦ Σ s : T ⟶ S, P(T, s)` on `Scheme.{u}`.
- `AlgebraicGeometry.ZariskiCovers`: a family of subfunctors of a presheaf on `Over S` covers it
  (Stacks, Definition 01JI).

## Main statements

- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over`: a Zariski
  sheaf on `Over S` with small values, covered by open subfunctors which are representable, is
  representable (Stacks, Lemma 01JJ, over a base).
- `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over_of_isAffine`:
  the same statement, with the hypotheses only tested on affine schemes.
- `AlgebraicGeometry.exists_opens_of_relative_isOpenImmersion`: a subfunctor `F ⊆ P` which is
  representable by open immersions (in the sense of `MorphismProperty.relative` for
  `uliftYoneda`) is cut out, over every `T` and `x ∈ P(T)`, by an open subscheme of `T`.
- `AlgebraicGeometry.isRepresentable_of_isSheaf_of_zariskiCovers`: a Zariski sheaf on `Over S`
  with small values, covered by representable subfunctors which are representable by open
  immersions, is representable (Stacks, Lemma 01JJ, in the form of Definition 01JI).

## Implementation notes

The hypotheses of `isRepresentable_of_isSheaf_over` are stated concretely, in the form of
Stacks, Definition 01JI: the family `ξ i ∈ P(X i)` is "injective" (`h_{X i} ⟶ P` is a
monomorphism), the locus where an element of `P(T)` comes from `X i` is an open subscheme of
`T`, and every point of every `T` lies in such a locus.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type w) [∀ T, Small.{u} (P.obj T)]

/-- The element of `Σ s : T ⟶ S, P(T, s)` obtained by pulling back `y ∈ P(Y)` along
`a : T ⟶ Y.left`. -/
noncomputable def sigmaOverMk {T : Scheme.{u}} {Y : Over S} (a : T ⟶ Y.left)
    (y : P.obj (op Y)) : Σ s : T ⟶ S, Shrink.{u} (P.obj (op (Over.mk s))) :=
  ⟨a ≫ Y.hom, equivShrink _ (P.map (Over.homMk a rfl : Over.mk (a ≫ Y.hom) ⟶ Y).op y)⟩

/-- Two elements `⟨s, x⟩` and `⟨s', x'⟩` of `Σ s : T ⟶ S, P(T, s)` agree if and only if
`s = s'` and `x` corresponds to `x'` under the identification `Over.mk s ≅ Over.mk s'`. -/
lemma sigma_mk_eq_iff {T : Scheme.{u}} {s s' : T ⟶ S} (x : P.obj (op (Over.mk s)))
    (x' : P.obj (op (Over.mk s'))) :
    (⟨s, equivShrink _ x⟩ : Σ s : T ⟶ S, Shrink.{u} (P.obj (op (Over.mk s)))) =
      ⟨s', equivShrink _ x'⟩ ↔ ∃ h : s = s',
        x = P.map (Over.homMk (𝟙 T) (by simp [h]) : Over.mk s ⟶ Over.mk s').op x' := by
  constructor
  · intro h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    refine ⟨rfl, ?_⟩
    rw [show (Over.homMk (𝟙 T) (by simp) : Over.mk s ⟶ Over.mk s) = 𝟙 _ by ext; simp]
    simpa using (equivShrink _).injective (eq_of_heq h)
  · rintro ⟨rfl, rfl⟩
    rw [show (Over.homMk (𝟙 T) (by simp) : Over.mk s ⟶ Over.mk s) = 𝟙 _ by ext; simp]
    simp

/-- The pullbacks of `y ∈ P(Y)` along `a` and of `y' ∈ P(Y')` along `a'` agree if and only
if they agree as elements of `P(W)`, for any `W : Over S` with underlying scheme `T` over which
`a` and `a'` are morphisms over `S`. -/
lemma sigmaOverMk_eq_iff {W Y Y' : Over S} (a : W.left ⟶ Y.left) (a' : W.left ⟶ Y'.left)
    (ha : a ≫ Y.hom = W.hom) (ha' : a' ≫ Y'.hom = W.hom)
    (y : P.obj (op Y)) (y' : P.obj (op Y')) :
    sigmaOverMk P a y = sigmaOverMk P a' y' ↔
      P.map (Over.homMk a ha).op y = P.map (Over.homMk a' ha').op y' := by
  rw [sigmaOverMk, sigmaOverMk, sigma_mk_eq_iff]
  let i : W ⟶ Over.mk (a ≫ Y.hom) := Over.homMk (𝟙 W.left) (by simp [ha])
  let j : Over.mk (a ≫ Y.hom) ⟶ W := Over.homMk (𝟙 W.left) (by simp [ha])
  have hij : j ≫ i = 𝟙 _ := by ext; simp [i, j]
  have e₁ : (Over.homMk a ha : W ⟶ Y) = i ≫ Over.homMk a rfl := by ext; simp [i]
  have e₂ : (Over.homMk a' ha' : W ⟶ Y') = i ≫
      (Over.homMk (𝟙 W.left) (by simp [ha, ha']) :
        Over.mk (a ≫ Y.hom) ⟶ Over.mk (a' ≫ Y'.hom)) ≫
        Over.homMk a' rfl := by ext; simp [i]
  rw [e₁, e₂]
  simp only [op_comp, Functor.map_comp_apply]
  constructor
  · rintro ⟨h, h'⟩
    rw [h']
  · intro h
    refine ⟨by rw [ha, ha'], ?_⟩
    have key : ∀ z, P.map j.op (P.map i.op z) = z := by
      intro z
      rw [← Functor.map_comp_apply, ← op_comp, hij, op_id, Functor.map_id_apply]
    have := congrArg (P.map j.op) h
    rwa [key, key] at this

/-- Every element of `Σ s : T ⟶ S, P(T, s)` is of the form `sigmaOverMk P (𝟙 T) y`. -/
lemma sigmaOverMk_id {T : Scheme.{u}} (x : Σ s : T ⟶ S, Shrink.{u} (P.obj (op (Over.mk s)))) :
    sigmaOverMk P (Y := Over.mk x.1) (𝟙 T) ((equivShrink _).symm x.2) = x := by
  obtain ⟨s, x⟩ := x
  obtain ⟨x, rfl⟩ := (equivShrink _).surjective x
  rw [sigmaOverMk, Equiv.symm_apply_apply, sigma_mk_eq_iff]
  exact ⟨by simp, rfl⟩

/-- Pulling back an element `sigmaOverMk P a y` further along `b`. -/
lemma sigmaOverMk_comp {T T' : Scheme.{u}} {Y : Over S} (b : T' ⟶ T) (a : T ⟶ Y.left)
    (y : P.obj (op Y)) :
    sigmaOverMk P (Y := Over.mk (a ≫ Y.hom)) b
      ((equivShrink _).symm (sigmaOverMk P a y).2) = sigmaOverMk P (b ≫ a) y := by
  rw [sigmaOverMk_eq_iff P (W := Over.mk (b ≫ a ≫ Y.hom)) _ _ rfl (by simp)]
  simp only [sigmaOverMk, Equiv.symm_apply_apply]
  rw [← Functor.map_comp_apply, ← op_comp]
  congr 3

/-- The presheaf `T ↦ Σ s : T ⟶ S, P(T, s)` on the category of schemes attached to a presheaf
`P` on `Over S` with small values. -/
@[simps obj]
noncomputable def sigmaOver : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Σ s : T.unop ⟶ S, Shrink.{u} (P.obj (op (Over.mk s)))
  map a := ↾fun x ↦ sigmaOverMk P (Y := Over.mk x.1) a.unop ((equivShrink _).symm x.2)
  map_id T := by
    ext x : 3
    exact sigmaOverMk_id P x
  map_comp {T T' T''} a b := by
    ext x : 3
    obtain ⟨s, x⟩ := x
    obtain ⟨x, rfl⟩ := (equivShrink _).surjective x
    dsimp
    rw [Equiv.symm_apply_apply]
    exact (sigmaOverMk_comp P (Y := Over.mk s) b.unop a.unop x).symm

/-- The restriction maps of `sigmaOver P` on the elements `sigmaOverMk P a y`. -/
lemma sigmaOver_map_sigmaOverMk {T T' : Scheme.{u}} {Y : Over S} (b : T' ⟶ T) (a : T ⟶ Y.left)
    (y : P.obj (op Y)) :
    (sigmaOver P).map b.op (sigmaOverMk P a y) = sigmaOverMk P (b ≫ a) y :=
  sigmaOverMk_comp P b a y

/-- Pulling back `P.map g.op z` along `a` is pulling back `z` along `a ≫ g.left`. -/
lemma sigmaOverMk_map {T : Scheme.{u}} {W Z : Over S} (a : T ⟶ W.left) (g : W ⟶ Z)
    (z : P.obj (op Z)) :
    sigmaOverMk P a (P.map g.op z) = sigmaOverMk P (a ≫ g.left) z := by
  rw [sigmaOverMk_eq_iff P (W := Over.mk (a ≫ W.hom)) _ _ rfl (by simp)]
  rw [← Functor.map_comp_apply, ← op_comp]
  congr 3

/-- An element of `P(Y)` is determined by its image in `sigmaOver P` over `Y.left`. -/
lemma sigmaOverMk_injective {Y : Over S} :
    Function.Injective (sigmaOverMk P (𝟙 Y.left) : P.obj (op Y) → _) := by
  intro y y' h
  rw [sigmaOverMk_eq_iff P (W := Y) _ _ (by simp) (by simp)] at h
  have e : (Over.homMk (𝟙 Y.left) (by simp) : Y ⟶ Y) = 𝟙 Y := by ext; simp
  simpa [e] using h

/-- An element `q` of `sigmaOver P` over `Z.left` whose structure morphism is `Z.hom`, viewed as
an element of `P(Z)`. -/
noncomputable def toObj {Z : Over S} (q : (sigmaOver P).obj (op Z.left)) (hq : q.1 = Z.hom) :
    P.obj (op Z) :=
  P.map (Over.homMk (𝟙 Z.left) (by simp [hq]) : Z ⟶ Over.mk q.1).op ((equivShrink _).symm q.2)

/-- `toObj` is a section of `sigmaOverMk P (𝟙 Z.left)`. -/
lemma sigmaOverMk_toObj {Z : Over S} (q : (sigmaOver P).obj (op Z.left)) (hq : q.1 = Z.hom) :
    sigmaOverMk P (𝟙 Z.left) (toObj P q hq) = q := by
  rw [toObj, sigmaOverMk_map]
  conv_rhs => rw [← sigmaOverMk_id P q]
  rw [sigmaOverMk_eq_iff P (W := Z) _ _ (by simp [hq]) (by simp [hq])]
  congr 3

/-- If `P` is a Zariski sheaf on `Over S`, then `sigmaOver P` is a Zariski sheaf on schemes. -/
theorem isSheaf_sigmaOver (hP : Presheaf.IsSheaf (zariskiTopology.over S) P) :
    Presheaf.IsSheaf zariskiTopology (sigmaOver P) := by
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  intro T R hR x hx
  have hS : Presieve.IsSheaf zariskiTopology (yoneda.obj S) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (zariskiTopology.yoneda.obj S).property
  let xS : Presieve.FamilyOfElements (yoneda.obj S) R.arrows := fun V f hf ↦ (x f hf).1
  have hxS : xS.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    exact congr_arg Sigma.fst (hx g₁ g₂ h₁ h₂ e)
  obtain ⟨s, hs, hs'⟩ := hS R hR xS hxS
  replace hs : ∀ (V : Scheme.{u}) (f : V ⟶ T) (hf : R f), f ≫ s = (x f hf).1 := hs
  let R' := (Sieve.overEquiv (Over.mk s)).symm R
  have hR' : R' ∈ zariskiTopology.over S (Over.mk s) :=
    GrothendieckTopology.overEquiv_symm_mem_over _ _ _ hR
  have hR'iff {Z : Over S} (g : Z ⟶ Over.mk s) : R'.arrows g ↔ R g.left :=
    Sieve.overEquiv_symm_iff _ _
  let y : Presieve.FamilyOfElements P R'.arrows := fun Z g hg ↦
    toObj P (x g.left ((hR'iff g).1 hg)) (by rw [← hs]; exact Over.w g)
  have hy (Z : Over S) (g : Z ⟶ Over.mk s) (hg : R'.arrows g) :
      sigmaOverMk P (𝟙 Z.left) (y g hg) = x g.left ((hR'iff g).1 hg) :=
    sigmaOverMk_toObj _ _ _
  have hyc : y.Compatible := by
    intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    apply sigmaOverMk_injective P
    rw [sigmaOverMk_map, sigmaOverMk_map, Category.id_comp, Category.id_comp,
      ← Category.comp_id g₁.left, ← Category.comp_id g₂.left,
      ← sigmaOver_map_sigmaOverMk, ← sigmaOver_map_sigmaOverMk, hy _ _ h₁, hy _ _ h₂]
    exact hx _ _ _ _ (congr_arg CommaMorphism.left e)
  obtain ⟨t, ht, ht'⟩ := hP R' hR' y hyc
  refine ⟨sigmaOverMk P (Y := Over.mk s) (𝟙 T) t, ?_, ?_⟩
  · intro V f hf
    have hg : R'.arrows (Over.homMk f rfl : Over.mk (f ≫ s) ⟶ Over.mk s) := (hR'iff _).2 hf
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
    refine Eq.trans ?_ (hy _ _ hg)
    rw [← ht _ hg, sigmaOverMk_map, Category.id_comp]
    rfl
  · intro q hq
    have h₁ : q.1 = s := hs' q.1 (fun V f hf ↦ congr_arg Sigma.fst (hq f hf))
    rw [← sigmaOverMk_toObj P (Z := Over.mk s) q h₁]
    congr 1
    refine ht' _ (fun Z g hg ↦ sigmaOverMk_injective P ?_)
    rw [hy _ _ hg, sigmaOverMk_map, Category.id_comp]
    refine Eq.trans (b := (sigmaOver P).map g.left.op
      (sigmaOverMk P (Y := Over.mk s) (𝟙 _) (toObj P (Z := Over.mk s) q h₁))) ?_ ?_
    · rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
    · rw [sigmaOverMk_toObj]
      exact hq _ _

section

variable {P} {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))

/-- The morphism `h_{X i} ⟶ sigmaOver P` classifying the element `ξ i`. -/
noncomputable def toSigmaOver (i : ι) : yoneda.obj (X i).left ⟶ sigmaOver P :=
  yonedaEquiv.symm (sigmaOverMk P (𝟙 (X i).left) (ξ i))

/-- The components of `toSigmaOver`. -/
lemma toSigmaOver_app {V : Scheme.{u}} (i : ι) (e : V ⟶ (X i).left) :
    (toSigmaOver X ξ i).app (op V) e = sigmaOverMk P e (ξ i) := by
  change (sigmaOver P).map e.op (sigmaOverMk P (𝟙 (X i).left) (ξ i)) = _
  rw [sigmaOver_map_sigmaOverMk, Category.comp_id]

variable {X ξ}

/-- If the locus where `y ∈ P(T)` comes from `X i` is the open `U`, then the pullback of
`toSigmaOver X ξ i` along the morphism classifying `y` is represented by `U`. -/
lemma exists_isPullback_toSigmaOver
    (hinj : ∀ i {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    {i : ι} {T : Over S} {y : P.obj (op T)} {U : T.left.Opens}
    (hU : ∀ (W : Over S) (a : W ⟶ T),
      (∃ b : W ⟶ X i, P.map a.op y = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U) :
    ∃ c : (U : Scheme.{u}) ⟶ (X i).left, ∀ (V : Scheme.{u}) (e : V ⟶ (X i).left)
      (a : V ⟶ T.left), sigmaOverMk P e (ξ i) = sigmaOverMk P a y ↔
        ∃ d : V ⟶ U, d ≫ c = e ∧ d ≫ U.ι = a := by
  obtain ⟨b₀, hb₀⟩ := (hU (Over.mk (U.ι ≫ T.hom)) (Over.homMk U.ι rfl)).2
    (by simp [Scheme.Opens.range_ι])
  refine ⟨b₀.left, fun V e a ↦ ?_⟩
  -- the key computation: pulling back along `d`
  have key (W : Over S) (d : W.left ⟶ U) (hd : d ≫ U.ι ≫ T.hom = W.hom) :
      P.map (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀, hd]) : W ⟶ X i).op (ξ i) =
        P.map (Over.homMk (d ≫ U.ι) (by simp [hd]) : W ⟶ T).op y := by
    have e₁ : (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀, hd]) : W ⟶ X i) =
        (Over.homMk d (by simp [hd]) : W ⟶ Over.mk (U.ι ≫ T.hom)) ≫ b₀ := by ext; simp
    have e₂ : (Over.homMk (d ≫ U.ι) (by simp [hd]) : W ⟶ T) =
        (Over.homMk d (by simp [hd]) : W ⟶ Over.mk (U.ι ≫ T.hom)) ≫
          Over.homMk U.ι rfl := by ext; simp
    rw [e₁, e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hb₀]
  constructor
  · intro h
    have h₁ : e ≫ (X i).hom = a ≫ T.hom := congr_arg Sigma.fst h
    rw [sigmaOverMk_eq_iff P (W := Over.mk (a ≫ T.hom)) _ _ h₁ rfl] at h
    have hr : Set.range a ⊆ U := (hU (Over.mk (a ≫ T.hom)) (Over.homMk a rfl)).1 ⟨_, h.symm⟩
    let d := IsOpenImmersion.lift U.ι a (by rwa [Scheme.Opens.range_ι])
    have hd : d ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
    refine ⟨d, ?_, hd⟩
    have := key (Over.mk (a ≫ T.hom)) d (by simp [← hd])
    have e₃ : (Over.homMk (d ≫ U.ι) (by simp [hd]) : Over.mk (a ≫ T.hom) ⟶ T) =
        Over.homMk a rfl := by ext; simp [hd]
    rw [e₃, ← h] at this
    exact congr_arg CommaMorphism.left (hinj i _ _ this)
  · rintro ⟨d, rfl, rfl⟩
    rw [sigmaOverMk_eq_iff P (W := Over.mk (d ≫ U.ι ≫ T.hom)) _ _ (by simp [Over.w b₀])
      (by simp)]
    exact key (Over.mk (d ≫ U.ι ≫ T.hom)) d rfl

end

/-- If `sigmaOver P` is representable, then so is `P`. -/
lemma isRepresentable_of_isRepresentable_sigmaOver [(sigmaOver P).IsRepresentable] :
    P.IsRepresentable := by
  obtain ⟨Y, ⟨e⟩⟩ := Functor.IsRepresentable.has_representation (F := sigmaOver P)
  set u := e.homEquiv (𝟙 Y)
  let A : Over S := Over.mk u.1
  let y₀ : P.obj (op A) := (equivShrink _).symm u.2
  have he {T : Scheme.{u}} (a : T ⟶ Y) : e.homEquiv a = sigmaOverMk P (Y := A) a y₀ := by
    rw [← Category.comp_id a, e.homEquiv_comp]
    refine (congr_arg ((sigmaOver P).map a.op) (sigmaOverMk_id P u).symm).trans ?_
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
  have hbij (W : Over S) : Function.Bijective (fun a : W ⟶ A ↦ P.map a.op y₀) := by
    refine ⟨fun a b h ↦ ?_, fun z ↦ ?_⟩
    · have h' : sigmaOverMk P a.left y₀ = sigmaOverMk P b.left y₀ :=
        (sigmaOverMk_eq_iff P (W := W) _ _ (Over.w a) (Over.w b) _ _).2 h
      rw [← he, ← he] at h'
      exact Over.OverMorphism.ext (e.homEquiv.injective h')
    · have hq := e.homEquiv.apply_symm_apply (sigmaOverMk P (𝟙 W.left) z)
      rw [he] at hq
      have h₁ : e.homEquiv.symm (sigmaOverMk P (𝟙 W.left) z) ≫ A.hom = W.hom := by
        simpa [sigmaOverMk] using congr_arg Sigma.fst hq
      refine ⟨Over.homMk _ h₁, ?_⟩
      replace hq := (sigmaOverMk_eq_iff P (W := W) _ _ h₁ (by simp) _ _).1 hq
      have e₁ : (Over.homMk (𝟙 W.left) (by simp) : W ⟶ W) = 𝟙 W := by ext; simp
      simpa [e₁] using hq
  exact ⟨A, ⟨{
    homEquiv := Equiv.ofBijective _ (hbij _)
    homEquiv_comp := fun f a ↦ by simp }⟩⟩

/-- **Representability is local, over a base.** Let `P` be a Zariski sheaf on `Over S` with
`u`-small values, and let `ξ i ∈ P(X i)` be a family of elements such that

* the induced maps `h_{X i} ⟶ P` are injective;
* for every `T` and `x ∈ P(T)` there is an open `U ⊆ T` such that a morphism `a : W ⟶ T`
  factors through `U` if and only if `a^* x` is the pullback of `ξ i` along some
  `W ⟶ X i`;
* every point `t` of every `T` lies in such an open for some `i`.

Then `P` is representable. This is Stacks, Lemma 01JJ, for schemes over `S`; it is deduced from
Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`. -/
theorem isRepresentable_of_isSheaf_over (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (hcov : ∀ (T : Over S) (x : P.obj (op T)) (t : T.left),
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i)) :
    P.IsRepresentable := by
  let F : Sheaf zariskiTopology (Type u) := ⟨sigmaOver P, isSheaf_sigmaOver P hP⟩
  let f : (i : ι) → yoneda.obj (X i).left ⟶ F.obj := toSigmaOver X ξ
  -- the open subscheme of `T` over which `x` comes from `X i`
  have hpb (i : ι) (T : Scheme.{u}) (x : (sigmaOver P).obj (op T)) :
      ∃ (U : T.Opens) (c : (U : Scheme.{u}) ⟶ (X i).left),
        (∀ (V : Scheme.{u}) (e : V ⟶ (X i).left) (a : V ⟶ T),
          (f i).app (op V) e = (sigmaOver P).map a.op x ↔
            ∃ d : V ⟶ U, d ≫ c = e ∧ d ≫ U.ι = a) ∧
        ∀ t : T, (∃ (W : Over S) (a : W ⟶ Over.mk x.1) (b : W ⟶ X i),
          t ∈ Set.range a.left ∧ P.map a.op ((equivShrink _).symm x.2) = P.map b.op (ξ i)) →
            t ∈ U := by
    obtain ⟨U, hU⟩ := hopen i (Over.mk x.1) ((equivShrink _).symm x.2)
    obtain ⟨c, hc⟩ := exists_isPullback_toSigmaOver hinj hU
    refine ⟨U, c, fun V e a ↦ ?_, fun t ⟨W, a, b, ht, h⟩ ↦ (hU W a).1 ⟨b, h⟩ ht⟩
    rw [toSigmaOver_app, ← hc V e a]
    conv_lhs => rw [← sigmaOverMk_id P x]
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
  have hf (i : ι) : IsOpenImmersion.presheaf (f i) := by
    refine MorphismProperty.relative.of_exists (fun T g ↦ ?_)
    obtain ⟨U, c, hc, -⟩ := hpb i T (yonedaEquiv g)
    refine ⟨U, yoneda.map c, U.ι, IsPullback.of_forall_isPullback_app (fun V ↦ ?_),
      inferInstance⟩
    rw [Types.isPullback_iff]
    refine ⟨?_, fun d d' ⟨_, h⟩ ↦ (cancel_mono U.ι).1 h, fun e a h ↦ ?_⟩
    · ext d : 3
      change (f i).app V (d ≫ c) = g.app V (d ≫ U.ι)
      rw [← map_yonedaEquiv g]
      exact (hc V.unop _ _).2 ⟨d, rfl, rfl⟩
    · replace h : (f i).app V e = g.app V a := h
      rw [← map_yonedaEquiv g] at h
      exact (hc V.unop e a).1 h
  have : Presheaf.IsLocallySurjective zariskiTopology (Sigma.desc f) := by
    refine ⟨fun {T} x ↦ ?_⟩
    have H (t : T) : ∃ (i : ι) (U : T.Opens) (c : (U : Scheme.{u}) ⟶ (X i).left),
        t ∈ U ∧ (f i).app (op U) c = (sigmaOver P).map U.ι.op x := by
      obtain ⟨i, W, a, b, ht, h⟩ := hcov (Over.mk x.1) ((equivShrink _).symm x.2) t
      obtain ⟨U, c, hc, hU⟩ := hpb i T x
      exact ⟨i, U, c, hU t ⟨W, a, b, ht, h⟩, (hc _ _ _).2 ⟨𝟙 _, by simp, by simp⟩⟩
    choose i U c ht hc using H
    rw [mem_grothendieckTopology_iff]
    refine ⟨Scheme.Cover.mkOfCovers T (fun t ↦ (U t : Scheme.{u})) (fun t ↦ (U t).ι)
      (fun t ↦ ⟨t, by
        have h : t ∈ Set.range (U t).ι := by rw [Scheme.Opens.range_ι]; exact ht t
        exact h⟩), ?_⟩
    rintro V g ⟨t⟩
    refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (X i).left) (i t)).app _ (c t), ?_⟩
    refine Eq.trans ?_ (hc t)
    exact congr_arg
      (fun φ : yoneda.obj (X (i t)).left ⟶ F.obj ↦ φ.app (op (U t : Scheme)) (c t))
      (Sigma.ι_comp_desc f (i t))
  have := Scheme.LocalRepresentability.isRepresentable (F := F) hf
  exact isRepresentable_of_isRepresentable_sigmaOver P

section Affine

variable {P} {ι : Type u} {X : ι → Over S} {ξ : ∀ i, P.obj (op (X i))}

/-- The pullback of `x ∈ P(T)` along `a : W ⟶ T` comes from `X i` if and only if the
corresponding element of `sigmaOver P` comes from `X i`. -/
lemma exists_map_eq_iff_exists_sigmaOverMk_eq {W T : Over S} (a : W ⟶ T) (x : P.obj (op T))
    (i : ι) : (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔
      ∃ c : W.left ⟶ (X i).left, sigmaOverMk P a.left x = sigmaOverMk P c (ξ i) := by
  constructor
  · rintro ⟨b, h⟩
    exact ⟨b.left, (sigmaOverMk_eq_iff P (W := W) _ _ (Over.w a) (Over.w b) _ _).2 h⟩
  · rintro ⟨c, h⟩
    have hc : c ≫ (X i).hom = W.hom := by
      rw [← Over.w a]
      exact (congr_arg Sigma.fst h).symm
    exact ⟨Over.homMk c hc, (sigmaOverMk_eq_iff P (W := W) _ _ (Over.w a) hc _ _).1 h⟩

/-- If the maps `h_{X i} ⟶ P` are injective on affine schemes, then the maps
`toSigmaOver X ξ i` are injective on all schemes. -/
lemma eq_of_sigmaOverMk_eq
    (hinj : ∀ i {T : Over S} [IsAffine T.left] (a b : T ⟶ X i),
      P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    {i : ι} {T : Scheme.{u}} {c c' : T ⟶ (X i).left}
    (h : sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i)) : c = c' := by
  refine T.affineCover.hom_ext _ _ fun j ↦ ?_
  have h' := congr_arg ((sigmaOver P).map (T.affineCover.f j).op) h
  rw [sigmaOver_map_sigmaOverMk, sigmaOver_map_sigmaOverMk] at h'
  have h₁ : (T.affineCover.f j ≫ c') ≫ (X i).hom = (T.affineCover.f j ≫ c) ≫ (X i).hom :=
    (congr_arg Sigma.fst h').symm
  rw [sigmaOverMk_eq_iff P (W := Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom)) _ _ rfl h₁]
    at h'
  have : IsAffine (Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom)).left := by
    dsimp
    infer_instance
  exact congr_arg CommaMorphism.left (hinj i _ _ h')

/-- **Gluing lifts along `toSigmaOver`.** If `P` is a Zariski sheaf and the maps
`toSigmaOver X ξ i` are injective, then an element of `sigmaOver P` over `T` comes from `X i`
as soon as its restrictions to the members of an open cover of `T` do. -/
lemma exists_sigmaOverMk_eq_of_openCover (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ i {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i) → c = c')
    {i : ι} {T : Scheme.{u}} (s : (sigmaOver P).obj (op T))
    (𝒰 : Scheme.OpenCover.{u} T)
    (h : ∀ j, ∃ c : 𝒰.X j ⟶ (X i).left,
      (sigmaOver P).map (𝒰.f j).op s = sigmaOverMk P c (ξ i)) :
    ∃ c : T ⟶ (X i).left, s = sigmaOverMk P c (ξ i) := by
  choose c hc using h
  have hglue (j k : 𝒰.I₀) : pullback.fst (𝒰.f j) (𝒰.f k) ≫ c j = pullback.snd _ _ ≫ c k := by
    refine hinj i _ _ ?_
    rw [← sigmaOver_map_sigmaOverMk, ← sigmaOver_map_sigmaOverMk, ← hc, ← hc,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms c hglue, ?_⟩
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_sigmaOver P hP)
  refine (hF.isSeparated (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f))
    (mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)).ext ?_
  rintro V _ ⟨Z, g, _, ⟨j⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hc, sigmaOver_map_sigmaOverMk,
    sigmaOver_map_sigmaOverMk, sigmaOver_map_sigmaOverMk, 𝒰.ι_glueMorphisms]

/-- A variant of `exists_sigmaOverMk_eq_of_openCover` for a cover given by open neighbourhoods
of all points. -/
lemma exists_sigmaOverMk_eq_of_forall_mem (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ i {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i) → c = c')
    {i : ι} {T : Scheme.{u}} (s : (sigmaOver P).obj (op T))
    (h : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ c : (U : Scheme.{u}) ⟶ (X i).left,
      (sigmaOver P).map U.ι.op s = sigmaOverMk P c (ξ i)) :
    ∃ c : T ⟶ (X i).left, s = sigmaOverMk P c (ξ i) := by
  choose U hU c hc using h
  let 𝒰 : Scheme.OpenCover.{u} T := {
    I₀ := T, X t := U t, f t := (U t).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun t ↦ ⟨t, by simpa using hU t⟩, inferInstance⟩ }
  exact exists_sigmaOverMk_eq_of_openCover hP hinj s 𝒰 fun t ↦ ⟨c t, hc t⟩

/-- **The open locus, from affine test schemes.** If the locus where an element of
`sigmaOver P` over an affine scheme comes from `X i` is open (tested on affine schemes), then
the same holds over arbitrary schemes, tested on arbitrary schemes. -/
lemma exists_opens_sigmaOver (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ i {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i) → c = c') {i : ι}
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (s : (sigmaOver P).obj (op T)), ∃ U : T.Opens,
      ∀ (W : Scheme.{u}) [IsAffine W] (a : W ⟶ T),
        (∃ c : W ⟶ (X i).left, (sigmaOver P).map a.op s = sigmaOverMk P c (ξ i)) ↔
          Set.range a ⊆ U)
    {T : Scheme.{u}} (s : (sigmaOver P).obj (op T)) : ∃ U : T.Opens,
      ∀ (W : Scheme.{u}) (a : W ⟶ T),
        (∃ c : W ⟶ (X i).left, (sigmaOver P).map a.op s = sigmaOverMk P c (ξ i)) ↔
          Set.range a ⊆ U := by
  let L (V : T.Opens) : Prop :=
    ∃ c : (V : Scheme.{u}) ⟶ (X i).left, (sigmaOver P).map V.ι.op s = sigmaOverMk P c (ξ i)
  refine ⟨sSup {V | L V}, fun W a ↦ ⟨?_, fun ha ↦ ?_⟩⟩
  · rintro ⟨c, hc⟩ _ ⟨w, rfl⟩
    obtain ⟨V₀ : T.Opens, hV₀, hw, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens
        (show a w ∈ (⊤ : T.Opens) from trivial)
    have : IsAffine V₀ := hV₀
    obtain ⟨U₀, hU₀⟩ := hopen V₀ ((sigmaOver P).map V₀.ι.op s)
    refine (TopologicalSpace.Opens.mem_sSup).2 ⟨V₀.ι ''ᵁ U₀, ?_, ?_⟩
    · -- the restriction of `s` to the image of `U₀` comes from `X i`
      obtain ⟨c', hc'⟩ : ∃ c' : (U₀ : Scheme.{u}) ⟶ (X i).left,
          (sigmaOver P).map (U₀.ι ≫ V₀.ι).op s = sigmaOverMk P c' (ξ i) := by
        refine exists_sigmaOverMk_eq_of_openCover hP hinj _ (U₀ : Scheme.{u}).affineCover
          fun j ↦ ?_
        rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc, op_comp,
          Functor.map_comp_apply]
        refine (hU₀ _ _).2 ?_
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, ← Scheme.Opens.range_ι U₀]
        exact Set.range_comp_subset_range _ _
      refine ⟨(V₀.ι.isoImage U₀).inv ≫ c', ?_⟩
      rw [← Scheme.Hom.isoImage_inv_ι, op_comp, Functor.map_comp_apply, hc',
        sigmaOver_map_sigmaOverMk]
    · -- the point `a w` lies in the image of `U₀`
      obtain ⟨W' : W.Opens, hW', hwW', hW'le⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 W.isBasis_affineOpens
        (show w ∈ a ⁻¹ᵁ V₀ from hw)
      have : IsAffine W' := hW'
      have hr : Set.range (a.resLE V₀ W' hW'le) ⊆ U₀ := by
        refine (hU₀ _ _).1 ⟨W'.ι ≫ c, ?_⟩
        rw [← Functor.map_comp_apply, ← op_comp, Scheme.Hom.resLE_comp_ι, op_comp,
          Functor.map_comp_apply, hc, sigmaOver_map_sigmaOverMk]
      refine ⟨a.resLE V₀ W' hW'le ⟨w, hwW'⟩, hr ⟨_, rfl⟩, ?_⟩
      simp
  · refine exists_sigmaOverMk_eq_of_forall_mem hP hinj _ fun w ↦ ?_
    obtain ⟨V, ⟨c, hc⟩, hV⟩ := (TopologicalSpace.Opens.mem_sSup).1 (ha ⟨w, rfl⟩)
    refine ⟨a ⁻¹ᵁ V, hV, a.resLE V (a ⁻¹ᵁ V) le_rfl ≫ c, ?_⟩
    rw [← Functor.map_comp_apply, ← op_comp, ← Scheme.Hom.resLE_comp_ι, op_comp,
      Functor.map_comp_apply, hc, sigmaOver_map_sigmaOverMk]

end Affine

/-- **Representability is local, over a base, tested on affine schemes.** This is
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over` with each of
its three hypotheses only required for affine test schemes: the injectivity of `h_{X i} ⟶ P`
on affine `T`, the openness of the locus where an element of `P(T)` comes from `X i` for affine
`T`, tested against affine `W ⟶ T`, and the covering condition for affine `T`. Since `P` is a
Zariski sheaf, the general case follows by covering `T` and `W` by affine opens. -/
theorem isRepresentable_of_isSheaf_over_of_isAffine
    (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} [IsAffine T.left] (a b : T ⟶ X i),
      P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) [IsAffine T.left] (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (hcov : ∀ (T : Over S) [IsAffine T.left] (x : P.obj (op T)) (t : T.left),
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i)) :
    P.IsRepresentable := by
  have hinj' (i : ι) {T : Scheme.{u}} (c c' : T ⟶ (X i).left)
      (h : sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i)) : c = c' :=
    eq_of_sigmaOverMk_eq hinj h
  -- an element of `sigmaOver P` over `T` is `sigmaOverMk P (𝟙 T) x` for `x ∈ P(T, s)`
  have hmap {T : Scheme.{u}} (s : (sigmaOver P).obj (op T)) {W : Scheme.{u}} (a : W ⟶ T) :
      (sigmaOver P).map a.op s = sigmaOverMk P (Y := Over.mk s.1) a ((equivShrink _).symm s.2) := by
    conv_lhs => rw [← sigmaOverMk_id P s]
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
  refine isRepresentable_of_isSheaf_over P hP X ξ (fun i T a b h ↦ ?_) (fun i T x ↦ ?_)
    (fun T x t ↦ ?_)
  · exact Over.OverMorphism.ext (hinj' i _ _
      ((sigmaOverMk_eq_iff P (W := T) _ _ (Over.w a) (Over.w b) _ _).2 h))
  · -- the open locus, for arbitrary `T`
    obtain ⟨U, hU⟩ := exists_opens_sigmaOver hP hinj' (i := i) (fun T hT s ↦ by
      obtain ⟨U, hU⟩ := @hopen i (Over.mk s.1) hT ((equivShrink _).symm s.2)
      refine ⟨U, fun W hW a ↦ ?_⟩
      rw [hmap]
      exact (exists_map_eq_iff_exists_sigmaOverMk_eq _ _ i).symm.trans
        (@hU (Over.mk (a ≫ s.1)) hW (Over.homMk a rfl))) (sigmaOverMk P (𝟙 T.left) x)
    refine ⟨U, fun W a ↦ ?_⟩
    rw [exists_map_eq_iff_exists_sigmaOverMk_eq, ← hU, sigmaOver_map_sigmaOverMk,
      Category.comp_id]
  · -- the covering condition, for arbitrary `T`
    obtain ⟨V : T.left.Opens, hV, ht, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.left.isBasis_affineOpens
        (show t ∈ (⊤ : T.left.Opens) from trivial)
    have : IsAffine (Over.mk (V.ι ≫ T.hom)).left := hV
    let x' := P.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ T.hom) ⟶ T).op x
    obtain ⟨i, W, a, b, ⟨w, hw⟩, h⟩ := hcov (Over.mk (V.ι ≫ T.hom)) x' ⟨t, ht⟩
    refine ⟨i, W, a ≫ Over.homMk V.ι rfl, b, ⟨w, ?_⟩, ?_⟩
    · simpa using congr_arg Subtype.val hw
    · rw [op_comp, Functor.map_comp_apply, h]

end AlgebraicGeometry.Scheme.LocalRepresentability

namespace AlgebraicGeometry

/-- **Subfunctors representable by open immersions.** If the inclusion of a subfunctor
`F ⊆ P` of a presheaf on `Over S` is representable by open immersions, then for every `T` and
`x ∈ P(T)` there is an open `U ⊆ T` such that a morphism `a : W ⟶ T` factors through `U` if
and only if `a^* x ∈ F(W)` (Stacks, Definition 01JI).

(blueprint: `lemma-representability-picard-functor`) -/
lemma exists_opens_of_relative_isOpenImmersion {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type (max w u)} {F : Subfunctor P}
    (hF : (IsOpenImmersion.inverseImage (Over.forget S)).relative uliftYoneda.{w} F.ι)
    (T : Over S) (x : P.obj (op T)) :
    ∃ U : T.left.Opens, ∀ (W : Over S) (a : W ⟶ T),
      P.map a.op x ∈ F.obj (op W) ↔ Set.range a.left ⊆ U := by
  let g : uliftYoneda.{w}.obj T ⟶ P := uliftYonedaEquiv.symm x
  have hg {W : Over S} (a : W ⟶ T) : g.app (op W) (ULift.up a) = P.map a.op x := rfl
  have hpb := hF.rep.isPullback g
  have hsnd : IsOpenImmersion (hF.rep.snd g).left := hF.property_snd g
  refine ⟨(hF.rep.snd g).left.opensRange, fun W a ↦ ?_⟩
  rw [Scheme.Hom.coe_opensRange]
  constructor
  · intro h
    obtain ⟨d, -, hd⟩ := Types.exists_of_isPullback (hpb.app (op W)) ⟨_, h⟩ (ULift.up a)
      (by rw [hg]; rfl)
    replace hd : d.down ≫ hF.rep.snd g = a := congr_arg ULift.down hd
    rw [← hd, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · intro h
    let d : W ⟶ hF.rep.pullback g := Over.homMk (IsOpenImmersion.lift _ a.left h) (by
      rw [← Over.w (hF.rep.snd g), IsOpenImmersion.lift_fac_assoc, Over.w a])
    have hd : d ≫ hF.rep.snd g = a := by ext; exact IsOpenImmersion.lift_fac _ _ _
    have := congr_arg (fun φ ↦ φ.app (op W) (ULift.up d)) hpb.w
    have h₂ : P.map a.op x = ((hF.rep.fst g).app (op W) (ULift.up d)).1 := by
      rw [← hg, ← hd]
      exact this.symm
    rw [h₂]
    exact ((hF.rep.fst g).app (op W) (ULift.up d)).2

/-- **Recognising subfunctors representable by open immersions.** Conversely to
`AlgebraicGeometry.exists_opens_of_relative_isOpenImmersion`, if for every `T` and
`x ∈ P(T)` there is an open `U ⊆ T` such that a morphism `a : W ⟶ T` factors through `U` if and
only if `a^* x ∈ F(W)`, then the inclusion `F ⊆ P` is representable by open immersions: the
pullback of `F` along `x : h_T ⟶ P` is represented by the open subscheme `U` of `T`
(Stacks, Definition 01JI).

(blueprint: `lemma-representability-picard-functor`) -/
lemma relative_isOpenImmersion_of_exists_opens {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type (max w u)} {F : Subfunctor P}
    (hF : ∀ (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens, ∀ (W : Over S) (a : W ⟶ T),
      P.map a.op x ∈ F.obj (op W) ↔ Set.range a.left ⊆ U) :
    (IsOpenImmersion.inverseImage (Over.forget S)).relative uliftYoneda.{w} F.ι := by
  refine MorphismProperty.relative.of_exists fun T g ↦ ?_
  obtain ⟨x, rfl⟩ := uliftYonedaEquiv.symm.surjective g
  obtain ⟨U, hU⟩ := hF T x
  let b : Over S := Over.mk (U.ι ≫ T.hom)
  let snd : b ⟶ T := Over.homMk U.ι
  have hb : P.map snd.op x ∈ F.obj (op b) :=
    (hU b snd).2 (by change Set.range U.ι ⊆ U; rw [Scheme.Opens.range_ι])
  refine ⟨b, uliftYonedaEquiv.symm ⟨_, hb⟩, snd,
    IsPullback.of_forall_isPullback_app fun W ↦ ?_, ?_⟩
  · rw [Types.isPullback_iff]
    refine ⟨?_, fun d d' ⟨_, h⟩ ↦ ?_, fun e a h ↦ ?_⟩
    · ext d
      change P.map d.down.op (P.map snd.op x) = P.map (d.down ≫ snd).op x
      rw [op_comp, Functor.map_comp_apply]
    · replace h : d.down.left ≫ U.ι = d'.down.left ≫ U.ι := congr_arg (·.down.left) h
      exact ULift.ext (Over.OverMorphism.ext ((cancel_mono U.ι).1 h))
    · replace h : e.1 = P.map a.down.op x := h
      have hrange : Set.range a.down.left.base ⊆ Set.range U.ι.base := by
        rw [Scheme.Opens.range_ι, ← hU, ← h]
        exact e.2
      let d : W.unop ⟶ b := Over.homMk (IsOpenImmersion.lift U.ι a.down.left hrange) (by
        simp [b, IsOpenImmersion.lift_fac_assoc])
      have hd : d ≫ snd = a.down := by ext; exact IsOpenImmersion.lift_fac _ _ _
      refine ⟨ULift.up d, Subtype.ext ?_, ULift.ext hd⟩
      change P.map d.op (P.map snd.op x) = e.1
      rw [← Functor.map_comp_apply, ← op_comp, hd, h]
  · change IsOpenImmersion U.ι
    infer_instance

/-- **Covers of a functor.** A family `F i` of subfunctors of a presheaf `P` on `Over S`
*covers* `P` if every element `x ∈ P(T)` lies locally on `T` in one of the `F i`: every point of
`T` has an open neighbourhood `U` with `x|_U ∈ F i (U)` for some `i` (Stacks, Definition 01JI).

(blueprint: `lemma-representability-picard-functor`) -/
def ZariskiCovers {S : Scheme.{u}} {P : (Over S)ᵒᵖ ⥤ Type w} {ι : Sort*}
    (F : ι → Subfunctor P) : Prop :=
  ∀ (T : Over S) (x : P.obj (op T)) (t : T.left), ∃ (i : ι) (U : T.left.Opens), t ∈ U ∧
    P.map (Over.homMk U.ι rfl : Over.mk (U.ι ≫ T.hom) ⟶ T).op x ∈
      (F i).obj (op (Over.mk (U.ι ≫ T.hom)))

/-- **The representability criterion for schemes** (Stacks, Lemma 01JJ). Let `P` be a presheaf
of sets on `Sch/S`, with `u`-small values, such that

1. `P` is a Zariski sheaf;
2. there is a family `(F i)` of subfunctors of `P` such that
   (a) each `F i` is representable,
   (b) each inclusion `F i ⊆ P` is representable by open immersions,
   (c) the family `F i` covers `P`.

Then `P` is representable by a scheme over `S`. Subfunctors (blueprint `def-pc-subfunctor`) are
`CategoryTheory.Subfunctor`, the Zariski sheaf property (blueprint
`def-pc-zariski-sheaf-property`) is `Presheaf.IsSheaf` for `zariskiTopology.over S`, and
representability by open immersions (blueprint `lemma-representability-picard-functor`) is
`MorphismProperty.relative` for `uliftYoneda`. The proof reduces to
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over`, applied to the
universal elements of the `F i`.

(blueprint: `lemma-representability-picard-functor`) -/
theorem isRepresentable_of_isSheaf_of_zariskiCovers {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type (max w u)} [∀ T, Small.{u} (P.obj T)]
    (hP : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) P) {ι : Type u}
    (F : ι → Subfunctor P)
    (hrep : ∀ i, (F i).toFunctor.IsRepresentable)
    (hopen : ∀ i, (IsOpenImmersion.inverseImage (Over.forget S)).relative uliftYoneda.{w}
      (F i).ι)
    (hcov : ZariskiCovers F) : P.IsRepresentable := by
  choose X e using fun i ↦ (hrep i).has_representation
  replace e := fun i ↦ (e i).some
  let ξ (i : ι) : P.obj (op (X i)) := ((e i).homEquiv (𝟙 (X i))).1
  have he (i : ι) {W : Over S} (b : W ⟶ X i) : ((e i).homEquiv b).1 = P.map b.op (ξ i) := by
    rw [← Category.comp_id b, (e i).homEquiv_comp]
    rfl
  have hmem (i : ι) {W : Over S} (z : P.obj (op W)) :
      (∃ b : W ⟶ X i, z = P.map b.op (ξ i)) ↔ z ∈ (F i).obj (op W) := by
    refine ⟨fun ⟨b, hb⟩ ↦ hb ▸ he i b ▸ ((e i).homEquiv b).2, fun h ↦ ?_⟩
    refine ⟨(e i).homEquiv.symm ⟨z, h⟩, ?_⟩
    rw [← he, Equiv.apply_symm_apply]
  refine Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over P hP X ξ
    (fun i T a b h ↦ (e i).homEquiv.injective (Subtype.ext (by rw [he, he, h])))
    (fun i T x ↦ ?_) (fun T x t ↦ ?_)
  · obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion (hopen i) T x
    exact ⟨U, fun W a ↦ (hmem i _).trans (hU W a)⟩
  · obtain ⟨i, U, ht, h⟩ := hcov T x t
    obtain ⟨b, hb⟩ := (hmem i _).2 h
    exact ⟨i, _, _, b, by simpa [Scheme.Opens.range_ι] using ht, hb⟩


end AlgebraicGeometry
