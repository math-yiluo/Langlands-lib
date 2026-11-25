/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Universal sections of presheaves on the small étale site

Let `E` be a presheaf of sets on the small étale site of a scheme `T`, and let `u : U ⟶ T` be a
morphism. A section `ξ ∈ E(V)` over an étale `T`-scheme `V` whose structure morphism factors
as `v : V ⟶ U` followed by `u` is *universal* relative to `u`
(`AlgebraicGeometry.Scheme.IsUniversalSection`) if for every étale `T`-scheme `W` together with
a factorisation `w : W ⟶ U` of its structure morphism, the `U`-morphisms `a : W ⟶ V` correspond
bijectively to the sections of `E` over `W`, by `a ↦ a^* ξ`. In other words `V` represents the
restriction of `E` to étale `U`-schemes, and `ξ` is the universal element.

This is the form in which we manipulate "the restriction of `E` to `U` is represented by `V`":
it involves no restriction functors between small étale sites, and it is stable under base
change (`AlgebraicGeometry.Scheme.IsUniversalSection.baseChange`). For `u = 𝟙 T` it says that
`V` represents `E` (`AlgebraicGeometry.Scheme.IsUniversalSection.isoUliftYoneda`).

We also record the forms of the sheaf condition for a single surjective étale morphism that are
used to descend sections.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {T : Scheme.{u}} (E : T.Etaleᵒᵖ ⥤ Type w)

/-- Composition in the small étale site is composition of the underlying morphisms. -/
@[simp]
lemma Etale.comp_left_eq {X Y Z : T.Etale} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

/-- The identity in the small étale site is the identity of the underlying scheme. -/
@[simp]
lemma Etale.id_left_eq (X : T.Etale) : (𝟙 X : X ⟶ X).left = 𝟙 X.left := rfl

/-- A section `ξ ∈ E(V)` is *universal* relative to `u : U ⟶ T` along `v : V ⟶ U` if for every
étale `T`-scheme `W` and every factorisation `w : W ⟶ U` of its structure morphism through `u`,
the map `a ↦ a^* ξ` from `U`-morphisms `W ⟶ V` to `E(W)` is bijective. When `v ≫ u` is the
structure morphism of `V`, this says that `V ⟶ U` represents the restriction of `E` to étale
`U`-schemes, with universal element `ξ`. -/
def IsUniversalSection {U : Scheme.{u}} (u : U ⟶ T) (V : T.Etale) (v : V.left ⟶ U)
    (ξ : E.obj (op V)) : Prop :=
  ∀ (W : T.Etale) (w : W.left ⟶ U), w ≫ u = W.hom →
    Function.Bijective (fun a : {a : W ⟶ V // a.left ≫ v = w} ↦ E.map a.1.op ξ)

namespace IsUniversalSection

variable {E} {U : Scheme.{u}} {u : U ⟶ T} {V : T.Etale} {v : V.left ⟶ U} {ξ : E.obj (op V)}

/-- Two `U`-morphisms into `V` pulling back a universal section to the same section agree. -/
lemma hom_ext (h : IsUniversalSection E u V v ξ) {W : T.Etale} {a b : W ⟶ V}
    (hab : a.left ≫ v = b.left ≫ v) (hu : (a.left ≫ v) ≫ u = W.hom)
    (hξ : E.map a.op ξ = E.map b.op ξ) : a = b :=
  congrArg Subtype.val (h W _ hu |>.1 (a₁ := ⟨a, rfl⟩) (a₂ := ⟨b, hab.symm⟩) hξ)

/-- Every section of `E` over `W` is the pullback of a universal section along a unique
`U`-morphism; this is the existence part. -/
lemma exists_hom (h : IsUniversalSection E u V v ξ) {W : T.Etale} (w : W.left ⟶ U)
    (hw : w ≫ u = W.hom) (e : E.obj (op W)) :
    ∃ a : W ⟶ V, a.left ≫ v = w ∧ E.map a.op ξ = e := by
  obtain ⟨a, ha⟩ := (h W w hw).2 e
  exact ⟨a.1, a.2, ha⟩

/-- **Uniqueness of universal sections.** Two universal sections relative to the same `u` are
related by a unique isomorphism over `U`. -/
lemma exists_iso (h : IsUniversalSection E u V v ξ) (hv : v ≫ u = V.hom)
    {V' : T.Etale} {v' : V'.left ⟶ U} {ξ' : E.obj (op V')} (h' : IsUniversalSection E u V' v' ξ')
    (hv' : v' ≫ u = V'.hom) :
    ∃ e : V ≅ V', e.hom.left ≫ v' = v ∧ E.map e.hom.op ξ' = ξ := by
  obtain ⟨a, ha, haξ⟩ := h'.exists_hom v hv ξ
  obtain ⟨b, hb, hbξ⟩ := h.exists_hom v' hv' ξ'
  have hab : a ≫ b = 𝟙 V := by
    refine h.hom_ext (W := V) ?_ ?_ ?_
    · rw [Etale.comp_left_eq, Etale.id_left_eq, Category.assoc, hb, ha, Category.id_comp]
    · rw [Etale.comp_left_eq, Category.assoc, Category.assoc, reassoc_of% hb, reassoc_of% ha, hv]
    · rw [op_comp, Functor.map_comp_apply, hbξ, haξ, op_id, Functor.map_id_apply]
  have hba : b ≫ a = 𝟙 V' := by
    refine h'.hom_ext (W := V') ?_ ?_ ?_
    · rw [Etale.comp_left_eq, Etale.id_left_eq, Category.assoc, ha, hb, Category.id_comp]
    · rw [Etale.comp_left_eq, Category.assoc, Category.assoc, reassoc_of% ha, reassoc_of% hb, hv']
    · rw [op_comp, Functor.map_comp_apply, haξ, hbξ, op_id, Functor.map_id_apply]
  exact ⟨⟨a, b, hab, hba⟩, ha, haξ⟩

/-- A universal section can be transported along an isomorphism of étale `T`-schemes. -/
lemma of_iso (h : IsUniversalSection E u V v ξ) {V' : T.Etale} (e : V' ≅ V) :
    IsUniversalSection E u V' (e.hom.left ≫ v) (E.map e.hom.op ξ) := by
  intro W w hw
  have hb := h W w hw
  let φ : {a : W ⟶ V' // a.left ≫ e.hom.left ≫ v = w} ≃ {a : W ⟶ V // a.left ≫ v = w} :=
    { toFun a := ⟨a.1 ≫ e.hom, by rw [Etale.comp_left_eq, Category.assoc]; exact a.2⟩
      invFun a := ⟨a.1 ≫ e.inv, by
        rw [Etale.comp_left_eq, Category.assoc, ← Category.assoc e.inv.left,
          ← Etale.comp_left_eq, e.inv_hom_id, Etale.id_left_eq, Category.id_comp]
        exact a.2⟩
      left_inv a := Subtype.ext (by simp)
      right_inv a := Subtype.ext (by simp) }
  convert hb.comp φ.bijective using 1
  ext a
  simp [φ, op_comp]

/-- A universal section along `v` is universal along every `v'` equal to `v`. -/
lemma of_eq (h : IsUniversalSection E u V v ξ) {v' : V.left ⟶ U} (hv : v = v') :
    IsUniversalSection E u V v' ξ :=
  hv ▸ h

end IsUniversalSection

section BaseChange

variable {E} {U : Scheme.{u}} {u : U ⟶ T} [AlgebraicGeometry.Etale u] {V : T.Etale}
  {v : V.left ⟶ U} {ξ : E.obj (op V)}

/-- If `v ≫ u` is étale and `u` is étale, then so is `v`. -/
lemma etale_of_comp_eq (hv : v ≫ u = V.hom) : AlgebraicGeometry.Etale v := by
  have : AlgebraicGeometry.Etale (v ≫ u) := by rw [hv]; infer_instance
  exact AlgebraicGeometry.Etale.of_comp v u

variable (hv : v ≫ u = V.hom) {O : Scheme.{u}} (o : O ⟶ U) (u' : O ⟶ T)
  [AlgebraicGeometry.Etale u']

/-- The base change `V ×_U O`, as an étale `T`-scheme through `u' : O ⟶ T`. -/
noncomputable def IsUniversalSection.baseChangeObj : T.Etale :=
  have : AlgebraicGeometry.Etale v := etale_of_comp_eq hv
  Etale.mk (pullback.snd v o ≫ u')

/-- The underlying scheme of the base change is the fibre product `V ×_U O`. -/
lemma IsUniversalSection.baseChangeObj_left :
    (IsUniversalSection.baseChangeObj hv o u').left = pullback v o := rfl

/-- The structure morphism of the base change is the second projection followed by `u'`. -/
lemma IsUniversalSection.baseChangeObj_hom :
    (IsUniversalSection.baseChangeObj hv o u').hom = pullback.snd v o ≫ u' := rfl


variable {o u'} in
/-- The projection `V ×_U O ⟶ V`, as a morphism of étale `T`-schemes. -/
noncomputable def IsUniversalSection.baseChangeHom (ho : o ≫ u = u') :
    IsUniversalSection.baseChangeObj hv o u' ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst v o) (by
    change pullback.fst v o ≫ V.hom = pullback.snd v o ≫ u'
    rw [← hv, ← ho, pullback.condition_assoc])

variable {o u'} in
/-- **Universal sections are stable under base change.** If `ξ` is universal relative to `u`
along `v`, then for `o : O ⟶ U` its pullback to `V ×_U O` is universal relative to `o ≫ u`
along the second projection. -/
lemma IsUniversalSection.baseChange (h : IsUniversalSection E u V v ξ) (ho : o ≫ u = u') :
    IsUniversalSection E u' (IsUniversalSection.baseChangeObj hv o u') (pullback.snd v o)
      (E.map (IsUniversalSection.baseChangeHom hv ho).op ξ) := by
  intro W w hw
  have hb := h W (w ≫ o) (by rw [Category.assoc, ho, hw])
  let φ : {a : W ⟶ IsUniversalSection.baseChangeObj hv o u' // a.left ≫ pullback.snd v o = w} →
      {a : W ⟶ V // a.left ≫ v = w ≫ o} := fun a ↦
    ⟨a.1 ≫ IsUniversalSection.baseChangeHom hv ho, by
      change (a.1.left ≫ pullback.fst v o) ≫ v = w ≫ o
      rw [Category.assoc, pullback.condition, ← Category.assoc, a.2]⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab ↦ Subtype.ext ?_, fun b ↦ ?_⟩
    · have hab' : a.1.left ≫ pullback.fst v o = b.1.left ≫ pullback.fst v o :=
        congrArg (fun c : {a : W ⟶ V // a.left ≫ v = w ≫ o} ↦ c.1.left) hab
      exact MorphismProperty.Over.Hom.ext (pullback.hom_ext hab' (a.2.trans b.2.symm))
    · refine ⟨⟨MorphismProperty.Over.homMk (pullback.lift b.1.left w b.2) (by
        change pullback.lift b.1.left w b.2 ≫ pullback.snd v o ≫ u' = W.hom
        rw [pullback.lift_snd_assoc, hw]), pullback.lift_snd _ _ _⟩, Subtype.ext ?_⟩
      exact MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
  convert hb.comp hφ using 1
  ext a
  simp [φ, op_comp]

/-- To check universality it suffices to consider the étale `T`-schemes of the form
`W ⟶ U ⟶ T`. -/
lemma IsUniversalSection.of_mk
    (h : ∀ (W : Scheme.{u}) (w : W ⟶ U) [AlgebraicGeometry.Etale w],
      Function.Bijective (fun a : {a : Etale.mk (w ≫ u) ⟶ V // a.left ≫ v = w} ↦
        E.map a.1.op ξ)) :
    IsUniversalSection E u V v ξ := by
  intro W w hw
  have : AlgebraicGeometry.Etale w := etale_of_comp_eq (V := W) hw
  let eW : Etale.mk (w ≫ u) ≅ W := MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ W.hom = w ≫ u
    rw [Category.id_comp, hw])
  let φ : {a : W ⟶ V // a.left ≫ v = w} ≃ {a : Etale.mk (w ≫ u) ⟶ V // a.left ≫ v = w} :=
    { toFun a := ⟨eW.hom ≫ a.1, by
        rw [Etale.comp_left_eq, Category.assoc, a.2]
        exact Category.id_comp _⟩
      invFun a := ⟨eW.inv ≫ a.1, by
        rw [Etale.comp_left_eq, Category.assoc, a.2]
        exact Category.id_comp _⟩
      left_inv a := Subtype.ext (by simp)
      right_inv a := Subtype.ext (by simp) }
  have hiso : Function.Bijective (E.map eW.hom.op) :=
    (isIso_iff_bijective _).1 (inferInstanceAs (IsIso ((E.mapIso eW.op).hom)))
  have key : (fun a : {a : Etale.mk (w ≫ u) ⟶ V // a.left ≫ v = w} ↦ E.map a.1.op ξ) ∘ φ =
      E.map eW.hom.op ∘ (fun a : {a : W ⟶ V // a.left ≫ v = w} ↦ E.map a.1.op ξ) := by
    ext a
    simp [φ, op_comp]
  have := (h W.left w).comp φ.bijective
  rw [key] at this
  exact (Function.Bijective.of_comp_iff' hiso _).1 this

end BaseChange

section Representable

variable {E} {V : T.Etale} {ξ : E.obj (op V)}

/-- A universal section relative to the identity of `T` is a universal element in the usual
sense: `a ↦ a^* ξ` is a bijection `(W ⟶ V) ≃ E(W)` for every étale `T`-scheme `W`. -/
lemma IsUniversalSection.bijective_of_id (h : IsUniversalSection E (𝟙 T) V V.hom ξ)
    (W : T.Etale) : Function.Bijective (fun a : W ⟶ V ↦ E.map a.op ξ) := by
  have hb := h W W.hom (Category.comp_id _)
  let φ : (W ⟶ V) ≃ {a : W ⟶ V // a.left ≫ V.hom = W.hom} :=
    { toFun a := ⟨a, MorphismProperty.Over.w a⟩
      invFun a := a.1
      left_inv _ := rfl
      right_inv _ := rfl }
  exact hb.comp φ.bijective

/-- Conversely, a universal element in the usual sense is a universal section relative to the
identity of `T`. -/
lemma IsUniversalSection.of_bijective
    (h : ∀ W : T.Etale, Function.Bijective (fun a : W ⟶ V ↦ E.map a.op ξ)) :
    IsUniversalSection E (𝟙 T) V V.hom ξ := by
  intro W w hw
  rw [Category.comp_id] at hw
  subst hw
  let φ : {a : W ⟶ V // a.left ≫ V.hom = W.hom} ≃ (W ⟶ V) :=
    { toFun a := a.1
      invFun a := ⟨a, MorphismProperty.Over.w a⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact (h W).comp φ.bijective

/-- **A universal section relative to the identity represents `E`.** -/
noncomputable def IsUniversalSection.isoUliftYoneda {E : T.Etaleᵒᵖ ⥤ Type (u + 1)}
    {ξ : E.obj (op V)} (h : IsUniversalSection E (𝟙 T) V V.hom ξ) :
    E ≅ uliftYoneda.{u + 1}.obj V :=
  (NatIso.ofComponents (fun W ↦ (Equiv.ofBijective
      (fun a : ULift.{u + 1} (W.unop ⟶ V) ↦ E.map a.down.op ξ)
      ((h.bijective_of_id W.unop).comp Equiv.ulift.bijective)).toIso) (fun {W W'} f ↦ by
    ext a
    change E.map (f.unop ≫ a.down).op ξ = E.map f (E.map a.down.op ξ)
    rw [op_comp, Functor.map_comp_apply]
    rfl)).symm

/-- The identity is a universal section of the presheaf represented by `V`. -/
lemma isUniversalSection_uliftYoneda (V : T.Etale) :
    IsUniversalSection (uliftYoneda.{w}.obj V) (𝟙 T) V V.hom ⟨𝟙 V⟩ := by
  refine IsUniversalSection.of_bijective fun W ↦ ?_
  convert (Equiv.ulift.{w}.symm.bijective : Function.Bijective (Equiv.ulift.{w}.symm :
    (W ⟶ V) → ULift (W ⟶ V))) using 1
  ext a
  exact congrArg ULift.up (Category.comp_id a)

end Representable

section Sheaf

variable {E}

/-- The sieve generated by a single morphism of étale `T`-schemes which is surjective is a
covering sieve of the small étale site. -/
lemma Etale.generate_singleton_mem {V N : T.Etale} (q : V ⟶ N)
    (hq : Function.Surjective q.left) :
    Sieve.generate (Presieve.singleton q) ∈ T.smallEtaleTopology N := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  change Sieve.ofArrows _ _ ∈ _
  rw [ofArrows_mem_smallEtaleTopology_iff]
  exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨⟨⟩, hq x⟩

/-- A sheaf on the small étale site satisfies the sheaf condition for a single surjective
morphism. -/
lemma Etale.isSheafFor_singleton (hE : Presheaf.IsSheaf T.smallEtaleTopology E) {V N : T.Etale}
    (q : V ⟶ N) (hq : Function.Surjective q.left) :
    Presieve.IsSheafFor E (Presieve.singleton q) :=
  (Presieve.isSheafFor_iff_generate _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 hE _ (Etale.generate_singleton_mem q hq))

/-- Sections of a sheaf on the small étale site are determined by their pullbacks along a
surjective morphism. -/
lemma Etale.map_injective_of_surjective (hE : Presheaf.IsSheaf T.smallEtaleTopology E)
    {V N : T.Etale} (q : V ⟶ N) (hq : Function.Surjective q.left) :
    Function.Injective (E.map q.op) :=
  Presieve.isSeparatedFor_singleton.1 (Etale.isSheafFor_singleton hE q hq).isSeparatedFor

/-- A section of a sheaf on the small étale site over `V` descends along a surjective morphism
`q : V ⟶ N` as soon as its pullbacks along any two morphisms equalised by `q` agree. -/
lemma Etale.exists_map_eq_of_surjective (hE : Presheaf.IsSheaf T.smallEtaleTopology E)
    {V N : T.Etale} (q : V ⟶ N) (hq : Function.Surjective q.left) (x : E.obj (op V))
    (hx : ∀ {Z : T.Etale} (p₁ p₂ : Z ⟶ V), p₁ ≫ q = p₂ ≫ q → E.map p₁.op x = E.map p₂.op x) :
    ∃ y, E.map q.op y = x :=
  (Presieve.isSheafFor_singleton.1 (Etale.isSheafFor_singleton hE q hq) x hx).exists

end Sheaf

end AlgebraicGeometry.Scheme
