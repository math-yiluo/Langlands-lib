/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Full faithfulness of base change along a universal homeomorphism

Let `f : X ⟶ Y` be a universal homeomorphism. We show that for every `Y`-scheme `T` and
every étale `Y`-scheme `V`, base change along `f` induces a bijection

```
  Hom_Y(T, V) ≃ Hom_X(T ×_Y X, V ×_Y X)
```

This is [Stacks 04DY]. In particular the base change functor `f.Etale : Y.Etale ⥤ X.Etale`
is fully faithful.

## Proof sketch

Faithfulness only uses that `f` is surjective and that `V ⟶ Y` is unramified: two
`Y`-morphisms `T ⟶ V` agreeing after composition with the surjection `T ×_Y X ⟶ T` factor
jointly through the diagonal of `V`, which is an open immersion.

For fullness we descend an `X`-morphism `a : T ×_Y X ⟶ V ×_Y X` through its graph.
Let `P = T ×_Y V` and `P_X = P ×_T (T ×_Y X)`. The graph `Γ : T ×_Y X ⟶ P_X` of `a` is a
section of the étale projection `P_X ⟶ T ×_Y X`, hence an open immersion. As `P_X ⟶ P` is
a homeomorphism, the image of `Γ` corresponds to an open subscheme `O ⊆ P`, and the
projection `q : O ⟶ T` is étale and becomes an isomorphism after base change along
`T ×_Y X ⟶ T`. Surjectivity and universal injectivity descend along surjections, so `q` is
an étale universally injective surjection, hence an isomorphism. The composite
`T ≅ O ⟶ P ⟶ V` is the required morphism.

## References

* [Stacks 04DY], Étale Cohomology, Theorem 59.45.1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Faithful

/-- Surjective morphisms are epimorphisms with respect to morphisms into an unramified
`Y`-scheme over a common `Y`-morphism. -/
lemma Scheme.Hom.ext_of_surjective_of_formallyUnramified {T' T V Y : Scheme.{u}}
    (π : T' ⟶ T) [Surjective π] (v : V ⟶ Y) [FormallyUnramified v] [LocallyOfFiniteType v]
    {a b : T ⟶ V} (hab : a ≫ v = b ≫ v) (h : π ≫ a = π ≫ b) : a = b := by
  let e : T ⟶ pullback v v := pullback.lift a b hab
  have he : π ≫ e = (π ≫ a) ≫ pullback.diagonal v := by
    apply pullback.hom_ext <;> simp [e, h]
  have hrange : Set.range e.base ⊆ Set.range (pullback.diagonal v).base := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', rfl⟩ := π.surjective t
    refine ⟨(π ≫ a) t', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]
  let l := IsOpenImmersion.lift (pullback.diagonal v) e hrange
  have hl : l ≫ pullback.diagonal v = e := IsOpenImmersion.lift_fac _ _ _
  have ha : a = l := by
    rw [show a = e ≫ pullback.fst v v by simp [e], ← hl, Category.assoc, pullback.diagonal_fst,
      Category.comp_id]
  have hb : b = l := by
    rw [show b = e ≫ pullback.snd v v by simp [e], ← hl, Category.assoc, pullback.diagonal_snd,
      Category.comp_id]
  rw [ha, hb]

end Faithful

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- Base change along a surjective morphism is faithful on morphisms between étale
schemes over the target. -/
instance etale_faithful : f.Etale.Faithful where
  map_injective {V V'} g h e := by
    apply MorphismProperty.Over.Hom.ext
    refine Scheme.Hom.ext_of_surjective_of_formallyUnramified (pullback.fst V.hom f) V'.hom
      (by simp) ?_
    rw [← etale_map_left_comp_fst, ← etale_map_left_comp_fst, e]

section Full

variable {T V : Scheme.{u}} (t : T ⟶ Y) (v : V ⟶ Y) [AlgebraicGeometry.Etale v]
  (a : pullback t f ⟶ pullback v f)

/-- **Fullness of base change along a universal homeomorphism**: every `X`-morphism
`T ×_Y X ⟶ V ×_Y X`, with `V` étale over `Y`, is the base change of a unique `Y`-morphism
`T ⟶ V`. This is the existence part, see
`AlgebraicGeometry.Scheme.Hom.ext_of_surjective_of_formallyUnramified` for uniqueness. -/
theorem exists_pullback_map_eq (ha : a ≫ pullback.snd v f = pullback.snd t f) :
    ∃ (g : T ⟶ V) (hg : g ≫ v = t),
      pullback.map t f v f g (𝟙 X) (𝟙 Y) (by simp [hg]) (by simp) = a := by
  classical
  -- `P = T ×_Y V` with its étale projection to `T`.
  let P : Scheme.{u} := pullback t v
  let pT : P ⟶ T := pullback.fst t v
  let pV : P ⟶ V := pullback.snd t v
  -- `πT: T ×_Y X ⟶ T` is a universal homeomorphism.
  let πT : pullback t f ⟶ T := pullback.fst t f
  -- `PX = P ×_T (T ×_Y X)`, with `πP: PX ⟶ P` a universal homeomorphism and
  -- `ρ: PX ⟶ T ×_Y X` étale.
  let PX : Scheme.{u} := pullback pT πT
  let πP : PX ⟶ P := pullback.fst pT πT
  let ρ : PX ⟶ pullback t f := pullback.snd pT πT
  -- The morphism `T ×_Y X ⟶ P` induced by `a`.
  let a' : pullback t f ⟶ P := pullback.lift πT (a ≫ pullback.fst v f) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← ha, Category.assoc, Category.assoc,
      pullback.condition])
  -- The graph of `a`, a section of `ρ`.
  let Γ : pullback t f ⟶ PX := pullback.lift a' (𝟙 _) (by simp [a', pT])
  have hΓρ : Γ ≫ ρ = 𝟙 _ := by simp [Γ, ρ]
  have hΓπP : Γ ≫ πP = a' := by simp [Γ, πP]
  have : AlgebraicGeometry.Etale ρ := inferInstanceAs (AlgebraicGeometry.Etale (pullback.snd pT πT))
  have : AlgebraicGeometry.Etale (Γ ≫ ρ) := by rw [hΓρ]; infer_instance
  have hΓ : AlgebraicGeometry.Etale Γ := Etale.of_comp Γ ρ
  have : Mono Γ := mono_of_mono_fac hΓρ
  have : IsOpenImmersion Γ := IsOpenImmersion.of_flat_of_mono Γ
  -- The open subscheme `O ⊆ P` corresponding to the image of the graph.
  have hπP : IsHomeomorph πP.base := πP.isHomeomorph
  let O : P.Opens := ⟨πP.base '' Set.range Γ.base, hπP.isOpenMap _ Γ.isOpenEmbedding.isOpen_range⟩
  let q : O.toScheme ⟶ T := O.ι ≫ pT
  have hq : AlgebraicGeometry.Etale q := inferInstance
  -- The base change of `q` along `πT` is (isomorphic to) `PX ×_P O`, which is the image of
  -- the graph, hence isomorphic to `T ×_Y X` via `Γ`.
  have hrange : Set.range (pullback.snd O.ι πP).base = Set.range Γ.base := by
    rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    exact Set.preimage_image_eq _ hπP.injective
  let e : pullback t f ≅ pullback O.ι πP :=
    IsOpenImmersion.isoOfRangeEq Γ (pullback.snd O.ι πP) hrange.symm
  have he : e.hom ≫ pullback.snd O.ι πP = Γ := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hsq : IsPullback (pullback.fst O.ι πP) (pullback.snd O.ι πP ≫ ρ) q πT :=
    (IsPullback.of_hasPullback O.ι πP).paste_vert (IsPullback.of_hasPullback pT πT)
  have hiso : IsIso (pullback.snd O.ι πP ≫ ρ) := by
    have : e.hom ≫ pullback.snd O.ι πP ≫ ρ = 𝟙 _ := by rw [← Category.assoc, he, hΓρ]
    exact IsIso.of_isIso_fac_left this
  -- Hence `q` is surjective and universally injective, so an isomorphism.
  have hsurj : Surjective q :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) (Q := @Surjective)
      hsq.flip inferInstance inferInstance
  have hinj : UniversallyInjective q := by
    have : MorphismProperty.DescendsAlong @UniversallyInjective @Surjective :=
      universallyInjective_eq_diagonal ▸ inferInstance
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyInjective)
      (Q := @Surjective) hsq.flip inferInstance inferInstance
  have hmono : Mono q := by
    rw [← pullback.isIso_diagonal_iff]
    have : Surjective (pullback.diagonal q) := (UniversallyInjective.iff_diagonal q).mp hinj
    exact isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (by ext1; simp)
  have : IsOpenImmersion q := IsOpenImmersion.of_flat_of_mono q
  have hqiso : IsIso q := isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (by ext1; simp)
  -- The lift of the graph to `O`.
  let γ : pullback t f ⟶ O.toScheme := IsOpenImmersion.lift O.ι (Γ ≫ πP) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨Γ.base x, ⟨x, rfl⟩, by simp⟩)
  have hγ : γ ≫ O.ι = Γ ≫ πP := IsOpenImmersion.lift_fac _ _ _
  have hγq : γ ≫ q = πT := by
    rw [show q = O.ι ≫ pT from rfl, ← Category.assoc, hγ, Category.assoc, ← Category.assoc, hΓπP]
    simp [a', pT]
  refine ⟨inv q ≫ O.ι ≫ pV, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, show pV ≫ v = pT ≫ t from pullback.condition.symm,
      IsIso.inv_comp_eq]
    simp [q]
  · apply pullback.hom_ext
    · have hlift : πT ≫ inv q = γ := by rw [IsIso.comp_inv_eq]; exact hγq.symm
      rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc,
        show pullback.fst t f = πT from rfl, hlift, hγ, Category.assoc, ← Category.assoc, hΓπP]
      simp [a', pV]
    · simp [ha]

/-- **Full faithfulness of base change along a universal homeomorphism**, formulated for arbitrary
pullback squares: given pullback squares exhibiting `PT` as `T ×_Y X` and `PV` as `V ×_Y X`, every
`X`-morphism `a : PT ⟶ PV` is the base change of a unique `Y`-morphism `T ⟶ V`. -/
theorem existsUnique_of_isPullback {PT PV : Scheme.{u}} {pT : PT ⟶ T} {qT : PT ⟶ X}
    (hT : IsPullback pT qT t f) {pV : PV ⟶ V} {qV : PV ⟶ X} (hV : IsPullback pV qV v f)
    (a : PT ⟶ PV) (ha : a ≫ qV = qT) :
    ∃! g : T ⟶ V, g ≫ v = t ∧ pT ≫ g = a ≫ pV := by
  have hsurj : Surjective pT := MorphismProperty.of_isPullback hT.flip inferInstance
  let a' : pullback t f ⟶ pullback v f := hT.isoPullback.inv ≫ a ≫ hV.isoPullback.hom
  have ha' : a' ≫ pullback.snd v f = pullback.snd t f := by
    simp [a', ha]
  obtain ⟨g, hg, hga⟩ := exists_pullback_map_eq f t v a' ha'
  refine ⟨g, ⟨hg, ?_⟩, fun g' ⟨hg', hg'a⟩ ↦ ?_⟩
  · have : pullback.fst t f ≫ g = a' ≫ pullback.fst v f := by
      rw [← hga, pullback.lift_fst]
    rw [← hT.isoPullback_hom_fst, Category.assoc, this, ← hV.isoPullback_hom_fst]
    simp [a']
  · refine Scheme.Hom.ext_of_surjective_of_formallyUnramified pT v (hg'.trans hg.symm) ?_
    have : pullback.fst t f ≫ g = a' ≫ pullback.fst v f := by
      rw [← hga, pullback.lift_fst]
    rw [hg'a, ← hT.isoPullback_hom_fst, Category.assoc, this, ← hV.isoPullback_hom_fst]
    simp [a']

end Full

section Instances

/-- Base change along a universal homeomorphism is full on étale schemes. -/
instance etale_full : f.Etale.Full where
  map_surjective {V V'} a := by
    obtain ⟨g, hg, hga⟩ := exists_pullback_map_eq f V.hom V'.hom a.left
      (MorphismProperty.Over.w a)
    refine ⟨MorphismProperty.Over.homMk g (by simp [hg]), ?_⟩
    apply MorphismProperty.Over.Hom.ext
    rw [← hga]
    apply pullback.hom_ext <;> simp [Hom.Etale]

/-- **Base change along a universal homeomorphism is fully faithful** on étale schemes,
[Stacks 04DY]. -/
@[stacks 04DY]
noncomputable def etaleFullyFaithful : f.Etale.FullyFaithful :=
  .ofFullyFaithful _

end Instances

end Scheme.Hom

end AlgebraicGeometry
