/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Over

/-!
# Complements on the small étale site

- `AlgebraicGeometry.Scheme.Etale.essentiallySmall`: the small étale site of `X : Scheme.{u}` is
  essentially small in the universe `u + 1`.
- `AlgebraicGeometry.Scheme.Hom.Etale`: the base change functor `Y.Etale ⥤ X.Etale`
  along a morphism `f : X ⟶ Y`; it preserves finite limits, is representably flat
  (`AlgebraicGeometry.Scheme.Hom.representablyFlat_etale`), is continuous for the small
  étale topologies (`AlgebraicGeometry.Scheme.Hom.isContinuous_etale`), and it is
  compatible with the projections `V ×_Y X ⟶ V` by
  `AlgebraicGeometry.Scheme.Hom.etale_map_left_comp_fst`.
- `AlgebraicGeometry.Scheme.Etale.isContinuous_forget_comp_overForget`: the functor from the
  small étale site of `X` to schemes is continuous for the big étale topology.
- `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`: a sieve on an object of the small
  étale site is a covering exactly when the arrows in it are jointly surjective. This is the
  sieve-level form of
  `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`.
- `AlgebraicGeometry.Scheme.Etale.baseChange` and
  `AlgebraicGeometry.Scheme.Etale.baseChangeHom`: for an étale morphism `g : W ⟶ X`, the
  base change `V ×_X W` of an étale `X`-scheme `V`, again as an étale `X`-scheme, and its
  projection to `V`.
- `AlgebraicGeometry.Scheme.Etale.ofArrows_baseChange_mem_smallEtaleTopology`: these base
  changes cover `V` as soon as the étale morphisms are jointly surjective.
- `AlgebraicGeometry.Scheme.Etale.isTerminalSectionsOfIsEmpty`: a sheaf on the small étale
  site has terminal sections over an object whose underlying scheme is empty. This is the
  sheaf condition for the empty covering. Hence every sheaf on the small étale site of an
  empty scheme is zero (`AlgebraicGeometry.Scheme.Etale.isZero_sheaf_of_isEmpty`).
- `AlgebraicGeometry.Scheme.Etale.isTerminalMkId`: `X`, with the identity, is a terminal object
  of its small étale site.
- `AlgebraicGeometry.Scheme.hasWeakSheafify_smallEtaleTopology`: sheafification for the
  localizations of the small étale site at all étale `U ⟶ X` gives sheafification for
  the small étale site itself, by localizing at the terminal object `𝟙 X`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{v} A] {X Y : Scheme.{u}}

variable (X) in
/-- The small étale site of a scheme `X : Scheme.{u}` has morphisms in `Type u`, so it is locally
small with respect to `u + 1`. Instance search does not derive this from
`locallySmall_of_univLE`, since it cannot solve the universe constraint `UnivLE.{u, u + 1}`. -/
instance Etale.locallySmall : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

variable (X) in
/-- The small étale site of a scheme `X : Scheme.{u}` is essentially small in the universe
`u + 1` of its objects. -/
instance Etale.essentiallySmall : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

section Functoriality

/-- The base change functor `Y.Etale ⥤ X.Etale` along a morphism `f : X ⟶ Y`, sending an
étale `V ⟶ Y` to the projection `V ×_Y X ⟶ X`. This is the functor along which the
pushforward `AlgebraicGeometry.Etale.lowerStar` and the pullback
`AlgebraicGeometry.Etale.upperStar` are defined. -/
def Hom.Etale (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

/-- The base change functor `f.Etale : Y.Etale ⥤ X.Etale`, `W ↦ W ×_Y X`, preserves finite
limits. The small étale sites have finite limits (`MorphismProperty.Over.hasFiniteLimits`):
the identity is a terminal object and fibre products are computed in schemes.
(blueprint: `situation-conventions`) -/
instance Hom.preservesFiniteLimits_etale (f : X ⟶ Y) : PreservesFiniteLimits f.Etale :=
  inferInstanceAs <|
    PreservesFiniteLimits (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f)

/-- The base change functor `f.Etale` is representably flat: the small étale site of `Y`
has finite limits and base change preserves them. -/
instance Hom.representablyFlat_etale (f : X ⟶ Y) : RepresentablyFlat f.Etale :=
  MorphismProperty.Over.representablyFlat_pullback @AlgebraicGeometry.Etale f

/-- The base change functor `f.Etale` preserves the covering sieves of the small étale
topologies: étale covers are stable under base change. -/
lemma Hom.coverPreserving_etale (f : X ⟶ Y) :
    CoverPreserving (smallEtaleTopology Y) (smallEtaleTopology X) f.Etale :=
  coverPreserving_overPullback @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl f

/-- The base change functor `f.Etale` is continuous for the small étale topologies: it
preserves covers by `AlgebraicGeometry.Scheme.Hom.coverPreserving_etale`, and compatible
families since it is representably flat. -/
instance Hom.isContinuous_etale (f : X ⟶ Y) :
    f.Etale.IsContinuous (smallEtaleTopology Y) (smallEtaleTopology X) :=
  isContinuous_overPullback @AlgebraicGeometry.Etale @AlgebraicGeometry.Etale le_rfl f

set_option backward.isDefEq.respectTransparency false in
/-- Base change along `f : X ⟶ Y` is compatible with the projections from the base changes
to the original étale `Y`-schemes:

```
   V ×_Y X ──(f.Etale.map g).left──→ U ×_Y X
      │                                 │
      │ pullback.fst V.hom f            │ pullback.fst U.hom f
      ↓                                 ↓
      V ────────────g.left────────────→  U
```
-/
lemma Hom.etale_map_left_comp_fst (f : X ⟶ Y) {U V : Y.Etale} (g : V ⟶ U) :
    (f.Etale.map g).left ≫ pullback.fst U.hom f = pullback.fst V.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

/-- Base change along `f : X ⟶ Y` is compatible with the projections to `X`. -/
lemma Hom.etale_map_left_comp_snd (f : X ⟶ Y) {U V : Y.Etale} (g : V ⟶ U) :
    (f.Etale.map g).left ≫ pullback.snd U.hom f = pullback.snd V.hom f :=
  pullback.lift_snd _ _ _

/-- The forgetful functor from the small étale site of `X` to `X`-schemes is continuous for
the étale topology on `Over X`. -/
instance Etale.isContinuous_forget :
    (Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) :=
  inferInstanceAs ((MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X).IsContinuous
    (X.smallGrothendieckTopology _) (X.overGrothendieckTopology _))

/-- The functor from the small étale site of `X` to schemes is continuous for the big étale
topology. -/
instance Etale.isContinuous_forget_comp_overForget :
    (Etale.forget X ⋙ Over.forget X).IsContinuous X.smallEtaleTopology etaleTopology :=
  Functor.isContinuous_comp _ _ _ (etaleTopology.over X) _

end Functoriality

section Sieves

/-- A sieve on an object of the small étale site is a covering exactly when the arrows in it
are jointly surjective. This is the sieve-level form of
`AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`, a sieve being generated by
the family of all its arrows. -/
lemma mem_smallEtaleTopology_iff {U : X.Etale} (S : Sieve U) :
    S ∈ X.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (V : X.Etale) (g : V ⟶ U), S g ∧ x ∈ Set.range g.left := by
  let ι := Σ V : X.Etale, { g : V ⟶ U // S g }
  have hS : Sieve.ofArrows (fun i : ι ↦ i.1) (fun i ↦ i.2.1) = S := by
    apply le_antisymm
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro V g ⟨i⟩
      exact i.2.2
    · intro V g hg
      exact ⟨V, 𝟙 V, g, Presieve.ofArrows.mk (⟨V, g, hg⟩ : ι), by simp⟩
  conv_lhs => rw [← hS, ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion]
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := h x
    exact ⟨i.1, i.2.1, i.2.2, hi⟩
  · intro h x
    obtain ⟨V, g, hg, hx⟩ := h x
    exact ⟨⟨V, g, hg⟩, hx⟩

end Sieves

section BaseChange

variable {W : Scheme.{u}} (g : W ⟶ X) [AlgebraicGeometry.Etale g] (V : X.Etale)

set_option backward.isDefEq.respectTransparency false in
/-- The base change `V ×_X W` of an étale `X`-scheme `V` along an étale morphism
`g : W ⟶ X`, viewed again as an étale `X`-scheme rather than as an étale `W`-scheme; it is
the image of `g.Etale.obj V` under the localization functor along `g`.

```
   V ×_X W ────→ W
      │          │ g
      ↓          ↓
      V ──V.hom─→ X
```
-/
def Etale.baseChange : X.Etale :=
  Etale.mk (pullback.fst V.hom g ≫ V.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The projection `V ×_X W ⟶ V`, a morphism of étale `X`-schemes. -/
def Etale.baseChangeHom : Etale.baseChange g V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom g) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of `V ×_X W` in `V` is the preimage of the range of `g`. -/
lemma Etale.range_baseChangeHom_left :
    Set.range (Etale.baseChangeHom g V).left.base = V.hom.base ⁻¹' Set.range g.base :=
  Pullback.range_fst V.hom g

end BaseChange

section Cover

variable (V : X.Etale) {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
  [∀ i, AlgebraicGeometry.Etale (g i)]

set_option backward.isDefEq.respectTransparency false in
/-- For a jointly surjective family of étale morphisms `g i : W i ⟶ X`, the base changes
`V ×_X W i` cover `V` in the small étale topology, for every étale `X`-scheme `V`. -/
lemma Etale.ofArrows_baseChange_mem_smallEtaleTopology
    (hg : ⋃ i, Set.range (g i).base = Set.univ) :
    Sieve.ofArrows (fun i => Etale.baseChange (g i) V)
        (fun i => Etale.baseChangeHom (g i) V) ∈ X.smallEtaleTopology V := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  have hrange : ∀ i, Set.range (Etale.baseChangeHom (g i) V).left.base =
      V.hom.base ⁻¹' Set.range (g i).base := fun i => Etale.range_baseChangeHom_left _ _
  simp only [hrange]
  rw [← Set.preimage_iUnion, hg, Set.preimage_univ]

end Cover

section EmptyObject

/-- The empty sieve on an object of the small étale site whose underlying scheme is empty is
a covering: the empty family of morphisms is (vacuously) jointly surjective. -/
lemma Etale.bot_mem_smallEtaleTopology (T : X.Etale) [IsEmpty T.left] :
    (⊥ : Sieve T) ∈ X.smallEtaleTopology T := by
  have hbot : (⊥ : Sieve T) = Sieve.ofArrows (Empty.elim : Empty → X.Etale) (fun i ↦ i.elim) := by
    simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty]
  rw [hbot, ofArrows_mem_smallEtaleTopology_iff]
  simp [Set.eq_univ_iff_forall, IsEmpty.forall_iff]

/-- A sheaf on the small étale site has terminal sections over an object whose underlying
scheme is empty. -/
def Etale.isTerminalSectionsOfIsEmpty
    (G : Sheaf X.smallEtaleTopology A) (T : X.Etale) [IsEmpty T.left] :
    IsTerminal (G.obj.obj (op T)) :=
  G.isTerminalOfBotCover T (Etale.bot_mem_smallEtaleTopology T)

/-- On the small étale site of an empty scheme every sheaf with values in a category with a
zero object is zero: its sections over every object are terminal. -/
lemma Etale.isZero_sheaf_of_isEmpty [Preadditive A] [HasZeroObject A] [IsEmpty X]
    (G : Sheaf X.smallEtaleTopology A) : IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  ext T
  have : IsEmpty T.unop.left := ⟨fun x ↦ isEmptyElim (show X from T.unop.hom.base x)⟩
  exact (Etale.isTerminalSectionsOfIsEmpty G T.unop).isZero.eq_of_src _ _

end EmptyObject

section Terminal

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms into the terminal étale `X`-scheme `X` are unique. -/
lemma Etale.hom_ext_mk_id {V : X.Etale} (a b : V ⟶ Etale.mk (𝟙 X)) : a = b :=
  MorphismProperty.Over.Hom.ext ((Category.comp_id _).symm.trans ((MorphismProperty.Over.w a).trans
    ((MorphismProperty.Over.w b).symm.trans (Category.comp_id _))))

/-- The scheme `X`, with the identity, is a terminal object of its small étale site. -/
noncomputable def Etale.isTerminalMkId (X : Scheme.{u}) : IsTerminal (Etale.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun V ↦ MorphismProperty.Over.homMk V.hom (Category.comp_id _))
    (fun _ _ ↦ Etale.hom_ext_mk_id _ _)

end Terminal

section Sheafify

variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) A]

/-- Sheafification for the localizations of the small étale site at all étale `U ⟶ X`
gives sheafification for the small étale site itself, by localizing at the terminal
object `𝟙 X`. -/
instance hasWeakSheafify_smallEtaleTopology : HasWeakSheafify X.smallEtaleTopology A :=
  X.smallEtaleTopology.hasWeakSheafify_of_over_isTerminal A terminalIsTerminal

end Sheafify

end Scheme

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- **Sheaves of sets on the small étale site.** A presheaf of sets `P` on the small étale site
`X.Etale` is a sheaf (an object of `Sheaf X.smallEtaleTopology (Type w)`) if and only if for
every étale `U` over `X` and every family `gᵢ : Vᵢ ⟶ U` of étale `X`-morphisms that is jointly
surjective, the diagram `P(U) → ∏ᵢ P(Vᵢ) ⇉ ∏ᵢⱼ P(Vᵢ ×_U Vⱼ)` is an equalizer: every family of
sections agreeing on the fibre products `Vᵢ ×_U Vⱼ` glues to a unique section on `U`.
(blueprint: `situation-conventions`) -/
theorem isSheaf_smallEtaleTopology_iff {X : Scheme.{u}} (P : X.Etaleᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf X.smallEtaleTopology P ↔
      ∀ (U : X.Etale) (ι : Type (u + 1)) (V : ι → X.Etale) (g : ∀ i, V i ⟶ U),
        ⋃ i, Set.range (g i).left = Set.univ →
        ∀ x : ∀ i, P.obj (op (V i)),
          (∀ i j, P.map (pullback.fst (g i) (g j)).op (x i) =
            P.map (pullback.snd (g i) (g j)).op (x j)) →
          ∃! s : P.obj (op U), ∀ i, P.map (g i).op s = x i := by
  rw [isSheaf_iff_isSheaf_of_type]
  constructor
  · intro h U ι V g hg x hx
    have hS := (ofArrows_mem_smallEtaleTopology_iff g).2 hg
    exact (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1
      ((Presieve.isSheafFor_iff_generate _).2 (h _ hS)) x hx
  · intro h U S hS
    let ι := Σ V : X.Etale, { g : V ⟶ U // S g }
    have hS' : Sieve.ofArrows (fun i : ι ↦ i.1) (fun i ↦ i.2.1) = S := by
      apply le_antisymm
      · rw [Sieve.ofArrows, Sieve.generate_le_iff]
        rintro V g ⟨i⟩
        exact i.2.2
      · intro V g hg
        exact ⟨V, 𝟙 V, g, Presieve.ofArrows.mk (⟨V, g, hg⟩ : ι), by simp⟩
    rw [← hS'] at hS ⊢
    rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff_pullbacks]
    exact h U ι _ _ ((ofArrows_mem_smallEtaleTopology_iff _).1 hS)

end AlgebraicGeometry.Scheme
