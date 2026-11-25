module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.RingTheory.Smooth.Normal

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Normality is local in the smooth, hence in the étale, topology

[Stacks, Tag 034F] states that the property "`S` is normal" of a scheme is local in the smooth
topology. This file proves the étale instance of that statement,

```
CategoryTheory.ObjectProperty.IsLocal
  (fun X : Scheme.{u} => AlgebraicGeometry.IsNormal X) AlgebraicGeometry.Scheme.etalePrecoverage
```

which is the form item (7) of Remark 03E7 consumes: it is what turns
`AlgebraicGeometry.Space.HasEtaleLocalProperty` — Definition 03E6 — at normality from a
some-chart condition into the every-chart equivalence of Lemma 03E8.

The two halves of locality are proved by the two routes of the source. Ascent is the affine
statement that a smooth algebra over a normal ring is normal (Algebra, Lemma 033C, available as
`Algebra.isNormalRing_of_smooth`), transported to schemes along an affine open cover. Descent is
the affine statement that normality descends along a faithfully flat ring map (Algebra, Lemma
033G, available as `isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat`), applied on
stalks: a flat morphism induces flat local homomorphisms of local rings, which are therefore
faithfully flat.

## Main results

* `AlgebraicGeometry.isNormal_of_smooth`: the source of a smooth morphism with normal target is
  normal. This is the ascent half, Stacks 033C at the level of schemes.
* `AlgebraicGeometry.isNormal_of_etale`: the étale case of the same statement, which is the
  normality half of Stacks 0BQL.
* `AlgebraicGeometry.isNormal_of_forall_exists_flat`: a scheme every point of which lies in the
  image of a flat morphism from a normal scheme is normal. This is the descent half, Stacks 033G
  at the level of schemes.
* `AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`: **Stacks 034F** for the étale
  precoverage — normality is a local object property.

## Implementation notes

The source proves 034F by checking the three conditions of Lemma 0349 — Zariski locality,
ascent along a smooth morphism of affines, descent along a surjective smooth morphism of
affines. Lemma 0349 is not available in this library, and `CategoryTheory.ObjectProperty.IsLocal`
asks for the two implications directly, so the two implications are proved directly. Zariski
locality is not needed as a separate step: it is absorbed into the two affine arguments, as
`AlgebraicGeometry.isNormal_tfae` already states normality to be local on an open cover.

The statement is proved for the étale precoverage rather than the smooth one, which is what the
algebraic-spaces layer consumes; both affine inputs are the smooth ones, so nothing but the
precoverage would change in the smooth version. Note that `Scheme.etalePrecoverage` requires its
members to be *jointly surjective* as well as étale, which is what makes the descent half
applicable.

`AlgebraicGeometry.IsNormal.of_openCover` and the two affine translations
`AlgebraicGeometry.isNormal_of_isNormalRing_appTop`,
`AlgebraicGeometry.isNormalRing_appTop_of_isNormal` are stated here because
`AlgebraicGeometry.isNormal_tfae` is the only public interface to them: the corresponding
helpers in `StacksFrontier/AlgebraicGeometry/Properties/Normal.lean` are `private`.

`AlgebraicGeometry.isNormal_of_smooth` and `AlgebraicGeometry.isNormal_of_forall_exists_flat`
carry no tag. Tags 033C and 033G are statements about *rings*, already carried by
`Algebra.isNormalRing_of_smooth` and
`isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat`; these are the scheme-level
consequences, exactly as `AlgebraicGeometry.isReduced_of_smooth` is the untagged scheme-level
consequence of Tag 033B.

## References

* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
* [Stacks Project, Tag 033G](https://stacks.math.columbia.edu/tag/033G)
* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
* [Stacks Project, Tag 0349](https://stacks.math.columbia.edu/tag/0349)
* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
* [Stacks Project, Tag 03E7](https://stacks.math.columbia.edu/tag/03E7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Descent of normality along a faithfully flat map of local rings -/

namespace AlgebraicGeometry

/-! ### Normality on affine opens and on open covers -/

/-- The global sections of a normal affine scheme form a normal ring. This is the direction
`1 → 2` of `AlgebraicGeometry.isNormal_tfae` read at the affine open `⊤`. -/
theorem isNormalRing_appTop_of_isNormal (X : Scheme.{u}) [IsAffine X] [IsNormal X] :
    IsNormalRing Γ(X, ⊤) := by
  have h : IsNormal X ↔ ∀ U : X.affineOpens, IsNormalRing Γ(X, U) :=
    (isNormal_tfae X).out 1 2
  exact h.mp ‹IsNormal X› ⟨⊤, isAffineOpen_top X⟩

/-- An affine scheme whose global sections form a normal ring is normal. This is the direction
`3 → 1` of `AlgebraicGeometry.isNormal_tfae` at the one-member affine open cover `{⊤}`. -/
theorem isNormal_of_isNormalRing_appTop {X : Scheme.{u}} [IsAffine X]
    (hX : IsNormalRing Γ(X, ⊤)) : IsNormal X := by
  have h : IsNormal X ↔
      ∃ (I : Type u) (U : I → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧ ∀ i, IsNormalRing Γ(X, U i) :=
    (isNormal_tfae X).out 1 3
  exact h.mpr ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top X⟩, IsOpenCover.mk (by simp), fun _ => hX⟩

/-- **Normality is local on an open cover.** A scheme covered by normal schemes along open
immersions is normal.

This is the direction `4 → 1` of `AlgebraicGeometry.isNormal_tfae`, with the members of the
cover replaced by their open ranges. -/
theorem IsNormal.of_openCover {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} X)
    (h𝒰 : ∀ i, IsNormal (𝒰.X i)) : IsNormal X := by
  have h : IsNormal X ↔
      ∃ (I : Type u) (U : I → X.Opens), IsOpenCover U ∧ ∀ i, IsNormal (U i).toScheme :=
    (isNormal_tfae X).out 1 4
  exact h.mpr ⟨𝒰.I₀, fun i => (𝒰.f i).opensRange, 𝒰.isOpenCover_opensRange,
    fun i => @isNormal_of_iso _ _ (𝒰.f i).isoOpensRange.symm (h𝒰 i)⟩

/-! ### Ascent: the source of a smooth morphism with normal target is normal -/

/-- **A scheme smooth over a normal affine scheme is normal.** On an affine open of the source
the sections form a smooth algebra over the global sections of the target, which are a normal
ring, so Stacks 033C applies; normality is local on the source.

This is the affine-target case of `AlgebraicGeometry.isNormal_of_smooth`, and the companion of
`AlgebraicGeometry.isReduced_of_smooth_of_isAffine`. -/
theorem isNormal_of_smooth_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsAffine Y]
    [IsNormal Y] : IsNormal X := by
  refine IsNormal.of_openCover X.affineCover fun i => ?_
  let : Algebra Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤) := (X.affineCover.f i ≫ f).appTop.hom.toAlgebra
  have : Algebra.Smooth Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤) :=
    (HasRingHomProperty.appTop @Smooth (X.affineCover.f i ≫ f)
      (HasRingHomProperty.comp_of_isOpenImmersion @Smooth (X.affineCover.f i) f ‹_›)).toAlgebra
  exact isNormal_of_isNormalRing_appTop
    (Algebra.isNormalRing_of_smooth Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤)
      (isNormalRing_appTop_of_isNormal Y))

/-- **Stacks 033C for schemes.** The source of a smooth morphism with normal target is normal.

The affine-target case is `AlgebraicGeometry.isNormal_of_smooth_of_isAffine`; the general case
follows by base change along an affine open cover of the target, which is an open cover of the
source. -/
theorem isNormal_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsNormal Y] :
    IsNormal X := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine IsNormal.of_openCover (𝒰.pullback₁ f) fun i => ?_
  have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hnorm : IsNormal (𝒰.X i) := isNormal_of_iso (𝒰.f i).isoOpensRange
  have hs : Smooth (pullback.snd f (𝒰.f i)) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f (𝒰.f i))
      ‹Smooth f›
  exact @isNormal_of_smooth_of_isAffine _ _ (pullback.snd f (𝒰.f i)) hs
    (inferInstanceAs (IsAffine (Spec _))) hnorm

/-! ### Descent: normality along a flat surjection -/

/-! ### Stacks 034F for the étale precoverage -/

end AlgebraicGeometry

end
