/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.AlgebraicGeometry.Descent
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# The Hilbert functor

For a morphism of schemes `f : X ⟶ S` and `d : ℕ`, the Hilbert functor `Hilb^d_{X/S}` sends an
`S`-scheme `T` to the set of closed subschemes `Z ⊆ X_T = X ×[S] T` such that the projection
`Z ⟶ T` is finite, flat and locally of finite presentation of degree `d`. Closed subschemes of
`X_T` are encoded by quasi-coherent ideal sheaves, i.e. by
`AlgebraicGeometry.Scheme.IdealSheafData`, and the degree is the rank function
`AlgebraicGeometry.Scheme.Hom.finrank` of a finite flat morphism. Functoriality is base change
of ideal sheaves, `AlgebraicGeometry.Scheme.IdealSheafData.comap`, along the base-change maps
`AlgebraicGeometry.baseChangeMap` of the fibre products `X ×[S] T`.

We then prove that `Hilb^d_{X/S}` is a sheaf for the fppf topology, by fpqc descent of finite
locally free closed subschemes. Representability of `Hilb^d_{X/S}` in general is proved in
`WeilConjectures.AlgebraicGeometry.Hilbert.Representability`, and the Hilbert schemes of curves
are in `WeilConjectures.AlgebraicGeometry.Hilbert.Curve`.

## Implementation notes

That the defining condition is stable under base change — `IsHilbertSubscheme.comap` — is the
one obligation in the construction of `hilbertPresheaf`. Finiteness, flatness and local finite
presentation are `MorphismProperty.IsStableUnderBaseChange` in Mathlib, and the rank is invariant
under base change by `AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback`.

## Main definitions

- `AlgebraicGeometry.IsHilbertSubscheme`: the condition cutting out the Hilbert functor.
- `AlgebraicGeometry.hilbertPresheaf`: the Hilbert functor `Hilb^d_{X/S}`
  (blueprint `sk-the-hilbert-functor--definition-1`).

## Main statements

- `AlgebraicGeometry.IsHilbertSubscheme.comap`: the defining condition is stable under base
  change.
- `AlgebraicGeometry.IsHilbertSubscheme.isInvertible`: for a smooth curve, the points of the
  Hilbert functor are relative effective Cartier divisors.
- `AlgebraicGeometry.IsHilbertSubscheme.eq_of_le`: two points of `Hilb^d_{X/S}(T)` one of
  which contains the other are equal.
- `AlgebraicGeometry.isSheaf_hilbertPresheaf`: `Hilb^d_{X/S}` is an fppf sheaf
  (blueprint `theorem-hilbert-schemes-points-smooth-curve--1`), hence a Zariski sheaf
  (`AlgebraicGeometry.isSheaf_zariskiTopology_hilbertPresheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The condition cutting out the Hilbert functor: the closed subscheme of `X_T = X ×[S] T`
described by the ideal sheaf `I` is finite, flat and locally of finite presentation of
degree `d` over `T`. -/
def IsHilbertSubscheme (f : X ⟶ S) (d : ℕ) (T : Over S)
    (I : (Limits.pullback f T.hom).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
    Flat (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        ∀ t, (I.subschemeι ≫ Limits.pullback.snd f T.hom).finrank t = d

/-- The defining condition of the Hilbert functor is stable under base change along a morphism
`φ : T' ⟶ T` of `S`-schemes.

Finiteness, flatness and local finite presentation are stable under base change, and so is the
rank `AlgebraicGeometry.Scheme.Hom.finrank`, since the closed subscheme cut out by the pullback
ideal sheaf is the base change of the one cut out by `I`. This makes `T ↦ Hilb^d_{X/S}(T)` a
contravariant functor by base change of closed subschemes, `AlgebraicGeometry.hilbertPresheaf`.

(blueprint: `prose-C-08`, `prose-C-08`) -/
theorem IsHilbertSubscheme.comap {f : X ⟶ S} {d : ℕ} {T T' : Over S} (φ : T' ⟶ T)
    {I : (Limits.pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f d T I) :
    IsHilbertSubscheme f d T' (I.comap (baseChangeMap f φ)) := by
  -- the closed subscheme cut out by the pullback is the base change of the one cut out by `I`
  have hsq : IsPullback ((I.comapIso (baseChangeMap f φ)).hom ≫ pullback.snd _ _)
      ((I.comap (baseChangeMap f φ)).subschemeι ≫ pullback.snd f T'.hom)
      (I.subschemeι ≫ pullback.snd f T.hom) φ.left :=
    ((IsPullback.of_hasPullback (baseChangeMap f φ) I.subschemeι).flip.paste_vert
      (isPullback_baseChangeMap f φ)).of_iso' (I.comapIso _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hI
  refine ⟨MorphismProperty.of_isPullback hsq h₁, MorphismProperty.of_isPullback hsq h₂,
    MorphismProperty.of_isPullback hsq h₃, fun t ↦ ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq]
  exact h₄ _

/-- **The points of the Hilbert functor of a smooth curve are divisors.** If `f : X ⟶ S` is
smooth of relative dimension `1`, then every point of `Hilb^d_{X/S}(T)` is a relative effective
Cartier divisor on `X_T/T`; in particular its ideal is invertible. This is
`AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat` for the base change
`X_T ⟶ T`, which is again smooth of relative dimension `1`. -/
theorem IsHilbertSubscheme.isInvertible {f : X ⟶ S} [SmoothOfRelativeDimension 1 f] {d : ℕ}
    {T : Over S} {I : (Limits.pullback f T.hom).IdealSheafData}
    (hI : IsHilbertSubscheme f d T I) : I.IsInvertible :=
  have : SmoothOfRelativeDimension 1 (Limits.pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat _ hI.1 hI.2.1 hI.2.2.1

/-- **Nested points of the Hilbert functor are equal.** If `Z ⊆ Z'` are closed subschemes of
`X_T` which are both finite locally free of degree `d` over `T`, i.e. their ideals `I' ≤ I`
both lie in `Hilb^d_{X/S}(T)`, then `Z = Z'`: the surjection `𝒪_{Z'} ⟶ 𝒪_Z` of finite locally
free `𝒪_T`-modules of the same rank `d` is an isomorphism. -/
theorem IsHilbertSubscheme.eq_of_le {f : X ⟶ S} {d : ℕ} {T : Over S}
    {I J : (Limits.pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f d T I)
    (hJ : IsHilbertSubscheme f d T J) (h : I ≤ J) : I = J := by
  obtain ⟨hI₁, hI₂, -, hI₄⟩ := hI
  obtain ⟨-, hJ₂, -, hJ₄⟩ := hJ
  have e : Scheme.IdealSheafData.inclusion h ≫ I.subschemeι ≫ pullback.snd f T.hom =
      J.subschemeι ≫ pullback.snd f T.hom :=
    Scheme.IdealSheafData.inclusion_subschemeι_assoc h _
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h) :=
    .of_comp_isClosedImmersion _ I.subschemeι
  have : Flat (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι ≫ pullback.snd f T.hom) := by
    rwa [e]
  have : IsIso (Scheme.IdealSheafData.inclusion h) :=
    Scheme.Hom.isIso_of_isClosedImmersion_of_finrank_eq _ (I.subschemeι ≫ pullback.snd f T.hom)
      fun t ↦ by rw [e, hI₄, hJ₄]
  rw [← I.ker_subschemeι, ← J.ker_subschemeι,
    ← Scheme.IdealSheafData.inclusion_subschemeι h, Scheme.Hom.ker_comp_of_isIso]

/-- The Hilbert functor. For `f : X ⟶ S` and `d : ℕ`, `Hilb^d_{X/S}` sends an `S`-scheme `T` to
the set of closed subschemes `Z ⊆ X_T = X ×[S] T`, encoded as quasi-coherent ideal sheaves `I`
on `X_T`, such that the projection `Z ⟶ T` is finite, flat, locally of finite presentation and
of degree `d`, the last condition meaning that its rank function `Scheme.Hom.finrank` is
constantly `d`.

An `S`-morphism `φ : T' ⟶ T` acts by pulling back the ideal sheaf along the base-change map
`X_{T'} ⟶ X_T`.

(blueprint: `sk-the-hilbert-functor--definition-1`, `prose-C-08`) -/
noncomputable def hilbertPresheaf (f : X ⟶ S) (d : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := { I : (Limits.pullback f T.unop.hom).IdealSheafData // IsHilbertSubscheme f d T.unop I }
  map φ := TypeCat.ofHom fun I ↦ ⟨I.1.comap (baseChangeMap f φ.unop),
    IsHilbertSubscheme.comap φ.unop I.2⟩
  map_id T := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp [baseChangeMap_id, Scheme.IdealSheafData.comap_id]))
  map_comp φ ψ := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp only [unop_comp, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
    rfl))

/-- **The Hilbert functor is an fppf sheaf.** `Hilb^d_{X/S}` is a sheaf for the fppf topology on
`S`-schemes, that is for `AlgebraicGeometry.Scheme.fppfTopology` localized to `Over S` (the big
fppf site of `S`, blueprint `definition-relative-picard-functor--1`), hence in particular for the
coarser Zariski topology (`AlgebraicGeometry.isSheaf_zariskiTopology_hilbertPresheaf`).

A covering sieve of `T` is in particular an fpqc covering of `T.left`, the base changes of `X_T`
along its members are the `X_{T'}`, and a compatible family of points of `Hilb^d_{X/S}` is a
descent datum of closed subschemes; it glues uniquely by
`AlgebraicGeometry.isSheaf_fpqc_finiteLocallyFreeSubscheme` (blueprint `det-thm-picard-descent`,
part (D2)).

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`) -/
theorem isSheaf_hilbertPresheaf (f : X ⟶ S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (hilbertPresheaf f d) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR x hx
  -- the covering family of `T.left` underlying `R`
  let ι := { p : Σ Y : Over S, Y ⟶ T // R p.2 }
  let g : ∀ i : ι, i.1.1.left ⟶ T.left := fun i ↦ i.1.2.left
  have hg : Sieve.ofArrows _ g ∈ Scheme.fpqcTopology T.left := by
    refine Scheme.fpqcTopology.superset_covering ?_
      (Scheme.fppfTopology_le_fpqcTopology _ ((GrothendieckTopology.mem_over_iff _ _).1 hR))
    rintro Y h ⟨Z, k, l, hk, rfl⟩
    exact (Sieve.mem_ofArrows_iff ..).mpr ⟨⟨⟨Z, k⟩, hk⟩, l, rfl⟩
  let I : ∀ i : ι, (pullback f i.1.1.hom).IdealSheafData := fun i ↦ (x i.1.2 i.2).1
  have hI (i : ι) : IsHilbertSubscheme f d i.1.1 (I i) := (x i.1.2 i.2).2
  have hcompat : ∀ ⦃W : Scheme.{u}⦄ ⦃i j : ι⦄ (a : W ⟶ pullback f i.1.1.hom)
      (b : W ⟶ pullback f j.1.1.hom), a ≫ baseChangeMap f i.1.2 = b ≫ baseChangeMap f j.1.2 →
      (I i).comap a = (I j).comap b := by
    intro W i j a b hab
    have hfst {Y Y' : Over S} (φ : Y ⟶ Y') :
        baseChangeMap f φ ≫ pullback.fst f Y'.hom = pullback.fst f Y.hom :=
      pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
    have hsnd {Y Y' : Over S} (φ : Y ⟶ Y') :
        baseChangeMap f φ ≫ pullback.snd f Y'.hom = pullback.snd f Y.hom ≫ φ.left :=
      pullback.lift_snd _ _ _
    have hab₁ : a ≫ pullback.fst f i.1.1.hom = b ≫ pullback.fst f j.1.1.hom := by
      simpa only [Category.assoc, hfst] using congrArg (· ≫ pullback.fst f T.hom) hab
    have hab₂ : (a ≫ pullback.snd f i.1.1.hom) ≫ i.1.2.left =
        (b ≫ pullback.snd f j.1.1.hom) ≫ j.1.2.left := by
      simpa only [Category.assoc, hsnd] using congrArg (· ≫ pullback.snd f T.hom) hab
    have hW : (a ≫ pullback.snd f i.1.1.hom) ≫ i.1.1.hom =
        (b ≫ pullback.snd f j.1.1.hom) ≫ j.1.1.hom := by
      simpa only [Category.assoc, Over.w] using congrArg (· ≫ T.hom) hab₂
    let Z : Over S := Over.mk ((a ≫ pullback.snd f i.1.1.hom) ≫ i.1.1.hom)
    let g₁ : Z ⟶ i.1.1 := Over.homMk (a ≫ pullback.snd f i.1.1.hom)
    let g₂ : Z ⟶ j.1.1 := Over.homMk (b ≫ pullback.snd f j.1.1.hom) hW.symm
    have hcomm : g₁ ≫ i.1.2 = g₂ ≫ j.1.2 := by
      ext
      exact hab₂
    have key := congrArg Subtype.val (hx g₁ g₂ i.2 j.2 hcomm)
    let s : W ⟶ pullback f Z.hom := pullback.lift (a ≫ pullback.fst f i.1.1.hom) (𝟙 W) (by
      simp [Z, pullback.condition])
    have hs₁ : s ≫ baseChangeMap f g₁ = a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfst g₁]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, hsnd g₁]
        exact pullback.lift_snd_assoc _ _ _ _ |>.trans (Category.id_comp _)
    have hs₂ : s ≫ baseChangeMap f g₂ = b := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfst g₂]
        exact (pullback.lift_fst _ _ _).trans hab₁
      · rw [Category.assoc, hsnd g₂]
        exact pullback.lift_snd_assoc _ _ _ _ |>.trans (Category.id_comp _)
    rw [← hs₁, ← hs₂, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact congrArg (Scheme.IdealSheafData.comap · s) key
  obtain ⟨J, hJ, hfin, hflat, hfp, hdeg, huniq⟩ := isSheaf_fpqc_finiteLocallyFreeSubscheme g hg
    (pullback.snd f T.hom) d (fun i ↦ baseChangeMap f i.1.2) (fun i ↦ pullback.snd f i.1.1.hom)
    (fun i ↦ isPullback_baseChangeMap f i.1.2) I (fun i ↦ (hI i).1) (fun i ↦ (hI i).2.1)
    (fun i ↦ (hI i).2.2.1) (fun i ↦ (hI i).2.2.2) hcompat
  refine ⟨⟨J, hfin, hflat, hfp, hdeg⟩, fun Y h hh ↦ Subtype.ext (hJ ⟨⟨Y, h⟩, hh⟩), ?_⟩
  intro y hy
  refine Subtype.ext (huniq _ fun i ↦ ?_)
  exact congrArg Subtype.val (hy i.1.2 i.2)

/-- The Hilbert functor is a Zariski sheaf, since it is an fppf sheaf and Zariski coverings are
fppf coverings.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, `rem-ptr-pc-fppf-site-5`) -/
lemma isSheaf_zariskiTopology_hilbertPresheaf (f : X ⟶ S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (hilbertPresheaf f d) := by
  have h := isSheaf_hilbertPresheaf f d
  rw [isSheaf_iff_isSheaf_of_type] at h ⊢
  refine Presieve.isSheaf_of_le _ (fun T R hR ↦ ?_) h
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hR


end AlgebraicGeometry
