/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-!
# Rigidity

The rigidity lemma says that a morphism `g : X ×_K Y ⟶ Z` of `K`-schemes, with `X` proper,
geometrically connected and geometrically reduced over `K`, `Y` connected and `Z` separated over
`K`, which contracts a single fibre `X ×_K {y₀}` to a point, necessarily factors through the
second projection. This file also records two propositions on the fibres of the morphism
`(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `Y`: the locus of `y` whose geometric fibre is contracted to
a point is closed, and the locus of `y` whose fibre has finite image is open. The second one is
independent of the rigidity lemma.

All three statements are set in the commutative square

```
  pullback fX fY ───── pullback.snd ─────▶ Y
        │        ╲                         │
        │         ╲  g                     │ fY
 pullback.fst      ╲                       │
        │           ╲                      │
        ▼            ▼                     ▼
        X ─── fX ──▶ Spec K ◀─── fZ ────── Z
```

in which `hg : g ≫ fZ = pullback.fst fX fY ≫ fX` says that `g` is a morphism of `K`-schemes.
The fibres of `(g, pr₂) = pullback.lift g (pullback.snd fX fY) _` over `Y` are spelled with
`AlgebraicGeometry.Scheme.Hom.fiberMap`.

The blueprint uses the rigidity lemma to prove that abelian varieties are commutative. That
corollary is proved instead in `WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic` from
Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`, so the results
below are recorded for their own sake and have no consumer in this repository yet.

## Main statements

- `AlgebraicGeometry.isClosed_setOf_subsingleton_range_fiberMap`: for a morphism `F : A ⟶ B` over
  `Y` with `A` universally open and locally of finite type and `B` separated over `Y`, the locus
  of `y : Y` whose geometric fibre `F_ȳ` has subsingleton image is closed in `Y`.
- `AlgebraicGeometry.isClosed_setOf_subsingleton_image`: the locus of `y : Y` whose geometric
  fibre is contracted to a single point is closed in `Y`.
- `AlgebraicGeometry.eventually_finite_image`: if the fibre over `y₀` has finite image, then so
  does the fibre over every `y` near `y₀`.
- `AlgebraicGeometry.exists_mem_and_comp_eq_of_subsingleton_image`: if `g` contracts the fibre
  over `y`, then `g` factors through the second projection over a neighbourhood of `y`.
- `AlgebraicGeometry.exists_eq_snd_comp`: the rigidity lemma, `g` factors through the second
  projection.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- The general form of blueprint `lemma-rigidity`. Let `F : A ⟶ B` be a morphism
of schemes over `Y`, with `a : A ⟶ Y` universally open and locally of finite type and with
`b : B ⟶ Y` separated. Then the locus of `y : Y` such that the base change
`F_ȳ : A_{κ(y)‾} ⟶ B_{κ(y)‾}` of `F` along the geometric point `ȳ` over `y` has subsingleton
image is closed.

Following the blueprint, write `Φ : A ×_Y A ⟶ B ×_Y B` for the product of `F` with itself and
`π : A ×_Y A ⟶ Y` for the projection. The locus is the complement of the image under `π` of the
open set `U` of points that `Φ` sends off the diagonal of `b`, and `π` is an open map. To see
that `y` lies outside `π(U)` exactly when the image of `F_ȳ` is a subsingleton, base change
along `ȳ`: the diagonal of `B_{κ(y)‾}` is the preimage of the diagonal of `b`
(`Scheme.Pullback.map_fst_mem_range_diagonal_iff`), and if the image of `F_ȳ` is a single point
then that point is a `κ(y)‾`-point, since `A_{κ(y)‾}` has a closed, hence rational, point. -/
theorem isClosed_setOf_subsingleton_range_fiberMap {A B Y : Scheme.{u}} (a : A ⟶ Y)
    (b : B ⟶ Y) [UniversallyOpen a] [LocallyOfFiniteType a] [IsSeparated b] (F : A ⟶ B)
    (hF : F ≫ b = a) :
    IsClosed {y : Y | (Set.range (Scheme.Hom.fiberMap F hF
      (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton} := by
  let Φ := pullback.map a a b b F F (𝟙 Y) (by simp [hF]) (by simp [hF])
  let π := pullback.fst a a ≫ a
  let U : Set ↑(pullback a a) := Φ ⁻¹' (Set.range (pullback.diagonal b))ᶜ
  have hU : IsOpen U :=
    (pullback.diagonal b).isClosedEmbedding.isClosed_range.isOpen_compl.preimage Φ.continuous
  suffices key : ∀ y, (Set.range
      (Scheme.Hom.fiberMap F hF (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton ↔
      y ∉ π '' U by
    convert (π.isOpenMap U hU).isClosed_compl using 1
    ext y
    exact key y
  intro y
  set p := Y.fromSpecAlgebraicClosureResidueField y
  have hp (q) : p q = y := by
    simp only [p, Scheme.fromSpecAlgebraicClosureResidueField, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  let FΩ := Scheme.Hom.fiberMap F hF p
  have hFΩ : FΩ ≫ pullback.snd b p = pullback.snd a p := by simp [FΩ, Scheme.Hom.fiberMap]
  let hA := pullback.map _ _ a a (pullback.fst a p) (pullback.fst a p) p
    pullback.condition.symm pullback.condition.symm
  let hB := pullback.map _ _ b b (pullback.fst b p) (pullback.fst b p) p
    pullback.condition.symm pullback.condition.symm
  let ΦΩ := pullback.map (pullback.snd a p) (pullback.snd a p) (pullback.snd b p)
    (pullback.snd b p) FΩ FΩ (𝟙 _) (by simp [hFΩ]) (by simp [hFΩ])
  have hcomm : hA ≫ Φ = ΦΩ ≫ hB := by
    ext <;> simp [hA, hB, Φ, ΦΩ, FΩ, Scheme.Hom.fiberMap]
  have hΦΩ₁ (v) : pullback.fst (pullback.snd b p) (pullback.snd b p) (ΦΩ v) =
      FΩ (pullback.fst (pullback.snd a p) (pullback.snd a p) v) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp [ΦΩ]
  have hΦΩ₂ (v) : pullback.snd (pullback.snd b p) (pullback.snd b p) (ΦΩ v) =
      FΩ (pullback.snd (pullback.snd a p) (pullback.snd a p) v) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    simp [ΦΩ]
  constructor
  · rintro hsub ⟨w, hw, hπw⟩
    apply hw
    obtain ⟨c, rfl⟩ : w ∈ Set.range (pullback.fst π p) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨IsLocalRing.closedPoint _, by rw [hp, hπw]⟩
    let ψ : pullback π p ⟶ pullback (pullback.snd a p) (pullback.snd a p) :=
      pullback.lift (pullback.lift (pullback.fst π p ≫ pullback.fst a a) (pullback.snd π p)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst π p ≫ pullback.snd a a) (pullback.snd π p)
          (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition))
        (by simp)
    have hψ : ψ ≫ hA = pullback.fst π p := by ext <;> simp [ψ, hA]
    rw [← hψ, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply,
      Scheme.Pullback.map_fst_mem_range_diagonal_iff]
    have : JacobsonSpace ↑(pullback a p) := LocallyOfFiniteType.jacobsonSpace (pullback.snd a p)
    obtain ⟨e, -, he⟩ := nonempty_inter_closedPoints
      ⟨pullback.fst (pullback.snd a p) (pullback.snd a p) (ψ c), Set.mem_univ _⟩
      isClosed_univ.isLocallyClosed
    let σ := pointOfClosedPoint (pullback.snd a p) e he
    have hσ : (σ ≫ FΩ) (IsLocalRing.closedPoint _) = FΩ e := by simp [σ]
    exact Scheme.Pullback.mem_range_diagonal_of_mem_range (σ ≫ FΩ) (by simp [σ, hFΩ]) _
      ⟨_, hσ.trans ((hsub ⟨_, rfl⟩ ⟨_, rfl⟩).trans (hΦΩ₁ _).symm)⟩
      ⟨_, hσ.trans ((hsub ⟨_, rfl⟩ ⟨_, rfl⟩).trans (hΦΩ₂ _).symm)⟩
  · intro hy
    rintro _ ⟨x₁, rfl⟩ _ ⟨x₂, rfl⟩
    by_contra hne
    obtain ⟨v, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd a p)
      (g := pullback.snd a p) x₁ x₂ (Subsingleton.elim _ _)
    refine hy ⟨hA v, fun h ↦ hne ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply,
        Scheme.Pullback.map_fst_mem_range_diagonal_iff] at h
      obtain ⟨β, hβ⟩ := h
      rw [← hΦΩ₁, ← hΦΩ₂, ← hβ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullback.diagonal_fst, pullback.diagonal_snd]
    · have : hA ≫ π = (pullback.fst _ _ ≫ pullback.snd a p) ≫ p := by
        simp [hA, π, pullback.condition]
      rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply, hp]

/-- Blueprint `lemma-rigidity`: The locus of constant fibres is closed

Let `X` be a `K`-scheme proper over `K`, let `Z` be separated over `K`, let `Y` be any
`K`-scheme and let `g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. For `y : Y` let
`g_ȳ : X_{κ(y)‾} ⟶ Z_{κ(y)‾}` be the base change of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` along the
geometric point `ȳ` over `y`. Then the locus `L = {y ∈ Y | g_ȳ(X_{κ(y)‾}) is a subsingleton}` is
closed in `Y`. For nonempty `X` the image of `g_ȳ` is a subsingleton exactly when it is a single
point.

Constancy must be tested on the geometric fibre, not on the set-theoretic image of
`X ×_K {y}` in `Z`: for `K` algebraically closed of characteristic `≠ 2`,
`X = Spec K ⊔ Spec K`, `Y = Z = 𝔸¹_K` and `g = (t ↦ t, t ↦ -t)`, that image is one point
exactly for `y` the generic point or `y = 0`, which is not a closed set. -/
theorem isClosed_setOf_subsingleton_image {X Y Z : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX]
    [IsSeparated fZ] (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) :
    IsClosed {y : Y | (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecAlgebraicClosureResidueField y)).base).Subsingleton} :=
  isClosed_setOf_subsingleton_range_fiberMap _ _ _ _

/-- Finiteness of the image is open in the parameter

Let `X` be proper over `K`, let `Z` be separated and locally of finite type over `K`, let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes and let `y₀ ∈ Y`. For `y : Y` let
`g_y : X_{κ(y)} ⟶ Z_{κ(y)}` be the fibre of `(g, pr₂) : X ×_K Y ⟶ Z ×_K Y` over `y`. If the
image of `g_{y₀}` is finite, then the image of `g_y` is finite for every `y` in some open
neighbourhood of `y₀`.

Following the blueprint, apply Stacks Tag 0AH8
(`exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`) to `h = (g, pr₂)` over
`Y`: as `h ≫ pr₂ = pr₂` is proper and `pr₂ : Z ×_K Y ⟶ Y` is separated and locally of finite type,
the image of `h` is finite over an open neighbourhood `U` of `y₀`, so its fibres over the points of
`U` are finite. The image of `g_y` is identified with `h (pr₂⁻¹ {y})` by
`Scheme.Hom.finite_range_fiberMap_iff`.

The rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp` does not depend on this result. -/
theorem eventually_finite_image {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [IsSeparated fZ]
    [LocallyOfFiniteType fZ] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecResidueField y₀)).base).Finite) :
    ∀ᶠ y in 𝓝 y₀, (Set.range (Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
        (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecResidueField y)).base).Finite := by
  set h := pullback.lift (f := fZ) (g := fY) g (pullback.snd fX fY)
    (by rw [hg, pullback.condition])
  have hh : h ≫ pullback.snd fZ fY = pullback.snd fX fY := pullback.lift_snd _ _ _
  replace hy₀ := (Scheme.Hom.finite_range_fiberMap_iff h hh y₀).1 hy₀
  have : IsProper (h ≫ pullback.snd fZ fY) := by rw [hh]; infer_instance
  obtain ⟨U, hy₀U, hU⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    h (pullback.snd fZ fY) y₀ (by rwa [hh])
  filter_upwards [U.isOpen.mem_nhds hy₀U] with y hy
  refine (Scheme.Hom.finite_range_fiberMap_iff h hh y).2 ?_
  refine ((Scheme.Hom.finite_preimage_singleton_of_isFinite_morphismRestrict
    (h.imageι ≫ pullback.snd fZ fY) hy).image h.imageι).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨h.toImage x, ?_, ?_⟩ <;>
    simp_all [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]

/-- Step 4 of blueprint `lemma-rigidity` (`lemma-rigidity`): if `X` is proper,
geometrically connected and geometrically reduced over `K` and `g : X ×_K Y ⟶ Z` contracts the
fibre `X ×_K {y}` of the second projection `pr₂` to a point, then `g` factors through `pr₂` over
an open neighbourhood `U` of `y`: there is `h : U ⟶ Z` over `K` such that `a ≫ g = b ≫ h`
whenever `a : T ⟶ X ×_K Y` and `b : T ⟶ U` agree in `Y`.

Following the blueprint, choose an affine open `V` around the image point. As `pr₂` is closed,
`Y ∖ pr₂ (g⁻¹ (Z ∖ V))` is an open neighbourhood of `y`; choose an affine open `U` around `y`
inside it, so that `g` maps `X ×_K U` into `V`. Since `Γ(X, 𝒪_X) = K` (Stacks 0BUG), flat base
change gives `Γ(X ×_K U, 𝒪) = Γ(U, 𝒪_U)`, so the morphism `X ×_K U ⟶ V` to the affine scheme
`V` factors through `pr₂ : X ×_K U ⟶ U`. -/
theorem exists_mem_and_comp_eq_of_subsingleton_image {X Y Z : Scheme.{u}}
    (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX]
    [GeometricallyConnected fX] [GeometricallyReduced fX] (g : pullback fX fY ⟶ Z)
    (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y : Y)
    (hy : (g '' (pullback.snd fX fY ⁻¹' {y})).Subsingleton) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ Z, h ≫ fZ = U.ι ≫ fY ∧
      ∀ {T : Scheme.{u}} (a : T ⟶ pullback fX fY) (b : T ⟶ U),
        a ≫ pullback.snd fX fY = b ≫ U.ι → a ≫ g = b ≫ h := by
  set p := pullback.snd fX fY
  obtain ⟨x, hx⟩ := p.surjective y
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  have hC : IsClosed (p '' (g ⁻¹' (V : Set Z)ᶜ)) :=
    p.isClosedMap _ (V.isOpen.isClosed_compl.preimage g.continuous)
  have hyC : y ∉ p '' (g ⁻¹' (V : Set Z)ᶜ) := by
    rintro ⟨x', hx', hx'y⟩
    exact hx' (hy ⟨x', hx'y, rfl⟩ ⟨x, hx, rfl⟩ ▸ hxV)
  obtain ⟨U, hU, hyU, hUC⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⟨_, hC.isOpen_compl⟩) hyC
  have : IsAffine U := hU
  have : IsAffine V := hV
  let fU := U.ι ≫ fY
  let j : pullback fX fU ⟶ pullback fX fY :=
    pullback.map _ _ _ _ (𝟙 X) U.ι (𝟙 _) (by simp) (by simp [fU])
  have hj : j ≫ p = pullback.snd fX fU ≫ U.ι := pullback.lift_snd _ _ _
  have hjV : Set.range (j ≫ g) ⊆ V := by
    rintro _ ⟨w, rfl⟩
    by_contra hw
    refine hUC (pullback.snd fX fU w).2 ⟨j w, hw, ?_⟩
    rw [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]
    rfl
  let φ : pullback fX fU ⟶ V := IsOpenImmersion.lift V.ι (j ≫ g) (by simpa using hjV)
  let _ : X.Over (Spec (.of K)) := ⟨fX⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  have : IsProper (X ↘ Spec (.of K)) := ‹IsProper fX›
  have : GeometricallyConnected (X ↘ Spec (.of K)) := ‹_›
  have : GeometricallyReduced (X ↘ Spec (.of K)) := ‹_›
  have : IsIso (pullback.snd fX fU).appTop :=
    Scheme.GlobalSectionsBijective.isIso_appTop_pullback_snd (k := K) (X := X) fU
  obtain ⟨h', hh'⟩ := (pullback.snd fX fU).exists_comp_eq_of_isIso_appTop φ
  have hfac : pullback.snd fX fU ≫ h' ≫ V.ι = j ≫ g := by
    rw [reassoc_of% hh']; exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hyU, h' ≫ V.ι, ?_, fun a b hab ↦ ?_⟩
  · refine (pullback.snd fX fU).cancel_left_of_isIso_appTop ?_
    rw [Category.assoc, reassoc_of% hfac, hg, pullback.condition]
    simpa using hj =≫ fY
  · have hab' : a ≫ pullback.fst fX fY ≫ fX = b ≫ fU := by
      rw [pullback.condition, reassoc_of% hab]
    have : a = pullback.lift (f := fX) (g := fU) (a ≫ pullback.fst fX fY) b
        (by simpa using hab') ≫ j := by
      ext
      · simp [j, pullback.map]
      · simp [j, p, hab, pullback.map]
    rw [this, Category.assoc, ← hfac, pullback.lift_snd_assoc]

/-- Blueprint `lemma-rigidity`: The rigidity lemma

Let `X`, `Y`, `Z` be `K`-schemes with `X` proper, geometrically connected and geometrically
reduced over `K`, with `Y` connected and with `Z` separated over `K`, and let
`g : X ×_K Y ⟶ Z` be a morphism of `K`-schemes. If `g (X ×_K {y₀})` is a single point for some
point `y₀ ∈ Y`, then `g` factors through the second projection: `g = pr₂ ≫ h` for some
`h : Y ⟶ Z`, that is, the triangle

```
  pullback fX fY ─── pullback.snd ──▶ Y
             ╲                        │
              ╲  g                    │ h
               ╲                      ▼
                ╲──────────────────▶ Z
```

commutes. The set `g (X ×_K {y₀})` is spelled as the range of the restriction of `g` to the
scheme-theoretic fibre of `pr₂` over `y₀`; the point `y₀` need not be `K`-rational.

Neither geometric hypothesis on `X` can be dropped on its own. For `K = ℝ`, `X = Spec ℂ`,
`Y = 𝔸¹_ℝ`, `Z = 𝔸¹_ℂ` and `g` the identity of `X ×_K Y = 𝔸¹_ℂ`, `X` is connected and
geometrically reduced but not geometrically connected, and `g` does not factor. For `K`
imperfect of characteristic `p`, `a ∈ K ∖ K^p`, `K' = K(a^{1/p})`, `X = Spec K'`, `Y = 𝔸¹_K`,
`Z = 𝔸¹_{K'}` and `g` the identity of `X ×_K Y = 𝔸¹_{K'}`, `X` is geometrically connected and
reduced but not geometrically reduced, and `g` does not factor since `pr₂ : 𝔸¹_{K'} ⟶ 𝔸¹_K` is
not a monomorphism. In both examples `Γ(X, 𝒪_X) ≠ K`.

This is also blueprint `lemma-rigidity`. The proof follows the blueprint with one change: `L`
is the set of `y` near which `g` factors through `pr₂`. It is open by definition and contains
`y₀` by `AlgebraicGeometry.exists_mem_and_comp_eq_of_subsingleton_image` (Step 4). The same
lemma shows that `L` is the locus of `AlgebraicGeometry.isClosed_setOf_subsingleton_image`, so
it is closed, hence `L = Y` as `Y` is connected. The local factorizations glue because `pr₂` is
flat, surjective and quasi-compact, hence an effective epimorphism. This route needs neither
Step 2 (`AlgebraicGeometry.eventually_finite_image`) nor `Z` locally of finite type, nor `y₀`
`K`-rational. -/
theorem exists_eq_snd_comp {X Y Z : Scheme.{u}} (fX : X ⟶ Spec (.of K))
    (fY : Y ⟶ Spec (.of K)) (fZ : Z ⟶ Spec (.of K)) [IsProper fX] [GeometricallyConnected fX]
    [GeometricallyReduced fX] [ConnectedSpace Y] [IsSeparated fZ]
    (g : pullback fX fY ⟶ Z) (hg : g ≫ fZ = pullback.fst fX fY ≫ fX) (y₀ : Y)
    (hy₀ : (Set.range ((pullback.snd fX fY).fiberι y₀ ≫ g).base).Subsingleton) :
    ∃ h : Y ⟶ Z, g = pullback.snd fX fY ≫ h := by
  set p := pullback.snd fX fY
  -- `L` is the set of points `y` near which `g` factors through `p`.
  let L : Set Y := {y | ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ Z, h ≫ fZ = U.ι ≫ fY ∧
      ∀ {T : Scheme.{u}} (a : T ⟶ pullback fX fY) (b : T ⟶ U), a ≫ p = b ≫ U.ι → a ≫ g = b ≫ h}
  have hL : L = Set.univ := by
    have hLo : IsOpen L := isOpen_iff_forall_mem_open.mpr fun y ⟨U, hyU, hU⟩ ↦
      ⟨U, fun y' hy' ↦ ⟨U, hy', hU⟩, U.isOpen, hyU⟩
    have hy₀L : y₀ ∈ L := by
      refine exists_mem_and_comp_eq_of_subsingleton_image fX fY fZ g hg y₀ ?_
      rwa [← p.range_fiberι y₀, ← Set.range_comp]
    let F (y : Y) := Scheme.Hom.fiberMap
      (pullback.lift (f := fZ) (g := fY) g p (by rw [hg, pullback.condition]))
      (pullback.lift_snd _ _ _) (Y.fromSpecAlgebraicClosureResidueField y)
    have hp (y : Y) (q) : Y.fromSpecAlgebraicClosureResidueField y q = y := by
      simp only [Scheme.fromSpecAlgebraicClosureResidueField, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    have hLc : L = {y | (Set.range (F y).base).Subsingleton} := by
      ext y
      constructor
      · rintro ⟨U, hyU, h, hh, hfac⟩
        set yb := Y.fromSpecAlgebraicClosureResidueField y
        let yU : _ ⟶ U.toScheme := IsOpenImmersion.lift U.ι yb (by
          rintro _ ⟨q, rfl⟩
          simpa [yb, hp] using hyU)
        have hyUb : yU ≫ U.ι = yb := IsOpenImmersion.lift_fac _ _ _
        let s : Spec _ ⟶ pullback (pullback.snd fZ fY) yb :=
          pullback.lift (pullback.lift (yU ≫ h) yb (by rw [Category.assoc, hh, reassoc_of% hyUb]))
            (𝟙 _) (by rw [pullback.lift_snd, Category.id_comp])
        have hF : F y = pullback.snd p yb ≫ s := by
          have := hfac (pullback.fst p yb) (pullback.snd p yb ≫ yU)
            (by rw [Category.assoc, hyUb, pullback.condition])
          simp only [yb] at this
          ext <;> simp [F, s, yb, Scheme.Hom.fiberMap, pullback.map, this, pullback.condition, p]
        change (Set.range (F y).base).Subsingleton
        rw [hF, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
        exact (Set.subsingleton_of_subsingleton).image _
      · intro hy
        refine exists_mem_and_comp_eq_of_subsingleton_image fX fY fZ g hg y ?_
        let yb := Y.fromSpecAlgebraicClosureResidueField y
        have key : F y ≫ pullback.fst _ _ ≫ pullback.fst fZ fY = pullback.fst p yb ≫ g := by
          simp [F, yb, Scheme.Hom.fiberMap, pullback.map]
        have hgx (x : ↑(pullback fX fY)) (hx : x ∈ p ⁻¹' {y}) :
            ∃ a, g x = (pullback.fst fZ fY) (pullback.fst _ yb (F y a)) := by
          obtain ⟨a, rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := yb) x
            (IsLocalRing.closedPoint _) (hx.trans (hp y _).symm)
          refine ⟨a, ?_⟩
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, key]
        rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩
        obtain ⟨a₁, ha₁⟩ := hgx x₁ hx₁
        obtain ⟨a₂, ha₂⟩ := hgx x₂ hx₂
        rw [ha₁, ha₂, hy ⟨a₁, rfl⟩ ⟨a₂, rfl⟩]
    have hLc' : IsClosed L := hLc ▸ isClosed_setOf_subsingleton_image fX fY fZ g hg
    exact IsClopen.eq_univ ⟨hLc', hLo⟩ ⟨y₀, hy₀L⟩
  have : Surjective p := inferInstance
  have : Flat p := inferInstance
  have : QuasiCompact p := inferInstance
  refine ⟨EffectiveEpi.desc p g fun {T} g₁ g₂ e ↦ ?_, (EffectiveEpi.fac p g _).symm⟩
  refine Scheme.hom_ext_of_forall _ _ fun τ ↦ ?_
  obtain ⟨U, hU, h, -, hfac⟩ : (g₁ ≫ p) τ ∈ L := hL ▸ Set.mem_univ _
  refine ⟨(g₁ ≫ p) ⁻¹ᵁ U, hU, ?_⟩
  rw [← Category.assoc, hfac _ ((g₁ ≫ p) ∣_ U) (by simp),
    ← Category.assoc, hfac _ ((g₁ ≫ p) ∣_ U) (by simp [← e])]

end AlgebraicGeometry
