/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.EtaleCoverThickeningLift
import WeilConjectures.AlgebraicGeometry.FiniteOpenPartitionThickeningTransport

/-! # Descent of finite splitting through a surjective closed immersion

Source: Stacks Project Tag 04DZ and steps 2--3 of
`lem-weil-pbc-generic-finite-noetherian-scheme-splitting`.
(blueprint: lem-weil-pbc-finite-splitting-closed-immersion-descent)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project Tag 04DF; step 3 of finite splitting descent.
A finite morphism is integral. Universal injectivity descends after pulling back the
surjective precomposition to each test square, and surjectivity cancels directly.
(blueprint: lem-weil-pbc-finite-splitting-closed-immersion-descent) -/
private theorem universalHomeomorphism_of_surjective_precomp
    {A B C : Scheme.{u}} (a : A ⟶ B) (g : B ⟶ C)
    [Surjective a] [IsFinite g] [IsUniversalHomeomorphism (a ≫ g)] :
    IsUniversalHomeomorphism g := by
  have : Surjective g := Surjective.of_comp a g
  have : UniversallyInjective g := by
    constructor
    intro B' C' b c g' h
    let a' := pullback.snd a b
    have : Surjective a' := inferInstance
    have hh : IsPullback (a' ≫ g') (pullback.fst a b) c (a ≫ g) :=
      (IsPullback.of_hasPullback a b).flip.paste_horiz h
    have : UniversallyInjective (a' ≫ g') :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hh.flip inferInstance
    intro y₁ y₂ hy
    obtain ⟨x₁, rfl⟩ := a'.surjective y₁
    obtain ⟨x₂, rfl⟩ := a'.surjective y₂
    exact congrArg a' ((a' ≫ g').injective hy)
  exact {}

/-- Finite etale-local splitting into universal homeomorphisms descends through a
surjective closed immersion. This is a statement over a fixed open, with no
Noetherian, density, affine, or generic-splitting assumption.

Source: Stacks Project Tag 04DZ; steps 2--3 of
`lem-weil-pbc-generic-finite-noetherian-scheme-splitting`.
(blueprint: lem-weil-pbc-finite-splitting-closed-immersion-descent)

Proof: Restrict r to U. This is again a surjective closed immersion, and hence a
universal homeomorphism. The equivalence of small etale sites lifts each scheme
of the given cover and its structural map to U. The lifted maps jointly cover U:
their base changes do, and the vertical maps are homeomorphisms on points.
Pulling back the finite source to a lifted cover gives a surjective closed
immersion from the old source. Transport its finite disjoint open partition
along this homeomorphism. Each open in a finite disjoint open partition is also
closed, so its inclusion is finite, and its map to the lifted cover is finite.
For each transported piece, the old piece is its base change along the
surjective closed immersion of covers. The old component map is universally
bijective. After any base change, the vertical maps remain bijective, so the
lifted component map is universally bijective as well. Its finiteness makes it
integral; universal injectivity and surjectivity then make it a universal
homeomorphism. Pullback associativity identifies these pieces with those in
the displayed statement. An empty partition transports to an empty partition;
an empty base admits the empty etale cover. No witness is chosen to define data
in another declaration: the entire conclusion is propositional existence. -/
theorem finite_splitting_descends_surjective_closedImmersion
    {X Y R : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (r : R ⟶ Y) [IsClosedImmersion r] [Surjective r] (U : Y.Opens)
    (h : ∃ 𝒯 : Cover.{u} etalePrecoverage (r ⁻¹ᵁ U).toScheme, ∀ i,
      ∃ (n : ℕ)
        (W : Fin n → (pullback (𝒯.f i) (pullback.snd f r ∣_ (r ⁻¹ᵁ U))).Opens),
        (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
        ∀ j, IsUniversalHomeomorphism
          ((W j).ι ≫ pullback.fst (𝒯.f i) (pullback.snd f r ∣_ (r ⁻¹ᵁ U)))) :
    ∃ 𝒯 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
      ∃ (n : ℕ) (W : Fin n → (pullback (𝒯.f i) (f ∣_ U)).Opens),
        (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
        ∀ j, IsUniversalHomeomorphism
          ((W j).ι ≫ pullback.fst (𝒯.f i) (f ∣_ U)) := by
  obtain ⟨𝒯, h𝒯⟩ := h
  obtain ⟨𝒮, h𝒮⟩ := exists_etale_cover_thickening_lift f r U 𝒯
  refine ⟨𝒮, fun i ↦ ?_⟩
  obtain ⟨k, t, p, htClosed, htSurj, hpClosed, hpSurj, hcomm⟩ := h𝒮 i
  have : IsClosedImmersion t := htClosed
  have : Surjective t := htSurj
  have : IsClosedImmersion p := hpClosed
  have : Surjective p := hpSurj
  obtain ⟨n, W, hcover, hdisj, hW⟩ := h𝒯 k
  obtain ⟨V, hVcover, hVdisj, hV⟩ :=
    exists_finite_open_partition_thickening_transport p n W hcover hdisj
  refine ⟨n, V, hVcover, hVdisj, fun j ↦ ?_⟩
  obtain ⟨hVfinite, a, _, haSurj, ha⟩ := hV j
  have : IsFinite (V j).ι := hVfinite
  have : Surjective a := haSurj
  have : IsUniversalHomeomorphism
      ((W j).ι ≫ pullback.fst (𝒯.f k) (pullback.snd f r ∣_ (r ⁻¹ᵁ U))) := hW j
  have : IsUniversalHomeomorphism
      (a ≫ ((V j).ι ≫ pullback.fst (𝒮.f i) (f ∣_ U))) := by
    rw [← Category.assoc, ha, Category.assoc, hcomm, ← Category.assoc]
    infer_instance
  exact universalHomeomorphism_of_surjective_precomp a
    ((V j).ι ≫ pullback.fst (𝒮.f i) (f ∣_ U))

end AlgebraicGeometry.Scheme
