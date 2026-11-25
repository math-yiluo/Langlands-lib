/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Length
import WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLifting

/-!
# Artinian lifting criterion for smoothness at a point

Source: Stacks Project, More on Morphisms, Lemma 02HX, (1) iff (3), and Algebra,
Definition 02HS (blueprint: lem-weil-pbc-smooth-artinian-lifting-at-point).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private abbrev ArtinianTests {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B]
    [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
    (φ : B' →+* B),
    Function.Surjective φ → Module.length B' ↥(RingHom.ker φ) = 1 →
    ∀ (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S),
      α ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ β →
      α (IsLocalRing.closedPoint B) = x →
      ∃ γ : Spec (CommRingCat.of B') ⟶ X,
        Spec.map (CommRingCat.ofHom φ) ≫ γ = α ∧ γ ≫ f = β

private lemma artinian_point_eq {B : Type u} [CommRing B] [IsArtinianRing B]
    [IsLocalRing B] (p : PrimeSpectrum B) : p = IsLocalRing.closedPoint B := by
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.asIdeal)

private lemma smooth_near_open_iff {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X) (k : T ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : g ≫ k = j ≫ f) (y : Y) :
    (∃ U : X.Opens, j y ∈ U ∧ Smooth (U.ι ≫ f)) ↔
      (∃ W : Y.Opens, y ∈ W ∧ Smooth (W.ι ≫ g)) := by
  constructor
  · rintro ⟨U, hy, hU⟩
    let W := j ⁻¹ᵁ U
    let l := j.resLE U W le_rfl
    have := hU
    have hl : Smooth (l ≫ (U.ι ≫ f)) := inferInstance
    have he : (W.ι ≫ g) ≫ k = l ≫ (U.ι ≫ f) := by
      rw [Category.assoc, h, ← Category.assoc, ← j.resLE_comp_ι (U := U) (V := W) le_rfl,
        Category.assoc]
    have hgk : Smooth ((W.ι ≫ g) ≫ k) := he.symm ▸ hl
    exact ⟨W, hy, MorphismProperty.of_postcomp @Smooth (W' := @IsOpenImmersion)
      (W.ι ≫ g) k inferInstance hgk⟩
  · rintro ⟨W, hy, hW⟩
    let l := W.ι ≫ j
    have := hW
    have hl : Smooth (l ≫ f) := by
      change Smooth (W.ι ≫ j ≫ f)
      rw [← h, ← Category.assoc]
      infer_instance
    refine ⟨l.opensRange, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    have := hl
    have hs : Smooth (l.isoOpensRange.inv ≫ (l ≫ f)) := inferInstance
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using hs

private lemma artinian_tests_open_iff {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (j : Y ⟶ X) (k : T ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : g ≫ k = j ≫ f) (y : Y) :
    ArtinianTests f (j y) ↔ ArtinianTests g y := by
  constructor
  · intro H B' B _ _ _ _ _ _ φ hφ hlen α β hsq hpoint
    have hi : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint B) =
        IsLocalRing.closedPoint B' := artinian_point_eq _
    have hs : (α ≫ j) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ (β ≫ k) := by
      rw [Category.assoc, ← h, ← Category.assoc, hsq, Category.assoc]
    obtain ⟨γ, hγa, hγb⟩ := H B' B φ hφ hlen (α ≫ j) (β ≫ k) hs
      (by simp only [Scheme.Hom.comp_apply, hpoint])
    have hγpoint : γ (IsLocalRing.closedPoint B') = j y := by
      rw [← hi, ← Scheme.Hom.comp_apply, hγa, Scheme.Hom.comp_apply, hpoint]
    have hrange : Set.range γ ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [artinian_point_eq p, hγpoint]
      exact ⟨y, rfl⟩
    let δ := IsOpenImmersion.lift j γ hrange
    have hδ : δ ≫ j = γ := IsOpenImmersion.lift_fac j γ hrange
    refine ⟨δ, ?_, ?_⟩
    · apply (cancel_mono j).mp
      simpa only [Category.assoc, hδ] using hγa
    · apply (cancel_mono k).mp
      rw [Category.assoc, h, ← Category.assoc, hδ]
      exact hγb
  · intro H B' B _ _ _ _ _ _ φ hφ hlen α β hsq hpoint
    have hi : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint B) =
        IsLocalRing.closedPoint B' := artinian_point_eq _
    have ha : Set.range α ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [artinian_point_eq p, hpoint]
      exact ⟨y, rfl⟩
    have hbpoint : β (IsLocalRing.closedPoint B') = k (g y) := by
      rw [← hi, ← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hpoint]
      exact congrArg (fun m : Y ⟶ S ↦ m y) h.symm
    have hb : Set.range β ⊆ Set.range k := by
      rintro _ ⟨p, rfl⟩
      rw [artinian_point_eq p, hbpoint]
      exact ⟨g y, rfl⟩
    let a := IsOpenImmersion.lift j α ha
    let b := IsOpenImmersion.lift k β hb
    have hα : a ≫ j = α := IsOpenImmersion.lift_fac j α ha
    have hβ : b ≫ k = β := IsOpenImmersion.lift_fac k β hb
    have hs : a ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ b := by
      apply (cancel_mono k).mp
      rw [Category.assoc, h, ← Category.assoc, hα, Category.assoc, hβ]
      exact hsq
    have hp : a (IsLocalRing.closedPoint B) = y := by
      apply j.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα, hpoint]
    obtain ⟨δ, hδa, hδb⟩ := H B' B φ hφ hlen a b hs hp
    refine ⟨δ ≫ j, ?_, ?_⟩
    · rw [← Category.assoc, hδa, hα]
    · rw [Category.assoc, ← h, ← Category.assoc, hδb, hβ]

private lemma artinian_tests_spec_iff {R A : Type u} [CommRing R] [CommRing A]
    (φ₀ : R →+* A) (q : PrimeSpectrum A) :
    ArtinianTests (Spec.map (CommRingCat.ofHom φ₀)) q ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B]
        [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
        (φ : B' →+* B), Function.Surjective φ →
        Module.length B' ↥(RingHom.ker φ) = 1 →
        ∀ (ρ : R →+* B') (a : A →+* B),
          a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q.asIdeal →
          ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ := by
  constructor
  · intro H B' B _ _ _ _ _ _ φ hφ hlen ρ a hsq hpoint
    have hs : Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom φ₀) =
        Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun ψ ↦ Spec.map (CommRingCat.ofHom ψ)) hsq
    obtain ⟨γ, hγa, hγb⟩ := H B' B φ hφ hlen
      (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom ρ)) hs
      (PrimeSpectrum.ext hpoint)
    obtain ⟨a', rfl⟩ := Spec.map_surjective γ
    refine ⟨a'.hom, ?_, ?_⟩
    · exact congrArg CommRingCat.Hom.hom (Spec.map_injective (by
        simpa only [← Spec.map_comp] using hγa))
    · exact congrArg CommRingCat.Hom.hom (Spec.map_injective (by
        simpa only [← Spec.map_comp] using hγb))
  · intro H B' B _ _ _ _ _ _ φ hφ hlen α β hsq hpoint
    obtain ⟨a, rfl⟩ := Spec.map_surjective α
    obtain ⟨ρ, rfl⟩ := Spec.map_surjective β
    have hs : a.hom.comp φ₀ = φ.comp ρ.hom :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective (by
        simpa only [← Spec.map_comp] using hsq))
    obtain ⟨a', ha', hρ⟩ := H B' B φ hφ hlen ρ.hom a.hom hs
      (congrArg PrimeSpectrum.asIdeal hpoint)
    refine ⟨Spec.map (CommRingCat.ofHom a'), ?_, ?_⟩
    · rw [← Spec.map_comp]
      exact congrArg (fun ψ ↦ Spec.map (CommRingCat.ofHom ψ)) ha'
    · rw [← Spec.map_comp]
      exact congrArg (fun ψ ↦ Spec.map (CommRingCat.ofHom ψ)) hρ

/-- Source: Stacks Project, More on Morphisms, Lemma 02HX, (1) iff (3), with small
extensions as in Algebra, Definition 02HS
(blueprint: lem-weil-pbc-smooth-artinian-lifting-at-point).

A locally finite type morphism over a locally Noetherian scheme is smooth on a
neighbourhood of `x` iff every compatible diagram at `x` lifts along each surjection
of Artinian local rings whose kernel has module length one. The consequences
that the kernel is a residue-field module and is square zero are not extra hypotheses.

Proof, following the five steps of the blueprint node:
1. Choose affine neighbourhoods `V = Spec R` of `f(x)` and `U = Spec A` of `x`
   with `f(U)` contained in `V`. Local Noetherianity (pqf-def-locnoeth) makes `R`
   Noetherian, and local finite type (def-weil-finite-type-morphism) makes `A`
   finite type over `R`. Factor the restriction through `V`
   (lem-weil-pbc-morphism-factors-through-open-subscheme).
2. Both test spectra have a unique point
   (lem-weil-pbc-artinian-local-unique-prime), so the test maps factor through `U`
   and `V`. The affine spectrum correspondence (def-weil-affine-spectrum)
   identifies their commutative square with a commutative square of ring maps,
   with the maximal ideal pulling back to the prime corresponding to `x`.
   Cancel the open inclusion using lem-weil-pbc-open-immersion-monomorphism.
3. A lift also has image `x`, so it factors through `U`. The same correspondence
   and cancellation identify scheme lifts with ring lifts, giving exactly the
   test condition of lem-weil-pbc-smooth-at-prime-artinian-lifting.
4. Restriction to open subschemes, composition with their inclusions, and
   invariance under isomorphism (lem-weil-pbc-smooth-restrict-open-subschemes)
   identify smoothness on a neighbourhood of `x` with smoothness on a
   neighbourhood of the corresponding prime of `A`.
5. Apply lem-weil-pbc-smooth-at-prime-artinian-lifting to the Noetherian ring `R`
   and finite type `R`-algebra `A`; steps 2--4 identify both sides of its equivalence.
-/
theorem smooth_near_iff_artinian_lifting_at_point
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian S] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B]
        [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
        (φ : B' →+* B),
        Function.Surjective φ → Module.length B' ↥(RingHom.ker φ) = 1 →
        ∀ (α : Spec (CommRingCat.of B) ⟶ X)
          (β : Spec (CommRingCat.of B') ⟶ S),
          α ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ β →
          α (IsLocalRing.closedPoint B) = x →
          ∃ γ : Spec (CommRingCat.of B') ⟶ X,
            Spec.map (CommRingCat.ofHom φ) ≫ γ = α ∧ γ ≫ f = β := by
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
  let φ₀ := (f.appLE V U hUV).hom
  let q := hU.primeIdealOf ⟨x, hxU⟩
  have : IsNoetherianRing Γ(S, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hcomm : Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec = hU.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  have hn := smooth_near_open_iff f (Spec.map (CommRingCat.ofHom φ₀))
    hU.fromSpec hV.fromSpec hcomm q
  have ht := artinian_tests_open_iff f (Spec.map (CommRingCat.ofHom φ₀))
    hU.fromSpec hV.fromSpec hcomm q
  have hx : hU.fromSpec q = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have H := hn.trans ((smooth_on_open_iff_artinian_lifting.{u, u}
    φ₀ (f.finiteType_appLE hV hU hUV) q.asIdeal).trans
      (artinian_tests_spec_iff φ₀ q).symm |>.trans ht.symm)
  convert H using 2
  · exact congrArg (fun z : X ↦ fun W : X.Opens ↦ z ∈ W ∧ Smooth (W.ι ≫ f)) hx.symm
  · exact hx.symm

end AlgebraicGeometry
