/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma 02HT, (1) implies (3); Definition 02HS.
(blueprint: lem-weil-pbc-smooth-at-prime-artinian-lifting-forward).

Proof in words, with step numbers inherited from the parent plan:
1. Principal opens form a basis of Spec A (def-weil-affine-spectrum). The localization
   map identifies Spec A_g with D(g) (lem-weil-pbc-principal-localization-open-immersion,
   def-weil-open-immersion). Smoothness is unchanged by that isomorphism and by restriction
   (lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-morphism-factors-through-open-subscheme). Thus an open smooth neighbourhood
   exists iff some g outside q makes R -> A_g smooth
   (lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-smooth-ring-map).
2. The kernel I of the surjection B' -> B is proper because B is nonzero. It lies
   in the maximal ideal of B'. The Jacobson radical of an Artinian ring is nilpotent;
   in a local ring it is the maximal ideal, so I is nilpotent. This argument works for
   every such surjection, without needing the length-one assumption.
3. Given the smooth A_g and a diagram, a(g) is a unit because its preimage maximal
   ideal is q. Factor a through A_g. Regard the resulting map and B' -> B as maps
   of R-algebras using the compatibility in the diagram. Smoothness implies formal
   smoothness, so Mathlib's `Algebra.FormallySmooth.liftOfSurjective` lifts the map
   A_g -> B through the nilpotent kernel. Compose with A -> A_g to obtain a'; the
   lifting identity and the algebra-homomorphism identity give both required equations.
-/
theorem smooth_on_open_artinian_lifting_forward
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (φ₀ : R →+* A) (hfinite : φ₀.FiniteType) (q : Ideal A) [q.IsPrime] :
    (∃ W : (Spec (CommRingCat.of A)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))) →
    (∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ) := by
  classical
  have _hfinite := hfinite
  intro hopen
  obtain ⟨W, hqW, hs⟩ := hopen
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hqg, hgW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hqW W.isOpen
  let L := Localization.Away g
  let j := Spec.map (CommRingCat.ofHom (algebraMap A L))
  have hjW : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact (PrimeSpectrum.localization_away_comap_range L g).le.trans hgW
  let k := IsOpenImmersion.lift W.ι j hjW
  have : IsOpenImmersion k := by
    apply IsOpenImmersion.of_comp k W.ι
  have : Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀)) := hs
  have hsj : Smooth (j ≫ Spec.map (CommRingCat.ofHom φ₀)) := by
    rw [← IsOpenImmersion.lift_fac W.ι j hjW, Category.assoc]
    infer_instance
  have hsm : ((algebraMap A L).comp φ₀).Smooth := by
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom ((algebraMap A L).comp φ₀))).mp
    simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using hsj
  intro B' B _ _ _ _ _ _ φ hφ _ ρ a hcomm hqa
  let : Algebra R L := ((algebraMap A L).comp φ₀).toAlgebra
  let : Algebra R B' := ρ.toAlgebra
  let : Algebra R B := (φ.comp ρ).toAlgebra
  have : Algebra.Smooth R L := hsm
  have hag : IsUnit (a g) := by
    rw [← not_not (a := IsUnit (a g)), ← mem_nonunits_iff,
      ← IsLocalRing.mem_maximalIdeal]
    rw [← Ideal.mem_comap, hqa]
    exact hqg
  let ag : L →+* B := IsLocalization.Away.lift g hag
  have hagcomp : ag.comp (algebraMap A L) = a :=
    IsLocalization.Away.lift_comp g hag
  let agR : L →ₐ[R] B :=
    { toRingHom := ag
      commutes' := fun r => by
        change ag (algebraMap A L (φ₀ r)) = φ (ρ r)
        rw [← RingHom.comp_apply, hagcomp]
        exact RingHom.congr_fun hcomm r }
  let φR : B' →ₐ[R] B := { toRingHom := φ, commutes' := fun _ => rfl }
  have hker : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B')
    refine ⟨n, ?_⟩
    apply le_antisymm _ bot_le
    change (RingHom.ker φ) ^ n ≤ 0
    rw [← hn]
    apply pow_le_pow_left'
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ)
  let l := Algebra.FormallySmooth.liftOfSurjective agR φR hφ hker
  refine ⟨l.toRingHom.comp (algebraMap A L), ?_, ?_⟩
  · ext x
    exact (Algebra.FormallySmooth.liftOfSurjective_apply agR φR hφ hker
      (algebraMap A L x)).trans (RingHom.congr_fun hagcomp x)
  · ext r
    exact l.commutes r

end AlgebraicGeometry
