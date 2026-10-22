# Inner-conjugation maps on continuous cohomology

This module builds the inner-conjugation automorphisms `σ_a` of Mathlib's continuous cohomology `continuousCohomology n A` of a topological group `G` with coefficients in a topological representation `A : TopRep k G`. It also proves their evaluation formulas, identity and composition laws, and naturality. Everything is defined through Mathlib's `ContinuousCohomology.cochainsMap`, `ContinuousCohomology.cocyclesMap` and `ContinuousCohomology.map` from `Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality`, applied to a group map and a coefficient morphism built here. The module assumes neither of these maps nor their compatibility.

## Source

Serre, *Local Fields* (literature ID `serre-1979-local-fields`), Chapter VII, §5 "Change of Group", printed page 115 (PDF page 121), defines the map associated to a compatible pair. Here `f : G' → G` is a group homomorphism, `A` is a `G`-module, `A'` is a `G'`-module and `g : A → A'` is additive:

> We say that f and g are compatible when g(f(s')·a) = s'·g(a) for all s' ∈ G', a ∈ A; this amounts to saying that g is a G'-homomorphism of f*A into A'.

The resulting homomorphism `(f, g)* : H^q(G, A) → H^q(G', A')` is "said to be associated to the pair (f, g)". Printed page 116 (PDF page 122) then defines the inner-conjugation automorphisms:

> Consider the case G = G', A = A', with the map f: G → G being the inner automorphisms s ↦ tst⁻¹, and g: A → A being a ↦ t⁻¹a. One checks that these two maps are compatible, hence they define automorphisms σ_t of the cohomology H^q(G, A).

Serre states this for abstract groups and modules. This module carries out the same construction for continuous cochains, with Mathlib's `ContinuousCohomology.map φ f n` playing the role of `(f, g)*`. Mathlib's coefficient argument `f : TopRep.res φ X ⟶ Y` is exactly Serre's compatibility condition, read as "g is a G'-homomorphism of f*A into A'". The same page goes on to Serre's Proposition 3, which says the `σ_t` are the identity. That proposition is not formalized here, and nothing in this module claims that `σ_a` is trivial for an arbitrary `a`.

## Universes and generality

The construction section takes an arbitrary ring `k : Type u` with a topology, any topological group `G : Type v`, and `A : TopRep.{max v w} k G`. The coefficient ring and the group live in independent universes. The coefficient carrier lies in `max v w` for an arbitrary `w`. This is the most general form Mathlib's API supports: the standard resolution `TopRep.resolutionX` iterates `TopRep.coind₁`, whose carrier `C(G, A)` lies in `max v w`, so Mathlib's cochains, cocycles and cohomology are only defined for carriers in a universe of the form `max v w`, that is, at least the universe of `G`. Because `G` is both the source and the target group, Mathlib's requirement that all groups in `ContinuousCohomology.map` share one universe imposes nothing extra. There are no finiteness, compactness, profiniteness or arithmetic assumptions.

## Group maps

- `innerConjugation a : G →ₜ* G` is `g ↦ a * g * a⁻¹` (`innerConjugation_apply`). It is continuous by Mathlib's `IsTopologicalGroup.continuous_conj a`, and it is a homomorphism by the `group` tactic.
- `innerConjugation_one : innerConjugation 1 = ContinuousMonoidHom.id G`.
- `innerConjugation_mul a b : innerConjugation (a * b) = (innerConjugation a).comp (innerConjugation b)`.
- `innerConjugationEquiv a : G ≃ₜ* G` is the same map viewed as a continuous automorphism, with inverse `g ↦ a⁻¹ * g * a`. It comes with `innerConjugationEquiv_apply` and `innerConjugationEquiv_symm_apply`, and `innerConjugationEquiv_toContinuousMonoidHom` says its underlying continuous homomorphism is `innerConjugation a` (by `rfl`).

## Coefficient maps and compatibility

- `ρ_apply_ρ_apply g h x : A.ρ g (A.ρ h x) = A.ρ (g * h) x` is a small helper.
- `innerConjugation_compatible a g x : A.ρ a⁻¹ (A.ρ (a * g * a⁻¹) x) = A.ρ g (A.ρ a⁻¹ x)` is Serre's compatibility of `s ↦ asa⁻¹` with `x ↦ a⁻¹x`, proved from `a⁻¹ (a g a⁻¹) = g a⁻¹`. `innerConjugation_compatible_inv` is the matching identity for `A.ρ a`.
- `innerConjugationCoefficient A a : TopRep.res (innerConjugation a) A ⟶ A` is the morphism of topological `G`-representations whose underlying continuous linear map is `A.ρ a⁻¹` (`innerConjugationCoefficient_hom_apply`). Its equivariance is `innerConjugation_compatible`.
- `innerConjugationCoefficientInv A a : A ⟶ TopRep.res (innerConjugation a) A` is given by `A.ρ a`. `innerConjugationCoefficientIso A a` packages the two as an isomorphism, and its simp projections `_hom` and `_inv` name its forward and inverse maps.

## Maps on resolutions, cochains, cocycles and cohomology

- `innerConjugationResolution A a i` is Mathlib's `ContinuousCohomology.resolutionMap` for this pair, on the `i`-th term of the standard resolution. In degree `0` it is `A.ρ a⁻¹` (`innerConjugationResolution_zero_apply`). In degree `i + 1` it sends `F` to `g ↦ innerConjugationResolution A a i (F (a * g * a⁻¹))` (`innerConjugationResolution_succ_apply`).
- `innerConjugationCochains A a` is `ContinuousCohomology.cochainsMap (innerConjugation a) (innerConjugationCoefficient A a)`, an endomorphism of `TopRep.homogeneousCochains A` (`innerConjugationCochains_eq`). Its component in degree `i` is the resolution map in degree `i + 1`, restricted to invariants (`innerConjugationCochains_f_apply`). A homogeneous `i`-cochain is a `G`-invariant continuous function of `i + 1` curried variables. The explicit formulas in degrees `0` and `1` are
  `σ_a(σ)(g) = A.ρ a⁻¹ (σ (a g a⁻¹))` and `σ_a(σ)(g, h) = A.ρ a⁻¹ (σ (a g a⁻¹) (a h a⁻¹))`
  (`innerConjugationCochains_zero_apply` and `innerConjugationCochains_one_apply`).
- `innerConjugationCocycles A a n` is `ContinuousCohomology.cocyclesMap` for the pair (`innerConjugationCocycles_eq_cyclesMap`).
- `innerConjugationMap A a n : continuousCohomology n A ⟶ continuousCohomology n A` is `ContinuousCohomology.map (innerConjugation a) (innerConjugationCoefficient A a) n` (`innerConjugationMap_eq`). Equivalently, it is the homology map of `innerConjugationCochains A a` (`innerConjugationMap_eq_homologyMap`). `π_innerConjugationMap` says it commutes with the projection `ContinuousCohomology.π` from cocycles to cohomology.

## Compatibility certificates

- Identity: `innerConjugationCochains_one`, `innerConjugationCocycles_one` and `innerConjugationMap_one` say that for `a = 1` the cochain, cocycle and cohomology maps are identities. In particular `innerConjugationMap A 1 n = 𝟙 (continuousCohomology n A)`. The proof rewrites by Mathlib's `ContinuousCohomology.cochainsMap_id` and uses `innerConjugation_one` together with `A.ρ 1⁻¹ x = x`.
- Composition: `innerConjugationCochains_mul`, `innerConjugationCocycles_mul` and `innerConjugationMap_mul` say that the map for `a * b` is the map for `a` followed by the map for `b`. In diagrammatic order, `σ_{ab} = σ_a ≫ σ_b`, i.e. `σ_{ab} = σ_b ∘ σ_a`. The degree-`0` formula above forces this order: applying `σ_a` and then `σ_b` to a cochain `σ` gives `g ↦ A.ρ b⁻¹ (A.ρ a⁻¹ (σ (a b g b⁻¹ a⁻¹))) = A.ρ (a b)⁻¹ (σ ((a b) g (a b)⁻¹))`. The proof uses Mathlib's `ContinuousCohomology.cochainsMap_comp`, `innerConjugation_mul`, and `A.ρ (a * b)⁻¹ = A.ρ b⁻¹ ∘ A.ρ a⁻¹`. The `@[reassoc]` forms are generated.
- Invertibility: `innerConjugationCochainsIso A a` and `innerConjugationIso A a n` are the isomorphisms with forward map `σ_a` and inverse `σ_{a⁻¹}`. Their identities follow from the composition and identity laws. `innerConjugationIso_one` says the isomorphism for `a = 1` is `Iso.refl`. `innerConjugationIso_mul` says `innerConjugationIso A (a * b) n = innerConjugationIso A a n ≪≫ innerConjugationIso A b n`.
- Naturality: for a morphism `f : A ⟶ B` in `TopRep.{max v w} k G`, `innerConjugationCochains_naturality` and `innerConjugationMap_naturality` say that `σ_a` commutes with Mathlib's coefficient maps `ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f` and `ContinuousCohomology.map (ContinuousMonoidHom.id G) f n`. The proof composes with `cochainsMap_comp` on both sides and uses the equivariance `f.hom (A.ρ a⁻¹ x) = B.ρ a⁻¹ (f.hom x)` (`TopRep.hom_comm_apply`).

## Internal helpers and the Library comparison

The congruence lemmas `cochainsMap_congr_of_apply` and `map_congr_of_apply` are internal helpers with no literature source. They state that equal group maps and pointwise-equal coefficient maps give equal cochain and cohomology maps, which handles the dependent domain `TopRep.res φ X`. The published `Langlands.Continuous.continuousCochainsMap_congr` in `Langlands.Cohomology.Continuous.EquivalenceTransport` proves the same thing, but only when all groups, the ring and the carriers share one universe. This module needs independent universes, so it reproves the lemma with the same proof.

The Library's `continuousCohomologyIso e f q` (same module) transports continuous cohomology along a continuous group equivalence and a coefficient isomorphism, in a common universe and over a commutative ring. The comparison section specializes to `k G : Type u`, `CommRing k` and `A : TopRep.{u} k G`. There, `continuousCohomologyIso_innerConjugation` proves that this transport, applied to `innerConjugationEquiv a` and `innerConjugationCoefficientIso A a`, equals `innerConjugationIso A a q`. Both forward maps are definitionally the same `ContinuousCohomology.map`.
