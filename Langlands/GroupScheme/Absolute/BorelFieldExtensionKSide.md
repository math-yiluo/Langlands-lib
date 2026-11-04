# Primes below a Borel coordinate kernel with solvable rational points

Worker 1498.

This helper module supplies the step over the small field in the maximality argument of
the proof of `Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement`. Throughout,
`k` is an algebraically closed field, `G` is a group scheme over `Spec k` with affine
structure morphism and of locally finite type, and `i : B ⟶ G` is a morphism of group
schemes. Rational points are morphisms `Over.mk (𝟙 (Spec k)) ⟶ G.X`, and the coordinate
kernel `BorelExistence.coordinateKernel i` is the kernel of `i` on global sections.

## Declarations

- `BorelFieldExtension.toSpecΓ_asIdeal_apply`: for a morphism of schemes `f : Y ⟶ X` and
  a point `y` of `Y`, the prime of global functions of `X` given by `X.toSpecΓ (f y)` is
  the preimage under `f.appTop` of the prime of global functions of `Y` given by
  `Y.toSpecΓ y`. This is the naturality `Scheme.toSpecΓ_naturality`.
- `BorelFieldExtension.ker_appTop_le_toSpecΓ`: the kernel of `f.appTop` is contained in
  the prime of `X.toSpecΓ (f y)`.
- `BorelFieldExtension.toSpecΓ_asIdeal_of_field`: for a morphism `x : Spec k ⟶ X` from
  the spectrum of a field (any field, not necessarily algebraically closed) and any point
  `a` of `Spec k`, the prime of `X.toSpecΓ (x a)` is the kernel of `x.appTop`. The only
  prime of a field is zero, and `Scheme.ΓSpecIso` is injective.
- `BorelFieldExtension.ker_appTop_le_comp`: the kernel of `g.appTop` is contained in the
  kernel of `(f ≫ g).appTop`.
- `BorelFieldExtension.coordinateKernel_le_of_solvable_points`: let `i` be a Borel
  inclusion (`IsBorelSubgroup i`), let `𝔭` be a prime ideal of `Γ(G.X.left, ⊤)` contained
  in the coordinate kernel of `i`, and let `Γ` be a solvable subgroup of the group of
  rational points of `G` that contains every rational point `x` whose global-section
  kernel contains `𝔭`. Then the coordinate kernel of `i` is contained in `𝔭`, so the two
  are equal.

## Proof of the main lemma

1. Let `ζ : Z ⟶ G` be the closed subgroup from the published
   `rationalPointClosureSubgroup` for `Γ`. Its image is the closure of the locations of
   the points of `Γ`.
2. Since `G` is affine, `G.X.left.toSpecΓ` is a homeomorphism. Let `ξ` be the point
   mapped to the prime `𝔭`. A point `y` is a specialization of `ξ` exactly when `𝔭` is
   contained in the prime of `y` (`PrimeSpectrum.le_iff_specializes`).
3. The point `ξ` lies on `Z`. Since `G` is locally of finite type over a field, it is a
   Jacobson space, so the closure of `ξ` is the closure of its closed points
   (`closure_inter_closedPoints`). Every closed point `p` in that closure is the location
   of a rational point `x` (`pointOfClosedPoint`), and the kernel of `x` is the prime of
   `p` (`toSpecΓ_asIdeal_of_field`). This kernel contains `𝔭`, so `x ∈ Γ` and `p` lies in
   the closed image of `ζ`.
4. The subgroup `B` factors through `Z`. Every rational point of `B` gives a point of `G`
   whose kernel contains the coordinate kernel of `i`, hence contains `𝔭`, so it lies in
   `Γ`. Its location is closed and lies on `Z`. Lifting it with `pointOfClosedPoint`
   and `rationalPoint_ext` gives a rational point of `Z` with the same image. Now `B` is
   reduced (it is smooth over a field,
   `SmoothReducedProof.isReduced_of_smooth_over_field`), so
   `SubgroupFunctor.exists_factor_of_algClosed_points` gives a factorization through `ζ`.
   Since `B` is connected, `IdentityComponent.factor` factors it further through the
   identity component `Z⁰`. Let `j` be the composite of `identityComponentι Z` and `ζ`,
   a closed subgroup inclusion.
5. The group scheme `Z⁰` is solvable. By `isSolvableGroupScheme_iff_isSolvable_points`,
   it suffices that its rational points form a solvable group. Composition with `j` is an
   injective group homomorphism (`j` is a closed immersion, hence a monomorphism). It
   lands in `pointClosureSubgroup G Γ`, which is solvable by
   `isSolvable_pointClosureSubgroup`.
6. By maximality of the Borel inclusion `i`, the factorization `g : B ⟶ Z⁰` is an
   isomorphism. Hence the coordinate kernel of `i` is contained in that of `j`
   (`BorelExistence.coordinateKernel_le` applied to `inv g`).
7. The point `ξ` specializes to the identity point of `G`: the identity of `G` is the
   image of the identity of `B`, and the kernel of `i` on sections is contained in its
   prime. Write `ξ = ζ ξ'`. Since `ζ` is an embedding, `ξ'` specializes to the identity
   point of `Z`. The identity component of `Z` is an open neighbourhood of that point
   (`IdentityComponent.isClopen_identitySet`), so it contains `ξ'`, and `ξ = j w` for
   some point `w` of `Z⁰`. Then `𝔭`, the prime of `ξ`, contains the kernel of `j`, which
   contains the coordinate kernel of `i`.
