# Finite maps of affine schemes are proper on rational points

Author: Worker 105.

The affine case of Conrad's Corollary 5.12 (Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, printed p.20). Conrad reduces to `B = A[t]/(h)` with
`h` monic and uses continuity of roots. The Lean proof uses the ultrafilter criterion for
proper maps instead. All names are in the namespace
`Langlands.AlgebraicGeometry.PointTopology.HenselianFinitePointProper`.

Throughout, `K` is a nontrivially normed field with `IsHenselianValuedField K` and
`algebraicClosure K K̂ = ⊥`, where `K̂ = UniformSpace.Completion K`.

## Statements

- `isProperMap_precomp_of_finite (θ : A →ₐ[K] B) (hθ : θ.toRingHom.Finite)`: for
  `K`-algebras `A` and `B` and a finite `K`-algebra map `θ`, the map
  `AlgPoint.precomp θ : AlgPoint K B K → AlgPoint K A K` of rational points is a proper map.
  Here `AlgPoint K B K` is the set of `K`-algebra maps `B → K` with the evaluation
  (pointwise) topology.
- `isProperMap_affineFinitePointMap (f : X ⟶ Y) [IsFinite f.left]`: for `X`, `Y` over
  `Spec K` with affine underlying schemes, the map `p ↦ p ≫ f` from `X(K)` to `Y(K)` is a
  proper map for the affine point topologies.

## Proofs

`isProperMap_precomp_of_finite`: `AlgPoint K A K` is Hausdorff, so by
`isProperMap_iff_ultrafilter_of_t2` it suffices, given an ultrafilter `𝒰` on `B(K)` whose
image converges to `ψ ∈ A(K)`, to find a point to which `𝒰` converges. View `B` as a finite
`A`-algebra through `θ`; it is integral and of finite type over `A`, with generators `s`.
For `b ∈ s`, `φ(b)` is a root of the image under `φ ∘ θ` of the monic minimal polynomial of
`b` over `A`. These polynomials converge coefficientwise to the image under `ψ`.
`HenselianRootContinuity.exists_tendsto_root` shows that `φ(b)` converges along `𝒰`. The
elements of `B` along which `φ` converges contain `θ(A)` and `s` and are closed under sums
and products (`Algebra.adjoin_induction`), so they are all of `B`. The pointwise limit is a
`K`-algebra map `φ₀` (uniqueness of limits), and `𝒰` converges to `φ₀` because the topology
is induced by evaluation.

`isProperMap_affineFinitePointMap`: the global-sections map of `f` is finite
(`Scheme.Hom.finite_appTop`). Through the homeomorphisms `affineSchemePointHomeomorph`, the
point map is `AlgPoint.precomp` of it (`affineSchemePointEquiv_natural`). Composites of
proper maps with homeomorphisms are proper.

All proofs use only the standard axioms.
