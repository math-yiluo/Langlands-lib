# Reduction of the finite-field envelope compatibility

Worker 1387, reusing the proof structure of Worker 1523's infinite-field reduction. This module proves a conditional theorem. It does not prove any of
the three propositions it assumes.

## Main theorem

`torusGeneratedEnvelopeAlgebraicClosureFinite_of` takes three Library
propositions as explicit hypotheses:

- `hbc : MaximalTorusBaseChangeStatement.{u}`: a closed torus is maximal exactly
  when its base change to a field extension is maximal;
- `hconj : MaximalTorusConjugacyStatement.{u}`: over an algebraically closed
  field, two maximal tori of a smooth connected affine group are conjugate by a
  rational point;
- `htr : FiniteFieldMaximalTorusTransporterStatement.{u}`: over a finite field,
  some maximal torus `j₀ : T₀ ⟶ G` has all its conjugates, by points of `G` on
  every test scheme, inside `closedTorusEnvelope G`.

It concludes `TorusGeneratedEnvelopeAlgebraicClosureFiniteStatement.{u}`: for
every finite field `k` and every smooth affine `G` over `Spec k` with connected
underlying space,
`(closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
closedTorusEnvelope G_k̄` as subgroup functors, on every test scheme.

## Proof

Write `K = AlgebraicClosure k`, `b = toAlgebraicClosure k`, `F` for base
change along `b`, and `G_K = F.obj G`. The proof follows the published
infinite-field reduction `torusGeneratedEnvelopeAlgebraicClosureInfinite_of`
and reuses its helper `EnvelopeInfiniteReduction.exists_isMaximalTorus_factor`.
Only the step placing the conjugates of `(T₀)_K` in the envelope differs.

1. **Criterion.** By `closedTorusEnvelope_baseChange_eq_iff_containsTori`, the
   equality holds once `(closedTorusEnvelope G).baseChange b` contains every
   closed `K`-torus of `G_K`. The group `G_K` is again smooth, affine and
   connected (`connectedSpace_baseChange_of_smooth_affine`).
2. **The maximal torus.** `htr` supplies a maximal torus `j₀ : T₀ ⟶ G` with the
   conjugation property. By `hbc`, `F.map j₀` is a maximal torus of `G_K`.
3. **Conjugates of `(T₀)_K`.** Fix a `K`-point `g` of `G_K` and a point `t` of
   `(T₀)_K` over a test scheme `T'` over `Spec K`. By `comp_innerIso_hom`, the
   image of `t` under `F.map j₀ ≫ int(g)` is `c * x * c⁻¹`, where
   `x = t ≫ F.map j₀` and `c` is the constant family of `g` over `T'`.
   Membership in the base-changed envelope is, by definition
   (`SubgroupFunctor.mem_baseChange`), membership of the image under the
   multiplicative equivalence `baseChangePointsEquiv b G T'` in the envelope of
   `G`, over `T'` regarded as a scheme over `Spec k`. That equivalence carries
   `c * x * c⁻¹` to the conjugate of the image of `x` by the image of `c`. The
   image of `x` lies in the range of `j₀`, because `range (F.map j₀)` is the
   base change of `range j₀` (`SubgroupFunctor.range_baseChangeHom`). The
   conjugation property of `htr` therefore applies on that test scheme.
4. **All `K`-tori.** Let `i : S ⟶ G_K` be a closed `K`-torus.
   `exists_isMaximalTorus_factor` factors `i` as `f ≫ i'` with `i'` a maximal
   torus. By `hconj` there are a `K`-point `g` and an isomorphism `φ` with
   `F.map j₀ ≫ int(g) = φ ≫ i'`. Hence
   `range i ≤ range i' ≤ range (φ ≫ i') = range (F.map j₀ ≫ int(g))`, and the
   last range lies in the base-changed envelope by step 3.

## Provenance

The route is an internal derivation from published Library results and the
three explicit hypotheses. It follows the deduction of extension compatibility
in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition, proof of
Proposition A.2.11, printed pp.477–478: once the conjugates of a maximal torus
over the algebraic closure lie in the base-changed subgroup, conjugacy of
maximal tori places every torus of `G_k̄` there. The finite-field argument of the
source (printed pp.478–480) is what the hypothesis `htr` isolates; it is not
proved in this module.
