# Ordered parabolic orbits indexed by minimal representatives

Module: `Langlands.Representation.Aubert.General.RationalGeometricOrbitOrdering`,
namespace `Langlands.Aubert.General.RationalPointFamily`. Author: Worker 4021.

This module works with the actual standard rational-point families. It shows
that the inverses of the lifts of the minimal representatives of
`W_I \ W / W_J` meet every actual parabolic double coset `P_J \ G(k) / P_I`
exactly once. It then re-indexes an ordered orbit cover of `P_J \ G(k)` by
these lifts.

Every result here assumes the published proposition
`StandardParabolicPointsStatement` as an explicit premise `hPoints`, which this
module does not prove. Its proof is a separate task (Task 3790). The other
premises are:

- connected reductivity, the maximal split torus and the generic cocharacter;
- `HasPointNormalizerComparison` and `HasPointCentralizerComparison`;
- the actual Coxeter system `cs` and `actualLeviWeylIdentification`;
- finiteness of the relative Weyl group.

## Declarations

- `doubleCoset_mk_eq_iff_mem` translates Mathlib's equality
  `DoubleCoset.mk W_J W_I a = DoubleCoset.mk W_J W_I b` into membership of `b`
  in the intrinsic double coset `doubleCoset cs J I a`.
- `doubleCoset_inv_lift_bijective I J lift hlift` takes any section `lift` of
  the actual normalizer quotient (`QuotientGroup.mk (lift w) = w`). It proves
  that the map
  `w ↦ DoubleCoset.mk P_J P_I (lift w)⁻¹`, from minimal representatives
  `w ∈ minimalReps cs I J` to `DoubleCoset.Quotient P_J P_I`, is bijective.

  Injectivity: the published
  `parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints` turns equality
  of the parabolic double cosets of `(lift a)⁻¹` and `(lift b)⁻¹` into equality
  of the Weyl double cosets `W_J a⁻¹ W_I = W_J b⁻¹ W_I`. Both `a⁻¹` and `b⁻¹`
  are minimal in `W_J \ W / W_I` by `isMinimal_inv`, so
  `minimalRepresentativeUnique_proof` gives `a = b`.

  Surjectivity: `Group.exists_doubleCoset_rep_of_equiv`, applied to the
  published `standardParabolicDoubleCosetEquiv` and its value formula, writes
  each double coset as `P_J n P_I` with `n` an actual normalizer point. Take
  `w` minimal in `W_I y⁻¹ W_J`, where `y` is the class of `n`, using
  `exists_minimal_in_doubleCoset`. Then `(lift w)⁻¹` lies in the same
  parabolic double coset, by the same comparison theorem.

  This is where the general orbit convention `P_J w⁻¹` in
  `P_J \ G / P_I` is reconciled with the target's indexing by `W_I \ W / W_J`.
- `finite_parabolicDoubleCoset` proves that `P_J \ G(k) / P_I` is finite: it
  is the image of the finite set of minimal representatives.
- `minimalOrbitOrdering I J hPJ hPI lift hlift` assumes a topology on `G(k)`
  that makes it a nonarchimedean, locally compact, Hausdorff, σ-compact group,
  with `P_J` and `P_I` closed. It produces three things:
  - a length `m`;
  - an equivalence `e : Fin m ≃ {w // w ∈ minimalReps cs I J}`;
  - an ordered orbit cover `t : Geometric.OrderedDoubleCosets P_J P_I m` with
    `t.representative q = lift (e q)` for every `q`.

  It takes the published `Geometric.closedSubgroupOrbitOrdering`, which uses
  finiteness of the double cosets, and aligns the resulting cover with the
  bijection above using the published
  `OrderedDoubleCosets.classifiedRepresentatives`. Every minimal
  representative therefore occurs exactly once, its lift is the literal orbit
  representative, and the initial unions remain open.

## Provenance and dependencies

This is an internal derived construction. Mathematically, it is the Bruhat
indexing of parabolic double cosets by minimal-length representatives
(Borel–Tits 5.20; Renard V.4.5), entering through the published
`StandardParabolicPointsStatement`, together with the orbit ordering of BZ77 5.2.
The proof bodies use only the declarations named above and elementary group
algebra. They use no geometric-lemma expansion, adjointness, cuspidal support,
character independence or Langlands classification. The imported module
closure is larger.
