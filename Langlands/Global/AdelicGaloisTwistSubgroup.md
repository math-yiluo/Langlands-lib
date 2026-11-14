# Galois twisting of norm-one points of subgroups (Lemma S)

Statement-only helper module for the proof of `GaloisBorelTwistingStatement` (Task 5268). Both statements are proved in module `AdelicGaloisTwistSubgroupProof`.
Internal interfaces (no literature counterpart; they are the adelic-point form of the facts
that the Galois action is by continuous automorphisms preserving `|χ| = 1` conditions, and
that it carries points of a subgroup to points of its Galois translate).

Notation: `G_L = AffineWeil.unitBaseChange F L G`; `galoisTwist F L G σ` is the Galois
automorphism of the upper adelic points `G_L(𝔸_L)` (module `AdelicGaloisTwistMap`);
`radicalGaloisHom f σ` is the canonical Galois translate of a subgroup `f : P → G_L`
(Library, `UnipotentRadicalGalois`); `normOneSubgroup L H` is `H(𝔸_L)^1`; `rationalSection`
is the adelic image of a rational point; `innerIso m` is conjugation by `m`.

- `GaloisTwistNormOneStatement` (Lemma S1): `galoisTwist F L G σ` maps `G_L(𝔸_L)^1` into
  itself.
- `GaloisTwistSubgroupStatement` (Lemma S2): let `f : P → G_L` and `g : Q → G_L` be closed
  subgroups (`IsClosedSubgroup`) and `m` a rational point with
  `range (radicalGaloisHom f σ) = range (g ≫ innerIso m)`. Then for every `p ∈ P(𝔸_L)^1`
  there is `q ∈ Q(𝔸_L)^1` with `galoisTwist σ (f p) = m · g(q) · m⁻¹`.

Proof outline. By D1 (`twistPoint_comp_radicalGaloisHom`, module `AdelicGaloisTwistDescent`)
`galoisTwist σ (f p)` is the image of `twistPoint F L σ P p` under `radicalGaloisHom f σ`, and
`twistPoint` preserves norm-one points (Lemma C, `TwistPointNormOneStatement`). S1 is the
case `f = 𝟙`, using that homomorphisms preserve norm-one points (`map_normOneSubgroup_le`).
For S2, the range equality gives an isomorphism `e` from the source of `radicalGaloisHom f σ`
to `Q` with `e ≫ g ≫ innerIso m = radicalGaloisHom f σ`
(`IsClosedSubgroup.sourceIsoOfRangeEq(_hom_comp)`, after `IsClosedSubgroup.comp_iso`); take
`q` the image of `twistPoint p` under `e`, and evaluate `innerIso m` on adelic points.

Used for the norm-one parts of clauses 3 and 4 of `IsGaloisBorelTwist` (clause 4 with
`f = g = Standard.parabolicHom i ν ∅`).
