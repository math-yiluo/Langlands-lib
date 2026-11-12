# The relative Weyl group is the same over every connected test scheme

Author: Worker 3870.

`Langlands.GroupScheme.relativeWeylGroupRestrict_bijective` proves the exact published
proposition `Langlands.GroupScheme.RelativeWeylGroupRestrictStatement.{u}` (module
`Langlands.GroupScheme.Rational.TorusNormalizerStatement`) at an arbitrary universe `u`.
For every field `k : Type u`, connected reductive group scheme `G` over `Spec k`, maximal
split torus `i : T ⟶ G` and `U : Over (Spec k)` whose underlying space is connected, the
restriction map `relativeWeylGroupRestrict i U : N(k)/Z(k) → N(U)/Z(U)` is bijective. Here
`N(U)/Z(U)` is the quotient of groups of points `pointWeylGroup i U`, not the points of a
quotient scheme. No perfectness, characteristic, finiteness or quotient-scheme hypothesis is
added.

## Proof

The theorem applies the published reduction
`relativeWeylGroupRestrictStatement_of_structuralInputs` (module
`Rational.RelativeWeylRestrictReduction`) to published proofs of its five structural inputs:

1. `genericMinimalParabolic` (module `Rational.GenericMinimalParabolicProof`): for a
   generic cocharacter `ν` of `T`, the dynamic parabolic of `ν ≫ i` is a minimal parabolic;
2. `minimalParabolicConjugacy` (module `Rational.MinimalParabolicConjugacyProof`): minimal
   parabolics are conjugate by rational points;
3. `minimalParabolicSplitTorusConjugacy` (module
   `Rational.MinimalParabolicSplitTorusConjugacyProof`): two maximal split tori inside one
   minimal parabolic `P` are conjugate by a rational point of `P`;
4. `genericCentralizer` (module `Rational.GenericCentralizerProof`): the dynamic centralizer
   of a generic cocharacter is the torus centralizer;
5. `parabolicSelfNormalizer` (module `Rational.ParabolicNormalizerProof`): a parabolic
   subgroup is its own normalizer on every test scheme.

The reduction proves the two halves as follows.

- **Injectivity** is `relativeWeylGroupRestrict_injective` (module
  `Rational.TorusNormalizerRigidity`). It uses only that `T` is a split torus, `i` is a
  monomorphism and `U` is nonempty.
- **Surjectivity** is `RelativeWeylSurjective.relativeWeylGroupRestrict_surjective_of_rigid`
  (module `Rational.RelativeWeylSurjectiveReduction`), applied to inputs 1–5 and to the
  rigidity of split tori over connected `U`,
  `TorusConjugation.exists_isNormalizingAut_of_connected`. A point `g ∈ N(U)` acts on `T`
  through one automorphism `σ`. A cocharacter `ν` with `ν` and `ν ≫ σ` generic gives two
  minimal parabolics. Inputs 2 and 3 give a rational `n ∈ N(k)` carrying the first onto the
  second. Then `(n|_U)⁻¹ g` normalizes the first parabolic, so it lies in it by input 5, and
  it lies in `Z(U)` by input 4 and the dynamic decomposition `P(χ) = Z(χ) U(χ)`.

## Sources and the Milne errata

The statement's Markdown derives the target from Milne, *Algebraic Groups* (2017),
25.16(b)(c) and 25.17, and Borel–Tits, *Groupes réductifs* (1965), Théorème 5.3. The
surjectivity argument recombines the steps of Borel–Tits 5.3 (printed pp.96–97), as the
Markdown of `Rational.RelativeWeylSurjectiveReduction` explains.

The official Milne errata (`milne-2017-algebraic-groups-errata-2026-11-02`, entry for p.549)
say that the classical proofs of the relative root system results are incomplete, and refer
to Conrad–Gabber–Prasad (2015). The proof here does not use those results or their
classical proofs. No root-system axiom of the relative roots is used: the surjectivity
argument uses only finiteness of the set of relative roots and genericity of cocharacters.
The structural inputs are proved along the arbitrary-field routes of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Appendix C.2: Theorem C.2.3 for
conjugacy of maximal split tori, and Lemma C.2.2, Proposition C.2.4 and Theorem C.2.5 for
conjugacy of minimal parabolics. The modules of the inputs describe those proofs.
