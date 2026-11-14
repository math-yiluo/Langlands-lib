# Springer's compactness theorem for a central maximal split torus

Closing module of Task 5268, for the Library statement `CentralSplitCompactQuotientStatement`
(module `AdelicSiegelChamberReduction`; Springer 1994, Theorem (C), "if" direction).

- `centralSplitCompactQuotient_of_galoisTwist (hS1 hS2) : CentralSplitCompactQuotientStatement.{u}`.
  Its only hypotheses are the two Lemma S statements of module `AdelicGaloisTwistSubgroup`:
  `GaloisTwistNormOneStatement` and `GaloisTwistSubgroupStatement`. The proof applies
  `centralSplitCompactQuotient_of_splitInputs` (module `AdelicSpringerCentralCompactness`) to
  three inputs:
  - the published split fundamental-set theorem `splitAdelicFundamentalSet`;
  - the published split Siegel overlap estimate `splitSiegelOverlap`;
  - the Galois twisting `galoisBorelTwisting_of hS1 hS2` (module
    `AdelicGaloisBorelTwistingProof`).

- `centralSplitCompactQuotient : CentralSplitCompactQuotientStatement.{u}`: the unconditional
  theorem, `centralSplitCompactQuotient_of_galoisTwist galoisTwistNormOne galoisTwistSubgroup`,
  with the Lemma S proofs from module `AdelicGaloisTwistSubgroupProof`. Its axioms are
  `propext`, `Classical.choice` and `Quot.sound`.

## Map of the helper modules

All helper modules are in `Langlands/Global/` and each has its own Markdown file. In
dependency order:

1. `AdeleGaloisAction`: the automorphism `σ̃ = σ ⊗ 1` of `𝔸_L = L ⊗_F 𝔸_F` for
   `σ ∈ Gal(L/F)`, its continuity, the induced idele automorphism, and the fact that `σ̃`
   preserves the normalized idele norm (`full_idelesMap`).
2. `AdelicGaloisTwistMap`: the Galois twist `galoisTwist F L G σ` of the upper adelic points
   `G_L(𝔸_L)`, with clauses 1 and 2 of `IsGaloisBorelTwist` (rational points, scalar
   extensions of ground norm-one points).
3. `AdelicGaloisTwistDescent`: the twist through the Library's canonical descent;
   `twistPoint` and D1 (`twistPoint_comp_radicalGaloisHom`).
4. `AdelicGaloisTwistNormOne` (statement of Lemma C) and `AdelicGaloisTwistNormOneProof`
   (its proof, by Worker 10): `twistPoint` preserves norm-one points.
5. `AdelicGaloisTwistSubgroup` (statements of Lemma S: S1 and S2) and
   `AdelicGaloisTwistSubgroupProof` (their proofs `galoisTwistNormOne`,
   `galoisTwistSubgroup`).
6. `AdelicGaloisTwistTorus`: naturality of the twist for `F`-homomorphisms, and invariance of
   the norms of characters of a base-changed torus (`normCharacter_galoisTwist`).
7. `AdelicGaloisBorelTwistingProof`: `galoisBorelTwisting_of hS1 hS2 :
   GaloisBorelTwistingStatement.{u}`, using the published Lemma Q
   (`splitBorelGaloisRootAction`).
8. `AdelicGaloisOverlapMatchingProof`: `splitGaloisOverlapMatching :
   SplitGaloisOverlapMatchingStatement.{u}`, the first half of Springer's §3.5 argument.
9. `AdelicSpringerCentralCompactness`: `centralSplitCompactQuotient_of_splitInputs`, the
   second half of Springer's §3.5 argument, which uses the central maximal split torus.
10. `AdelicSpringerCentralCompactnessProof` (this module): the closing theorem.

The helper statements `TwistPointNormOneStatement`, `GaloisTwistNormOneStatement` and
`GaloisTwistSubgroupStatement` are internal interfaces with no literature counterpart. Each is
proved in this bundle, so the closing theorem has no hypotheses.
