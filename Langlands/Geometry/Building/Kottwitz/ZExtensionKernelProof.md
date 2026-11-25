# Proof of the kernel clause of KP Proposition 11.5.3

This module proves
`Langlands.Geometry.Building.Kottwitz.ZExtensionKottwitzKernelSurjectivityStatement`
(module `Kottwitz.ZExtensionKernelStatement`) unconditionally, as the theorem
`zExtensionKottwitzKernelSurjectivity`. That statement is the kernel clause of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.3,
printed page 431, PDF page 462 (source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`). For every z-extension
`1 → Z → H → G → 1` it says that `p : H → G` maps the Kottwitz kernel of `H` onto the
Kottwitz kernel of `G`. The first conjunct is about points over
`K = UnramifiedClosure F`, for groups over any compatible field of definition `k`. The
second is about `F`-rational points and the rational maps `reductiveKottwitzRational`.

The module adds no hypotheses. Every input is a theorem already proved in the Library.
The module contains no mathematics of its own: it only puts together two published
conditional reductions and their proved premises.

## Declarations

- `reductiveKottwitzExistence_assembled : ReductiveKottwitzExistenceStatement.{u}`.
  This is KP Lemma 11.5.1 as existence, with the surjectivity and z-extension clauses
  (statement in module `Kottwitz.ReductiveMapStatement`). The proof applies
  `reductiveKottwitzExistence_of_remaining_inputs` (module
  `Kottwitz.ReductiveMapRemainingInputs`) to four proved theorems:
  - `fundamentalInertiaMapStatement` (module `Kottwitz.FundamentalInertiaMapProof`);
  - `zExtensionPointSurjectivity` (module `GroupScheme.Torus.ZExtensionPointSurjectivityProof`);
  - `centralTorusInertiaExactness` (module `Kottwitz.CentralTorusExactnessProof`);
  - a proof of `ZExtensionCommonDominationStatement`, built inside the theorem.
    Given z-extensions `z` and `t` of `G`, it applies `zExtensionMorphismDomination`
    (module `GroupScheme.ZExtensionMorphismDominationProof`) with `f = 𝟙 G`. This gives
    `w`, `r`, `s` with `r ≫ z.p = w.p` and `s ≫ t.p = w.p ≫ 𝟙 G`, and `simpa` removes
    the identity.

  The proof of `reductiveKottwitzFunctoriality` (module
  `Kottwitz.ReductiveFunctorialityProof`) builds the same common domination proof and
  applies the same conditional theorem. It obtains point surjectivity through
  `zExtensionPointSurjectivity_of_inducedTorusQuotient` and does not state existence as
  a separate theorem.
- `reductiveKottwitzDescent_assembled : ReductiveKottwitzDescentStatement.{u}`. This is
  Galois descent of the Kottwitz maps and their restriction to `F`-rational points
  (statement in module `Kottwitz.ReductiveMapStatement`). The proof applies
  `reductiveKottwitzDescent_of_inputs` (module `Kottwitz.ReductiveMapDescentReduction`)
  to five theorems:
  - `simplyConnectedDerivedKottwitz_proof` (module `Kottwitz.SimplyConnectedDerivedKottwitzProof`);
  - `reductiveKottwitzExistence_assembled`;
  - `fundamentalInertiaMapStatement`;
  - `torusInertiaComparison_proof` (module `Kottwitz.TorusInertiaComparisonProof`);
  - `generalTorusKottwitzEquivariance` (module `Kottwitz.TorusKottwitzEquivariance`).
- `zExtensionKottwitzKernelSurjectivity : ZExtensionKottwitzKernelSurjectivityStatement.{u}`
  is the target.

The two auxiliary theorems prove `ReductiveKottwitzExistenceStatement` and
`ReductiveKottwitzDescentStatement`. The Library had no proof of either when this module
was written.

## The proof of `zExtensionKottwitzKernelSurjectivity`

`zExtensionKottwitzKernelSurjectivityStatement_iff` (module `Kottwitz.ZExtensionKernelReduction`)
says that the target is the conjunction of `ZExtensionUnramifiedKottwitzKernelStatement`
and `ZExtensionRationalKottwitzKernelStatement`; its proof is `Iff.rfl`. The proof
applies the reverse direction of this equivalence to the following two proofs.

1. *First conjunct (points over `K`).* `zExtensionUnramifiedKernelReduction` (module
   `Kottwitz.ZExtensionKernelReduction`) proves

   `ReductiveKottwitzExistenceStatement → ReductiveKottwitzFunctorialityStatement →
   CentralTorusInertiaExactnessStatement → ZExtensionUnramifiedKottwitzKernelStatement`.

   It is applied to `reductiveKottwitzExistence_assembled`,
   `reductiveKottwitzFunctoriality` and `centralTorusInertiaExactness`.
2. *Second conjunct (`F`-rational points).* `zExtensionRationalKernelReduction` (module
   `Kottwitz.ZExtensionRationalKernelReduction`) proves

   `ReductiveKottwitzFunctorialityStatement → ReductiveKottwitzDescentStatement →
   CentralTorusInertiaExactnessStatement → (Inj) → (Cor) →
   ZExtensionPointSurjectivityStatement → ZExtensionRationalKottwitzKernelStatement`.

   It is applied to six arguments:
   - `reductiveKottwitzFunctoriality`;
   - `reductiveKottwitzDescent_assembled`;
   - `centralTorusInertiaExactness`;
   - for (Inj), the function sending `F` (with its instances) and `z : ZExtension G` to
     `inducedCentralTorusInertiaInjectivity.zExtension F (UnramifiedClosure F)
     (SeparableClosure F) z`. Here `inducedCentralTorusInertiaInjectivity` (module
     `Kottwitz.CentralTorusInertiaInjectivityProof`) proves
     `InducedCentralTorusInertiaInjectivityStatement`. Its `.zExtension` corollary (module
     `Kottwitz.CentralTorusInertiaInjectivityStatement`), taken at the tower
     `F → UnramifiedClosure F → SeparableClosure F`, says that
     `π₁(z.Z)_I → π₁(z.H)_I` is injective, which is (Inj);
   - for (Cor), `inducedTorusKottwitzRationalSurjectivity` (module
     `Kottwitz.InducedTorusRationalSurjectivityProof`). It proves
     `InducedTorusKottwitzRationalSurjectivityStatement` (KP Corollary 11.1.9, printed
     p.425 / PDF p.456), whose body is (Cor) verbatim;
   - `zExtensionPointSurjectivity`.

The Markdown files of the two reduction modules describe the mathematical argument:
the snake step on `K`-points, and on rational points the lifting of invariant classes
through the injective map `π₁(i)` followed by Corollary 11.1.9.

The module compiles. Its three theorems use only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
