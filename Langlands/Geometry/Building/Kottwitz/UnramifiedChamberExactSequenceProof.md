# KP Proposition 11.6.1: proof

This module proves `Kottwitz.UnramifiedChamberExactSequenceStatement` at an
arbitrary universe `u`. The theorem is `Kottwitz.unramifiedChamberExactSequence`.
The statement is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 11.6.1 (printed page 432, PDF page 463), for the canonical building
over the maximal unramified extension `K` attached to supplied apartment data.

It says: let `F` be a nonarchimedean local field, `G` a connected reductive
`F`-group, `Cch` a chamber of that building, `P` the setwise stabilizer of `Cch`
in `G(K)`, and κ = `reductiveKottwitzOnBaseChange F G hG`. Then

- κ restricted to `P` is surjective, and
- `E.zeroPoints ⊓ B.pointwiseFixer Cch = ker κ ⊓ P` for every unramified zero
  datum `E` of the base-changed group.

## The implemented proof

The proof is one term. It applies the published reduction
`Kottwitz.unramifiedChamberExactSequence_of_statements`
(module `Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceReduction`).
That reduction derives the target from three premises. Each premise is supplied
by a proved Library theorem:

1. `ReductiveKottwitzExistenceStatement`: proved by
   `Kottwitz.reductiveKottwitzExistence_assembled`
   (module `Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof`). The
   reduction uses only its K-point surjectivity conjunct.
2. `UnramifiedZeroKernelStatement` (KP Proposition 11.5.4 over `K`: every
   unramified zero subgroup is the kernel of the Kottwitz map). It is obtained
   from the published implication `Kottwitz.unramifiedZeroKernel_of_torus_zExtension`
   (module `Langlands.Geometry.Building.Kottwitz.ZeroKernelAssembly`), whose type
   is `UnramifiedZeroKernelReductionStatement`. The four inputs of that
   implication are supplied in order by:
   - `Kottwitz.torusKottwitzKernel : TorusKottwitzKernelStatement`
     (module `...Kottwitz.TorusKernelProof`);
   - `Kottwitz.simplyConnectedDerivedKottwitz_proof : SimplyConnectedDerivedKottwitzStatement`
     (module `...Kottwitz.SimplyConnectedDerivedKottwitzProof`);
   - `Kottwitz.reductiveKottwitzExistence_assembled : ReductiveKottwitzExistenceStatement`;
   - `Kottwitz.zExtensionKottwitzKernelSurjectivity : ZExtensionKottwitzKernelSurjectivityStatement`
     (module `...Kottwitz.ZExtensionKernelProof`).
3. `MaximalUnramified.SimplyConnectedNormalizerAffineWeylStatement`: proved by
   `MaximalUnramified.simplyConnectedNormalizerAffineWeyl`
   (module `Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof`).

The module adds no other declarations. The reduction's Markdown explains how the
three premises give the two conclusions. In short:

- surjectivity: a zero subgroup acts transitively on chambers and lies in
  ker κ, and κ is surjective on `G(K)`;
- the kernel equality: ker κ is rewritten as `E.zeroPoints`. Then an element of
  `E.zeroPoints` that stabilizes `Cch` fixes it pointwise, by the normalizer
  premise.

The proof route differs from KP's, which uses `G_sc(K)` and KP Proposition 7.6.4.
The reduction's Markdown describes the route the Lean proof actually takes.

The development check reports 0 errors, 0 warnings and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Provenance: Kaletha–Prasad, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Proposition 11.6.1 (printed p. 432 / PDF p. 463).
