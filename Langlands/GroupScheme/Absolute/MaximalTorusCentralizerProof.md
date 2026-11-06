# Proof: a maximal torus of a connected reductive group is its own centralizer

Worker 303. `Langlands.GroupScheme.maximalTorusCentralizer` proves exactly the
published proposition `Langlands.GroupScheme.MaximalTorusCentralizerStatement.{u}`
(module `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement`) at an
arbitrary universe `u`. The statement pair and everything it imports are unchanged.

For every field `k : Type u`, every group scheme `G` over `Spec k` with
`IsConnectedReductive G`, every commutative group scheme `T` over `Spec k` and every
`j : T ⟶ G` with `IsMaximalTorus j`, it gives the equality of subgroup functors

`torusCentralizer j = SubgroupFunctor.range j`

on every test scheme over `Spec k`. There are no further hypotheses: `k` need not be
perfect or algebraically closed, and `T` need not be split.

## Implemented proof

The proof is one application of the published
`maximalTorusCentralizer_of_structuralInputs` (module
`Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly`). That
theorem derives `MaximalTorusCentralizerStatement.{u}` from three propositions. Each is
supplied by its proof in the Library:

- `DynamicCentralizerReductiveStatement.{u}` by `dynamicCentralizerReductive` (module
  `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`). A closed subgroup
  representing the dynamic centralizer of a cocharacter of a connected reductive group
  is connected reductive.
- `NoTorusUnipotentStatement.{u}` (Milne 17.81) by `noTorusUnipotent` (module
  `Langlands.GroupScheme.Torus.NoTorusUnipotent`). A smooth connected affine group that
  receives only trivial homomorphisms from tori is unipotent.
- `SolvableTorusQuotientStatement.{u}` (Milne 16.33(a),(c)) by `solvableTorusQuotient`
  (module `Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof`). Over an
  algebraically closed field, a smooth connected solvable affine group has a smooth
  connected normal unipotent closed subgroup whose fppf quotient is a split torus.

The assembly's Markdown describes how the three inputs are combined. In outline:

1. Over an algebraically closed field, a generic cocharacter `ν` of the maximal torus
   identifies `torusCentralizer j` with the dynamic centralizer of `ν ≫ j`. The first
   input makes a closed representative `C` of it connected reductive, and `T` is a
   central maximal torus of `C`.
2. In that central case, the quotient `C/T` has no nontrivial torus (Milne 16.43, a
   Library proof), so it is unipotent by the second input, and `C` is solvable. The
   third input and the trivial unipotent radical of `C` make `C` a torus, so `T = C`.
3. Over an arbitrary field, the Library reduction
   `maximalTorusCentralizer_of_centralMaximalTorusBaseChange` (module
   `Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction`) passes to the
   algebraic closure. Maximality of `T` after base change (the central case of Milne
   17.82) comes from `centralMaximalTorusBaseChangeReduction` and
   `noTorusBaseChangeReduction`, the latter again using the second input over `k`.

`maximalTorusCentralizer` uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Corollary 17.84, printed p.379 (one-based PDF p.395): "A torus `T` in a reductive group
`G` is maximal if and only if `C_G(T) = T`". The theorem proves the "only if" direction,
as stated. Milne derives it from Theorem 17.82 and Proposition 17.61(a). The Lean proof
follows the same split into a base change step and an algebraically closed step, but
proves the algebraically closed step through dynamic centralizers instead of Milne's
Borel subgroup argument, as explained in the assembly's Markdown.
