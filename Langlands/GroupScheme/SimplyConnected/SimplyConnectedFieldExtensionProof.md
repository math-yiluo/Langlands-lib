# Simple connectedness under arbitrary field extension

Author: Worker 4034.

The theorem `Langlands.GroupScheme.isSimplyConnectedFieldExtension` proves exactly
the published `Langlands.GroupScheme.IsSimplyConnectedFieldExtensionStatement.{u}`
from `Langlands.GroupScheme.SimplyConnected.FieldExtensionStatement`.

Let `k K : Type u` be fields with an arbitrary `Algebra k K`, and let `G` be an
actual group scheme over `Spec k` with `IsSimplyConnected G`. The theorem gives
`IsSimplyConnected` for the actual pullback

```lean
(GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G
```

The extension may be transcendental or inseparable. Either field may be
imperfect or have positive characteristic. The universe `u` is arbitrary.
The theorem adds no premise to the statement.

## Implemented proof

The Lean proof is one term. It applies the published conditional assembly
`isSimplyConnectedFieldExtension_of_descent_and_splitStructure`, from
`Langlands.GroupScheme.SimplyConnected.FieldExtensionStructuralAssembly`, to
published proofs of its seven inputs:

1. `simplyConnectedCoverTensorDescent`, from
   `Langlands.GroupScheme.Descent.TensorFullCoverProof`, proves
   `SimplyConnectedCoverTensorDescentStatement`. It is used at universes
   `u, u`.
2. `splitSimplyConnectedCoverExistence`, from
   `Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof`, proves
   `SplitSimplyConnectedCoverExistenceStatement`.
3. `simplyConnectedCentralCoverUniversalProperty`, from
   `Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof`, proves
   `SimplyConnectedCentralCoverUniversalProperty`.
4. `maximalTorusBaseChange`, from
   `Langlands.GroupScheme.Torus.MaximalBaseChangeProof`, proves
   `MaximalTorusBaseChangeStatement`.
5. `rootDatumExistence`, from
   `Langlands.GroupScheme.Reductive.RootDatumExistence`, proves
   `RootDatumExistenceStatement`.
6. `SplitSimplyConnectedCorootSpanStatement` is the necessity half of the
   integral coroot criterion. The Library has no direct theorem for it. The
   proof obtains it from `splitSimplyConnectedCorootSpan_of_inputs`, in
   `Langlands.GroupScheme.SimplyConnected.SplitNecessityAssembly`, applied
   to the triple of three published theorems:
   - `splitReductiveExistence`, from
     `Langlands.GroupScheme.Reductive.SplitExistence`. This is the Existence
     Theorem for split reductive groups.
   - `splitCentralIsogenyExistence`, from
     `Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof`.
     This is the central case of the Isogeny Theorem.
   - `splitSemisimpleRootDatum`, from
     `Langlands.GroupScheme.Reductive.SplitSemisimplicity`. This is the
     root-datum criterion for semisimplicity.

   This triple is exactly `SplitSimplyConnectedCorootSpanInputsStatement`.
7. `splitCorootSpanSimplyConnected`, from
   `Langlands.GroupScheme.SimplyConnected.SplitCriterion`, proves
   `SplitCorootSpanSimplyConnectedStatement`. This is the sufficiency half
   of the integral coroot criterion.

The assembly itself already supplies four more published proofs.
`isSemisimpleFieldExtension` gives semisimplicity under arbitrary field
extension. `centralIsogenyBaseChange` preserves central isogenies under base
change. `torusFiniteGaloisSplitting` gives finite Galois splitting of tori.
`Langlands.FieldTheory.finiteGaloisTensorDecomposition` gives the finite
Galois tensor decomposition. The proof imports each module above by its Lean
name. Compilation reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Route of the imported reductions

This section summarizes the published deductions that the assembly calls.
Nothing here is reproved in the new module.

- **Reflection from an algebraic closure.** `IsSimplyConnected.of_fieldExtension`
  in `GeometricReduction` handles a central isogeny `f : H ⟶ G_K` from an
  arbitrary semisimple `K`-group `H`. Its base change to the algebraic closure
  `K̄` is a central isogeny into a simply connected group, so it is an
  isomorphism. Since `Spec K̄ ⟶ Spec K` is fpqc, `f` is an isomorphism.
  Only `H` and `f` are base changed, and they are defined over `K`. No
  `K`-group or `K`-isogeny is assumed to descend to `k`.
- **Splitting the problem.** `isSimplyConnectedFieldExtension_of_geometricInputs`
  embeds the algebraic closure `k̄` into `K̄` over `k`. It uses
  `baseChangeCompIso` to identify `(G_K)_{K̄}` with `(G_{k̄})_{K̄}`. So it needs
  two inputs: ascent from `k` to `k̄`, and ascent between algebraically closed
  fields.
- **Ascent with a split maximal torus.**
  `IsSimplyConnected.fieldExtension_of_splitMaximalTorus` in
  `SplitFieldExtensionReduction` treats a split maximal torus `T` of `G`. It
  takes a reduced root datum of `T` from input 5, and input 6 shows that its
  coroots span the cocharacter lattice. The root datum and the coroot span
  carry over to the base-changed torus, which stays maximal by input 4. Then
  input 7 gives simple connectedness of `G_K`. Over an algebraically closed
  field, `maximalTorusExistence` gives a maximal torus. Finite Galois
  splitting shows that this torus is split, which settles the second input.
- **Ascent to `k̄`.** `isSimplyConnectedAlgebraicClosureAscent_of_tensorDescent`
  in `ClosureAscentReduction` picks a finite Galois extension `L/k` over which
  `G` has a split maximal torus. Inputs 2 and 3 give a simply connected cover
  `C ⟶ G_L` with its universal property. Input 1 and the tensor
  decomposition descend this supplied cover to a central isogeny `D ⟶ G`
  over `k` whose base change recovers `C ⟶ G_L`. Since `G` is simply
  connected, `D ⟶ G` is an isomorphism, so `G_L` is isomorphic to the simply
  connected `C` (`IsSimplyConnected.fieldExtension_of_coverRecovery`). The
  split-torus step then carries this from `L` to `k̄`.

## Scope and provenance

This is derived assembly from published Library theorems. All predicates are
the unchanged published ones. `IsSemisimple` keeps the full possibly
nonreduced centre, and central isogenies keep their full scheme-theoretic
kernels, tested on all schemes. Every base change uses the actual
`GroupScheme.baseChange` functor. No definition, target statement or imported
file is changed.

The mathematical source is recorded in the statement's Markdown. In CGP,
*Pseudo-reductive groups*, second edition (2015), source
`conrad-gabber-prasad-2015-pseudo-reductive`, Corollary A.4.11(1), printed
pp.500–501 (PDF pp.526–527), says that the simply connected central cover's
"formation commutes with any extension of the base field". The definition of
simple connectedness comes just before it, on printed p.500. This task re-read
those two pages. CGP's proof uses Galois descent to reduce to separably closed
fields and then the coroot criterion, Theorem A.4.10. The Library route above
also turns on the coroot criterion and a finite Galois descent of the cover.
It reaches arbitrary extensions through algebraic closures and fpqc
reflection.
