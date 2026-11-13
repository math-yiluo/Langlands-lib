# Characteristic decomposition in finite length: proof

Module `Langlands.Representation.Smooth.FiniteLengthCharacteristicDecompositionProof`.
Worker 277 wrote this proof for Task 5790.

The theorem `Langlands.finiteLengthCharacteristicDecomposition` has type exactly
`Langlands.FiniteLengthCharacteristicDecompositionStatement.{uG, uV}`.
It proves that the uniform generalized character spaces for an arbitrary
central subgroup are independent, span the representation, and have finite
nonzero support. The group and representation universes remain independent;
the theorem adds no hypothesis to the published statement.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, III.1.10, Proposition, printed p.64 / PDF p.70, with the
characteristic-space setup on printed p.63 / PDF p.69. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This proves the finite-length case stated in the unchanged
[statement module](FiniteLengthCharacteristicDecompositionStatement.md).
The implemented proof uses the published finite central action algebra rather
than directly repeating Renard's induction on representation length. That
finiteness result already incorporates the finite-length and Schur arguments.

## Implemented proof

Let `Z ≤ center G`, let `A` be the given smooth finite-length complex
representation, and write `τ` for its restriction to `Z`.

1. Centrality gives a commutative group structure on `Z` and the natural
   homomorphism `c : Z →* center G`. The theorem
   `PQFiniteLengthAction.centralActionSpan_finite` shows that the actual
   operators `τ z` span a finite-dimensional complex vector space.
2. Finite length of `A.representation.asModule` implies that this group-algebra
   module is Noetherian and hence finitely generated. The map `c` is continuous
   for the subgroup topologies. Together with smoothness,
   `centralAction_isLocallyConstant` makes the entire operator-valued action
   `z ↦ τ z` locally constant.
3. Apply `finiteActionCommutativeSpectrum` to `τ`. It supplies a finite set `S`
   consisting of open-kernel characters with nonzero ordinary eigenspaces, and
   says that their uniform generalized character spaces span `A`.
4. Prove independence for all characters `χ : Z →* ℂˣ`. Since the operators
   commute, Mathlib's
   `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo` gives
   independence of their simultaneous maximal generalized eigenspaces, indexed
   by functions `Z → ℂ`. Sending a character to its complex-valued function is
   injective. Each uniform generalized character space is contained in the
   corresponding simultaneous maximal generalized eigenspace: its single
   exponent works for every `z`. Independence passes to these subspaces.
5. Spanning over `S` implies spanning over all characters. By independence and
   `iSupIndep.mem_of_biSup_eq_top`, every nonzero generalized character component
   has its character in `S`. The nonzero support is therefore finite.
6. Identify the published generalized commutative character submodule with the
   target's exact formula
   `⨆ m : ℕ, ⨅ z : Z, ker ((A.representation z − χ z • LinearMap.id)^m)`.
   The definition is a supremum of the uniform finite character spaces, and
   `mem_commutativeCharacterSpace` identifies each such space with the displayed
   infimum of kernels. Thus the same exponent `m` is used for all elements of
   `Z`, as required.

The finite-spectrum theorem's additional uniform nilpotence conclusion is not
needed. No admissibility premise is used.

## Imports

| Module | Role |
| --- | --- |
| `Smooth.FiniteLengthCharacteristicDecompositionStatement` | Exact published target |
| `Intertwining.PQFiniteLengthAction` | Finite-dimensional central operator span in finite length |
| `Smooth.CentralOperatorExpansionProof` | Local constancy from smooth finite generation |
| `Exponents.FiniteActionSpectrumProof` | Finite spanning set of generalized character components |
| `Mathlib.LinearAlgebra.Eigenspace.Pi` | Simultaneous generalized eigenspace independence |
