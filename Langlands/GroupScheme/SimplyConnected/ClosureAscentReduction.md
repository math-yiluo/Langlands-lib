# Conditional simple-connectedness ascent through a finite splitting field

Worker 416. This internal construction assembles conditional ascent to an
algebraic closure and then conditional arbitrary field-extension ascent.
It retains every substantial structural result as an explicit input. It
does not prove the unrestricted host proposition or any input proposition.
Fields and schemes retain arbitrary universe `u`; the tensor descent input
is specialized to index universe `u`.

Four inputs are shared by the three deductions:

- `SimplyConnectedCoverTensorDescentStatement`, descent of a supplied full
  cover with an actual recovered arrow and source isomorphism;
- the literal finite-Galois tensor decomposition proposition, supplying an
  `L`-algebra equivalence from `L ⊗[k] L` to `Gal(L/k) → L` with formula
  `e (a ⊗ b) σ = a * σ b`;
- `SplitSimplyConnectedCoverExistenceStatement`, a central isogeny from a
  simply connected group to a semisimple group with split maximal torus;
- `SimplyConnectedCentralCoverUniversalProperty`, the separate full
  universal property of such a central isogeny.

`IsSimplyConnected.fieldExtension_of_finiteGalois_splitMaximalTorus`
starts with a simply connected `G` over `k` and a finite Galois extension
`L/k` over which `G_L` is semisimple with a split maximal torus. The
split-cover existence input supplies `π : C → G_L`, with simply connected
source and central-isogeny predicate. The universal-property input upgrades
this to the full `IsSimplyConnectedCover` predicate. The tensor input
supplies its explicit equivalence and formula. Tensor descent then gives
an actual full cover `a : D → G` and an actual isomorphism `j : D_L ≅ C`
with the recovery equation `a_L = j.hom ≫ π`.

The existing `IsSimplyConnected.fieldExtension_of_coverRecovery` uses
simple connectedness of `G` to make `a` an isomorphism and hence make `π`
an isomorphism. It transfers simple connectedness of `C` to `G_L`. The
cover source is not assumed to have a split maximal torus.

`isSimplyConnectedAlgebraicClosureAscent_of_tensorDescent` is a `def`
whose value is a conditional proof of
`IsSimplyConnectedAlgebraicClosureAscentStatement`. It additionally assumes semisimplicity ascent, maximal-torus preservation, root-datum
existence, both integral coroot criteria and finite Galois splitting of
tori. The existing finite Galois splitting helper produces `L` as above.
The first theorem gives simple connectedness of `G_L`. An actual
`k`-algebra embedding `ι : L → AlgebraicClosure k` exists by
`IsAlgClosed.lift`. With the induced `L`-algebra structure on the closure,
the existing split-maximal-torus ascent theorem proves simple
connectedness of the iterated base change. The relation `ι.commutes`
identifies the composite map of spectra with `toAlgebraicClosure k`.
The existing `baseChangeCompIso` transports the iterated conclusion to
the actual algebraic-closure pullback of `G`. The local `linter.defProp`
setting allows this proof-valued construction, following the existing
conditional-construction convention in `SplitFieldExtensionReduction`.

`isSimplyConnectedFieldExtension_of_tensorDescent_and_corootCriterion`
also assumes central-isogeny preservation under base change. It feeds
the preceding algebraic-closure ascent result to the existing geometric
and split-coroot reduction, obtaining the exact arbitrary-universe
`IsSimplyConnectedFieldExtensionStatement` as a conditional conclusion.
The final quantified extensions have no perfection, characteristic,
separability, algebraicity or finiteness restriction. Finiteness and the
Galois condition apply only to an auxiliary splitting field chosen inside
the proof.

All group extensions use the actual pullback along the spectrum of their
algebra maps. The full field-only simple-connectedness predicate and
scheme-theoretic central kernels on all test schemes are unchanged.
No arbitrary isogeny over an extension is assumed to descend.

The deduction has internal provenance: it combines the named interfaces,
actual recovery equation, algebraic embedding and base-change comparison.
All imported pairs are public Library modules. The split-cover statement
interface was originally supplied by Worker 1391, and Worker 1347 supplied
the finite-Galois tensor interface used as a literal hypothesis here. Their
private proofs are not part of this module. The private tensor construction
and reflection proofs are not imported by this module and supply no
accepted evidence. The tensor-existence input has its literal type
pending publication of its separately assigned statement. TensorFullCoverStatement and
CoverRecovery are public at the workspace base. The construction and its
supporting lemmas prove none of the structural input propositions. They
provide conditional composition for the host proof, which remains open.
