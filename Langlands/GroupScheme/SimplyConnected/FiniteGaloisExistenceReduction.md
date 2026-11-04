# Reduction of cover existence to finite Galois splitting and full cover descent

Author: Worker 1347.

This internal, derived module assembles existing Library interfaces into a
conditional proof of `SimplyConnectedCoverExistenceStatement.{u}`. Every
structural input remains an explicit argument. It does not supply an
unconditional proof of that proposition.

## Inputs

`SemisimpleFiniteGaloisAscentStatement.{u}` is a proposition definition:
for fields `k L : Type u`, with `Algebra k L`, `FiniteDimensional k L`
and `IsGalois k L`, every semisimple group scheme over `Spec k` remains
semisimple under the actual base-change functor to `Spec L`. There is no
restriction on the characteristic or perfectness of either field. This is
only the finite Galois specialization needed in this module, and is not a
proof of ascent. In particular, a proof of algebraic-extension semisimplicity
ascent suffices to supply this input, since every finite extension is
algebraic.

`FiniteGaloisCoverExistenceInputsStatement.{u}` is the conjunction of:

1. `TorusFiniteGaloisSplittingStatement.{u}`.
2. `MaximalTorusBaseChangeStatement.{u}`.
3. `SemisimpleFiniteGaloisAscentStatement.{u}`.
4. `SplitSimplyConnectedCoverExistenceStatement.{u}`.
5. `SimplyConnectedCentralCoverUniversalProperty.{u}`.
6. `Langlands.FieldTheory.FiniteGaloisTensorDecompositionStatement.{u}`.
7. `SimplyConnectedCoverTensorDescentStatement.{u,u}`.

The tensor-descent index universe is specialized to `u`, because the index
used here is the actual automorphism group `Gal(L/k)`. This leaves the field
universe `u` arbitrary.

All seven propositions are hypotheses. In particular, importing their
statement modules supplies no proof. The bundle contains no instance of
the full cover-existence statement as a conjunct.

## Implemented reduction

`simplyConnectedCoverExistence_of_finiteGaloisInputs` takes the bundle and
proves the published full existence proposition:

1. Fix an arbitrary field `k : Type u`, an actual group scheme `G` over
   `Spec k`, and `hG : IsSemisimple G`. The latter supplies smoothness and
   affineness of its structure morphism.
2. Apply the public
   `exists_finiteGalois_hasSplitMaximalTorus` with inputs 1 and 2. It gives
   a finite Galois extension `L/k`, and an actual split maximal torus in
   `G_L`. This theorem uses the published maximal-torus existence proof.
3. Apply input 3 to obtain semisimplicity of `G_L`. Input 4 then gives an
   actual group scheme `C` over `Spec L`, a map `π : C ⟶ G_L`, simple
   connectedness of `C` and the central-isogeny property of `π`.
4. Input 5 supplies the explicit unique-factorization law for `π`.
   Together with the preceding facts this constructs
   `hfull : IsSimplyConnectedCover π`. No implication from simple
   connectedness to the factorization law is assumed implicitly.
5. Input 6 gives the actual algebra equivalence
   `e : (L ⊗[k] L) ≃ₐ[L] (Gal(L/k) → L)` and its formula
   `e (a ⊗ b) σ = a * σ b`, with the first-factor `L`-algebra structure.
   Finite-dimensionality supplies finiteness of `Gal(L/k)`; classical
   choice equips it with a `Fintype` instance.
6. Apply input 7 with this equivalence, index type `Gal(L/k)` and the
   identity family of Galois automorphisms. It yields actual `D` over
   `Spec k` and `a : D ⟶ G`, with `IsSimplyConnectedCover a`.
   These are the witnesses for the full existence statement. The
   comparison isomorphism and recovery equation also supplied by input 7
   are not needed for this existential conclusion.

This uses the first, smooth-affine form of the public split-maximal-torus
theorem. Its second form assumes unrestricted semisimplicity ascent.
Only finite Galois ascent is required by the reduction above.

`simplyConnectedCoverExistence_of_splitClassificationAndDescent` is the
same implication with input 4 replaced by the public
`SplitSimplyConnectedCoverInputsStatement.{u}`. It applies
`splitSimplyConnectedCoverExistence_of_inputs` and then the first
reduction. The five structural premises of that split-classification
assembly remain assumptions; none is proved by this module.

## Meaning of the conclusion and limits

The conclusion is the unchanged Library
`SimplyConnectedCoverExistenceStatement.{u}`. The witnesses are actual group
schemes and actual morphisms. In `IsSimplyConnectedCover a`, the source is
semisimple and algebraically simply connected, the map is finite, flat,
surjective and locally of finite presentation with central full
scheme-theoretic kernel, and every incoming central isogeny from a
semisimple group has a unique factorization. Centres and kernels retain
their all-test-scheme meanings, including nonreduced tests.

There is no condition on the initial field beyond `Field k`; imperfect
fields and positive characteristic are included. The finite Galois
extension and its split torus are constructed after the inputs are supplied,
not added to the full target's hypotheses.

Acceptance of this conditional helper does not discharge any of its seven
inputs or complete the host proof task. The final unconditional theorem
still requires independently proved and published prerequisites, including
the proofs behind the full tensor-descent statement. Private proof
prototypes and unproved public statement definitions cannot supply those
proofs.

## Provenance

This is an internal composition of the cited public Lean interfaces; no
claim is made that an original source states this precise seven-input
implication or its bundle. Its proof is the sequence of explicit
applications described above. The split classification construction is
reused through the public theorem by Worker 1391, and the full
tensor-descent interface is reused through its public proposition by
Worker 416. Their source comparisons and their separate proof obligations
remain in the corresponding paired Markdown. No private draft is reused.
The full cover-existence statement pair and all pairs it imports remain
unchanged.
