# Reduction of relative central quotients to multiplicative-type inputs

`RelativeCentralQuotientReductionStatement` is the `Prop`-valued
definition of the implication below. `relativeCentralQuotientReduction`
proves it using the parameterized assembly theorem.

`relativeCentralQuotient_of_multiplicativeType_inputs` proves the implication

```text
RelativeMultiplicativeTypeClosedSubgroupStatement →
RelativeCentralMultiplicativeTypeQuotientStatement →
MultiplicativeTypeNormalCentralStatement →
RelativeCentralQuotientStatement
```

in every universe. These three input propositions remain explicit
hypotheses. This module does not prove any of them, and therefore does not
provide an unconditional proof of the final statement.

The conclusion is the published
`RelativeCentralQuotientStatement`: for every scheme, reductive group, flat
central closed subgroup and supplied actual fppf quotient, the quotient is
reductive, its centre has the prescribed full preimage, both directions
of the maximal-torus correspondence hold, and target maximal tori are
determined by their preimages.

The proof assembles the following actual group-scheme constructions and
subgroup-functor identities:

1. Factor the central kernel through the published relative centre and
   use its kernel-square flatness and local finite presentation with the
   closed-subgroup input to obtain relative multiplicative type.
2. The affine central quotient input constructs another quotient with
   the same kernel. General fppf comparison transfers affinity to the
   supplied target, and smoothness descent and the published field
   central quotient theorem give reductivity.
3. The normal-centrality input makes the actual preimage of the target
   centre central in the source. Flat surjective descent of commutation
   proves the opposite containment.
4. For the forward torus direction, quotient the source maximal torus by
   the central kernel and embed this quotient in the ambient target.
   The supplied-image maximality theorem gives maximality and the kernel
   comparison gives the exact full-preimage identity.
5. For the reverse direction, use étale local existence and conjugacy of
   maximal tori, lift conjugators fppf locally, and descend the relative
   torus property of the actual preimage. Self-centralization gives
   maximality on all residue fibres.
6. Finally, full inverse image under an fppf homomorphism reflects equality
   of monomorphically represented subgroups. Closedness of the target
   torus inclusions supplies the required monomorphisms.

This is an internal derived assembly of the imported geometry, centre,
torus image and preimage, and inverse-image reflection results. It
introduces no new source translation. The source correspondence of the
target is recorded in `RelativeCentralQuotientStatement.md`;
each supporting module describes its own implemented proof and explicit
input assumptions.
