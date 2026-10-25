# Uniqueness of the local factors of constructed restricted tensors

`Langlands.restrictedTensorFactorUniqueness` proves exactly the closed proposition
`Langlands.RestrictedTensorFactorUniquenessStatement.{uI, uG, uV, uW}`.
The index type, local groups, source local carriers and target local carriers
retain four independent universes. All hypotheses of the published statement
remain inside that proposition: the local topological groups and compact open
subgroups, admissible irreducible complex representations, independent finite
exceptional sets, nonzero subgroup-fixed reference vectors outside those sets,
and the almost-everywhere one-dimensional fixed-space conditions.

The conclusion is that an equivariant linear equivalence of the two actual
constructed restricted tensor representations gives a genuine equivariant linear
equivalence between the two local representations at every index. The theorem
introduces no additional hypotheses and does not modify the published statement
or any construction it imports.

Fix an index `i` and a supplied global equivalence `q`. The proof constructs
`qLocal` from the same linear equivalence, evaluating the intertwining law of `q`
at `RestrictedTensor.localInsertion H i g`. This insertion is the existing
singleton monoid hom into the actual restricted product. Thus `qLocal`
intertwines the restrictions of the two global actions to `G i`.

The published `RestrictedTensor.productLocalTensorSeparation` identifies each
restriction with its own local factor tensored with a complementary restricted
tensor on which `G i` acts trivially. For the source, that complementary space is
exactly

```text
Space ℂ (fun j : Outside {i} => V j)
  (tailSet {i} E) (fun j => r.family j).
```

The target uses `W`, `E'` and `s` independently. Composing the inverse source
separation, `qLocal`, and the target separation gives an equivalence between
these two tensor representations.

Every source local carrier is nontrivial because irreducibility means that its
monoid-algebra module is simple and nonzero. The proof installs these instances
using `IsSimpleModule.nontrivial`, then applies
`RestrictedTensor.localTensorTail_nontrivial` to `r.family` and
`r.family_nonzero`. This establishes nontriviality of the source complementary
space, even when the complement is empty.

Finally, `TensorMultiplicity.nonempty_equiv_of_tensor_trivial` cancels the
trivial multiplicity spaces. That published lemma takes a nonzero source pure
tensor, applies the tensor equivalence, and selects a target basis coefficient
detecting its nonzero image. Composing the source slice with that coefficient
gives a nonzero intertwiner between the two irreducible local representations.
The irreducible-intertwiner bijectivity theorem makes it a representation
equivalence. Only the source complementary space needs an explicit
nontriviality instance.

This algebraic proof uses the reference-vector invariance, nonvanishing and
local irreducibility assumptions. The topology, admissibility and fixed-line
conditions remain in the exact target but are not needed for this implication.
There is no spherical-Hecke commutativity assumption. Arbitrary finite and
infinite index types are covered; for an empty index type the pointwise
conclusion is vacuous, and the nontrivial-tail construction includes empty
tails. This theorem concerns uniqueness of supplied constructed tensors and
does not prove general factorization existence or the other clauses of
`FlathRestrictedTensorStatement`.

The source motivation is D. Flath, *Decomposition of representations into tensor
products* (1979), the final sentence of the proof of Theorem 1 on printed p.180
(one-based PDF p.176), with Example 2 and Theorem 2 on printed p.181
(PDF p.177). The registered source is `flath-1979-tensor-products`, the Corvallis
Part I volume with SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The published target explains its extraction of uniqueness for already
constructed tensors from the isotypic-restriction argument. The implemented
proof realizes that argument using the published local separation and
slice/coefficient cancellation laws; it does not use the source's general
existence theorem as an assumption.
