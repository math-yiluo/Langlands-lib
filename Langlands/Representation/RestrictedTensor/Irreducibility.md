# Irreducibility of actual algebraic restricted tensor representations

This is an internal consequence of the published finite external-tensor
irreducibility theorem and the Library's actual algebraic direct-limit
construction of restricted tensors. It is needed to connect the finite
spectral presentations of the factorization of partial Rankin–Selberg
Whittaker integrals (`ArchimedeanFactorizationStatement`) to their irreducible
actual finite factors.
It introduces no alternative carrier or representation.

`Langlands.RestrictedTensor.RestrictedTensorIrreducibilityStatement` asserts
that the genuine restricted tensor representation is irreducible under the
following hypotheses. The scalar ring `k` is a field, `I` is an arbitrary index
type, and each `G i` is a group acting on a `k`-vector space `V i` by `ρ i`.
Supply subgroups `H i`, a finite exceptional set `E` and reference vectors
`e i` fixed by `H i` outside `E`. Assume these reference vectors are nonzero
outside `E`, each local representation is irreducible, and every local
self-intertwiner is a scalar multiple of its identity. The conclusion is
irreducibility of the existing
`representation H ρ E e he` on the existing `Space k V E e`.

The theorem `restrictedTensorIrreducibility` proves the proposition, using the
more directly applicable `representation_isIrreducible`. All four universe
parameters remain free. There is no topology or admissibility assumption; the
scalar self-intertwiner condition is retained explicitly. It is not automatic
for arbitrary fields. The exceptional reference values at indices in `E` are
unused. Both finite and empty index types are allowed.

The proof uses the actual finite stage maps `of`.

1. `stageGroupElement S g` extends a tuple in `∏ i : S, G i` by the identity
   outside the finite stage `S`. It lies in the actual cofinite restricted
   product because every subgroup contains the identity. The lemma
   `of_external` proves that `of` intertwines this element with the finite
   external tensor action. It checks this equality on pure tensors, using
   `representation_pure_of_mem`, and then obtains it for every stage vector
   by linearity.
2. Given an invariant subspace `N` of the restricted tensor, its inverse image
   under any stage embedding is a subrepresentation of that stage's finite
   external tensor. The proved `FiniteTensor.isIrreducible_external` applies
   using local irreducibility and the supplied scalar self-intertwiners. If
   this inverse image contains a nonzero vector, it is the whole stage.
3. Take a nonzero vector of `N` and an arbitrary target vector. Both are images
   of finite stages by `exists_of`. Enlarge these two stages to their union.
   The first vector remains nonzero at the union, since its image in the
   limit is nonzero. The previous step places every vector of the union stage
   in `N`, in particular the target vector. Thus any nonzero invariant
   subspace is the whole space.
4. Local irreducibility gives nonzero local spaces. The existing
   `space_nontrivial` theorem, using the nonzero reference hypothesis, gives
   a nonzero vector of the restricted tensor. This excludes equality of the
   zero and whole subrepresentations and completes irreducibility. The
   remaining case, an invariant subspace with no nonzero vector, is zero.

The argument uses finite external-tensor simplicity and the specified
transition maps rather than assuming global restricted-tensor irreducibility.
It proves neither restricted-tensor admissibility nor a Whittaker product
formula. Applying it to a supplied spectral presentation still requires
establishing its local scalar self-intertwiner hypotheses and transporting
through that presentation's actual equivariance. Continuous archimedean
Whittaker factorization and the unconditional Rankin–Selberg factorization
statement are not proved here.
