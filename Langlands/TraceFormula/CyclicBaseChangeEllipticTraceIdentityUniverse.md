# Universe reduction for the elliptic twisted trace identity

`CyclicBaseChangeEllipticTraceIdentityUniverseReductionStatement` says that
`CyclicBaseChangeEllipticTraceIdentityStatement` for number fields in a common universe
implies `CyclicBaseChangeEllipticTraceIdentityStatement` for number fields in independent
universes. The universes of the two spectral presentations stay fixed. The theorem
`cyclicBaseChangeEllipticTraceIdentity_of_sameUniverse` proves the implication. This
reduction is derived from the Library's elliptic trace identity statement and
arithmetic pullback. In particular, the published trace identity and the formulation
`CyclicBaseChangeEllipticTraceIdentityWithConclusion`, which names its local conclusion,
are definitionally equal.

## Changing the upper field

Given `E/F` as in the trace identity, take an `F`-algebra isomorphism `e : E ≃ₐ[F] E'`,
where `E'` lies in the universe of `F` (`exists_algEquiv_baseUniverse`). This uses
finiteness from `IsCyclicAlgebra` and separability in characteristic zero. The
primitive-element construction uses the quotient by the primitive element's
minimal polynomial. `NumberField.of_ringEquiv` and `adeleQuotientCompact` supply the
number field and compactness hypotheses for `E'`.

Conjugating `σ` by `e` keeps its order and transports its fixed elements. The
`F`-algebra isomorphism preserves the degree, giving `IsCyclicAlgebra` for the
conjugated automorphism with the original prime degree. Every infinite place of
`E'` is the pullback of an infinite place of `E` along `e⁻¹`. The proof transports
unramifiedness using `InfinitePlace.IsUnramified.comap_algHom`.

The bijection on finite places, given by `finitePlaceEquiv`, respects lying over
each place of `F` by `liesOver_finitePlaceEquiv_algEquiv`. It therefore also
preserves uniqueness of the place above each of the two designated finite places
`v` and `v'`. Arithmetic pullback takes the upper cuspidal realization and
presentation to `E'`. It preserves supercuspidality at their corresponding
places by `arithmeticComap_localComponent_isSupercuspidal`.

For weak base change, reindex the two attached spectral systems via
`SpectralSystem.IsArithmeticWeakBaseChangeOf.reindex_of_comm` for the identity of
`F` and `e`. `cuspidalSpectralArithmeticComap` attaches these reindexed systems
to the transported cuspidal classes. Arithmetic pullback along the identity
fixes the class over `F`. Apply the common-universe identity to the data over
`E'` and the original data over `F`.

## Returning the local conclusion

At `v`, use the `F_v`-algebra isomorphism
`ε = id ⊗ e : F_v ⊗_F E ≃ₐ[F_v] F_v ⊗_F E'`. It is continuous in both
directions by the module topologies. The equality intertwining the tensor
actions of `σ` and its conjugate holds on pure tensors and extends by
additivity.

Let `w` and `q` be the corresponding places of `E` and `E'`. The completion
isomorphism `E_w ≃+* E'_q` commutes with the local component maps from the
tensor algebras via `ε`. The lemma `finiteTensorMap_congr_apply` checks this
on a tensor `a ⊗ y` using `finiteTensorMap_tmul` and
`finiteCompletionEquiv_algEquiv_completionMap`, then extends by tensor
induction. Passing to matrices gives the equality of the composite group
homomorphisms. `arithmeticComapLocalComponentEquiv` identifies the original
local component with the new one pulled back along the completion isomorphism.
It composes the equivalences with the two tensor factors and the equivalence
from pulling back that factor along inverse group isomorphisms.

`CyclicBaseChangeEllipticConclusion.of_arithmeticComap` uses these facts in
`ellipticTraceIdentity_transport_comp`. This transfers admissibility, the
intertwiner and the trace identity for every Haar measure to the original upper
representation, using the same nonzero constant.
