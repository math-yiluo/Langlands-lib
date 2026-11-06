# A common finite Galois splitting field for two actual tori

This internal construction packages a single field extension that splits two
actual tori over the same arbitrary field. The field and both group schemes live
at an arbitrary universe `u`; the construction retains that universe.

`TorusCommonFiniteGaloisSplittingData k T Q` consists of a field `E : Type u`,
an algebra structure over `k`, finite dimensionality, the Galois property, and
proofs that the actual scalar extensions of `T` and `Q` to `E` are split tori.
The data type itself accepts any two group schemes. Its constructor
`IsTorus.commonFiniteGaloisSplitting` requires precisely that each is a torus.

The implementation first applies the published theorem
`torusFiniteGaloisSplitting` to `T`, giving a finite Galois extension `K/k`.
It applies that theorem again to the scalar extension `Q_K`, giving a finite
Galois extension `L/K`. Torus preservation here is the published
`IsTorus.baseChange_of_isAlgebraic`. The composite extension `L/k` is finite and
separable. The scalar-tower comparison
`IsSplitTorus.baseChange_fieldTower_iff` shows that both original tori split over
`L`. An embedding into `SeparableClosure k` then places `L` inside its finite
normal closure `E`. Mathlib supplies finite dimensionality and normality of
this closure; separability follows from the separable closure. Finally,
`IsSplitTorus.baseChange_fieldTower` transports both splitting proofs to `E`.
Classical choice extracts the resulting field and proofs as data. The field,
algebra, finite-dimensionality and Galois projections are registered as instances.

The provenance is an internal combination of the existing finite Galois
splitting theorem, its scalar-tower transport lemmas, and Mathlib's finite
normal-closure construction. It supplies the common-field part of the Levi
cocenter root-model task. Root data, ambient maximality, the character image,
and Galois corrections require their separate geometric arguments.
