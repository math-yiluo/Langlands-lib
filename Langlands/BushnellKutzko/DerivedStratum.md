# Refinements and derived strata

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, §2.2, first paragraph,
printed p. 51 (PDF p. 63). The final auxiliary predicate abbreviates the
conclusion used in (2.4.1)(iii) and (2.4.2)(vi), printed pp. 65–66.

`Stratum.IsRefinement S T` says that `S` is simple, `T` has the same
hereditary order and level, its depth is `S.r−1`, and
`T.b − S.b ∈ 𝔓^{−S.r}`. Thus `T` is exactly a stratum of the form
`[𝔄,n,r−1,β+b]` with the required perturbation.

`Stratum.IsGeneratedField S E` expresses that the given field action
identifies `E` with `K[S.b]`: some generator `β : E` maps to `S.b`
under the published `subfieldEmbedding`, and `Algebra.adjoin K {β} = ⊤`.
It fixes the field meant by the source rather than supplying any
of the theorem conclusions.

`Stratum.IsDerivedStratum S E b s D` defines the relation between
the original simple stratum, a perturbation, a tame corestriction and
the derived stratum. Here `D` is an actual
`Stratum (integralClosure O E) E V`, in `End_E(V)`.
The predicate requires the source's simplicity and generated field,
`b ∈ 𝔓^{−r}`, equality of the underlying sets of lattices at each
integer index, and the equations `D.n = r`, `D.r = r−1`, `D.b = s(b)`.
In particular it specifies every component of `[𝔅,r,r−1,s(b)]`.

The source's `𝔅 = 𝔄 ∩ End_E(V)` is represented by the chain over the
integral closure with those same lattices, exactly the mechanism
in the published `SubfieldOrderStatement`. If `O = 𝒪[F]` and
`K = F`, the ring `integralClosure O E` is definitionally
`subfieldIntegers F E`. The general formulation also applies at
subsequent extension-field stages. The supplied algebra structures
only express the scalar towers; no structural theorem is a field.

The relation formulation defines derived strata without using an
unproved theorem to select a chain or assert the existence of a
stratum. Whenever such a stratum is supplied, all its parameters
are fixed by these equations. Existence conclusions can quantify
the actual strata explicitly.

`Stratum.DerivedEquivalentToSimple` does that: it states the
existence of an actual derived stratum `D` and an equivalent simple
stratum `C` over `E` with the same chain and integer parameters.
It is internal notation for a conclusion, not an assumption or
a theorem. In particular its existential chain requirement
prevents any vacuity from a missing centralizer-chain construction.
