# Functoriality of the finite-type Weil-restriction algebra

Worker 105 extends the existing canonical universal-property functoriality of
`TauCeti.Algebra.WeilRestriction` to
`Langlands.Algebra.WeilRestrictionFiniteType`. The implementation adapts the
published `Langlands/TauCeti/RingTheory/WeilRestriction/Basic.lean`,
upstream commit `8428d6217f74afa72531df0bc85d7b57ab72810f`, by the Tau Ceti
contributors. Its Apache 2.0 attribution is retained; the license is in
`licenses/TauCeti/`. The old finite-presentation interface is unchanged.

This is derived infrastructure for Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Example 2.4, printed page 3. In
particular it supplies the actual map needed to state preservation of closed
immersions without adding a finite-presentation hypothesis.

The commutative `A`-algebra `B` is finite projective. The commutative
`B`-algebras `C`, `D` and `E` are finite type. There are no topological,
faithfulness, field, Noetherianity or freeness hypotheses; the algebra
universes are independent.

`map A B φ`, for `φ : C →ₐ[B] D`, is the actual `A`-algebra map between the
two constructed representing algebras. It is classified by composing `φ` with
the universal point of `D`. `homEquiv_map` and
`lTensor_map_universalPoint` state this exact law on universal points.
`homEquiv_comp_map` identifies precomposition by the constructed map with
precomposition by `φ`, on represented points at every test algebra.
`map_id` and `map_comp` prove the identity and composition laws by the
universal-point extensionality theorem.

On finitely presented input algebras,
`finitePresentationAlgEquiv_map` proves that the new map agrees with the
published TauCeti map under the canonical representing-algebra comparisons
from `FiniteType.lean`. Its proof applies the representing equivalence and
uses the two universal-point laws. Thus this is a compatible finite-type
extension of the existing functor. Preservation of surjections and the
corresponding actual-scheme closed-immersion assertion are separate
proposition/proof obligations.
