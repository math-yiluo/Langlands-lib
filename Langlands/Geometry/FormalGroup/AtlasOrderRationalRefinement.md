# Refinement of rational formal atlas maps commuting with the full order

This is internal algebraic infrastructure for rational formal maps with an
order action. It derives restriction from `AtlasRationalRefinement`, the
chartwise centralizer in `AtlasOrderRationalMorphism`, and the actual integral
order-equivariant coefficient isomorphisms in `AtlasOrderRefinement`. No
additional original-literature assertion is made.

Let `O` and `R` be commutative rings with an `O`-algebra structure on `R`, let
`D` be a ring with an `O`-algebra structure, and let `F` be a field with an
`O`-algebra structure. The formal atlases `X` and `Y` have finite, possibly
different, coordinate types and equal principal covers `h : X.opens = Y.opens`.
They carry full `D`-actions `E` and `E'`. A supplied `CoverRefinement X`
includes a finer principal cover and, for each finer chart, a selected original
chart whose generator becomes invertible there. Its retargeting to `Y`
uses that same finer cover and transports the selected charts along `h`.
All algebra tests are in the base-ring universe.

`RationalHom.restrict_mem` proves that the existing ambient rational restriction
belongs to the full-order chartwise centralizer for the refined actions.
For a usable finer chart `b` over a test algebra `A`, it forms the composite
of the rationalized source `orderChartIso.hom`, the original order-equivariant
rational chart map at the selected original chart, and the rationalized target
`orderChartIso.inv`. These three maps commute with every element of `D`.
The ambient `onChart_restrict` equation identifies their composite with the
restriction on that chart. Transporting the commutation equation across this
equality proves the claim. This uses actual formal maps and their coefficient
comparisons.

`RationalHom.restrict` packages that ambient restriction as an `F`-linear map
between the two chartwise centralizers. Its underlying map is exactly the
existing restriction of global rational atlas Hom, as `restrict_val` states.
Linearity follows from the ambient linear map and equality of subtypes.
`restrict_ofHom`, `restrict_id`, and `restrict_comp` respectively identify it
with rationalization of integral order-linear restriction and prove preservation
of identity and composition. For composition, the second map is restricted
along the retargeted intermediate refinement. `restrictRingHom` bundles the
endomorphism case as a ring map for actual rational formal composition.

`RationalHom.onChart_restrict` gives the same conjugation equation inside the
full-order rational coordinate Hom, so both sides retain their order-commutation
proofs. Its proof applies subtype extensionality and the ambient chart equation.

For quasi-isogenies, assume also that `O` is a domain and `F` is its fraction
field. `QuasiIsogeny.restrict` restricts the forward and inverse full-order
rational maps along the corresponding source refinements. The two inverse
equations follow from the ambient restricted quasi-isogeny by subtype
extensionality; no new inverse assumptions are supplied. The projection lemmas
`restrict_hom` and `restrict_inv` give these two maps, and `toAtlas_restrict`
identifies the underlying ambient quasi-isogeny. Restriction preserves `refl`,
`symm`, `trans`, and rationalization `ofIso` of integral order-linear
isomorphisms. The proofs use uniqueness from the forward map and the rational
restriction laws above.

Here full-order rational Hom is the chartwise centralizer inside
`F ⊗[O] BasicAtlas.Hom`, not the tensor product of integral `D`-linear Hom.
The construction retains global finite tensor sums and a supplied selected
refinement. It asserts no injectivity, surjectivity, independence of choices,
identification with all locally rational maps, or rational gluing theorem.
Heights, framing, polarizations, moduli representability and level structures
remain separate constructions.
