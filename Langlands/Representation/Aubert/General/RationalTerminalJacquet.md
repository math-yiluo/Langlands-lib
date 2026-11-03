# Jacquet comparisons on the actual rational-point smooth category

Worker 194 specializes the three published `TerminalJacquet` targets to the
literal standard rational-point families and proves the intrinsic normalization
adapter `standardLeviUnipotent_isUnimodular`. The source for the comparisons is
Aubert's 1996 erratum, printed p.4690, Remark (1), from the definition of
`D̃_G(E) = E#` through display (**). The support category `Alg({I})` is defined
on printed p.4687. These are proposition definitions, not proofs of the three
representation-theoretic assertions.

The ambient group is `RationalPoint k G.X` for a general connected reductive
group over a nonarchimedean local field, with its explicitly installed
evaluation `pointTopology`. The torus is an actual maximal split torus and
the cocharacter is generic. The finite simple-root enumeration comes from
`HasRelativeRootSystem` and splitness through `simpleRelativeRootFintype`;
every linear order on that actual subtype is quantified for the exterior
coordinates. No split-group, quasisplit-group, characteristic-zero or
positive-rank restriction is imposed.

The intrinsic normalization section names its local topology instance
`rationalTerminalJacquetPointTopology`. This internal naming correction allows
this module and `RationalCorrectedTheorem36` to be imported together: their
anonymous instances previously generated the same declaration name. The
instance still reduces to `pointTopology`, and the proposition definitions
and normalization argument retain their existing mathematical content.

The subgroups are precisely `parabolic i ν`, `levi i ν` and `unipotent i ν`.
The named standard-cocharacter and Levi-intersection assertions supply their
ambient and inside-Levi semidirect decompositions. Where needed, the named
order and endpoint statements supply increasing parabolics, decreasing
radicals and the full-root endpoints. The actual point-group topology
properties and closedness of radicals and Levis remain explicit intermediate
inputs.

`standardLeviUnipotent_isUnimodular` installs the locally compact topology of
each closed Levi. For each restricted radical it applies the published
compact-limit unimodularity theorem to closedness pulled back along the
subtype inclusion. Thus the compact-limit assertion inside the literal Levi
supplies the required modulus identity. Ambient unimodularity in the associated
comparison is likewise derived by `standardUnipotent_isUnimodular`. Neither
normalization is an arbitrary field of complex data. The inside-Levi
compact-limit premise is stated separately; this file does not derive it
from the ambient compact-limit premise.

All three targets use `IsInSupportCategory` through the published
`TerminalJacquet.supportObjects`, substituting
`rootAssociation i ν hN hZ`. Every irreducible subquotient must therefore
come from actual normalized cuspidal induction. The same representative
conjugates the literal Levis and carries the actual root subsets under the
normalizer/full-centralizer character action. The category is the full smooth
subcategory, with all equivariant maps. There is no finite-length,
admissibility or irreducibility premise on its objects.

`RationalJacquetCuspidalStatement` separately requires that `r_I(E)` is
cuspidal inside the actual Levi `M(I)` whenever `E ∈ Alg({I})`. This support
theorem is a representation-theoretic obligation, rather than a structural
assumption used to construct the complex.

`RationalFixedLeviComparisonStatement` requires a natural isomorphism
`D̃_{M(I)} ∘ r_I ≅ r_I` on that full support category. The Levi terminal
functor is the actual `LeviComplex.sharpFunctor` on restricted standard
subgroups, with support subset `Finset.univ` inside `I`; it retains its
degree-zero quotient. Its maps are the canonical induced quotient maps
inherited from the published complex.

`RationalAssociatedLeviComparisonStatement` requires the natural form of
display (**):

`r_I ∘ D̃_G ≅ Ad(n) ∘ D̃_{M(I')} ∘ r_{I'}`.

Here the relative Weyl group is the actual normalizer/full-centralizer
quotient of `torusPoints i`. The Coxeter labels are actual simple relative
roots. `RootLengthComparison`, `PositiveSimpleReflectionComparison`,
`actualLeviWeylIdentification`, `minimalityLengthCriterion` and
`associatedSubsetLaws` explicitly tie this system to the root action and
standard Levi Weyl images. In particular, the published
`rootSet_associatedSubset` identifies `I' = associatedSubset actual I`
with the actual root image `w_I⁻¹(I)`, where
`w_I = longestRep actual I` in `D(I,∅)`.

The separately named `actualAssociatedLeviConjugation` is also retained.
Every normalizer lift `n` of `w_I` is quantified in the generic target;
its subgroup equality supplies the actual conjugation functor with action
`x ↦ σ(n⁻¹ x n)`. The ambient terminal functor is the same actual
`rationalSharpFunctor` at support `I`, and the other terminal functor is
the full-support Levi cokernel at `I'`. All Jacquet functors are the actual
normalized coinvariant functors. `Nonempty` asks for a complete natural
isomorphism, including inverses and naturality with all maps. This functorial
form strengthens the displayed source object comparison; no such isomorphism
is supplied here.

The corrected filtration proof remains necessary: use two-sided modified
Bruhat support, establish double-coset minimality before the geometric lemma,
compare consecutive modified supports, and identify the actual surviving
transition maps up to exterior signs, as repaired in Ban–Jantzen (2016),
Section 4, printed pp.161–162. A finite Weyl filtration does not impose
finite length on `E`. The terminal cokernel remains present; no final
vanishing is asserted. Proposition 3.2 remains unresolved.

The topology, compact-limit, point-comparison, root and Coxeter inputs are
intermediate obligations to discharge or match to the parent's itemized
external structural ledger before final parent closure. The cuspidality
and natural-comparison targets remain representation-theoretic proof
obligations. No class formula is asserted here; those consequences require
separate finite-length and Euler arguments. Transitive imports reach
classification modules, so this file makes no classification-independence
claim.
