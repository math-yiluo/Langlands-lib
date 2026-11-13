# Smooth integral models of maximal algebraically bounded subgroups

`MaximalBoundedIntegralModelStatement.{u}` is the maximal-subgroup
construction step in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 8.3.1, printed pp. 295–296 / PDF pp. 326–327.
The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The statement starts from the original smooth affine group `G` over a
valued field `K` whose canonical integer ring is a Henselian DVR with
algebraically closed residue field. A supplied subgroup `B` is maximal
among algebraically bounded subgroups of the actual `rationalPoints G`,
where boundedness means bounds on every actual global regular
function. It asks for an actual smooth affine flat finite-type model
whose specified generic identification gives the literal subgroup
equality `M.integralPoints = B`.

This is a derived subresult of the source's proof for a vertex. The
proof paragraph uses a faithful closed linear representation, a stable
full lattice, the general linear model on that lattice, schematic
closure and smoothening. That paragraph uses no connectedness,
reductivity, building or openness condition once the maximal bounded
subgroup has been supplied. The statement neither constructs such a
subgroup nor asserts that one exists.

The accompanying `LatticeStabilizerBoundedness` helper module proves
that preservation of a full lattice in a closed representation implies
algebraic boundedness. Its proof uses finite generation, clearing
denominators and the published matrix-entry boundedness theorem. This
provides the bounded overgroup to which maximality applies.

The existence proposition in this module is unproved. A separate
conditional construction in the shared draft records how the four
open stable-lattice, general-linear-model, closure and smoothening
propositions imply it; those propositions are not premises of this
existence target. Proving those existence inputs, or giving another
unconditional construction, remains the obligation of the exact proof
successor. In particular, the target assumes neither a stable lattice
nor an ambient integral model, schematicity witness or model comparison.

The registered *Corrections and additions* (2024), source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 37 adds perfectness of the residue field to Section 8.3. The
algebraically closed residue field in this statement is perfect. The
source's finite-intersection step for a union of facets and its later
model-axiom constructions are separate obligations.
