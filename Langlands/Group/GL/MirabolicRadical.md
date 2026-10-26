# Actual mirabolic radical coordinates and standard Levi maps

Author: Worker 653.

This module constructs matrix subgroups and maps used in Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
§3.1, printed p.450 (PDF page 11, zero-based index 10). The registered original is
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 3.1–3.2 and §1.8, printed p.444, fix the group and localization
conventions for the subsequent character construction. No applicable errata
entry for this source was found in the supplied public notes or literature.

The source calls the subgroup of `GL_m` with final row `(0,...,0,1)` `P_m`.
The published Library uses `GeneralLinear.mirabolic n F` for `P_(n+1)`.
Thus this module's `radical n F` is the source's `V_(n+1)`.
The construction reuses that published group and `GeneralLinear.rankInclusion`.
The coordinate equivalences, explicit entry laws, range identifications and
topological proofs are derived implementation results. The algebra is proved
over every commutative ring `F`, in arbitrary universe, rather than only over
the local fields of the source.

## Radical and coordinates

Within `Langlands.GeneralLinear.Mirabolic`, `radical n F` is the actual subgroup
of `mirabolic n F` whose entries satisfy

```
g i j.castSucc = if i = j.castSucc then 1 else 0    (j : Fin n).
```

Together with the inherited mirabolic last row this specifies precisely
`u(v) = [[I_n,v],[0,1]]`. Its subgroup proof expands a matrix product against
these fixed identity columns. Applying the same product formula to `g⁻¹*g`
proves closure under inverse.

`radicalElement v` constructs this matrix as a unit from the indicated block
matrix, with inverse `u(-v)`, then reindexes the blocks by `finSumFinEquiv`.
`radicalElement_first`, `radicalElement_last` and `radicalElement_bottom` give
all entries. `radicalCoordinates` extracts entries `(i.castSucc, Fin.last n)`.
The two inverse identities follow by entrywise matrix equality, dividing the
indices into `castSucc` and `last` cases. Block multiplication proves
`radicalElement (v+w) = radicalElement v * radicalElement w`.

`radicalEquiv : radical n F ≃* Multiplicative (Fin n → F)` packages these maps.
`radicalEquiv_apply` gives its forward entry formula;
`radicalEquiv_symm_first` and `radicalEquiv_symm_last` give the inverse entries.
The bottom row is inherited from mirabolic membership. The inclusion
`radicalToUpperUnipotent` lands in the published actual ambient
`GeneralLinear.upperUnipotent (n+1) F`: the fixed columns kill every strictly
lower entry and give diagonal ones. Its value is the same ambient matrix.

## Levi and successor subgroups

`levi : GeneralLinear n F →* mirabolic n F` is precisely `g ↦ diag(g,1)`.
It is `rankInclusion 1` with the last-row equations proved using its block
entry laws. `levi_first`, `levi_last`, and `levi_bottom` specify its entries,
and `levi_injective` uses the published injectivity of rank inclusion.
`successor : mirabolic n F →* mirabolic (n+1) F` restricts this construction
to the smaller mirabolic group; `successor_first` and `successor_last` give
its nontrivial block and zero final column. It is injective as a composite.

`leviSubgroup` and `successorSubgroup` are the actual ranges of these
homomorphisms. `leviEquiv` and `successorEquiv` identify their original groups
with these actual embedded subgroups. The forward maps retain the matrices
just described. Their inverse entry formulas recover the leading block.

`levi_mul_radicalElement` proves `diag(g,1)*u(v) = u(g*v)*diag(g,1)` by
expanding all four blocks with the finite-sum formula for matrix products.
Here `g*v` means exactly `g.val.mulVec v`, so
`(g*v) i = ∑ j : Fin n, g.val i j * v j`, without transposing the matrix.
Cancellation gives `levi_conjugate_radicalElement`. The formula proves
normalization in one direction; applying it to `g⁻¹` proves the reverse
membership implication. This gives the actual subgroup witnesses
`leviSubgroup_le_normalizer` and `successorSubgroup_le_normalizer` required
by character localization.

## Topologies and boundary rank

All groups and subgroups have their inherited matrix-unit topologies.
With any topology on `F`, coordinate extraction, the upper-unipotent inclusion,
and both standard embeddings are continuous. `leviContinuousEquiv` and
`successorContinuousEquiv` also have continuous inverse maps: values and
inverse values of their leading matrix blocks are continuous coordinate
projections. This uses the topology on units, without assuming continuity
of inversion in `F`.

For a topological commutative ring, `continuous_radicalElement` checks
continuity of the displayed block values and inverse block values;
the only nonconstant entries are `v i` and `-v i`. Hence
`radicalContinuousEquiv` upgrades the coordinate isomorphism to a topological
group isomorphism. With a Hausdorff coefficient topology, `radical_isClosed`
expresses the radical as an intersection of closed entry equations; that
closedness theorem itself does not require ring operations to be continuous.

All constructions include `n=0`. The empty vector space has one element;
`radical_rankOneSubsingleton` follows from the published triviality of
`mirabolic 0 F = P_1`. `GeneralLinear 0 F` remains the published group of
units of the actual matrix ring on `Fin 0`, so the Levi map still has its
literal matrix meaning. No positive-rank assumption is used.
