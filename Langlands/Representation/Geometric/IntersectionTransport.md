# Weyl transport between actual Levi intersections

This definition pair supplies the middle transport functor in the GL
geometric lemma. It constructs the group equivalence between the actual
intersections in product-Levi coordinates, proves its matrix formulas and
continuity, and transports actual smooth representations and intertwiners.
It does not assert the geometric lemma or the standardness of either
intersection.

## Groups and conventions

Let `F` be a commutative ring, let `B` and `C` be ordered positive block
shapes of the same rank `n`, and let `w` be any permutation of `Fin n`.
Write `M` and `N` for the embedded block Levis and write `p(w)` for the
existing permutation matrix, which sends `e_j` to `e_(w j)`.

The existing `sourceLevi F B C w` is the subgroup of the actual product
`B.Levi F` consisting of `m` such that
`p(w) * B.leviEmbedding F m * p(w)⁻¹` lies in `N`. Thus its embedded image
is `M ∩ w⁻¹(N)`. Similarly, `sourceLevi F C B w⁻¹` is the subgroup of
`C.Levi F` whose embedded image is `N ∩ w(M)`. These are actual matrix
subgroups and product coordinates, not abstract groups supplied with
assumed conjugation data. All permutations are allowed: minimality is
needed later to identify these intersections with standard refinements,
but is unnecessary for conjugation and representation transport.

## Constructed equivalence

`Langlands.Geometric.intersectionLeviMap` first embeds a source element,
conjugates its matrix by `p(w)`, and recovers the target product coordinates
using the inverse of the existing `C.leviEquiv F`. Membership in the source
intersection is exactly the evidence that this conjugated matrix belongs
to the embedded target Levi.

`intersectionLeviMap_embedding` proves the precise matrix formula.
`intersectionLeviMap_mem` proves that its value belongs to the target
intersection, and `intersectionLeviHom` packages the resulting homomorphism.
`intersectionLeviHom_inverse` proves that inverse conjugation recovers the
source element, using injectivity of the actual block embedding and group
cancellation. `intersectionLeviConjugation` packages both maps as a group
equivalence, with both inverse identities and multiplicativity proved.
The forward and inverse formulas are exposed by
`intersectionLeviConjugation_embedding` and
`intersectionLeviConjugation_symm_embedding`.

For any topology making `F` a topological ring, the matrix groups have
the existing units topology, the product Levis have the product topology,
and the intersections have the subgroup topology.
`continuous_intersectionLeviMap` follows from continuity of the block
embedding, multiplication by the fixed conjugating matrices, and the
inverse coordinate map. `intersectionLeviConjugationContinuous` packages
the equivalence with continuity in both directions. No local compactness,
field structure or residue characteristic is required for this construction.

## Representations and the functor

The coefficient field is complex, with no topology imposed on the
representation carrier. Its universe is independent of the ring universe.
`intersectionTransport` pulls an actual representation of the source
intersection back along the inverse of `intersectionLeviConjugation`.
Consequently, a target element acts through its inverse-conjugate source
element. `intersectionTransport_apply` states that action formula, while
the inverse embedding formula identifies it with `p(w)⁻¹ n p(w)` in the
ambient matrix group.

`intersectionTransportMap` keeps the underlying linear map of an
intertwiner and verifies equivariance after that pullback. Its application
formula is proved. `isSmooth_intersectionTransport` proves smoothness by
the published continuous-pullback result, using continuity of inverse
conjugation. Finally, `intersectionTransportFunctor` is the functor
between the actual `SmoothRep` categories. The identity and composition
laws follow from the unchanged linear maps and are proved in Lean.
Neither admissibility nor irreducibility is assumed.

## Provenance and dependencies

Original source: Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups. I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.7, printed page 443 (PDF page 4), defines transport along a group
isomorphism by the inverse isomorphism in the action. Sections 2.11–2.12,
printed page 448 (PDF page 9), use the conjugation map from
`M ∩ w⁻¹(N)` to `w(M) ∩ N` in the graded geometric-lemma functor. Section
6.3, printed page 468 (PDF page 29), identifies the corresponding
parabolic triples when `w` is minimal.

The construction is derived from those source conventions and the
published concrete GL block embeddings. Its elementary conjugation
identities hold over every commutative ring; its smooth transport holds
for any topological ring. These extensions concern only the construction,
not an extension of the p-adic geometric-lemma theorem.

The pair reuses `Geometric.WeylDefinitions`, `Category.Basic`, and
`Smooth.Transfer.PullbackProof`. The existing `intersectionConjugation`
in `WeylDefinitions` operates on intersections of subgroups in one
ambient group; the new equivalence gives the corresponding explicit
maps in the two different product-Levi coordinate groups required by
Jacquet and induction functors. It does not replace that ambient
construction. The existing whole-Levi transport in
`CuspidalSupport.LeviDefinitions` assumes that `w` conjugates the entire
source Levi onto the target; the present construction applies to their
intersections without such an assumption.

The standard-refinement identification of these intersections, their
normalized Jacquet and induction functors, and the natural filtration
asserted by BZ77 section 2.12 remain separate obligations. All intrinsic
group, continuity, intertwiner and functor laws for this pair are proved;
no theorem truth, quotient classification or filtration is assumed as data.
