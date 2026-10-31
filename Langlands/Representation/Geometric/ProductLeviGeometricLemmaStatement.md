# The normalized geometric lemma inside a product Levi of GL

This module states Bernstein–Zelevinsky's geometric lemma, section 2.12, for
the group `G = B.Levi F.Carrier`, a standard block-diagonal Levi subgroup of
`GL(n,F)`, using the actual normalized refined induction and refined Jacquet
functors of the Library. The pieces are the existing `GL_n` geometric-lemma
pieces `geometricPieceFunctor`, restricted to the minimal representatives that
lie in the Weyl group of `B.Levi`. The aggregate
`Langlands.Geometric.PadicProductLeviGeometricLemmaTheorem` is a proposition
definition; this module does not prove it.

## Setting and actual groups

Fix a prime `p`, an actual finite extension `F : PadicField p` of the p-adic
field, its compatible `TopologicalData T`, a natural number `n`, a coarse
ordered positive block shape `B : BlockShape n`, and two refinements
`Q S : BlockRefinement B`. A refinement gives an ordered positive block shape
of every block of `B`. Write `D = B.flatten Q` and `C = B.flatten S` for the
flattened shapes of `n`. All representations have complex coefficients, the
smooth categories use `T.topology` and the induced subgroup topologies, and no
admissibility, irreducibility or finite-length hypothesis is imposed.

Inside `G = B.Levi F.Carrier` the refinement `Q` gives the standard parabolic
`refinedParabolic F B Q`, with Levi `refinedLevi F B Q` and unipotent radical
`refinedUnipotent F B Q`; likewise for `S`. These are BZ's parabolic triples
`(P, M, U)` of `G` for the standard subgroups `M = refinedLevi F B Q` and
`N = refinedLevi F B S`.

The published `flattenedLeviEquivContinuous F B Q` is a continuous
multiplicative equivalence from `D.Levi F.Carrier` onto `refinedLevi F B Q`.
By the published `flattenedLeviEquiv_embedding`, its composite with the
block-diagonal inclusion of `B.Levi` into `GL(n,F)` is the block-diagonal
inclusion of `D.Levi`. So both sides are the same subgroup of `GL(n,F)` in
different coordinates.

`BlockMinimalRepresentatives B Q S` is the subtype of the existing
`MinimalRepresentatives D C` whose underlying permutation lies in
`blockWeyl B`, the permutations preserving every block of `B`. It is a finite
type, because `MinimalRepresentatives D C` is a subtype of permutations of
`Fin n`.

## The composite and the asserted gluing

`innerJacquetInductionFunctor T B Q S` is the actual composite

1. `SmoothRep.pullbackFunctor` along the inverse of
   `flattenedLeviEquivContinuous F B Q`, from smooth representations of
   `D.Levi` to those of `refinedLevi F B Q`;
2. `T.normalizedRefinedInductionFunctor B Q`, normalized smooth induction from
   `refinedParabolic F B Q` to `B.Levi`, with the positive half of
   `T.refinedLeviModulus B Q`;
3. `T.normalizedRefinedJacquetFunctor B S`, the normalized coinvariants of
   `refinedUnipotent F B S` (the upper refined Jacquet functor), with the
   inverse half of `T.refinedLeviModulus B S`;
4. `SmoothRep.pullbackFunctor` along `flattenedLeviEquivContinuous F B S`,
   back to smooth representations of `C.Levi`;
5. `SmoothRep.toRep`.

This is BZ's `F = r_{N,G} ∘ i_{G,M}` for `G = B.Levi`, read on flattened
coordinates. Its source is `SmoothRep.{0,uF,uV} ℂ (D.Levi F.Carrier)` and its
target is `Rep.{max uF uV} ℂ (C.Levi F.Carrier)`; induction enlarges the
carrier universe to `max uF uV`. These are exactly the source and target of
`geometricPieceFunctor T D C w ...`.

`ProductLeviGeometricLemmaTheorem T B Q S` asserts the existence of:

- for every `w : BlockMinimalRepresentatives B Q S`, a refinement `S' w` of
  `D` and a refinement `R' w` of `C`;
- the three subgroup equalities `IsIntersectionRefinement D C w (S' w)` and
  `IsIntersectionRefinement C D w⁻¹ (R' w)` from the `GL_n` statement;
- a finite enumeration `e : Fin m ≃ BlockMinimalRepresentatives B Q S`, each
  index exactly once;
- an `IsGluedFrom` relation between `innerJacquetInductionFunctor T B Q S` and
  the published graded functors
  `geometricPieceFunctor T D C w (S' w) (R' w) ...`, typed by the Levi
  components of the equalities.

The refinements and equalities precede the filtration in the existential
quantifiers. All of these are conclusions, not theorem-truth inputs. As in
`GeometricLemmaStatement`, the imported `IsGluedFrom` means a filtration of
the actual composite by natural subfunctors, starting at zero and ending at
the whole functor, after a permutation of the finite list, with a natural
isomorphism from each successive quotient functor to its graded functor. It
asserts a filtration, not a splitting. The enumeration and the filtration are
chosen once for the whole source category, and zero graded pieces are
allowed.

`PadicProductLeviGeometricLemmaTheorem` universally quantifies this statement
over the prime, the actual finite p-adic extension, the compatible topology,
positive rank `n`, the coarse shape `B`, and both refinements. It asserts
nothing for arbitrary topological groups or positive-characteristic fields.

## Source correspondence and provenance

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I*, Annales scientifiques de l'École Normale Supérieure
(4) 10 (1977), 441–472, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 2.1, printed page 446 (PDF page 7), sets up the theory for any
connected reductive group `G` with fixed minimal parabolic and split torus,
standard subgroups `M < G` and parabolic triples. Section 2.2 gives the
`GL(n)` example, where standard subgroups are block-diagonal Levis of ordered
partitions. Section 2.11, printed page 448 (PDF page 9), defines
`W^{M,N} = {w ∈ W | w(M ∩ P₀) ⊂ P₀, w⁻¹(N ∩ P₀) ⊂ P₀}` and states that
`M ∩ w⁻¹(N) < M` and `w(M) ∩ N < N`. Section 2.12 on the same page states
the geometric lemma: `r_{N,G} ∘ i_{G,M}` is glued from
`F_w = i_{N,N'} ∘ w ∘ r_{M',M}` for `w ∈ W^{M,N}`, with an enumeration, a
filtration and functorial quotient isomorphisms. Gluing is defined in 1.10 and
1.11 (printed page 445, PDF page 6).

This module applies 2.12 to `G = B.Levi`, a product of general linear groups
and hence connected reductive, with the upper triangular matrices of `B.Levi`
as minimal parabolic, the diagonal torus, `M = refinedLevi F B Q` and
`N = refinedLevi F B S`. The dictionary to the `GL_n` objects is derived, not
quoted:

- The Weyl group of `B.Levi` is `blockWeyl B`. `W^{M,N}` computed in
  `blockWeyl B` is the set of permutations in `blockWeyl B` that increase on
  every block of `D` and whose inverses increase on every block of `C`, that
  is, `BlockMinimalRepresentatives B Q S`. Because `blockWeyl D` and
  `blockWeyl C` lie in `blockWeyl B`, these are exactly the `GL_n` minimal
  representatives of the double cosets contained in `blockWeyl B`.
- A permutation in `blockWeyl B` normalizes `B.Levi`, which contains
  `D.Levi`. Hence the `GL_n` intersections `D.Levi ∩ w⁻¹(P_C)`,
  `D.Levi ∩ w⁻¹(C.Levi)` and `D.Levi ∩ w⁻¹(U_C)` used by
  `IsIntersectionRefinement` equal BZ's intersections taken inside `B.Levi`,
  and symmetrically for `w⁻¹`.
- The Jacquet and induction functors inside the pieces are normalized by the
  moduli of the refined parabolics of `D.Levi` and `C.Levi`, which depend
  only on these Levis and not on the ambient group, as in BZ's
  `r_{M',M}` and `i_{N,N'}`. The outer functors use
  `T.refinedLeviModulus`, the product of the block moduli, which is the
  modulus of the refined parabolic in `B.Levi`.
- `flattenedLeviEquivContinuous` and `flattenedLeviEquiv_embedding` identify
  BZ's `M` and `N` with `D.Levi` and `C.Levi` as subgroups of `GL(n,F)`.

The `GL_n` specialization in `GeometricLemmaStatement` records why no extra
positive character appears in the normalized pieces (BZ77 6.3–6.4) and which
induction constructors are used. The same remarks apply inside `B.Levi`,
which is compact modulo each of its parabolic subgroups. Bundling the
refinements with the filtration combines 2.12 with the standardness statement
2.11(b), as in the `GL_n` module. The subtype, the composite functor and the
flattened coordinates are internal constructions needed to express this
specialization with the existing `GL_n` pieces. The module introduces no
arbitrary functor parameters and no axioms, and it does not supply the
compactness, Haar-modulus, standardness or gluing proofs.
