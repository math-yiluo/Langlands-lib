# Proof of the Bezout count for a section against a linear system

`Langlands.AlgebraicGeometry.Picard.linearSystemBaseLocusBezout` proves the
published proposition
`Langlands.AlgebraicGeometry.Picard.LinearSystemBaseLocusBezoutStatement.{u}`
from the module of the same name. The theorem's type is that proposition itself,
in an arbitrary universe `u`, with no further hypotheses. The statement pair and
everything it imports are unchanged.

So the proof gives the following. Take an integral, Noetherian, separated scheme
`X` that is proper over a field `K`, with `0 < e` and `topologicalKrullDim X ≤ e`.
Take a line bundle `L`, a section `s` of `L ^ p` with nonempty generation open,
and a set `S` of sections of `L ^ q` whose base locus
`B = {x | ∀ t ∈ S, x ∉ L.sectionOpen t}` is finite. Suppose every point of `B`
where `s` vanishes has a stalk of ring Krull dimension `e`. Then the number of
points of `B` where `s` vanishes is at most
`e! * p * q ^ (e - 1) * (lineBundleEulerPolynomial f L e).coeff e`.

All helper declarations are in namespace
`Langlands.AlgebraicGeometry.Picard.LinearSystemBaseLocusBezout`. The module sets
`backward.isDefEq.respectTransparency false`, like the Library modules it builds
on. It declares local instances for the quasi-coherence of the structure module,
of tensor powers of a line bundle and of the cokernel of a section map, taken
from the published line-bundle and cokernel lemmas.

## Route, and how it differs from the statement's suggested route

The statement's Markdown suggests one route. Cut `O_X` by `s`. Then cut
`e - 1` more times by generic members of the `K`-span of `S`, chosen with
`[Infinite K]` to avoid the finitely many associated points. Before each cut,
remove the subsheaf supported in `B`, so that embedded points do not create a
kernel. Finally compare the Euler characteristic of a finite-support sheaf with
the size of its support.

The Lean proof takes a different route. It does not choose generic sections,
does not use `[Infinite K]`, and never takes a quotient by a subsheaf supported
in `B`. Instead it inducts on the dimension and uses the published filtration
of a coherent sheaf by ideal sheaves on integral closed subschemes. Every cut is
a cut of the structure sheaf of an integral scheme by a section that generates
somewhere. Such a section map is injective, so embedded points never produce a
kernel.

- **Generic sections.** None are produced. On each integral piece, the proof
  uses any one member of `S` whose generation open on that piece is nonempty.
  If no such member exists, the whole piece lies in the finite set `B`, so it
  has dimension `0` and contributes nothing in positive degree.
- **Embedded points.** After the first cut, the cokernel can have embedded
  components, possibly inside `B`. The proof never cuts this cokernel by a
  section. It filters the cokernel by the published
  `coherentIntegralIdealFiltration`. Each graded factor is the pushforward of a
  nonzero ideal sheaf `I_j` on an integral closed subscheme `W_j`. The
  degree-`d` coefficient of the cokernel is the sum of the factors'
  coefficients. On each `W_j`, the induction hypothesis is applied to `W_j`
  itself, not to `I_j`. The published
  `coherentEulerPolynomial_ideal_coeff_eq_structureModule` identifies the two
  coefficients when `dim W_j ≤ d`. A piece of dimension less than `d`, embedded
  or not, is still covered by the same induction hypothesis: it has no point of
  coheight `≥ d`, and its coefficient is `0`.

## The induction predicate

`BezoutCountInDimension d` is an internal `Prop`-valued definition used only as
the induction statement. It is not a published statement and introduces no
intersection-number, degree or Chow-group API. It says: for every field `K`,
every integral, Noetherian, separated `Z` proper over `K` with
`topologicalKrullDim Z ≤ d`, every line bundle `N` on `Z`, every `q` and every
set `S` of sections of `N ^ q` with finite base locus,

`#{x ∈ B | d ≤ coheight x} ≤ d! * q ^ d * (lineBundleEulerPolynomial f N d).coeff d`

in `ℚ`, where the count is `Set.ncard`. Here `coheight x` is the coheight of `x`
in the specialization order of `Z` (larger means more generic). By Mathlib's
`ringKrullDim_stalk_eq_coheight` it is the Krull dimension of the stalk at `x`.
There is no infinite-field premise and no hypothesis on a separate section `s`.

`bezoutCountInDimension` proves it for every `d` by induction, from
`bezoutCountInDimension_zero` and `bezoutCountInDimension_succ`.

## Topological helpers

- `le_iff_of_isInducing` and `strictMono_of_isInducing`: an inducing map of
  schemes reflects and preserves the specialization order
  (`Scheme.le_iff_specializes`, `IsInducing.specializes_iff`).
- `exists_lift_le_coheight`: let `i : W → Z` be a closed embedding and `p` a
  strict chain of generizations in `Z` whose most generic member lies in the
  range of `i`. Every member of the chain specializes from that member, so it
  lies in the closed range. The chain therefore lifts to a strict chain in `W`
  of the same length, and the lift of `p.head` has coheight at least that
  length (`length_le_coheight_head`).
- `coheight_le_topologicalKrullDim`: the coheight of a point of a scheme is at
  most `topologicalKrullDim`. This uses `ringKrullDim_stalk_eq_coheight` and the
  order isomorphism between points and irreducible closed sets
  (`irreducibleSetEquivPoints`, `coheight_le_krullDim`).
- `stalkSupport_last_subset`: the stalk support of the last term of a
  `CoherentFiltration` lies in the union of the stalk supports of its graded
  factors. This is induction along the filtration with the published
  `stalkSupport_shortExact`.

## Krull's principal ideal theorem on a chart

`exists_series_of_not_mem_trivializationOpen` takes a locally Noetherian scheme
`Z`, a line bundle `N`, a global section `u` and a point `x` where `u` vanishes
with `d + 1 ≤ coheight x`. It returns a strict chain of generizations
`x = p 0 < p 1 < ... < p d` of length `d` whose most generic member `p d` still
lies in the vanishing locus of `u`.

Proof. Choose a trivializing open around `x` and an affine open `V ∋ x` inside
it. The published `exists_inf_trivializationOpen_eq_basicOpen` gives
`a ∈ Γ(Z, V)` with `V ∩ trivializationOpen u = Z.basicOpen a`. The ring
`R = Γ(Z, V)` is Noetherian, and `x` corresponds to a prime `P` of `R` with
`a ∈ P`. Coheight is preserved by the open immersion `Spec R → Z`
(`coheight_eq_of_isOpenImmersion`), and `idealHeight_eq_coheight` turns it into
height, so `d + 1 ≤ height P`. Mathlib's form of Krull's principal ideal
theorem, `Ideal.height_le_height_add_one_of_mem`, gives
`height P ≤ height (P / (a)) + 1` in `R / (a)`. Hence `P / (a)` has coheight at
least `d` in `Spec (R / (a))`, and `exists_series_of_le_coheight` gives a chain of
length `d` starting there. Map it to `Z` along `Spec (R / (a)) → Spec R → Z`.
This composite is inducing, so the chain stays strict
(`strictMono_of_isInducing`). Its first member is `x`. Its last member lies in
`V` and outside `Z.basicOpen a`, since `a` maps to `0` in `R / (a)`. So it lies
outside `trivializationOpen u`.

## The cut step

`hasSupportDimensionLT_sectionHom_cokernel`: on an integral scheme of dimension
at most `d + 1`, the cokernel of the section map of a section with nonempty
generation open has support dimension less than `d + 1`. The published
`supportDimension_sectionHom_cokernel` says the support dimension is the
dimension of the vanishing locus. That locus is a proper closed subset, so its
dimension plus one is at most `d + 1` (`topologicalKrullDim_add_one_le_of_isClosed`).

`ncard_piece_le` handles one graded factor. Let `Z` be proper over `K`, let
`i : W → Z` be a closed immersion with `W` integral, and let `I` be a nonzero
ideal sheaf on `W` whose pushforward has support dimension less than `d + 1`.
Then `IsLocallyNoetherian`, `CompactSpace`, `IsNoetherian` and separatedness of
`W` follow from `i`. The published `supportDimension_ideal` and
`hasSupportDimensionLT_pushforward_iff` give `dim W ≤ d`. Pull `N` and `S` back
to `W` with `LineBundle.pullback` and `LineBundle.pullbackPowSection`;
`LineBundle.sectionOpen_pullbackPowSection` says the pulled-back generation
opens are preimages. So the pulled-back base locus is the preimage of `B`,
finite because `i` is injective. The induction hypothesis on `W`, with
`i ≫ f`, bounds the points `w` of `W` with `i w ∈ B` and `d ≤ coheight w` by
`d! * q ^ d` times the degree-`d` coefficient of the line-bundle polynomial of
`W`. The published `coherentEulerPolynomial_pushforward` and
`coherentEulerPolynomial_ideal_coeff_eq_structureModule` identify that
coefficient with the degree-`d` coefficient of the pushforward of `I` on `Z`.

`ncard_le_of_cut` is the cut step. Let `Z` be integral, Noetherian, separated
and proper over `K` with `dim Z ≤ d + 1`. Let `u` be a section of `N ^ r` with
nonempty generation open, and let `S` have finite base locus `B`. Assume
`BezoutCountInDimension d`. Then

`#{x ∈ B | u(x) = 0, d + 1 ≤ coheight x} ≤ d! * q ^ d * ((d + 1) * r * c)`,

where `c` is the degree-`(d + 1)` coefficient of `lineBundleEulerPolynomial f N
(d + 1)`.

1. Let `C` be the cokernel of the section map of `u`. It has finite affine
   sections and support dimension less than `d + 1`. The published
   `sectionCokernelEulerCoefficient` gives
   `(coherentEulerPolynomial f C N d).coeff d = (d + 1) * r * c`.
2. `coherentIntegralIdealFiltration` filters `C`. The proof packages the result
   as a `CoherentFiltration` with factors `i_j _* I_j`. By
   `CoherentFiltration.hasSupportDimensionLT_iff` every factor has support
   dimension less than `d + 1`. By `coherentEulerPolynomial_eq_sum` the
   degree-`d` coefficient of `C` is the sum of the factors' coefficients.
3. Let `A_j` be the set of `w ∈ W_j` with `i_j w ∈ B` and `d ≤ coheight w`.
   Every counted point `x` lies in some `i_j(A_j)`. The Krull lemma above gives
   a chain of length `d` from `x` whose last member lies in the vanishing locus
   of `u`. By the published `stalkSupport_sectionHom_cokernel_eq` that locus is
   the stalk support of `C`. By `stalkSupport_last_subset` and
   `stalkSupport_pushforward` the last member lies in the image of some `W_j`.
   `exists_lift_le_coheight` lifts `x` to `w ∈ W_j` with `d ≤ coheight w`.
4. The union of the sets `i_j(A_j)` lies in `B`, so it is finite. Each `i_j` is
   injective, so `#i_j(A_j) = #A_j`. Then `Set.ncard_le_ncard`,
   `Set.ncard_iUnion_le_of_fintype`, `ncard_piece_le` for each `j`, and steps 1
   and 2 give the bound.

## Base case

`bezoutCountInDimension_zero`. Let `Z` be integral with `dim Z ≤ 0`. Every point
has coheight `0`, so it is maximal in the specialization order. Every point
specializes from the generic point, so it equals the generic point
(`Specializes.antisymm`, `Inseparable.eq`). Hence `Z` has at most one point and
the count is at most `1`. The degree-`0` truncation of the line-bundle
polynomial is the constant `χ(O_Z)` (`coherentEulerPolynomial_zero_eq_C`). The
structure sheaf of an integral scheme is nonzero (`not_isZero_structureSheaf`),
and its support dimension is less than `1`. So
`coherentEulerCharacteristic_pos_iff_of_supportDimensionLT_one` gives
`χ(O_Z) ≥ 1`. The right side is `0! * q ^ 0 * χ(O_Z) = χ(O_Z) ≥ 1`.

## Induction step

`bezoutCountInDimension_succ`. Let `dim Z ≤ d + 1`.

- If some `t ∈ S` has nonempty generation open, apply `ncard_le_of_cut` with
  `u = t` and `r = q`. Every point of `B` lies in the vanishing locus of `t`, so
  the cut step counts exactly the points of `B` with coheight `≥ d + 1`. Its
  bound is `d! * q ^ d * (d + 1) * q * c = (d + 1)! * q ^ (d + 1) * c`.
- Otherwise every member of `S` vanishes everywhere, so `B = Z`, and `Z` is
  finite. `Z` is locally of finite type over a field, hence a Jacobson space
  (`LocallyOfFiniteType.jacobsonSpace`). A finite Jacobson scheme is discrete,
  so `dim Z = 0` (`topologicalKrullDim_zero_of_discreteTopology`). No point has
  coheight `≥ d + 1`, so the count is `0`. Every sheaf on `Z` has support
  dimension less than `d + 1`, so the published
  `coherentEulerPolynomial_coeff_eq_zero_of_supportDimensionLT` makes the
  degree-`(d + 1)` coefficient `0`. Both sides are `0`.

## Main theorem

Write `e = d + 1`, using `0 < e`. Hypothesis 3 says each counted point has stalk
dimension `e`. By `ringKrullDim_stalk_eq_coheight` its coheight is `e`, so the
counted set equals the set of points of `B` where `s` vanishes with coheight
`≥ d + 1`. `Nat.card_coe_set_eq` turns `Nat.card` into `Set.ncard`. Then
`ncard_le_of_cut` with `u = s`, `r = p` and `bezoutCountInDimension d` gives the
bound `d! * q ^ d * (d + 1) * p * c = e! * p * q ^ (e - 1) * c`.

## Where each hypothesis is used

- `[Infinite K]`: not used. The proof works over any field.
- `IsIntegral X`: in the cut by `s` (`sectionCokernelEulerCoefficient`, the
  support of the cokernel and its dimension). Integrality of the pieces `W_j`
  comes from the filtration.
- `IsNoetherian`, separatedness and properness: they define the Euler
  polynomials. Noetherianity is needed for the filtration and the Krull
  argument. They pass to the closed subschemes `W_j`. Finite type over `K`
  gives the Jacobson property in the degenerate case.
- `0 < e`: to write `e = d + 1`.
- `topologicalKrullDim X ≤ e`: in the cut step, for the cokernel coefficient
  identity and the support-dimension bound.
- Nonempty generation open of `s`: in the cut by `s`, for the same identity and
  for the support of the cokernel.
- Finite base locus: the counted sets lie in `B`, so they are finite and
  `Set.ncard` behaves additively. It also passes to each `W_j` and, in the
  degenerate case, makes `Z` finite.
- Local dimension `e` at the counted points: only the inequality
  `e ≤ coheight x` is used.

## Dependencies

The module imports the statement module, the published Library modules
`Picard.SectionCokernelEulerCoefficientProof`,
`Picard.ClosedImmersionPullbackAmpleProof`,
`Picard.AffineGenerationLocusIntersectionProof`,
`Modules.CoherentIntegralIdealFiltrationProof`,
`Modules.AmpleCoherentEulerCoefficientProof` and
`Picard.SectionCutDimensionProof`, and five Mathlib modules. The Library results
it uses are defined in these modules and reached through those imports
(paths under `Langlands/AlgebraicGeometry/`):

- `Picard/SectionCokernelEulerCoefficientProof.lean`:
  `sectionCokernelEulerCoefficient`.
- `Modules/CoherentIntegralIdealFiltrationProof.lean`:
  `coherentIntegralIdealFiltration`.
- `Modules/CoherentEulerFiltration.lean`: `CoherentFiltration`,
  `CoherentFiltration.hasSupportDimensionLT_iff`,
  `CoherentFiltration.coherentEulerPolynomial_eq_sum`.
- `Modules/CoherentEulerPushforward.lean`: `coherentEulerPolynomial_pushforward`.
- `Modules/CoherentEulerCoefficientSupport.lean`:
  `coherentEulerPolynomial_ideal_coeff_eq_structureModule`,
  `coherentEulerPolynomial_coeff_eq_zero_of_supportDimensionLT`.
- `Modules/CoherentEulerPolynomialZeroDimensional.lean`:
  `coherentEulerPolynomial_zero_eq_C`,
  `coherentEulerCharacteristic_pos_iff_of_supportDimensionLT_one`.
- `Modules/IntegralSupportDimensionProof.lean`: `supportDimension_ideal`,
  `supportDimension_sectionHom_cokernel`.
- `Modules/ClosedSupportDimension.lean`: `hasSupportDimensionLT_pushforward_iff`,
  `hasSupportDimensionLT_iff_supportDimension`.
- `Modules/ClosedStalkSupport.lean`: `stalkSupport_shortExact`.
- `Modules/ClosedPushforwardSupport.lean`: `stalkSupport_pushforward`.
- `Modules/SupportDimension.lean`: `HasSupportDimensionLT.of_topologicalKrullDim_le`.
- `Picard/IntegralAmpleSectionCokernelProof.lean`:
  `stalkSupport_sectionHom_cokernel_eq`.
- `Picard/ClosedImmersionPullbackAmpleProof.lean`: `LineBundle.pullbackPowSection`,
  `LineBundle.sectionOpen_pullbackPowSection`.
- `Picard/AffineGenerationLocusIntersectionProof.lean`:
  `exists_inf_trivializationOpen_eq_basicOpen`.
- `Picard/LineBundleEulerPolynomial.lean`: `lineBundleEulerPolynomial`,
  `hasFiniteAffineSections_lineBundle`.

The Mathlib imports are `Mathlib.AlgebraicGeometry.Properties`
(`ringKrullDim_stalk_eq_coheight`), `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`LocallyOfFiniteType.jacobsonSpace`), `Mathlib.Topology.JacobsonSpace`,
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_le_height_add_one_of_mem`) and `Mathlib.Data.Set.Card.Arithmetic`
(`Set.ncard_iUnion_le_of_fintype`).

The module introduces no intersection-number, degree or Chow-group API. Its
only definition is the internal induction predicate `BezoutCountInDimension`.

## Provenance

The bound is the classical Bezout bound in the cohomological form of The Stacks
Project, Section 33.45 (tag 0BEL), as described in the statement's Markdown. The
induction over integral pieces, with Krull's principal ideal theorem used to keep
counted points of large coheight on a piece, is this proof's own organization.
It is not taken from a numbered result in that source.
