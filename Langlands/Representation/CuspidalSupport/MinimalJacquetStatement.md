# Minimal nonzero quasicuspidal Jacquet descent

Authors: Worker 186 and Worker 205.

`Langlands.CuspidalSupport.MinimalNonzeroJacquetTheorem.{uF,uV}` is a
proposition definition stating nonzero quasicuspidal Jacquet descent. It
quantifies every prime `p`, every actual `F : PadicField.{uF} p`, every
compatible `T : F.TopologicalData`, and every natural rank `n`, including
zero. With `T.topology` on the field and `T.generalLinearTopology n` on
`GL_n(F)`, every nonzero object
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)` has a block shape
`B : GeneralLinear.BlockShape n` such that the actual normalized Jacquet
object `J := (T.normalizedJacquetFunctor B).obj A` is nonzero and satisfies
`IsLeviQuasicuspidal B J.representation`.

The entire all-prime, all-field, all-topology, all-rank assertion is inside
this one proposition. The field and representation carrier universes are
independent; the Jacquet quotient retains the carrier universe `uV`.
`Nontrivial` expresses nonzeroness of a complex vector space. Smoothness
is part of the input category. There is no irreducibility, admissibility,
finite-length, finite-generation, chosen-support, or preselected-Jacquet
hypothesis. The conclusion concerns the whole Jacquet module, with no
choice of an irreducible constituent or quotient. This pair states the
future proof target and proves no instance of it.

## Actual constructions and conventions

The pair imports the published `CuspidalSupport.LeviDefinitions` and
`Jacquet.Parabolic` modules. A block shape describes an ordered partition
into positive sizes, with its actual upper block parabolic and product
Levi. The whole-group parabolic is allowed: it is the one-block shape for
positive rank and the empty shape at rank zero. No unique Levi or
maximal-block-count assertion is added to the conclusion.

The functor uses the actual quotient `B.JacquetModule A.representation`
by the unipotent action. On this quotient the Levi action is multiplied
by the inverse positive half modulus, `delta_B(m)^(-1/2)`. Smoothness of
this actual normalized object is already proved in the imported
construction. No functor or its required properties are supplied as
hypothetical data.

`IsLeviQuasicuspidal B` tests every `BlockRefinement B` whose actual
refined parabolic subgroup is proper, requiring its unipotent
coinvariants to be a subsingleton. Normalization changes the action but
not the quotient carrier, so this vanishing condition is the source's
quasicuspidality condition for normalized Jacquet modules. The relevant
minimality is precisely this absence of further nonzero proper Jacquet
quotients; no separate minimality witness is required.

## Original source and derived rank-zero case

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups. I*, Annales scientifiques de l'Ecole Normale Superieure (4)
10 (1977), 441–472. Registered source:
`bernstein-zelevinsky-1977-induced-i`. Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained source:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

The source correspondence is as follows:

- Section 1.2, printed p.443 / PDF p.4, defines `Alg G` as complex
  representations with open vector stabilizers, the smooth category used here.
- Sections 1.8(b)–1.9(c), printed pp.444–445 / PDF pp.5–6, give the
  normalized Jacquet convention and transitivity.
- Sections 2.1–2.4, printed p.446 / PDF p.7, identify standard Levi
  subgroups, specialize them to ordered block partitions for `GL_n`, state
  normalized transitivity in 2.3(c), and define quasicuspidality by
  vanishing of every proper standard Jacquet module.
- Section 2.14(1), first paragraph, printed p.449 / PDF p.10, directly
  asserts that every nonzero object of `Alg G` has a nonzero quasicuspidal
  Jacquet module for some standard Levi, citing 2.3(c). This assertion
  precedes the additional assumption that the object is a subquotient of
  the particular induced representation considered there.

For positive rank, the statement specializes that general reductive-group
assertion to actual `GL_n` over finite p-adic extensions. The rank-zero
case is an elementary extension under the Library's conventions, rather
than a claim that the source explicitly discusses `GL_0`: use the empty
block shape. The group `GL_0(F)` and its empty product Levi are trivial,
the unipotent action contributes zero relations, and the normalized
Jacquet quotient is isomorphic to the original vector space. There are
no proper block refinements, so quasicuspidality is vacuous. This explains
why no positivity hypothesis on `n` is needed; it is not a Lean proof of
that case in this pair.

## Descent rationale and remaining proof obligations

For positive rank one can start with the whole-group Jacquet module and
choose a standard Levi minimal among those with nonzero Jacquet module.
There are finitely many ordered positive block partitions. If a further
proper refinement had a nonzero Jacquet quotient, normalized transitivity
would give a smaller standard Levi with a nonzero Jacquet module of the
original input, contradicting minimality. The chosen module is thus
quasicuspidal. This is an explanation of the source's use of 2.3(c), not
an implemented proof.

A subsequent proof must justify the finite descent, the whole-group
identification (including the empty-block case), and the transitivity and
coordinate identifications comparing iterated refined quotients with a
direct standard-block quotient. The existing
`Langlands.Parabolic.NormalizedRefinementJacquetTransitivityClause` in
`Langlands.Representation.Parabolic.RefinementTransitivityStatement` is a
related statement target. Its output group is the actual `refinedLevi`; a
proof must identify this with the Levi of the flattened block shape. The
existence of that proposition is not a proof or an assumption of this pair. The later subquotient, association, and
finite-length conclusions in BZ77 section 2.14 are not asserted here.
