# The nonnegative cocharacter and actual split-central quotients: proof

`Langlands.GroupScheme.CocharacterUniformizer.coneQuotientComparison` proves
exactly `Langlands.GroupScheme.CocharacterUniformizer.ConeQuotientComparisonStatement`.
It keeps every universe, field and group-scheme parameter of the published
statement and adds no hypothesis. `F : Type u` is any nonarchimedean local
field in either characteristic. `G` is any connected reductive group scheme
over `F`, split or not. `i : T → G` is any maximal split torus, `ν` is any
generic cocharacter, and `a : A → G` is any split component. `f : A → T` is
any supplied morphism with `CommGroupScheme.groupHom f ≫ i = a`. Nonreduced
relative root systems and rank zero are included, since the proof makes no
case distinction on the roots.

Write `R` for `simpleRelativeRoots i ν`, `P` for its common integral
annihilator `RealTorusSpace.rootAnnihilatorInt T R`, `N` for the
rational-point image of `CA F A` under `f`, and `q` for
`QuotientGroup.mk' N`. The implemented proof has the following steps.

1. The published theorem `Langlands.GroupScheme.simpleRootSplitCentralImage`
   (exact proof of `SimpleRootSplitCentralImageStatement`) is applied at the
   same `F, G, T, i, ν, A, a, f`, with the same hypotheses. It gives the
   equality `P = (RealTorusSpace.cocharacterMapInt f).range`.
2. The published theorem `CocharacterUniformizer.quotientComparison` (exact
   proof of `QuotientComparisonStatement`) is applied to `A`, `T` and `f`.
   Its split-torus hypothesis on `T` is `hi.1.1`: the first conjunct of
   `IsMaximalSplitTorus i` is `IsSplitSubtorus i`, whose first conjunct is
   `IsSplitTorus T.toGrp`. Rewriting with the equality
   from step 1 gives a multiplicative group equivalence `e` from
   `cocharacterLattice T ⧸ P` onto the subgroup `(CA F T).map q` of
   `T(F)/N`. For every integral cocharacter `c`, `e` sends the class of
   `c` to `q (latticeSection F T c)` in `T(F)/N`.
3. A monoid homomorphism `g` from `Multiplicative (CocharacterCone.quotient T R)`
   to `CAplusQuotient F T R A f` sends an element `x` to the value of `e` at
   the underlying lattice class of `x`. To see that this value lies in
   `CAplusQuotient`, take the nonnegative representative `c` given by the
   image witness of `x` in `CocharacterCone.quotient`. The formula of
   step 2 writes the value as `q (latticeSection F T c)`. The section point
   `latticeSection F T c` is in `CAplusMonoid` by definition of that
   submonoid. The unit and product laws are those of `e`, transported
   through the subtype values.
4. `g` is injective. Equal images have equal values in `T(F)/N`, so `e`
   takes equal values at the two underlying lattice classes. Injectivity
   of `e` then makes the two classes equal, and hence the two monoid
   elements are equal.
5. `g` is surjective. Every element of `CAplusQuotient` is `q` of a section
   point `latticeSection F T c` with `c` nonnegative, by the definitions of
   `CAplusQuotient` and `CAplusMonoid`. The class of `c` lies in
   `CocharacterCone.quotient T R`, and the formula of step 2 shows that
   `g` sends it to the given element.
6. `MulEquiv.ofBijective` turns `g` into the required monoid equivalence.
   For a nonnegative `c`, the value of this equivalence at the class of `c`,
   taken in `T(F)/N`, is the value of `e` at that class. The formula of
   step 2 gives `q (latticeSection F T c)`, which is the required equality.

The proof uses the actual cocharacters, rational points, the chosen
uniformizer section and the supplied `f` throughout. It defines no
auxiliary declaration. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The comparison is the derived statement motivated by David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, V.2.5 (printed p.107 / PDF p.113) and V.3.23–V.3.24 (printed
p.117 / PDF p.123), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source quotient of V.3.24 is identified with its nonnegative integral
lattice model, as explained in the statement's Markdown. This proof gives
no finite-generation result and no strict-face partition. It does not prove
the source's general freeness assertion, which is false in general.

The proof is the reduction from the two comparison statements, with its two
hypotheses replaced by the published proofs; the unconditional proof was
compiled.
