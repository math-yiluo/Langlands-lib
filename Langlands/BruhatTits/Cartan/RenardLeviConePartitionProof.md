# Renard V.3.21.1 modulo the common norm kernel: proof

`Langlands.BruhatTits.Cartan.RenardLeviCones.leviConePartition` proves
[`LeviConePartitionStatement`](RenardLeviConePartitionStatement.md).
For each standard base Levi with split component `A`, the image of its
full nonnegative cone in `A(F)/⁰A` is partitioned by the images of the
strict cones of the split components of the containing standard
parabolics.

## Orders on quotient classes

The canonical valuation quotient equivalence
`rationalNormKernelQuotientEquiv` makes every character order well
defined on quotient classes: by `rationalNormKernelQuotientEquiv_mk`, the
order of the class of `x` at a character `χ` is `characterOrder A χ x`.
The private lemma `characterOrder_map` states that evaluating a character
on the image of a point under a morphism `g : B → A` is the same as
evaluating its restriction `g ≫ χ` on that point.

Let a class lie in the piece at `K`, represented by the image of a strict
point `y` of a split component `B` of the `K`-Levi. For a simple root `α`
in `K`, the order of the class at `f ≫ α` is zero, because the restriction
of `α` to `B` vanishes (`selectedRoot_restrict_eq_zero_standardLevi`).
For a simple root outside `K`, the order is positive, by the strict cone
condition (`mem_componentStrict_iff_order`). Hence the order is
nonnegative at every simple root, which gives containment in the image
of the nonnegative cone (`mem_componentPlus_iff_order`), and `K` is
recovered from the class as the set of simple roots where its order
vanishes. Uniqueness of the index follows.

## Every class of the cone lies in some piece

Start from a point `x` of the nonnegative cone of the base split
component. The uniformizer section (`isUniformizerLatticeSection`)
supplies a cocharacter `ζ` of `A` whose section point has the class of
`x`. Its image `ξ` in the ambient maximal split torus pairs with each
simple root `α` as the order of `x` at `f ≫ α`. It therefore pairs
nonnegatively with all simple roots, and it annihilates the roots in the
base index `J` (`latticePairing_cocharacterMapInt_standardLevi_eq_zero`).
The simple roots annihilated by `ξ` form an index `K ⊇ J` for which `ξ` is
a standard cocharacter (`isStandardCocharacter_simpleRootFace`).

The `K`-Levi has a split component `B` (`standardLeviSplitComponentStatement`).
The standard parabolic order (`standardParabolicOrder`) gives the
inclusion of the canonical `J`-Levi in the canonical `K`-Levi, and
`leviSplitComponentInclusion` supplies a compatible map `g : B → A`.
The strict uniformizer image theorem (`standardLeviStrictImage`) at
`g ≫ f` gives a strict point `y` of `B` whose image in `T` is the
section point of `ξ`. The base map `f : A → T` is a closed subgroup
embedding, so it is a monomorphism and its rational-point map is
injective. Since `f` sends the section point of `ζ` to the section point
of `ξ`, it follows that `g` sends `y` to the section point of `ζ`, whose
quotient class is the class of `x`. So the class lies in the piece at `K`.

## Source

David Renard's *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, gives the point inequalities in
V.3.21 (printed p. 116 / PDF p. 122) and the analogous real chamber
decomposition in V.3.16 (printed pp. 113–114 / PDF pp. 119–120).
The statement's Markdown explains the correction to (V.3.21.1).
The Lean proof realizes the corrected partition through the
uniformizer section and the actual split components.
