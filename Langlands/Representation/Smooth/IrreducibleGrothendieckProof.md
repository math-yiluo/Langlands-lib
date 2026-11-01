# Irreducibles form the integral basis of exact finite-length smooth K₀

Authors: Worker 320 (original proof) and Worker 585 (preparation, verification
and final documentation).

This module proves the published
`Langlands.SmoothRep.IrreducibleGrothendieckStatement` by showing that the
published integer-linear realization and composition-factor map are inverse.
The proof is an internal algebraic consequence of actual composition series,
Jordan–Hölder independence, exact multiplicity additivity and the universal
property of the exact quotient. Its two direct imports are
`Langlands.Representation.Smooth.IrreducibleGrothendieckStatement` and
`Langlands.Representation.Smooth.IrreducibleCompositionFactors`.

## The objects, labels and exact relations

Let `k : Type uR` be a field and `G : Type uG` a group with an arbitrary
`TopologicalSpace G`. All representation carriers lie in the independently
quantified `Type uV`. The map being proved bijective is exactly
`SmoothRep.realizeIrreducibles.{uR,uG,uV} k G` from the published
`IrreducibleLattice k G` to `FiniteLengthGrothendieckGroup k G`.

Each basis label is a genuine isomorphism class of actual irreducible smooth
representations. Equality of labels means existence of an actual equivariant
linear equivalence, equivalently an isomorphism of smooth objects. The factors
used in the proof are the actual graded quotients of invariant submodules,
with smoothness inherited through the actual inclusion and quotient maps.
Their labels are those of `IrreducibleRealization`, without any replacement or
resizing of the label type. An irreducible representation has finite length
over the group algebra `k[G]`; finite dimension over `k` is not required.

The target is the quotient of the free integral module on genuine
finite-length isomorphism classes by the span of `[B] - [A] - [C]` for every
actual short exact sequence. Here `IsShortExact` requires an injective first
intertwiner, a surjective second intertwiner, and equality of the first map's
range with the second map's kernel. This includes nonsplit sequences. The
published `factorMap` descends to this entire quotient because its
composition-factor sums are additive for every such sequence. The present
proof uses that descended map unchanged.

## The exact class of a composition series

`subrepresentation_hasFiniteLength` transfers finite group-algebra length
along the injective inclusion of an actual invariant submodule.
`filtration_step_shortExact` constructs the actual inclusion of each lower
invariant submodule into the next one and pairs it with the actual graded
quotient projection. Injectivity is that of submodule inclusion; surjectivity
is that of the quotient map. The equality of range and kernel is proved using
`Submodule.range_inclusion` and `Submodule.ker_mkQ`.

For a supplied finite filtration `s` with irreducible graded pieces and a
finite-length ambient object `A`, `realize_seriesClass` proves that realizing
the sum of its genuine irreducible labels gives the exact class of `A`.
Each step's short exact relation expresses the graded class as the difference
of the classes of its upper and lower submodules. Summing over `Fin n`
telescopes to the last submodule class minus the first.

The first submodule is zero. The helper
`ofRepresentation_eq_zero_of_subsingleton` proves its class vanishes by
applying an actual short exact sequence consisting of zero maps between
subsingleton objects, obtaining `[A] = [A] + [A]` and cancelling.
The last submodule is the full submodule; `subrepresentationTopEquiv` builds
an actual equivariant linear equivalence to `A` from its bijective inclusion.
The telescoping identity uses finite-sum endpoint formulas and covers the
empty-series case as well.

## The two inverse identities and bijectivity

`SmoothRep.IrreducibleGrothendieckProof.factorMap_comp_realize` proves
`factorMap.comp (realizeIrreducibles k G) = LinearMap.id`. Linear maps from
the free integral lattice are determined by their generators. Every genuine
irreducible label has an actual representative; the published generator
formula for realization and the published single-factor formula for an
irreducible object compute the composite on that generator. Integer linearity
handles every coefficient.

`SmoothRep.IrreducibleGrothendieckProof.realize_comp_factorMap` proves the
opposite composite equals identity. The published exact-quotient object
extensionality reduces it to the class of each actual finite-length object.
`factorMap_ofRepresentation` computes its factor sum, and
`realize_seriesClass` identifies the realization of that sum with the
original exact class. The published factor construction selects an actual
composition series from finite group-algebra length and proves independence
of that choice. No composition series is a premise of the final theorem.

Evaluating the two linear-map identities gives a left inverse and right
inverse of realization. Their injectivity and surjectivity consequences prove

```
Langlands.SmoothRep.irreducibleGrothendieckStatement.{uR,uG,uV}
    (k : Type uR) [Field k] (G : Type uG) [Group G] [TopologicalSpace G] :
  Langlands.SmoothRep.IrreducibleGrothendieckStatement.{uR,uG,uV} k G
```

There is no admissibility, finite-dimensionality, countability, resizing,
topological-group compatibility, composition-series or other theorem-valued
premise. The independent carrier universe is retained by subtypes and actual
module quotients. Classical choices already used for composition series do
not change these universes or the genuine labels.

## Actual general linear groups and product Levis

The directly proved specializations are
`Langlands.GeneralLinear.irreducibleGrothendieckStatement.{uV,uF} n F` and
`Langlands.GeneralLinear.BlockShape.irreducibleGrothendieckStatement.{uV,uF} F B`.
Their conclusions are exactly their respective published
`IrreducibleGrothendieckStatement` propositions. Each applies the generic
theorem at `.{0,uF,max uF uV}`, with coefficient field `ℂ`, to the actual group
`GeneralLinear n F` or `B.Levi F`, using the existing topology. The field
`F : Type uF` needs only `Field F` and `TopologicalSpace F`; the carrier
universe is `Type (max uF uV)`, and the specialization's universe order stays
`.{uV,uF}`. Every natural rank is allowed, including zero. Product-Levi
irreducibles are arbitrary irreducible smooth representations of the actual
product group; no tensor-factorization hypothesis is used.

## Provenance and independence

The proof derives the comparison from the published algebraic
Jordan–Hölder and exact-quotient constructions. The original smooth complex
motivation and its Aubert source are documented in the imported statement
pair; this proof does not use that source assertion as a proof of bijectivity
or attribute the arbitrary-field and arbitrary-topology generality to it.
No new literature assertion is transcribed here.

The complete project import closure consists of the new proof and 32
unchanged lower modules: generic filtration and Jordan–Hölder results,
smooth representations and their actual subquotients, the integral lattice,
and the basic GL and block-group definitions. It contains no Aubert operator,
parabolic induction, Jacquet functor, analytic theorem or segment,
multisegment, tempered, square-integrable or regular classification input.
The published comparison statement and all its dependencies are unchanged.
