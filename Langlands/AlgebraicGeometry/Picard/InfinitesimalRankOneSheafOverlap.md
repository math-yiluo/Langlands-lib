# Common-overlap coherence for the actual patched rank-one sheaf

This internal construction continues the published
`InfinitesimalRankOneSheaf` pair using the published ordinary pullback
construction `AffineCompositeTrivialization`.

Let `R,A,B,C` be commutative rings in an arbitrary common universe `u`,
with the two stated `R`-algebra structures on `A,B`, actual ring maps
`a : A → C`, `b : B → C`, and the stated categorical ring pullback square.
For a unit `c` of `C` and a specified unit lift `v` in `B`, the published
pair module is defined by `a(z₁) = c * b(z₂)`. Write `χ` for the actual
composite `R → A → C`, named `overlapMap`. The construction requires no
additional algebra structure on `C`.

## The same ordinary pullback and its transition

`firstOverlapIso` and `secondOverlapIso` trivialize the same ordinary pullback
of the actual patched sheaf along `Spec.map χ`. They apply
`affineCompositeUnitIso` to the published first and second leg
trivializations. That construction retains the canonical composition and
equal-morphism pullback comparisons and the canonical structure-sheaf
pullback isomorphism. The second factorization uses exactly the
commutativity of the given ring square, in the direction `h.w.symm`.

The two `adjoint_toOpen` lemmas send every associated-sheaf generator of a
pair `z` over every open `U` of `Spec R` to the coefficient sections
`a(z₁)` and `b(z₂)`, respectively, on the inverse-image open in `Spec C`.
These formulas describe those generators; they do not assert that every
section over an arbitrary open comes from a single global pair.

`overlap_identity` is the actual equality of ordinary pullback sheaf morphisms

```
firstOverlapIso.hom = secondOverlapIso.hom ≫ affineScalarHom c.
```

Here `affineScalarHom c` is the published multiplication morphism of the
structure sheaf of `Spec C`. The orientation follows from the defining
pair-module equation. Both `independent` lemmas give literal equality of the
corresponding isomorphisms for any two unit lifts of the same `c`.

## Prescribed diagonal morphisms and existence

For `c,d : Cˣ` and scalars `x : A`, `y : B` satisfying
`a(x) * c = d * b(y)`, the published `diagonalSheafMap` is induced by the
actual pair map `(z₁,z₂) ↦ (x*z₁,y*z₂)`. The two
`OverlapIso_diagonalSheafMap` lemmas state that its ordinary pullback along
`Spec.map χ`, followed by the target overlap trivialization, equals the
source overlap trivialization followed by multiplication by `a(x)` or
`b(y)`, respectively. The two `diagonalSheafIso` versions specialize these
actual morphism identities to prescribed compatible unit multipliers.

`exists_lineBundle_and_coherent_pullbackIsos` assumes surjectivity of `b` and
nilpotence of its actual kernel ideal. For every `c`, it gives the local
rank-one property of the same `patchedSheaf`, ordinary leg trivializations
`eA,eB`, their two all-open coordinate formulas, both all-open formulas for
the specified common-overlap composites of `eA,eB`, and the actual transition
identity between those composites. The common-overlap maps are explicitly
constructed from those very leg trivializations, rather than supplied as
unrelated isomorphisms. Only this existence result adds surjectivity and
nilpotence; the preceding constructions use the given unit lifts.

## Implemented proof and provenance

This is derived internal content. The only mathematical imports are the
published `InfinitesimalRankOneSheaf` and `AffineCompositeTrivialization`
modules. Their actual ordinary pullbacks and associated-sheaf generators
supply all input objects and formulas.

The two overlap coordinate formulas specialize the published all-open
composite-trivialization formula to the two coordinate projections.
Private generic lemmas compute adjoints after postcomposition and after
pullback of an associated module map, using the ordinary
pullback-pushforward adjunction's naturality and Mathlib
`tilde.toOpen_map_app`. Ordinary-pullback generator extensionality
`tildePullback_hom_ext` and the published scalar generator formula then
reduce the transition identity to `z.property`, the pair-module membership
equation. Keeping these computations generic avoids expanding concrete
composite isomorphisms in their proofs. Lift independence follows from the
published independence of the leg trivializations. Diagonal compatibility
uses the same generic adjunction calculation and the actual ring maps'
multiplicativity.

The existence proof reuses the published
`exists_lineBundle_and_pullbackIsos`, whose surjective nilpotent unit lifting
supplies the original leg trivializations. It applies the generic composite
formula to those isomorphisms and their coordinate identities, then uses the
same pair-module equation to prove their transition identity.

Arbitrary line-bundle patching, the global Picard-groupoid equivalence,
pointed deformation comparison, and representability remain separate
obligations.
