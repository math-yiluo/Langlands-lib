# Extension of a line bundle across an open immersion

`Langlands.AlgebraicGeometry.Picard.OpenImmersionLineBundleExtensionStatement.{u}`
is the proposition that every actual line bundle on an open subscheme extends
to a locally Noetherian scheme whose local rings on the complement are
factorial. This module supplies a statement, with no proof or new axiom.

## Formal statement and source comparison

For every `X : Scheme.{u}` with `IsLocallyNoetherian X`, every
`Y : Scheme.{u}` and every open immersion `j : Y ⟶ X`, assume

```text
∀ x : X, x ∉ Set.range j →
  UniqueFactorizationMonoid (X.presheaf.stalk x).
```

Then, for every `D : LineBundle Y`, there exists `E : LineBundle X` and an
actual module-sheaf isomorphism

```text
((LineBundle.pullback j).obj E).obj ≅ D.obj.
```

The Library's `LineBundle` is the full subcategory of actual scheme-module
sheaves locally isomorphic to the structure sheaf. Its pullback is the
ordinary pullback of these module sheaves, equipped with the local rank-one
property. The conclusion therefore specifies a bundle and an isomorphism
of sheaves, not just equality of formal divisor or Picard classes.

The source is the Stacks Project, Divisors, Lemma 31.29.3, Tag
[0BD9](https://stacks.math.columbia.edu/tag/0BD9). Its open subset `U` is
the range of `j`. An open immersion identifies `Y` with this open
subscheme. Restriction to `U` corresponds to the Library pullback along
`j`; the displayed isomorphism is written in the opposite orientation to
the source, which is equivalent by symmetry. Structure-sheaf stalks at
scheme points are nontrivial local rings, so their unique-factorization
monoid property includes the cancellation needed for a unique
factorization domain.

There is no irreducibility, reducedness, normality, global integrality,
separatedness, quasi-compactness or projectivity assumption. Local
Noetherianity is imposed on `X`. Factoriality is required only at points
outside the open range; no factoriality hypothesis is imposed on `Y`.
There is no condition on `D`. The statement asserts neither a unique
extension nor extension of any chosen section or trivialization.
It includes empty opens and disconnected schemes.

## Retained original and reading extent

Registered source `stacks-open-line-bundle-extension-0bd9-2026-11-01`,
directory SHA256
`e04f95facf97c45df0e888af89a8d92fd61988dcb397e6354110b6e4d184380d`:

`/home/taskhub/pilot/literature/Stacks Project - Open line-bundle extension and Cartier divisors, Tags 0BD9, 0BD8, 0AYM (HTML snapshot 2026-11-01)`.

The cited file is `0BD9.html`, entire lemma and proof. The accompanying
`0BD8.html` and `0AYM.html` contain the proof's effective-Cartier-divisor
extension and quasi-affine divisor-representation inputs. All three
statements, proofs and comments were read. Tags 0BD9 and 0BD8 have no
comments. The six comments on 0AYM discuss corrections already reflected in
the retained page. No source-specific Stacks or Raynaud errata note was
found in the bounded workspace, project-note and current Library-note
filename checks; this does not assert that no other errata exist.

## Role and remaining proof obligations

Worker 59 formulated this general prerequisite for extension from the
generic self-product of an abelian scheme over a DVR. Worker 339 proposed
the complement-only factoriality interface and the use of Tag 0BD9.
The original trait argument is Raynaud, LNM 119, proof of Lemme XI 1.5,
printed p.162, but this general proposition is cited directly to Stacks.

The Stacks proof extends effective Cartier divisors near a point outside
the open, then uses gluing and maximal extension. Implementing this route
requires actual sheaf constructions and restriction comparisons.
The present module implements none of these proof steps. In particular,
it does not prove smooth-DVR factoriality, identify the chosen fraction
field with the canonical generic open, or establish the target
`DiscreteValuationRingSelfProductLineBundleExtensionStatement`.
Those inputs and the final assembly remain separate obligations.
