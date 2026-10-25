# Geometric-point openness for a universal rigidified Picard parameter

`Langlands.AbelianScheme.FieldPicardZeroGeometricOpenLocusStatement.{u}`
is a proposition definition. It preserves the hypotheses of
`FieldPicardZeroOpenLocusStatement`: an arbitrary field `k : Type u`, an
abelian scheme `A : AbelianScheme (Spec k)`, a parameter `P : Over (Spec k)`,
an actual `L : RigidifiedFamily A P`, `LocallyOfFiniteType P.hom`, and the
full rigidified universal property

```text
RigidifiedLineBundle.IsUniversal A.X.hom
  (unitSection A) (unitSection_comp A) L.
```

This universal property classifies rigidified line-bundle isomorphism classes
on every test scheme over `k`; it is not restricted to field-valued tests.
Neither perfectness nor algebraic closedness is assumed for `k`.

The conclusion asks for an actual `U : P.left.Opens`. For every algebraically
closed field `K : Type u` and every actual scheme map
`s : Spec K → P.left`, it requires

```text
IsPicardZeroFamily A
  ((RigidifiedLineBundle.relativePullback A.X.hom
    (unitSection A) (unitSection_comp A)
    (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)
  ↔ Set.range s ⊆ (U : Set P.left).
```

The composite `s ≫ P.hom` gives `Spec K` its structure over `k`; no separately
chosen field homomorphism or compatibility hypothesis is needed. The bundle
in the criterion is the actual rigidified relative pullback of the supplied
family. By the published `isPicardZeroClass_classifyingMap_iff`, its family
condition is precisely the existing class condition on the canonical
classifier.

`IsPicardZeroFamily` uses `familyLineBundle` to move the underlying bundle
from the relative-family product to the actual base-changed abelian scheme.
It then applies `IsGeometricallyPicardZero`, which tests translation invariance
on every algebraically closed field-valued fibre. Thus the pulled-back family
still has all of its own geometric fibres tested. No algebraic-equivalence
or identity-component predicate replaces this condition.

## Original source and derived interface

The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Paragraph (6.2), printed p.88/PDF p.92, describes rigidified bundles, their
actual pullbacks, and the universal Poincaré bundle. Chapter VI §3, printed
p.95/PDF p.99, identifies the Picard functor of an abelian variety over a
field with rigidified line-bundle classes, and gives the point formula
`φ_L(x) = [t_x^*L ⊗ L⁻¹]`. Theorem (6.18) and Definition (6.19), printed
p.96/PDF p.100, describe the identity component and its restricted Poincaré
bundle. Corollary (7.22), printed p.106/PDF p.110, identifies `Pic⁰` with
the kernel of the homomorphism from the Picard scheme to the homomorphism
scheme. Its preceding Proposition (7.21), printed p.105/PDF p.109, supplies
the algebraically closed field argument used there.

These passages motivate this derived interface in the Library's chosen
definitions. Corollary (7.22) alone is not a proof of the displayed
criterion. A proof must construct the open subset in any supplied universal
pair `(P, L)` and establish the exact geometric comparison with translation
invariance of the actual pulled-back families. A route through the identity
component must justify its openness, transport from the universal property,
and the required fibre and base-change comparisons.

The declaration reuses Worker 390's proposed geometric-point interface and
imports only the published parent statement. It adds no ambient existence,
projectivity, identity-component comparison, openness, or dual-scheme
assumption. It supplies a statement, not a proof.

## Relation to the all-test-scheme target

The conclusion is restricted to geometric points. It does not establish the
parent's `IsPicardZeroOpenLocus` criterion for every test scheme and map,
including nonreduced schemes. That further assembly requires geometric
detection for actual pulled-back families, pullback composition, and geometric
points above scheme points. The parent statement and its imported definitions
are unchanged.
