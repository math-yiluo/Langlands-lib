# Explicit regular-action and left-ideal Noetherian criteria

This file contains three closed internal statement targets and their
aggregate, in namespace `Langlands.Algebra.UnitizationIdealNoetherian`.
Worker 709 drafted them and Worker 850 revised them. They use Mathlib's
actual `Unitization R A`, ordinary `Module` instances, `Submodule`,
`AddSubgroup`, `IsNoetherian` and `IsNoetherianRing`. Each declaration is a
`def` returning `Prop`. No result is proved in this file.

## Common data and the regular action law

Let `R : Type uR` be a commutative ring and `A : Type uA` a nonunital
ring. A nonunital ring is associative, but it need not be commutative or
have an identity element. `[Module R A]` gives scalar multiplication.
`[IsScalarTower R A A]` says `(r • a) * b = r • (a * b)`.
`[SMulCommClass R A A]` says `a * (r • b) = r • (a * b)`.
These are the hypotheses Mathlib uses to make `Unitization R A` a ring. Its
elements are pairs `u` with components `u.fst : R` and `u.snd : A`. The
product is `(r, a) * (s, b) = (r * s, r • b + s • a + a * b)` and the
identity is `(1, 0)`.

Each criterion binds an actual ordinary Mathlib instance
`[Module (Unitization R A) A]`. Mathlib modules are unital, so `(1, 0)`
acts as the identity. The instance is an arbitrary binder, not a
construction in this file. Each criterion then assumes the following
elementwise law, for all `u : Unitization R A` and all `a : A`:

```
u • a = u.fst • a + u.snd * a
```

This law makes the supplied action the regular left action
`(r, b) • a = r • a + b * a`. It is a hypothesis on the left of each
implication. It assumes no finite-generation or Noetherian comparison.

For a ring `S`, Mathlib defines `IsNoetherianRing S` as `IsNoetherian S S`:
every left ideal of `S` is finitely generated. `IsNoetherian S M` says
that every `S`-submodule of `M` is finitely generated.

## `RegularCriterionStatement`

This statement binds, in order, `R : Type uR`, `A : Type uA`,
`[CommRing R]`, `[NonUnitalRing A]`, `[Module R A]`,
`[IsScalarTower R A A]`, `[SMulCommClass R A A]` and
`[Module (Unitization R A) A]`, followed by the regular action law. It
then states

```
IsNoetherianRing (Unitization R A) ↔
  IsNoetherianRing R ∧ IsNoetherian (Unitization R A) A
```

So the unitization ring is left Noetherian if and only if `R` is
Noetherian and `A` is Noetherian as the supplied unitization module. The
scalar ring is not assumed Noetherian. Its Noetherianity is one conjunct
of the right-hand side.

## `ScalarIdealCriterionStatement`

This statement binds, in order, `R : Type uR`, `A : Type uA`,
`[CommRing R]`, `[IsNoetherianRing R]`, `[NonUnitalRing A]`,
`[Module R A]`, `[IsScalarTower R A A]`, `[SMulCommClass R A A]`,
`[Module (Unitization R A) A]` and
`[IsScalarTower R (Unitization R A) A]`, followed by the same regular
action law.

The last instance says `(r • u) • a = r • (u • a)`. Here `r • (s, b)`
is `(r * s, r • b)`. Given the regular law and `IsScalarTower R A A`, this
holds automatically:
`(r * s) • a + (r • b) * a = r • (s • a + b * a)`.
So binding it does not restrict the statement.

The statement equates `IsNoetherianRing (Unitization R A)` with this
property:

```
∀ P : Submodule R A,
  (∀ (a x : A), x ∈ P → a * x ∈ P) →
  ∃ S : Finset A, (↑S : Set A) ⊆ P ∧
    ∀ Q : Submodule R A,
      (∀ (a x : A), x ∈ Q → a * x ∈ Q) →
      (↑S : Set A) ⊆ Q → P ≤ Q
```

The variable `P` ranges over every actual `R`-submodule of `A`. Its
hypothesis says that `a * x ∈ P` for every `a : A` and every `x ∈ P`, so
`P` is stable under all left multiplications. Call such a submodule a
scalar-linear left ideal. The conclusion gives a finite subset `S` of `A`
contained in `P`. Every scalar-linear left ideal `Q` that contains `S`
must also contain `P`. Thus `P` is the smallest scalar-linear left ideal
containing the finite set `S`. Generation uses addition, scalars from `R`
and left multiplication by elements of `A`. The property does not say that
`P` is finitely generated as an ordinary `R`-module.

## `AdditiveIdealCriterionStatement`

This statement binds only `A : Type uA`, `[NonUnitalRing A]` and an
actual ordinary `[Module (Unitization ℤ A) A]`, followed by the regular
action law with `ℤ` in place of `R`. No other instance is bound. The ring
structure on `Unitization ℤ A` uses Mathlib's integer action of the
additive group, `AddCommGroup.toIntModule`. The compatibility instances
come from Mathlib's `NonUnitalNonAssocRing.int_isScalarTower` and
`AddGroup.int_smulCommClass`. In the law, `u.fst • a` is the integer
multiple of `a`.

The statement equates `IsNoetherianRing (Unitization ℤ A)` with this
property:

```
∀ P : AddSubgroup A,
  (∀ (a x : A), x ∈ P → a * x ∈ P) →
  ∃ S : Finset A, (↑S : Set A) ⊆ P ∧
    ∀ Q : AddSubgroup A,
      (∀ (a x : A), x ∈ Q → a * x ∈ Q) →
      (↑S : Set A) ⊆ Q → P ≤ Q
```

Here `P` and `Q` range over all additive subgroups of `A` that are stable
under left multiplication, that is, all additive left ideals. They are not
restricted to subgroups that are linear for some other scalar ring. The
meanings of `P`, `S` and `Q` are as before, with additive subgroups in
place of `R`-submodules. No field, algebra or extra scalar structure is
used. The statement has no Noetherian hypothesis on `ℤ`.

## `UnitizationIdealNoetherianStatement`

The aggregate is

```
RegularCriterionStatement.{uR, uA} ∧
  ScalarIdealCriterionStatement.{uR, uA} ∧
  AdditiveIdealCriterionStatement.{uA}
```

Its universe parameters are `uR` and `uA`, in that order. The scalar and
algebra universes are independent. The additive component uses only `uA`.
Every component binds all its carriers and structures internally, so each
one is a closed proposition.

## Scope

The criteria allow noncommutative algebras, the zero algebra and algebras
with zero multiplication. If `A` happens to have an identity, it is not
used: the unitization adjoins a new one. No identity in `A`, commutativity
of `A`, field of scalars, finite dimension, finite generation,
countability or nontriviality is assumed.

## Provenance and source boundaries

These are derived internal targets. The book does not state any of these
three equivalences as a separately numbered assertion. The intended
derivation is elementary algebra, which a later proof must formalize.
`A` is the kernel of the scalar projection from the unitization onto `R`,
and the quotient by this kernel is `R`. Under the regular law, the
submodules of the supplied module `A` are the left ideals of the
indicated kind. The targets were chosen because of the unitization and
finite-localization passages below.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Its PDF page number is the printed page number plus six.

- Global conventions, printed6/PDF12. Rings are not assumed unital unless
  explicitly stated. Even over a unital ring, modules are not assumed
  unital a priori. For a unital ring `A`, `M(A)` denotes the full
  subcategory of unital `A`-modules.
- I.2.1, printed14/PDF20. For a complex algebra `A` without unit, the book
  introduces `Ã = A ⊕ ℂ·1_A`, with `1_A` declared to be its unit. An
  `A`-module that is also a complex vector space becomes a unital
  `Ã`-module. Mathlib's `Unitization R A` is this construction, with `ℂ`
  replaced by an arbitrary commutative ring `R`. The regular law is the
  corresponding action of the unitization on `A` itself. The general
  scalar ring and the integer case are derived choices.
- C.II, final proposition, printed279/PDF285. This proposition assumes a
  commutative Noetherian complex algebra `B` and a finitely generated
  `B`-module whose localization at an endomorphism is also finitely
  generated. It uses Noetherian stabilization. These criteria are
  motivated by that use and do not formalize the proposition.
- A.I.3, example, printed249/PDF255. For a unital ring `A`, the book says
  that a module is of finite type in `M(A)` exactly when it is finitely
  generated, and that `M(A)` is Noetherian exactly when `A` is Noetherian.
  That example concerns the explicitly unital category `M(A)` of a unital
  ring. The targets here concern ordinary unital modules over the
  unitization. They do not identify these modules with any category of
  possibly nonunital `A`-modules or with the book's categorical
  finite-type notion.

The public source note `notes/renard/stable-quotients.md` audits the C.II
passage. It records that the final proposition has no dedicated target
and that its conventions must be checked against later interfaces. No
project errata note for the 2026 edition was found. The supplementary
author errata for the 2010 edition, `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were searched for these passages. Their PDF19 entry reuses
`Ã = A ⊕ ℂ·1_A` "as in I.2.1" for a different appendix theorem. The search
found no correction of the passages cited here. No author-issued erratum
is claimed for these targets.

For a possibly nonunital algebra, the book's phrase “Noetherian algebra”
admits several readings: Noetherianity of the unitization, a condition on
scalar-linear left ideals, a condition on all additive left ideals, or a
categorical condition. This file selects none of them. It records the
scalar-linear and the additive ideal domains separately. It asserts no
equivalence between the two ideal properties.

The targets construct no general action, Hom comparison, category
equivalence, restriction, quotient or stable-subobject lattice. They make
no comparison with the categorical finite-type or Noetherian predicates.
They do not state or prove the localization proposition, its
stable-power decomposition or its localized-pair identification. Those
obligations stay with whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`; this file neither discharges nor
narrows them. A separate proof task must wait until this aggregate is
published. It may then use independently published prerequisites or
prove the required algebra with full provenance.
