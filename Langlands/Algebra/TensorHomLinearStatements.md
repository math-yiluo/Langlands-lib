# Coefficient-linear tensor–Hom and associativity isomorphisms: statements

This file states that the canonical tensor–Hom and associativity isomorphisms of
Renard I.2.2 are linear for the coefficients. It covers the Theorem
(I.2.2.1)–(I.2.2.4) over the unitizations and the Corollary (I.2.2.5)–(I.2.2.7)
for nondegenerate modules over idempotented algebras. The namespace is
`Langlands.Algebra.TensorHomLinear`. The two closed propositions are
`Langlands.Algebra.UnitizedTensorHomLinearTheorem` (the Theorem) and
`Langlands.Algebra.NondegenerateTensorHomLinearTheorem` (the Corollary). Their
conjunction, at the same six universe levels (coefficients, two rings, three
carriers), is `Langlands.Algebra.TensorHomLinearTheorem`. These are statement
targets: the file proves none of them. It does prove the small helper
results that are needed to write the statements down. These are the coefficient
modules on the carriers and the commutation facts that make them modules.

## Provenance and source scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passages read for this unit are:

- the conventions on printed p.6 / PDF p.12, where an A–B bimodule is a left
  A-module and right B-module whose two actions commute, with no coefficient
  structure in the definition;
- I.2.1 on printed p.14 / PDF p.20. There an A-module that is also a complex
  vector space becomes a unital module over the unitization Ã. Separately, a
  nondegenerate module over an idempotented complex algebra A gets complex scalars
  recovered from the A-action, `λ m = (λ e) · m` when `e · m = m`. Hom and tensor
  over A and over Ã agree for these recovered scalars (I.2.1.2);
- the Theorem, the Corollary and its proof, and the naturality remark of I.2.2 on
  printed pp.15–16 / PDF pp.21–22.

In the source, R and S are complex algebras. The Theorem asserts natural
isomorphisms (I.2.2.1)–(I.2.2.4) over R̃ and S̃, with the formula (I.2.2.2)
`ψ(x)(y) = φ(x ⊗ y)`. The sentence before it says that R-modules become unital
R̃-modules, which by I.2.1 concerns modules that are also complex vector spaces.
The Corollary asserts (I.2.2.5)–(I.2.2.7) for nondegenerate modules over
idempotented algebras, with Hom and tensor over R and S. In (I.2.2.5)–(I.2.2.6)
the inner Hom is replaced by its nondegenerate part `Hom_S(Y, Z)_R`. The
Corollary's modules are the modules of the p.6 conventions, so its bimodule Y is
a bare pair of commuting actions. The complex structures on its spaces are the
canonical ones recovered by I.2.1, for which (I.2.1.2) is stated. The printed proof of the Corollary deduces it from the
Theorem and (I.2.1.2). It notes that maps from a nondegenerate module land in the
nondegenerate part.

The Theorem is formalized with given coefficients, as described below. The
Corollary is formalized with the recovered coefficients and one added
compatibility hypothesis on Y. That hypothesis corrects the source: under the
printed bare-bimodule convention, the canonical maps of the Corollary are not
always linear for the recovered coefficients. See
[the source issue and the correction](#source-issue-and-correction-the-bimodule-y-in-the-corollary)
below.

The additive content of all seven formulas is already published:
`Langlands.Algebra.NonUnitalTensorHomAdjunctionTheorem` gives (I.2.2.1)–(I.2.2.3)
and the refined (I.2.2.5)–(I.2.2.6), and
`Langlands.Algebra.NonUnitalTensorAssociativityTheorem` gives (I.2.2.4) and
(I.2.2.7). Both work over arbitrary nonunital rings with the original actions.
This unit adds only the coefficient structure. It reuses the published carriers
(`TensorHom`, `CurriedHom`, `RefinedHom`, `LeftTensor`, `RightTensor`) and the
published canonical predicates (`Canonical`, `RefinedCanonical`) unchanged. Each
conclusion asserts a `k`-linear equivalence whose underlying additive
equivalence, `E.toAddEquiv` or `End.toAddEquiv`, satisfies the published
canonical clauses. The equivalence is therefore the canonical one, and the
statement adds only that it is `k`-linear.

The coefficient ring is an arbitrary commutative ring `k` rather than `ℂ`, and
the algebras are nonunital `k`-algebras, meaning `Module k R` with
`IsScalarTower k R R` and `SMulCommClass k R R`. Renard's setting is the
instance `k = ℂ`. Nothing in the statements or the intended proofs uses a
property of `ℂ`.

## Helper constructions (proved here)

- `pointwiseSMul` and `pointwiseModule`: on the published additive group
  `NonUnitalModuleHom A M N`, the pointwise coefficients `(c • f) m = c • f m`,
  for a given `Module k N` that commutes with the action of `A`. Its fields are
  proved pointwise. The Library's `NondegenerateModuleHomScalars.homModule` is the
  same construction for the scalars recovered on a nondegenerate N. The Library
  has no version for given scalars, which the unitized Theorem needs.
- `rightSource_smulCommClass` and `source_smulCommClass`: the pointwise
  coefficients commute with the published residual source actions
  `NonUnitalBimoduleHomActions.rightSourceAction` and `sourceAction`. Both sides
  act on different arguments of the map, so the proof is `rfl` after
  extensionality. This is what makes the pointwise coefficients on the curried Hom
  `Hom_R̃(X, Hom_S̃(Y, Z))` well defined.
- `unitizedActionsCommute`: for an A–B bimodule Y whose given coefficients are
  compatible with both actions, the unitized actions of `Unitization k A` and
  `Unitization k B` commute. The unitized actions are the published adapters
  `CompatibleUnitizationTensor.leftNonUnitalModule` and `rightNonUnitalModule`.
  The commutation is derived from `ActionsCommute A B Y` and the compatibility
  instances, not assumed.
- `unitizedLeft_smulCommClass` and `unitizedRight_smulCommClass`: the given
  coefficients commute with the unitized actions. These repackage the published
  `CompatibleUnitizationTensor.left_smulCommClass` and `right_smulCommClass` for
  the `NonUnitalModule` adapters.
- `residual_smulCommClass`: on `Y ⊗_B Z`, the published right-factor coefficients
  `NondegenerateTensorScalars.compatibleModule`, `c • (y ⊗ z) = y ⊗ (c • z)`,
  commute with the published residual left action
  `NonUnitalBimoduleTensor.leftModule`, `a • (y ⊗ z) = (a • y) ⊗ z`. The proof
  is the published tensor extensionality `NonUnitalModuleTensor.hom_ext`. It is
  what puts coefficients on the nested tensor `X ⊗_R̃ (Y ⊗_S̃ Z)`.

## The Theorem: (I.2.2.1)–(I.2.2.4) over the unitizations

The modules carry given coefficients (`Module k X` and so on) that are compatible
with the original actions through `IsScalarTower` and `SMulCommClass`. This is
how the formalization reads I.2.1's "A-modules that are also complex vector
spaces". The source does not spell out the compatibility. It is needed for the
unitized action `(a, c) · m = a · m + c m` to be associative. For the bimodule Y,
one coefficient structure compatible with both actions is needed for the two
unitized actions to commute, so that Y is an R̃–S̃ bimodule at all. The unitized
actions are installed as local instances, and the published additive carriers
are formed over `Unitization k R` and `Unitization k S`. This is how I.2.1 turns
R-modules into unital R̃-modules. The bimodule commutation over the unitizations
is `unitizedActionsCommute`.

- `UnitizedRight.ExistsLinearCanonical` (I.2.2.1)–(I.2.2.2): X is a right
  R-module, Y an R–S bimodule and Z a right S-module. `tensorHomModule` gives
  `Hom_S̃(X ⊗_R̃ Y, Z)` the pointwise given coefficients of Z. `curriedHomModule`
  gives `Hom_R̃(X, Hom_S̃(Y, Z))` pointwise coefficients through those of the
  inner Hom (`innerHomModule`). The target asserts a `k`-linear equivalence whose
  additive equivalence is the published `Right.Canonical`, so
  `ψ(x)(y) = φ(x ⊗ y)`.
- `UnitizedLeft.ExistsLinearCanonical` (I.2.2.3): X is a left R-module, Y an S–R
  bimodule and Z a left S-module. The coefficients are the same as above, and the
  published `Left.Canonical` is used.
- `UnitizedAssoc.ExistsLinearCanonical` (I.2.2.4): X is a right R-module, Y an
  R–S bimodule and Z a left S-module. `leftTensorModule` gives
  `(X ⊗_R̃ Y) ⊗_S̃ Z` the right-factor coefficients
  `c • (t ⊗ z) = t ⊗ (c • z)`. `rightTensorModule` gives `X ⊗_R̃ (Y ⊗_S̃ Z)` the
  right-factor coefficients through those of `Y ⊗_S̃ Z`, which are in turn those
  of Z. Both are the published `NondegenerateTensorScalars.compatibleModule`. The
  target asserts a `k`-linear equivalence satisfying the published associativity
  `Canonical`.

`UnitizedTensorHomLinearTheorem` is the conjunction of the three targets,
quantified over all such data. It assumes no idempotentedness, nondegeneracy or
unit law.

Informally, and not stated in Lean, these are the natural coefficient structures
of the source. Over R̃ the scalar `c` acts through `(c, 0) ∈ R̃`. So Hom over R̃
and S̃ consists of `k`-linear maps, and tensors over R̃ already balance the
scalars: `(c • x) ⊗ y = x ⊗ (c • y)`. It therefore does not matter which factor
carries the coefficients of a tensor. The statements fix the right factor
because that is the published Library construction.

## The Corollary: (I.2.2.5)–(I.2.2.7) for nondegenerate modules

The modules here are the bare original modules without given coefficients. The
coefficients are the published scalars of I.2.1 recovered from the action on a
nondegenerate module (`NondegenerateScalars.module`):

- `NondegenerateRight.tensorHomModule` and `NondegenerateLeft.tensorHomModule`:
  the published `NondegenerateModuleHomScalars.homModule`, pointwise in the
  scalars recovered on the nondegenerate Z.
- `NondegenerateRight.refinedHomModule` and `NondegenerateLeft.refinedHomModule`:
  the published `homModule` on `Hom_R(X, Hom_S(Y, Z)_R)`, pointwise in the
  scalars recovered by R on the published nondegenerate part `Hom_S(Y, Z)_R`.
  Its nondegeneracy is the published `nondegeneratePart_isNondegenerate`. This
  is the literal reading of (I.2.2.5)–(I.2.2.6): `Hom_S(Y, Z)_R` is a
  nondegenerate R-module and so carries the I.2.1 scalars.
- `NondegenerateAssoc.leftTensorModule` and `rightTensorModule`: the published
  `NondegenerateTensorScalars.module`, with scalars recovered on the right
  factor. On `(X ⊗_R Y) ⊗_S Z` these are the scalars recovered on Z. On
  `X ⊗_R (Y ⊗_S Z)` they are recovered by R on `Y ⊗_S Z`, which is nondegenerate
  by the published `NondegenerateTensorFunctor.isNondegenerate`.

`NondegenerateRight.ExistsLinearRefinedCanonical` and its `Left` analogue
assert an additive E and a `k`-linear `End` satisfying the published
`RefinedCanonical E End.toAddEquiv`. So End is the canonical refined equivalence
and agrees with E after the inclusion of the nondegenerate part.
`NondegenerateAssoc.ExistsLinearCanonical` asserts a `k`-linear equivalence
satisfying the published associativity `Canonical`.

### Source issue and correction: the bimodule Y in the Corollary

**The literal reading fails.** By the p.6 convention, the Corollary's bimodule Y
is a pair of commuting actions with no coefficient structure. I.2.1 recovers two
coefficient structures on Y, one from each action when Y is nondegenerate for it.
Nothing in the printed hypotheses makes them agree. Then the canonical maps of the
Corollary need not be linear for the recovered coefficients. Here is a
counterexample to (I.2.2.5). Take
`R = S = X = Z = ℂ` with the ordinary actions, and let `Y = ℂ` with the ordinary
left action and the right action `y · s = y s̄`. Both actions on Y are unital,
hence nondegenerate, and they commute, so every printed hypothesis of the
Corollary holds. Then `Hom_S(Y, Z)` consists of the maps
`h_λ : t ↦ λ t̄`, `Hom_S(X ⊗_R Y, Z)` of the maps `x ⊗ y ↦ μ x̄ ȳ`, and the
canonical map sends φ to ψ with `ψ(x) = h_{φ(1 ⊗ 1) x̄}`. Multiplying φ by `c`
multiplies every `ψ(x)` by `c` as a function. The I.2.1 scalar `c` of
`Hom_S(Y, Z)_R` is recovered from the R-action `(h · r)(y) = h(r y)`, and it sends
`h_λ` to `h_{λ c̄}`, so it multiplies the function by `c̄`. Hence
`E(c φ) = c̄ · E(φ)`, and E is not linear (take `c = i` and `φ ≠ 0`). Both sides
are one-dimensional, so some linear isomorphism exists. What fails is the
linearity of the canonical map (I.2.2.2). The associativity (I.2.2.7) fails in
the same way. The canonical map sends `(x ⊗ y) ⊗ c z` to
`x ⊗ (y ⊗ c z) = x ⊗ ((c̄ y) ⊗ z)`, because `y ⊗ c z = (y · c) ⊗ z` in
`Y ⊗_S Z`. The R-recovered scalar `c` on `Y ⊗_S Z` instead gives
`x ⊗ ((c y) ⊗ z)`, and `Y ⊗_S Z ≅ ℂ` by `y ⊗ z ↦ ȳ z` is nonzero. The mirror example, with a conjugate left S-action,
does the same for (I.2.2.6). The S-recovered scalars on this Y are
`c ·_S y = c̄ y`, while the R-recovered ones are `c y`.

**Why the printed proof does not settle it.** The proof deduces the Corollary
from the Theorem and (I.2.1.2). To apply the Theorem, Y must be an R̃–S̃
bimodule. As explained above, that needs one coefficient structure on Y that is
compatible with both actions. (I.2.1.2) compares Hom and tensor over one
idempotented algebra and over its unitization, for the scalars recovered from
that algebra on a fixed module. It does not identify the two structures that
two commuting actions recover on the same bimodule. The proof therefore uses a
common coefficient structure on Y that the printed hypotheses do not supply. The
published audit
[duality-coefficient-conventions](../../notes/renard/duality-coefficient-conventions.md)
records the same point for I.4.2, with a similar conjugate example.

**The correction adopted.** Each closed Corollary clause adds the published
compatibility predicate, without introducing a new one:

- for (I.2.2.5) and (I.2.2.7),
  `NonUnitalBimoduleHomScalars.RightSourceCompatible k hS hSY`: for the scalars
  that S recovers on Y, `IsScalarTower k R Y`;
- for (I.2.2.6), `NonUnitalBimoduleHomScalars.SourceCompatible k hS hSY`: for the
  scalars that S recovers on Y, `IsScalarTower k Rᵐᵒᵖ Y`.

This is the common-coefficient reading of the Corollary. It is an added
hypothesis and does not follow from the printed hypotheses: the example above
satisfies those and violates it. It does hold whenever Y has one coefficient
structure compatible with both actions and is S-nondegenerate. Then the
S-recovered scalars are that structure, which is compatible with the R-action.
Informally, and not stated in Lean: when Y is also R-nondegenerate, the predicate
is equivalent to the agreement of the R-recovered and S-recovered scalars on Y.
Indeed, if `e · y = y` then `(c e) · y = c ·_S (e · y) = c ·_S y`. Conversely,
agreement and (I.2.1.1) for R give `(c r) · y = c ·_R (r · y) = c ·_S (r · y)`.

**Coverage.** These statements give the coefficient linearity of
(I.2.2.5)–(I.2.2.7) under the common-coefficient reading. The literal
recovered-coefficient assertion for bare bimodules is false by the example above
and is not formalized. The additive isomorphisms for bare bimodules remain the
published `NonUnitalTensorHomAdjunctionTheorem` and
`NonUnitalTensorAssociativityTheorem`.

### Hypotheses of the closed Corollary

Each clause has the Library's minimal style. It keeps a hypothesis only where it
is needed to state the target or for the target to hold. Apart from the
compatibility predicate, which is the correction above, every hypothesis follows
from the printed ones (idempotented algebras and nondegenerate modules).

- (I.2.2.5) and (I.2.2.6): idempotented R and S, nondegenerate X (needed for the
  refined equivalence, as in the published `RefinedExistenceTheorem`),
  S-nondegenerate Y (needed to state the compatibility), the compatibility, and
  nondegenerate Z (needed for the coefficients on the Hom groups).
  R-nondegeneracy of Y is not assumed.
- (I.2.2.7): idempotented R and S, R-nondegenerate Y (needed for the coefficients
  on `X ⊗_R (Y ⊗_S Z)`), S-nondegenerate Y, `RightSourceCompatible`, and
  nondegenerate Z. Nondegeneracy of X is not assumed, since neither coefficient
  module involves X.

## Naturality

The source's naturality in X, Y and Z is not restated here. The published
additive naturality statements quantify over all canonical additive witnesses:
`NonUnitalTensorHomAdjunction.Right.NaturalityTheorem` and
`RefinedNaturalityTheorem`, their `Left` analogues, and the third conjunct
(`Naturality`) of `NonUnitalTensorAssociativityTheorem`. They are
universe-polymorphic in the rings. They therefore apply to `E.toAddEquiv` and
`End.toAddEquiv` for every witness of the present targets, including over
`Unitization k R` and `Unitization k S` for the unitized Theorem.

## Intended proof route and outstanding obligations

The additive equivalences come from the published proved theorems. For the
unitized clauses they are applied to the unitized rings and actions. For the
Corollary they are the published refined and associativity equivalences.
Linearity is then checked on elements.

- Hom clauses: `E (c • φ) x y = c • φ (x ⊗ y) = (c • E φ) x y` by the pointwise
  definitions. In the Corollary the right-hand side uses the R-recovered scalars
  on `Hom_S(Y, Z)_R`. For h in the part fixed by an idempotent e, the
  compatibility and S-linearity of h give
  `h ((c e) · y) = h (c · (e · y)) = c · h (e · y) = c · h y`. The published
  `NonUnitalBimoduleHomScalarsParts.rightSourcePartRecoveredModule_eq` and
  `sourcePartRecoveredModule_eq` already identify, under the same compatibility
  predicates, the recovered scalars on these parts with the pointwise ones.
- Associativity clauses: both sides are additive, so it suffices to compare them
  on pure tensors (published tensor extensionality). There
  `(x ⊗ y) ⊗ c • z ↦ x ⊗ (y ⊗ c • z)`. In the Corollary, take idempotents e
  with `e · y = y` and f with `y · f = y`. Then
  `c • (y ⊗ z) = ((c e) · y) ⊗ z = (y · (c f)) ⊗ z = y ⊗ ((c f) · z) = y ⊗ c • z`.
  The steps use the compatibility and the balancing of the tensor over S. The
  last step uses an idempotent f' with `f' · z = z`, so that `c • z = (c f') · z`,
  and `y ⊗ (c f') · z = (y · f) ⊗ (c f') · z = y ⊗ (c f f') · z = y ⊗ (c f) · z`.

Only the helper constructions above are proved in this unit. The seven
coefficient-linearity conclusions and the two closed propositions are open
targets for a separate exact-target proof task.
