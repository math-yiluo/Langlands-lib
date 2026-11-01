# Simultaneous original and completed linear actions

Authors: Worker 1187 and Worker 1172. Worker 1172 supplied the direct reuse
of the published additive action and the individual fixing-idempotent and
composition formulas. The companion interface and degenerate-case checks adapt
probes supplied by Worker 6. All three workers are credited in the candidate.
All declarations in this module are in
`Langlands.Algebra.NondegenerateModuleLinearActions`.

## Original source and internal generalization

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, content SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained PDF is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The relevant original passages were read directly:

- Conventions and I.1.1–I.1.3, printed pp.5–9 / PDF11–15: associative
  nonunital algebra actions on abelian groups, idempotented algebras,
  nondegenerate modules, compatible right families and their extended action.
- I.1.8, printed pp.13–14 / PDF19–20: the simultaneous linear action
  (I.1.8.2) and its extension to the completed algebra.
- I.2.1, printed p.14 / PDF20: the canonical complex scalars on the
  original nondegenerate module and the compatibility identities (I.2.1.1).

No dedicated errata note for this source was found in the project at the time
of the source reading. The 2026 version governs this implementation.

Renard uses complex coefficients and a family indexed by simple-module
isomorphism classes in I.1.8. Here the commutative coefficient semiring and an
arbitrary indexed family are internal generalizations. They package the same
original and extended action formulas without any simple-module classification
or separation hypothesis. The exact complex specializations are
`complexOriginal` and `complexCompleted`.

The actual canonical scalar module and compatible-family action are reused by
importing `Langlands.Algebra.NondegenerateScalars` and
`Langlands.Algebra.IdempotentedRingRightLimitAction`. The latter already imports
the actual compatible-family ring. The published additive bundling
`IdempotentedRingRightLimit.actionAddHom` of the extended action is reused from
`Langlands.Algebra.NondegenerateModuleForgetful`. The present module does not
redefine those constructions or change their carriers.

## Inputs and named structures

The coefficient, algebra, index and carrier universes are independent:
`k : Type uK`, `A : Type uA`, `I : Type uI`, `M : I → Type uM`.
The assumptions are

```lean
[CommSemiring k] [NonUnitalRing A] [Module k A]
[IsScalarTower k A A] [SMulCommClass k A A]
[∀ i, AddCommGroup (M i)] [∀ i, NonUnitalModule A (M i)]
hA : IsIdempotented A
hM : ∀ i, IsNondegenerate A (M i)
```

The additive groups and algebra actions are the specified original structures.
No scalar module on a carrier, prior linear realization, compatibility
certificate, inverse map, faithfulness, nontriviality or dimension assumption
is supplied. The two algebra scalar hypotheses express bilinearity of its
multiplication over `k`. The original algebra may be noncommutative and
nonunital.

For one original carrier, `End k hA hM` abbreviates the actual `Module.End k M`
formed with `NondegenerateScalars.module k hA hM`. It has carrier universe `uM`.
`endRing` names its usual composition ring, and `endModule` names its pointwise
scalar module for that precise ring's additive structure. These are named
structures, installed locally; they introduce no global instances.

For a family, `EndProduct k hA hM` is the actual dependent function type
`∀ i, End k hA (hM i)`, in universe `max uI uM`. `productRing` uses the
coordinate `endRing` structures and `Pi.ring`; `productModule` uses the
coordinate `endModule` structures and `Pi.module`. Thus both the types of
linear endomorphisms and the ring/module structures on the product select the
canonical scalars on the original groups, even when other structures are
available to instance search.

## Intrinsic linearity and individual completed map

`act_smul` proves scalar preservation of the actual extended action. Fix
`x : IdempotentedRingRightLimit A`, `c : k` and `m : M`. Choose an actual
idempotent `e` with `e • m = m`, using `hM m`. The published identities
`NondegenerateScalars.action_smul` and `NondegenerateScalars.smul_action`
give

```text
e • (c • m) = (c • e) • m = c • (e • m) = c • m.
```

Consequently the same `e` fixes both vectors. Apply the published
`IdempotentedRingRightLimitAction.act_eq` at `e` to both completed actions.
The desired equality becomes

```text
x.val e • (c • m) = (c • x.val e) • m = c • (x.val e • m),
```

again by the two canonical scalar compatibility identities. This proof does
not require a completed operator to commute with every original `A`-operator.

`linearEnd k hA hM x` extends the published additive endomorphism
`IdempotentedRingRightLimit.actionAddHom hA hM x` of the original group with
the proved `act_smul`, giving an actual member of `End k hA hM`.
`linearEnd_coe`, `linearEnd_function`, `linearEnd_toAddMonoidHom` and
`linearEnd_apply` retain the entire function, the entire curried action, its
entire underlying additive homomorphism and the evaluation formula.
`linearEnd_apply_eq` evaluates it as `x.val e • m` at every actual idempotent
fixing `m`.

`completedHom k hA hM` is a unital ring homomorphism from exactly
`IdempotentedRingRightLimit.ring hA` to `endRing k hA hM`. Its zero, unit,
addition and multiplication proofs use linear-map extensionality and the
published `zero_act`, `unit_act`, `add_act` and `product_act` laws. In
particular multiplication is composition with the right factor applied first.
There is no supplied ring-map law or linear realization among the inputs.

`completedHom_coe`, `completedHom_function`,
`completedHom_additive_function` and `completedHom_apply` identify its whole
linear-endomorphism function, whole vector-action function, whole
additive-endomorphism function (exactly `actionAddHom hA hM`) and individual
applications. `completedHom_apply_eq` evaluates it as `x.val e • m` at every
fixing idempotent, and `completedHom_mul_apply` states its right-factor-first
composition order. The completed
ring's canonical map retains the original action:

- `completedHom_canonical` identifies the entire linear endomorphism at
  each canonical element with `NondegenerateScalars.toLinearEndHom`.
- `completedHom_comp_canonical` identifies the entire bundled nonunital ring
  homomorphisms after composition with
  `IdempotentedRingRightLimit.canonicalRingHom hA`.
- `completedHom_canonical_function`, `completedHom_canonical_apply` and
  `completedHom_canonical_additive_function` retain the whole function,
  the original application `a • m`, and the whole original additive action
  `NonUnitalModule.toEndHom`.

The pointwise canonical equality follows by linear-map extensionality from
`IdempotentedRingRightLimitAction.canonical_act`. The whole-map and
whole-function equalities use homomorphism extensionality and function
extensionality. These are intrinsic consequences and packaging of the
published action construction.

## Simultaneous maps, projections and product laws

`original k hA hM` is an actual nonunital `k`-algebra homomorphism
`A →ₙₐ[k] EndProduct k hA hM`, for the named product ring and module.
Its coordinate at `i` is exactly
`NondegenerateScalars.toLinearEndHom k hA (hM i)`. Its zero, addition,
multiplication and scalar laws are those of these actual coordinate maps,
lifted by function extensionality.

`completed k hA hM` is an actual unital ring homomorphism from the named
compatible-family ring to that same named product ring. Its coordinate is
`completedHom k hA (hM i)`; all four ring-map laws follow coordinatewise.
`original_coe` and `completed_coe` identify the entire unapplied bundled-map
functions. The respective `coordinate`, `function`, `additive_function` and
`apply` lemmas retain coordinate maps, whole vector-action functions, whole
underlying additive-map functions and individual applications.
`completed_apply_eq` gives the formula at every fixing idempotent.

`projection k hA hM i` is actual evaluation at coordinate `i`, bundled as
a unital ring homomorphism to the named coordinate endomorphism ring.
`algebraProjection` is the same evaluation as a nonunital `k`-algebra
homomorphism for the named scalar modules. Their `coe` and `apply` lemmas
identify the whole functions and their applications;
`algebraProjection_toNonUnitalRingHom` identifies their entire underlying
nonunital ring homomorphisms.

`projection_original`, `projection_original_ring` and
`projection_completed` are equalities of entire bundled maps after coordinate
projection. `completed_comp_canonical` proves equality of the entire
completed map restricted along `canonicalRingHom` with the original map after
forgetting scalar preservation. The proof applies homomorphism
extensionality, then coordinatewise the individual canonical compatibility.
`completed_canonical_function` and `completed_canonical_apply` retain its
whole function and its original-action applications.

`product_mul_apply` states explicitly that `(f * g) i m = f i (g i m)`.
`original_mul_apply` and `completed_mul_apply` give the same order for the
original and completed maps, by original action associativity and the
published completed product-action law. `complexOriginal_apply` and
`complexCompleted_apply` preserve the actual original and completed actions
in the complex specializations.

## Scope and verification

The companion `NondegenerateModuleLinearActionsChecks` checks complete
unapplied constructors and canonical/projection identities at independent
universes, with explicit unequal universe assignments in both directions.
It also checks original structure selection and the exact named constructed
structures under competition, and zero objects and empty indexing types.
Its paired Markdown describes those checks and their provenance.

This module constructs the maps and their intrinsic laws. The source's
separation criterion, equivalence with original-map injectivity, injectivity
of the completed extension, construction of simple-module isomorphism-class
indices, Schur central characters and categorical-centre-to-functions
comparisons are outside this construction and remain separate successors.
Compilation is development evidence; independent semantic review and Library
publication are separate requirements.
