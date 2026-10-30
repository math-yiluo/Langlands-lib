# The canonical compatible stable image for additive nonunital actions

Authors: Worker 709 and Worker 926. This pair defines two targets and
proves neither.
It uses the published canonical integer conversion of the original
additive nonunital action and its additive self-intertwiner.

## Provenance and scope

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Printed body page equals PDF page minus 6.

The final C.II proposition and proof, printed 279 / PDF 285, motivate
the stable-image conclusion. C.II's stability definition is on printed
276 / PDF 282. The actual endomorphism localization is the construction
in A.III.1, example 5 and its following lemma/corollary, printed 252–253 /
PDF 258–259. The conventions on printed 5–6 / PDF 11–12 and the Hom
distinction in I.2.1, printed 14 / PDF 20, with PDF 21 for context,
permit original additive nonunital actions and distinguish additive
intertwiners from complex-linear ones. Worker 709 directly read those
passages for the parent branch, most recently the complete PDF 285
passage on 30 October 2026. Worker 926 independently reread PDF 285,
282, 258–259, 11–12 and 20–21 on 30 October 2026, after confirming the
SHA256 above.

The registered older-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
has been read on PDF 18–19, independently by Worker 926 on 30 October
2026 after confirming its SHA256. It does not correct this final proposition
or settle the nonunital finiteness conventions and does not supersede
the 2026 original. The dedicated project and pinned Library source
errata file was absent at the preceding source audit.

These are internal derived, finiteness-free refinements. The
integer-linear normalization and uniqueness predicate are not
attributed as stated to Renard. The targets assume explicit stability
of a positive power and conclude its canonical compatible stable-image
identification. They do not assert eventual stability or interpret the
source's finite-type or Noetherian assumptions. Those comparisons and
the full source-facing final C.II proposition remain open.

## Original data and actual constructions

The acting ring `A : Type uA` has only `NonUnitalRing A`; it may be
noncommutative. The carrier `V : Type uV` has an additive commutative
group and its original `NonUnitalModule A V`. The original map
`f : NonUnitalModuleHom A V V` is additive and commutes with that
action. The two universes are independent and occur in order `uA uV`.
There is no complex vector-space structure, assumed scalar
compatibility, assumed map linearity, unit law, nondegeneracy,
nontriviality, dimension or finiteness hypothesis. Zero actions and
zero carriers are allowed.

Set `ρ = NonUnitalModule.toIntLinearEndHom (A := A) (V := V)` and
`a = f.toAddMonoidHom.toIntLinearMap`. Both use canonical integer
scalars of the given additive groups. In particular these scalars
are independent of the original ambient action even for `A = ℤ`
acting by zero. The published `f.toIntLinearIntertwiner` has exactly
this `a` as underlying linear map. Additivity gives integer linearity;
it is not an additional premise.

Use the existing actual `Localized a`, `iota a` and `localizedEnd a`.
The private generic abbrev `actualLocalizedScalarModule` selects the
existing scalar module of this generic localization before
specializing at integers. Installing it locally before `σ` and the
canonical-map equations retains exactly that module argument; it
constructs no new carrier, module action or localization. The actual
localized action is
`σ = localizedAction a ρ (fun b v => f.map_smul b v)`.

Install locally the existing source action
`CompatibleUnitization.module ρ` of `U = Unitization ℤ A`. Define

```text
powers m =
  CompatibleUnitization.toLinearIntertwiner
    ((CompatibleUnitization.ofLinearIntertwiner
        f.toIntLinearIntertwiner)^m)
K = (powers n).ker
I = (powers n).range.
```

The exponent is taken in the actual endomorphism ring for that
source U-module and converted back to an integer-linear intertwiner
of `ρ` with itself. Thus `K` and `I` are the existing compatible
submodules, rather than arbitrary chosen carriers or supplied
stability certificates. Their underlying integer submodules are
the kernel and image of the actual power. A future proof establishes
that the underlying map of `powers m` is exactly `a^m`.
The unitized module is selected by `letI`, with no new global instance.
The targets need no target U-module instance: `σ` and the restricted
action `I.restrictAction` already express the action equation.

## The two propositions

`AdditiveStablePowerImageAt f n` has no stability or finiteness premise.
It asserts `IsCompl K I` in the compatible-submodule lattice and a
unique integer-linear equivalence
`e : Localized a ≃ₗ[ℤ] I.toSubmodule` satisfying all three conditions:

1. `∀ b z, e (σ b z) = I.restrictAction b (e z)`.
2. `I.toSubmodule.subtype.comp (e.toLinearMap.comp (localizedEnd a)) =
   a.comp (I.toSubmodule.subtype.comp e.toLinearMap)`.
3. `e.symm.toLinearMap = (iota a).comp I.toSubmodule.subtype`.

The first is compatibility with the original A-action through its
automatic integer conversion. The second intertwines the actual
localized operator with `a`, as an equation of maps into the
original V. The third fixes the inverse to the restriction of the
actual canonical map. Every equation is inside the `ExistsUnique`
predicate, so uniqueness includes this normalization and is not a
claim that all unnormalized equivariant equivalences are equal.

The closed `AdditiveStablePowerImageStatement.{uA,uV}` binds all the
original data and `n : ℕ`, then assumes exactly

```text
0 < n
ker(a^n) = ker((a^n)^2)
range(a^n) = range((a^n)^2).
```

It concludes `AdditiveStablePowerImageAt f n`. The same positive
exponent occurs throughout. All displayed stability equalities are
of canonical integer submodules. No surjectivity, decomposition,
localization equivalence or desired-conclusion certificate is a
premise. Both public declarations are transparent Prop-valued
definitions.

## Derivation rationale and neighboring work

For a future proof, specialize the published ordinary
`EndomorphismLocalization.stablePowerImageStatement` at ℤ. It gives
ordinary complementarity and an equivalence whose inverse is the
actual canonical map restricted to `range(a^n)`. Prove coherence of
the actual unitized powers with `a^n`; forgetting the compatible
lattice then identifies `K` and `I` with the ordinary kernel and
image. Transport complementarity back through the injective
forgetful complete-lattice map.

The canonical map restricted to `I` is then bijective. Define `e`
as its inverse. The actual `localizedAction_iota` equation proves
action compatibility by the inverse's injectivity.
`iota_intertwines` and invariance of `range(a^n)` under `a` give the
operator equation. Equality of inverse linear maps gives uniqueness
from the third equation alone. This is a proposed proof route,
not an implemented proof or an extra premise.

The public complex-compatible stable-image pair
`Langlands.Algebra.RenardCompatibleStableImageStatements` and its
proof require complex-linear actions and maps. The public ordinary
stable-image target works over arbitrary commutative rings,
including ℤ, but has no original-action equation. This pair supplies
the distinct bridge from arbitrary original additive data. It
changes neither pair nor their independently owned branches.
The additive unitized Noetherian targets concern how to obtain
eventual stability; they are a separate statement unit and are not
imported here. These two targets have no Noetherian hypothesis.


## Development checks

Worker 709 compiled the canonical pair with the closed target inspected:
zero errors and warnings, `statement_returns_prop: true`, independent
`uA uV`, and only `propext`, `Classical.choice` and `Quot.sound`.
A separate inspection overlay checked the complete unapplied types and
readable bodies of both definitions, the parameterized target's
Prop return, and the closed target at universe pairs `(0,1)` and `(1,0)`.
Explicit-argument output checked the canonical integer modules, the
actual source unitized module used by powers, the compatible K/I,
and the actual localized scalar module in the equivalence type.
The private generic alias creates no global instance.

A private induction also checked that the converted unitized power has
exactly `f.toAddMonoidHom.toIntLinearMap ^ m` as underlying integer-linear
map for every m. These are declaration, scalar and power-coherence
checks, not proofs of either target or independent semantic acceptance.
The inspection overlay and its diagnostics are excluded from this pair.

Worker 926 recompiled the unchanged Lean file on 30 October 2026 and
inspected both declarations. There were zero errors and warnings. Each
returns a Prop, has universe parameters `uA uV`, and uses only `propext`,
`Classical.choice` and `Quot.sound`. A separate private overlay printed
both complete types and bodies, including all explicit arguments. It
confirmed the closed target at universe pairs `(0,1)` and `(1,0)`. In
the type of `e`, Lean gives `Localized a` the module selected by
`actualLocalizedScalarModule`. It gives the carrier of `I.toSubmodule`
the canonical integer module of that submodule's additive group. The
overlay also checked, by `rfl` at reducible-and-instances
transparency, that this module equals the submodule's own restricted
integer module.
