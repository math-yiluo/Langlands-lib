# Original-action additive tensor-Hom equivalences: statements

This file states two additive tensor-Hom equivalences, whole-map naturality in
all three variables, and refinements through the actual nondegenerate part of
Hom. The namespace is `Langlands.Algebra.NonUnitalTensorHomAdjunction`, with
independent `Right` and `Left` families. The combined closed proposition is
`Langlands.Algebra.NonUnitalTensorHomAdjunctionTheorem`. These are statement
interfaces, not proofs of the main equivalences or naturality. Helpers implement
the actual evaluation pairings, elementary balancing, packaging of the published
maps and the elementary landing-in-the-part argument.

## Provenance and source scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Read passages are the original module and idempotent conventions, printed
pp.5–7 / PDF pp.11–13; the tensor and unitization comparison I.2.1, printed
p.14 / PDF p.20; and the full theorem, corollary, proof and subsequent naturality
remark in I.2.2, printed pp.15–16 / PDF pp.21–22.

The source theorem I.2.2.1–I.2.2.3 concerns complex algebras, their unitizations
and complex-linear Hom and tensor constructions. The source corollary
I.2.2.5–I.2.2.6 assumes idempotented complex algebras and nondegenerate modules;
its Hom term is the nondegenerate part for the indicated residual action. The
proof on printed p.16 identifies maps into that part with ambient maps because
images of nondegenerate modules are nondegenerate. The subsequent remark
specifies naturality in X, Y and Z.

The statements here are internal additive generalizations. They use arbitrary
associative nonunital rings and the specified original additive groups and
actions, without choosing complex coefficients or a unitization. The core
allows degenerate and zero actions and needs no unit law, idempotentedness,
nondegeneracy, commutativity, nontriviality or dimension assumption. The refined
existence statement needs only idempotented R and nondegenerate X. It imposes
no idempotentedness on S and no nondegeneracy on Y, Z or the whole Hom. This
weaker hypothesis list is an intrinsic strengthening justified by the direct
idempotent argument; it is not a quotation of the source's complex corollary.

The earlier-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was consulted at PDF pp.1–2 and pp.18–19. The correction on PDF p.1 concerns the
later induction adjunction; the Hom naturality correction on PDF p.18 uses
postcomposition covariantly and precomposition contravariantly, as here. Those
pages do not replace the governing 2026 formulation. No additional registered
errata note for the governing source was present in the supplied notes. Renard
refers to bibliography [34], pp.97–98, for his theorem. This development does
not claim to have read that reference: the intended proof route is the direct
original quotient-lift argument described below.

## Actual carriers and action sides

All original Hom spaces are `NonUnitalModuleHom` with their published pointwise
additive groups and original composition. All tensors are the published
`NonUnitalModuleTensor.Tensor`, its inherited additive group, `tmul`, `map`
and universal additive `lift`. No replacement tensor, Hom, residual action or
abstract universal-property object is supplied. `ActionsCommute` and
`NonUnitalBimoduleHom` retain the original bimodule actions. Local installation
of a named residual action fixes its precise instance in each abbreviation and
map; it does not change an original ring, group or module structure.

In `Right`, X is a right R-module, Y is an R–S bimodule with commuting actions,
and Z is a right S-module. A right action means a left action of the opposite
ring. `TensorHom` is the original right S-linear Hom from `Tensor R X Y` to Z,
using exactly `NonUnitalBimoduleTensor.rightModule X hY` on the tensor.
`CurriedHom` is the original right R-linear Hom from X into
`NonUnitalModuleHom Sᵐᵒᵖ Y Z`, using exactly
`NonUnitalBimoduleHomActions.rightSourceAction hY` on that inner Hom. Its action
is `(op r • h) y = h (r • y)`.

In `Left`, X is a left R-module, Y is an S–R bimodule with commuting actions,
and Z is a left S-module. `TensorHom` is the original left S-linear Hom from
`Tensor R Y X` to Z, with `NonUnitalBimoduleTensor.leftModule hY X`.
`CurriedHom` is the original left R-linear Hom from X into
`NonUnitalModuleHom S Y Z`, with exactly
`NonUnitalBimoduleHomActions.sourceAction hY`. Its action is
`(r • h) y = h (op r • y)`. This family preserves the supplied left action on X
and right action on Y directly; it introduces no double-opposite action.

The ring universes uR and uS, and the six carrier universes uX, uY, uZ, uX',
uY', uZ', are independent. Each per-triple existence target binds just its own
three independent carrier universes; naturality allows all six simultaneously.

## Canonical equivalences and inverse lifts

For each handed family, `Canonical E` specifies the forward evaluation formula,
the entire inverse additive map as the published lift, the inverse evaluation
on pure tensors, and both complete inverse identities. On the right,
`(E φ x) y = φ (tmul R X Y x y)` and the actual pairing is
`evaluationPairing ψ : X →+ Y →+ Z`, with value `ψ x y`. On the left,
`(E φ x) y = φ (tmul R Y X y x)` and the actual pairing is
`evaluationPairing ψ : Y →+ X →+ Z`, again with value `ψ x y`.

`evaluationPairing_balanced` proves balancing from ψ's original R-linearity
and the specified residual source action. It is not a supplied certificate.
The whole underlying additive map of `E.symm ψ` is explicitly equal to
`NonUnitalModuleTensor.lift R` of that actual pairing and its implemented
balancing proof. `InverseIdentities E` exposes
`E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id _` and
`E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id _`.

`ExistsCanonical` concludes existence of E with these clauses. The closed
`ExistenceTheorem` quantifies over every original set of ring, group and action
data and concludes `ExistsCanonical`. Neither an equivalence, curry/uncurry
map, bijectivity nor a conclusion certificate is an existence premise.

## Whole-map naturality

Maps f : X' → X and g : Y' → Y act contravariantly; k : Z → Z' acts
covariantly. They are original one-sided intertwiners and the original bimodule
intertwiner respectively. `tensorHomMap` is the actual additive map
`P φ = k.comp (φ.comp tensorMap)`. Its tensor map is exactly the published
`rightMap hY' hY f g` on the right and `leftMap hY' hY g f` on the left. Their
underlying additive maps are respectively
`NonUnitalModuleTensor.map R f g.toLeftHom` and
`NonUnitalModuleTensor.map R g.toRightHom f`.

`curriedHomMap` uses the published `mapAddHom` and the one-sided Hom natural map
`rightSourceMap hY hY' g k` or `sourceMap hY hY' g k`. Its value at x' is
`k.comp ((ψ (f x')).comp g.toRightHom)` on the right and
`k.comp ((ψ (f x')).comp g.toLeftHom)` on the left. There is no unrelated
residual action on Z. `Naturality E E'` asserts both equalities of complete
additive maps:

```text
E'.toAddMonoidHom.comp P = Q.comp E.toAddMonoidHom,
E'.symm.toAddMonoidHom.comp Q = P.comp E.symm.toAddMonoidHom.
```

`NaturalityTheorem` is closed over the original data, all three maps and any
witnesses E and E' satisfying the canonical clauses. The separate closed
existence targets assert unconditional existence at every triple.

## Actual nondegenerate-part refinement

`HomPart hR` is exactly `nondegeneratePart hR.op H` on the right and
`nondegeneratePart hR H` on the left, with its original inherited group, action
and subtype inclusion. `RefinedHom` is the original Hom from X into this actual
part. `map_mem_part` proves that every original ψ from nondegenerate X lands in
it: choose an idempotent e fixing x, and use ψ's original linearity to see that
e also fixes ψ x. No nondegeneracy of the whole H is assumed or concluded.

`inclusionMap`, denoted J, is exactly published original-Hom postcomposition
with `(HomPart hR).subtype`. `RefinedCanonical E End` includes the ambient
canonical clauses, refined pure-tensor evaluation after the subtype inclusion,
and both comparisons of whole additive maps:

```text
J.comp End.toAddMonoidHom = E.toAddMonoidHom,
End.symm.toAddMonoidHom = E.symm.toAddMonoidHom.comp J.
```

`ExistsRefinedCanonical` concludes existence of both E and End with those
comparisons. `RefinedExistenceTheorem` is closed and assumes only hR and
nondegeneracy of the original action on X beyond the core data.

`refinedHomMap` uses exactly `NonUnitalModuleHom.restrictNondegeneratePart`
of the published inner Hom natural map, with hR.op on the right and hR on the
left, followed by the original-Hom precomposition in f. `RefinedNaturality`
uses this Qnd and the same P in both complete additive-map equations.
`RefinedNaturalityTheorem` quantifies over compatible ambient/refined witnesses
and assumes nondegeneracy of X and X'.

## Intended proof route and outstanding obligations

The intended direct proof curries by evaluation on pure tensors, obtains
original linearity from the named residual actions, and uncurries through the
existing quotient lift of the implemented balanced pairing. Original-Hom
extensionality and tensor extensionality prove both inverses and both naturality
equations. The implemented idempotent landing argument then permits restricting
the codomain to the actual part; original inclusion and restriction give the
refined comparisons and naturality. The main conclusions of this route remain
unproved in this statement unit.

Additive equivalences alone do not supply Renard's complex-linear equivalences.
Coefficient and unitization comparisons remain explicit parent obligations,
as do associativity I.2.2.4/I.2.2.7, the exactness proposition, actual categorical
adjunctions and the F, pseudo-F, I and P constructions. This file does not claim
complete coverage of I.2.2. A separate exact-target proof successor must consume
the statement declarations after their independent acceptance and publication.
