# Prescribed additive tensor smoothing and naturality

This statement family specifies the inverse identities, prescribed additive
equivalence and naturality of the two published tensor-smoothing maps. It imports
`Langlands.Algebra.NonUnitalTensorSmoothing`. All seven declarations below are
Prop-valued definitions in
`Langlands.Algebra.NonUnitalTensorSmoothingStatements`. The named closed target
`TensorSmoothing` is stated, not proved.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The tensor-smoothing argument is in I.4.3, printed p.25 / one-based PDF p.31.
Its original nonunital and nondegenerate conventions are in I.1.1–I.1.2,
printed pp.5–7 / PDF pp.11–13, and the tensor conventions are in
I.2.1–I.2.2, printed pp.14–16 / PDF pp.20–22. These passages were read
for this statement family. The registered supplementary
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, was also checked. The 2026 edition governs.

The source asserts that the canonical inclusion
`N_A ⊗_A M → N ⊗_A M` is an isomorphism and constructs its inverse from
`(n,m) ↦ (n·e) ⊗ m`, where `e·m = m`. It verifies the two inverse identities
on generators, using a common fixer for the first composite. The whole-map
identities, bijectivity predicates, explicit additive-equivalence packaging
and its exact map pins here specify that assertion over the published
construction. The two tensor naturality squares and their prescribed-equivalence
versions are derived interfaces: the source does not display these squares.
Its subsequent natural Hom isomorphism and completion argument are separate
from this statement family.

The source's displayed choice-independence calculation has an absorption
direction error: its assumptions give `e h = e`, whereas its final step
would need `e h = h`. The imported construction already proves the intended
choice independence in the actual quotient by the valid chain
`(n·h) ⊗ m = (n·h) ⊗ (e·m) = ((n·h)·e) ⊗ m = (n·e) ⊗ m`,
using `h e = e`. This statement imports those maps and their proved
every-fixer formula; it does not use the invalid displayed step as a premise.

## Original hypotheses, carriers and maps

The ring `A : Type uA` carries its specified `NonUnitalRing A` and
`hA : IsIdempotented A`. The latter says that every finite set lies in a
single idempotent corner, equivalently that it has an idempotent two-sided
local unit.

The original right module is `N : Type uN` with its specified `AddCommGroup N`
and `NonUnitalModule Aᵐᵒᵖ N`. Thus `n·a` means `MulOpposite.op a • n`.
The original left module is `M : Type uM` with its specified `AddCommGroup M`
and `NonUnitalModule A M`. Only this left module receives a witness
`hM : IsNondegenerate A M`: every `m` is fixed by some actual idempotent of
`A`. Naturality uses an independently sized original right module
`N' : Type uN'` and left module `M' : Type uM'` with the same kinds of
specified group and action structures, and only a left witness `hM'`.

In the formulas below the abbreviations are explanatory notation:

```text
NA = nondegeneratePart hA.op N
T0 = NonUnitalModuleTensor.Tensor A NA M
T1 = NonUnitalModuleTensor.Tensor A N M
I  = NonUnitalTensorSmoothing.inclusion hA N M : T0 →+ T1
P  = NonUnitalTensorSmoothing.reverse hA N hM : T1 →+ T0.
```

Here `NA` is the published subtype of original vectors fixed by an
idempotent of the opposite ring, with its inherited original group and
action. The tensors are precisely the published quotients of the integer
tensor products by the original balancing relations. No tensor object or
tensor group structure is supplied as an extra parameter.

The entire inclusion `I` is exactly the published tensor `map` of the actual
subtype inclusion and the identity of `M`. The entire reverse `P` is the
published balanced lift of `reverseBiadditive hA N hM`. Its public
`reverse_tmul` formula uses `smoothing hA n e`, the actual element of `NA`
whose original value is `MulOpposite.op (e : A) • n`, for every idempotent
`e` fixing `m`. The statement does not expose the construction's chosen fixer.

There is no nondegeneracy, unit law, faithful-action condition, coefficient
module or scalar compatibility assumption on either original right module.
In particular a nonzero additive group with zero right action is allowed.
No complex `Module` on any original carrier is assumed or installed. The
five universes are independent, and there is no dimension, nontriviality or
finiteness condition. Zero rings and zero carriers are included under the same
original hypotheses.

The source uses an idempotented complex algebra. This statement generalizes
its additive assertion to an arbitrary associative nonunital ring: the
published maps, local fixing idempotents, balancing equations and inverse
and naturality formulations use only ring multiplication and the original
additive actions. This ring generalization is internal mathematical
packaging, not an assertion that the source states that generality.
The complex-algebra case specializes it by adding the source's complex
algebra structure on `A`; no complex structure on `N`, `M`, `N'` or `M'`
is needed to specialize these additive targets. Recovering complex scalars
and obtaining complex-linear refinements remain separate.

## Proposition components

`InverseIdentities hA N hM` states both equalities of entire additive maps:

```text
P.comp I = AddMonoidHom.id T0
I.comp P = AddMonoidHom.id T1.
```

`Bijectivity hA N hM` states `Function.Bijective I ∧ Function.Bijective P`.
Neither inverse identity nor bijectivity is an input hypothesis.

`EquivalenceData hA N hM E`, for `E : T0 ≃+ T1`, is the conjunction of
the two entire-map pins

```text
E.toAddMonoidHom = I
E.symm.toAddMonoidHom = P
```

and both pure-tensor formulas:

```text
E (tmul A NA M n m) = tmul A N M (n : N) m
E.symm (tmul A N M n m) =
  tmul A NA M (smoothing hA n e) m       whenever (e : A) • m = m.
```

The first formula quantifies over every `n : NA` and `m : M`; the second
over every `n : N`, `m : M` and fixing idempotent `e : Idempotent A`.
`PrescribedEquivalence hA N hM` concludes that such an `E` exists.
An equivalence satisfying inverse laws is therefore never assumed to obtain
the desired conclusion.

For the actual original intertwiners
`f : NonUnitalModuleHom Aᵐᵒᵖ N N'` and
`g : NonUnitalModuleHom A M M'`, write

```text
fA = f.restrictNondegeneratePart hA.op
F  = NonUnitalModuleTensor.map A f g
F0 = NonUnitalModuleTensor.map A fA g.
```

The restriction `fA` is the published map on the actual subtypes; its
original value at `n` is `f (n : N)`. Let `I'` and `P'` be the same
published inclusion and reverse at `N', M', hM'`.
`Naturality hA hM hM' f g` states the two entire-map squares

```text
F.comp I = I'.comp F0
F0.comp P = P'.comp F.
```

`EquivalenceNaturality hA hM hM' f g` concludes the existence of
`E : T0 ≃+ T1` and the corresponding `E'` at `N', M'`, each satisfying
its full `EquivalenceData`, together with the entire-map equalities

```text
F.comp E.toAddMonoidHom = E'.toAddMonoidHom.comp F0
F0.comp E.symm.toAddMonoidHom = E'.symm.toAddMonoidHom.comp F.
```

Both the equivalences and these squares are conclusions. Their full map
pins identify both functions with the prescribed comparison maps, so the
existentials cannot substitute unrelated equivalences. Joint naturality
in arbitrary `f` and `g` includes each separate factor naturality by taking
the other intertwiner to be its original identity.

`TensorSmoothing` is closed: it universally quantifies `A`, all its stated
structure and `hA`, then `N`, `M`, their original structures and `hM`.
For each such tuple it concludes `InverseIdentities`, `Bijectivity` and
`PrescribedEquivalence`. It then universally quantifies `N'`, `M'`, their
original structures, `hM'`, `f` and `g`, and concludes both `Naturality`
and `EquivalenceNaturality`. It retains the five independent universe
parameters `uA, uN, uM, uN', uM'` and is suitable as the exact target
of a later proof.

## Checks and remaining proof boundary

The paired `NonUnitalTensorSmoothingStatementsChecks` companion checks
the complete unapplied declaration interfaces and the full closed target
body at arbitrary independent universes and at the unequal assignments
`(0,1,2,3,4)` and `(4,3,2,1,0)`. It also checks specialization to zero
right actions, zero boundaries and the original complex-algebra context.
Its Markdown describes those checks in detail. These interface and
specialization checks do not prove `TensorSmoothing`.

This unit supplies no proof of the inverse identities, bijectivity,
prescribed equivalence or naturality targets. A proof of the exact
published closed proposition is a separate successor. Recovered scalar
wrappers and complex-linear refinements, completion/full-dual comparisons,
the source Hom-chain, its representability argument and formula (I.4.3.1)
remain separate obligations. There is no dependency on the residual
coefficient adapter.

Worker 1187 authored this principal statement pair. Worker 345 audited the
source and interfaces and authored the companion checks.
