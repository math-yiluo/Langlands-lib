# Prescribed additive tensor smoothing and naturality

Worker 1205 proves the entire unchanged Library proposition
`Langlands.Algebra.NonUnitalTensorSmoothingStatements.TensorSmoothing.{uA,uN,uM,uN',uM'}`.
The exact-target theorem is
`Langlands.Algebra.NonUnitalTensorSmoothingProof.tensorSmoothing`; the module
imports `Langlands.Algebra.NonUnitalTensorSmoothingStatements`. All helper
names below are in `Langlands.Algebra.NonUnitalTensorSmoothingProof`.

## Source, hypotheses and provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.4.3, printed p.25 / one-based
PDF p.31. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1205 read this passage, the conventions at I.1.1–I.1.2, printed pp.5–7 /
PDF11–13, and I.2.1–I.2.2, printed pp.14–16 / PDF20–22. The registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2, was also read; the 2026 edition governs.

Renard proves that the canonical inclusion from `N_A ⊗_A M` to `N ⊗_A M`
is an isomorphism using the reverse on generators `(n,m) ↦ (n·e) ⊗ m`, where
`e·m = m`. The imported construction supplies that actual balanced reverse
and its formula for every fixing idempotent. It also supplies the correction
to the source's displayed absorption-direction error in choice independence;
this proof uses the published formula and requires no further choice-independence
argument. The equivalence packaging and the joint naturality squares are
internal consequences of this additive comparison. The source does not
display the two squares.

Here `A : Type uA` is an associative nonunital ring with `hA : IsIdempotented A`.
The original right module `N : Type uN` has its specified additive group and
`NonUnitalModule Aᵐᵒᵖ N`. The original left module `M : Type uM` has its
specified additive group and `NonUnitalModule A M`, with a witness
`hM : IsNondegenerate A M`. Write `NA = nondegeneratePart hA.op N`.
Both `Tensor A NA M` and `Tensor A N M` are precisely the imported original
balancing quotients. Write `I = inclusion hA N M` and `P = reverse hA N hM`.

Only `M` is required to be nondegenerate. In particular `N` can be a nonzero
group with zero right action. No original scalar `Module`, unit law,
dimension, nontriviality or finiteness assumption is introduced. For naturality,
`N' : Type uN'` and `M' : Type uM'` have the corresponding original structures,
and only `M'` receives nondegeneracy. All five universes are independent.
The arbitrary-ring additive scope is an internal generalization of the source's
complex-algebra setting, already specified by the published target; the
complex-algebra case specializes this family. Zero rings and zero carriers
remain covered by the same proof without case distinctions.

## Implemented proof

`inverseIdentities` proves the equalities of entire additive maps
`P.comp I = id` and `I.comp P = id` with
`NonUnitalModuleTensor.hom_ext A`, reducing each to all pure tensors.
For each left vector `m`, choose `e` from `hM m`, so `e·m = m`.
The published `inclusion_tmul` and `reverse_tmul` evaluate each composite.
For the composite on the smaller tensor, the actual subtype element
`smoothing hA (n : N) e` is definitionally the inherited right action
`op e • n`. Balancing inside `Tensor A NA M` gives

```text
P(I(n ⊗ m)) = (n·e) ⊗ m = n ⊗ (e·m) = n ⊗ m.
```

This implemented route uses only a fixer of `m`, whereas the source chooses
a common fixer for both factors. For the other composite, smoothing has
original value `op e • n`; balancing in `Tensor A N M` gives the same chain.
Thus both equalities concern the prescribed entire maps on their actual
quotients.

`bijectivity` evaluates the two whole-map identities at arbitrary tensors,
obtains left inverse laws in each direction, and applies their injectivity
and surjectivity consequences. No inverse law is an input hypothesis.

`prescribedEquivalence` constructs an `AddEquiv` with forward function `I`
and inverse function `P`; its inverse laws are the identities just proved,
and its additivity is that of `I`. Both entire additive-map pins are
reflexivity equalities. Its forward generator formula is the imported
`inclusion_tmul`, and its inverse generator formula is exactly the imported
`reverse_tmul`, quantified over every `e : Idempotent A` fixing `m` and using
precisely `smoothing hA n e`.

For original intertwiners `f : NonUnitalModuleHom Aᵐᵒᵖ N N'` and
`g : NonUnitalModuleHom A M M'`, `naturality` proves both entire-map squares
using pure-tensor extensionality. The forward square is definitional on
pure tensors: `f.restrictNondegeneratePart hA.op` has underlying value
`f (n : N)`. For the reverse square, choose a fixer `e` of `m`. The equation
`g.map_smul` shows that `e` fixes `g m` too, so the same every-fixer formula
applies to both reverse maps. After `map_tmul`, the sole remaining equality
is the subtype equality

```text
f.restrictNondegeneratePart hA.op (smoothing hA n e)
  = smoothing hA (f n) e,
```

proved by `Subtype.ext (f.map_smul (op (e : A)) n)`. This establishes joint
naturality in both original factors, including degenerate right modules.

`equivalenceNaturality` chooses the prescribed equivalences at both pairs
and rewrites all four entire-map pins. The resulting forward and inverse
squares are exactly those proved by `naturality`. Each existential retains
its complete `EquivalenceData`, including every generator formula.
Finally `tensorSmoothing` introduces the universally quantified original
structures and intertwiners and assembles these five components into the
unchanged closed target.

## Checks and scope

The theorem type explicitly names the published closed proposition at
five independent universe variables. The two final complete closed-target
examples also specialize it to the unequal assignments `(0,1,2,3,4)` and
`(4,3,2,1,0)`, checking that no universe identification is needed.

This proof supplies the additive tensor-smoothing family. Scalar refinements,
actual dual-completion maps and comparisons, the Hom-chain, representability
and formula (I.4.3.1) remain separate obligations. None is assumed or proved
here.
