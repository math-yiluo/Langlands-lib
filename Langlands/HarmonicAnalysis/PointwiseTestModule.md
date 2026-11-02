# Smooth multipliers on original nondegenerate pointwise test modules

This module constructs the smooth-function action in Renard II.2.5 on an
original nondegenerate module over the pointwise test algebra. Its namespace is
`Langlands.HarmonicAnalysis.PointwiseTestModule`. Write
\(A=\texttt{PointwiseTestAlgebra.Carrier X}\) and
\(S=\texttt{LocallyConstant X ℂ}\). The input consists of the supplied topology on
`X`, the unchanged additive group `M`, its specified
`μM : NonUnitalModule A M`, and `hM : IsNondegenerate A M` for that action.
There is no supplied complex or smooth-function module on `M`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The governing lemma is II.2.5, printed p.39 / PDF45. II.2.4 and the test-algebra
example are on printed p.38 / PDF44; the surrounding sheaf/module theorem is on
printed p.40 / PDF46. These three PDF pages were read. The source's t.d.
convention was checked on printed p.30 / PDF36: Hausdorff with a compact-open
neighborhood basis.

The supplementary *Corrections et compléments* for the 2010 edition,
registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF2–3, explains the relative compact-indicator nondegeneracy convention. That
clarification is already present in the governing 2026 passage. The relative
predicate below implements that convention.

## Actual action and intrinsic laws

`PointwiseTestAlgebra` supplies the actual compactly supported locally constant
tests, their faithful inclusion `inclusion : A →ₙₐ[ℂ] S`, their smooth
multiplication action `ambientModule`, compact-clopen characteristic functions,
and the proved `isIdempotented : IsIdempotented A`. Multiplication here is
pointwise multiplication.

`testScalarTower` and `testSMulCommClass` supply the two compatibility
instances needed to apply `NondegenerateScalars` with `k = S` and this
particular `A`. Their proofs evaluate the actual functions and use
associativity and commutativity in `ℂ`. These instances concern smooth
scalars acting on tests and tests multiplying tests.

`module hM : Module S M` is the specialization

```lean
NondegenerateScalars.module (LocallyConstant X ℂ)
  PointwiseTestAlgebra.isIdempotented hM
```

It is a named structure for local installation, so choosing it does not require
an unrelated global scalar instance. It retains `μM` and the given additive
group. All unital module laws are fields of this actual structure. They come
from the published intrinsic construction, whose raw formula is
\[
 f\mathbin{\bullet}m=(f\mathbin{\bullet}e)\mathbin{\bullet}_{\mu_M}m
\]
for a chosen original idempotent fixer \(e\) of \(m\). Its proof of independence
uses a common upper idempotent. Its additive law uses one idempotent fixing
both summands, and its multiplicative law uses compatibility of smooth
multiplication on tests with test multiplication. Thus the construction uses
the original action throughout.

## Characteristic fixers and the source formula

`exists_characteristic_fixer hM m` proves that there are an actual set
`U : Set X`, `hU : IsClopen U` and `hc : IsCompact U` with
`characteristic hU hc • m = m` for the original action `μM`.
To obtain them, the proof takes an original idempotent fixer `e` from `hM m`
and sets \(U=\operatorname{support}(e)\). This support is compact and clopen
by the published test-function results. The support indicator satisfies
\(\chi_U e=e\), by `characteristic_mul_eq_self_iff`. Associativity of the
original action then gives \(\chi_U m=m\). Characteristic fixers are
conclusions of nondegeneracy.

For every such original fixer, `smul_eq hM f m hU hc hm` gives
\[
 f\mathbin{\bullet}m
   =(f\mathbin{\bullet}\chi_U)\mathbin{\bullet}_{\mu_M}m.
\]
The expression \(f\mathbin{\bullet}\chi_U\) is the actual compact test obtained
by multiplying the two functions. `fixer_independent` equates these right-hand
sides for any two compact-clopen characteristics fixing \(m\). Both results
specialize the published general fixing-idempotent formulas.

`inclusion_smul hM a m` proves that an included test acts exactly by its
specified original action:
\[
 \operatorname{inclusion}(a)\mathbin{\bullet}m
   =a\mathbin{\bullet}_{\mu_M}m.
\]
The proof evaluates the smooth formula using an original fixer, then uses
`PointwiseTestAlgebra.inclusion_smul` to identify the test product and the
original action law to remove the fixer.

`IsRelativelyNondegenerate originalAction σM : Prop` takes both a specified
original `NonUnitalModule A M` and a specified `Module S M`. Its condition is
that every vector is fixed under `σM` by
`inclusion (characteristic hU hc)` for some actual compact-clopen `U`.
The original action is an explicit parameter; the predicate itself imposes
no compatibility premise on that action and `σM`.
`isRelativelyNondegenerate hM` proves the condition for
`originalAction = μM` and `σM = module hM`, by combining the characteristic
fixer with `inclusion_smul`. `smul_eq_of_inclusion_fixes` also exposes the
formula when the fixing hypothesis is phrased using this ambient inclusion.

This predicate is relative to compact indicators. Generic nondegeneracy over
the unital ring `S` is a different condition: its global unit fixes every
vector of every unital `S`-module.

`smul_action` and `action_smul` give, with the chosen smooth action explicit,
\[
 f\mathbin{\bullet}(a\mathbin{\bullet}_{\mu_M}m)
  =(f\mathbin{\bullet}a)\mathbin{\bullet}_{\mu_M}m,\qquad
 a\mathbin{\bullet}_{\mu_M}(f\mathbin{\bullet}m)
  =(f\mathbin{\bullet}a)\mathbin{\bullet}_{\mu_M}m.
\]
The named `isScalarTower` and `smulCommClass` adapters follow from these
identities through the published general construction. All refer to the
actual pointwise smooth action on tests and the retained original action on
`M`.

## Exact comparison with complex scalars

`const_smul` compares the two specified structures on the unchanged carrier:

```lean
(letI := module hM; LocallyConstant.const X c • m) =
  (letI := NondegenerateScalars.module ℂ
    PointwiseTestAlgebra.isIdempotented hM; c • m)
```

The proof unfolds their raw scalar formulas using the same original chosen
fixer. `PointwiseTestAlgebra.const_smul` identifies multiplication of that
test by the constant function with its existing complex scalar
multiplication.

`constantRestriction hM : Module ℂ M` is actual restriction of `module hM`
along `LocallyConstant.constRingHom`, using `Module.compHom`.
`constantRestriction_eq` proves equality with the exact module
`NondegenerateScalars.module ℂ PointwiseTestAlgebra.isIdempotented hM`.
It applies `Module.ext'` to the preceding scalar equality. This comparison
assumes no prior complex structure on `M`.

## Original intertwiners and chosen structures

Given original nondegenerate actions on `M` and `N`,
`toLinearMap hM hN f` is an actual smooth-linear map from an original
`f : NonUnitalModuleHom A M N`. The complete constructor interface is:

```lean
∀ {X : Type uX} [TopologicalSpace X]
  {M : Type uM} [AddCommGroup M]
  [μM : NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]
  {N : Type uN} [AddCommGroup N]
  [μN : NonUnitalModule (PointwiseTestAlgebra.Carrier X) N]
  (hM : IsNondegenerate (PointwiseTestAlgebra.Carrier X) M)
  (hN : IsNondegenerate (PointwiseTestAlgebra.Carrier X) N)
  (f : NonUnitalModuleHom (PointwiseTestAlgebra.Carrier X) M N),
  letI := module hM
  letI := module hN
  M →ₗ[LocallyConstant X ℂ] N
```

The independently quantified original actions are parameters of `hM`, `hN`
and `f`, and each chosen smooth module is explicit in the result. The
elaborated interface retains these structures when specialized to equal
carrier types.

The implementation specializes `NondegenerateScalars.toLinearMap`.
Its linearity argument uses an original idempotent fixing the input vector;
the original intertwiner sends that vector to one fixed by the same
idempotent. Applying the two scalar formulas and the original intertwining
identity proves smooth linearity.
`toLinearMap_apply` records pointwise agreement, and
`toLinearMap_toAddMonoidHom` preserves the entire original additive map.
`toLinearMap_id` and `toLinearMap_comp` preserve identities and composition;
their proofs are definitional equalities. Composition has a separately
specified third original action `μP` on `P : Type uP` and uses
`module hM`, `module hN` and `module hP` explicitly. The four universes
`uX`, `uM`, `uN` and `uP` are independent.

## Topological scope and construction boundary

The intrinsic construction works for every supplied topology. It assumes no
separation, local compactness, countability, finite dimension, or
nonemptiness. All characteristic sets are required to be compact and clopen.
The support construction and formulas preserve empty sets, empty spaces and
zero modules. For example, on an empty space the test algebra is zero, so
original nondegeneracy itself forces each vector to be zero; no extra
nonemptiness assumption is introduced.

For the source's Hausdorff t.d. spaces, compact open sets are closed and
therefore clopen. The published
`PointwiseTestAlgebra.characteristicOfCompactOpen` supplies their indicators
with the same pointwise values. This is the source specialization of the
arbitrary-topology compact-clopen construction. The compact-open
neighborhood basis is part of the source's setting and is unnecessary for
this intrinsic construction.

The characteristic-fixer derivation, concrete compatibility adapters,
restriction equality and interface wrappers are derived content implementing
the cited source construction through published `NondegenerateScalars`.
This module supplies no new uniqueness theorem, restriction/extension
equivalence, scalar sheaf, module-to-sheaf construction, stalk comparison or
sheaf/module equivalence. Those remain separate statement and proof
obligations.
