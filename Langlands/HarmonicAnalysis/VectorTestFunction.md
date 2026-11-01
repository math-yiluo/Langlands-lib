# Vector-valued test functions and canonical tensor maps

This construction implements the function spaces and maps in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.1.2, printed p.32 / PDF p.38, equations (II.1.2.3) and
(II.1.2.4). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The namespace is `Langlands.HarmonicAnalysis.VectorTestFunction`. Its space
universe `uX` and value universe `uV` are independent.

## Actual spaces and scalar agreement

Renard's \(C^\infty(X,V)\) is the existing Mathlib `LocallyConstant X V`,
with its pointwise complex vector space structure from
`Mathlib.Topology.LocallyConstant.Algebra`. This uses the given topology on
`X`. The arbitrary complex vector space `V` has `AddCommGroup V` and
`Module ℂ V`; no topology, norm, dimension or choice of basis is required.

`compactlySupportedSubmodule X V` consists of those actual locally
constant maps whose underlying function has `HasCompactSupport`.
Its carrier `Space X V` is \(D(X,V)\), with the inherited complex vector
space structure. Support means the closure, in the supplied topology on
`X`, of the set of points with nonzero value. Compact support is stable
under addition and constant scalar multiplication. The membership,
local constancy, compact support, extensionality and pointwise operations
are exposed by the corresponding lemmas.

`inclusion` is the actual submodule inclusion into `LocallyConstant X V`.
The linear equivalence `scalarEquiv` identifies the original published
`SchwartzBruhat X` with `Space X ℂ`. Both directions leave the underlying
function unchanged. They only package its local constancy and compact
support into the two different existing representations.
`scalarInclusion` composes this equivalence with `inclusion`, giving the
original scalar test functions as locally constant complex functions.
The evaluation laws in both directions and for both inclusions are proved.

## Canonical tensor maps

All tensor products are algebraic tensor products over \(\mathbb C\).
`smoothBilinear` is the actual bilinear map sending \((f,v)\) to
the locally constant function \(x\mapsto f(x)v\). Local constancy follows
by composing `f` with the function \(z\mapsto zv\), which needs no target
topology. Pointwise vector space laws prove bilinearity.

`smoothTensorMap` is its lift by the tensor universal property:

\[
 C^\infty(X,\mathbb C)\otimes_{\mathbb C}V
 \longrightarrow C^\infty(X,V).
\]

`compactBilinear` applies the same formula to the original scalar
`SchwartzBruhat X`. The zero value is preserved by \(z\mapsto zv\).
The Mathlib `HasCompactSupport.comp_left` lemma therefore proves compact
support of the result. `compactTensorMap` is the corresponding lift:

\[
 D(X)\otimes_{\mathbb C}V\longrightarrow D(X,V).
\]

The pure-tensor identities, including their evaluation at every `x`,
are proved for both maps. `inclusion_compactTensorMap` proves for every
tensor that forgetting compact support after the compact map agrees with
the smooth map after applying `scalarInclusion` on the first tensor
factor and the identity on `V`. Its proof uses the pure-tensor and addition
cases of tensor induction.

## Scope and remaining source assertions

The constructions require only a topology on `X`. Thus they include all
the source's Hausdorff locally compact totally disconnected spaces,
without adding separation, compactness, countability or nonemptiness
assumptions. Empty spaces and the zero value space remain available.
The scalar equivalence and inclusion square are derived representation
compatibilities; their role is to connect Renard's formulas to the
existing Library scalar carrier.

The source additionally calls both canonical maps injections and proves
the compact map surjective, hence an isomorphism. Those are separate
statement and proof obligations. This construction supplies the actual
spaces and linear maps and their compatibility laws; it does not assert
those further properties.
