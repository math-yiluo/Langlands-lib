# Proof of tensor injectivity for ideals containing maximal-ideal powers

This module proves the published proposition
`Langlands.Algebra.FiniteColengthTensorInjectivityStatement.{u,v}`, imported by
Lean module name from `Langlands.Algebra.FiniteColengthTensorInjectivityStatement`.
It does not change that statement pair or anything it imports. The closing
theorem is `Langlands.Algebra.finiteColengthTensorInjectivity.{u,v}`. Its entire
type is `FiniteColengthTensorInjectivityStatement.{u, v}`, with two independent
universes and no further hypotheses or parameters.

Restated: let \(R\) be a commutative Noetherian local ring with maximal ideal
\(\mathfrak m\), and let \(M\) be any \(R\)-module such that
\(M\otimes_R\mathfrak m\to M\otimes_R R\) is injective. Then
\(M\otimes_R J\to M\otimes_R R\) is injective for every ideal \(J\) with
\(\mathfrak m^n\subseteq J\) for some \(n\). Both maps are
`LinearMap.lTensor M` of the ideal inclusion, so \(M\) is the left tensor
factor throughout.

## Helper results

The three helpers are in the namespace
`Langlands.Algebra.FiniteColengthTensorInjectivity`. They are stated for
`R : Type u` and `M : Type v`, with `CommRing R`, `AddCommGroup M` and
`Module R M`. The second and third also assume `IsLocalRing R`. None of them
assumes that \(R\) is Noetherian.

- `lTensor_top_subtype_injective` (line 17) proves that
  `LinearMap.lTensor M (⊤ : Ideal R).subtype` is injective. In other words,
  \(M\otimes_R R\to M\otimes_R R\), induced by the inclusion of the unit
  ideal, is injective. The local hypothesis is not needed here.
- `lTensor_inclusion_sup_span_injective` (line 34) is the one-step extension.
  It takes the hypothesis `hm`, that
  `LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype` is injective,
  an ideal `J`, an element `x ∉ J`, and the hypothesis
  `∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ J`. It proves that
  `LinearMap.lTensor M (Submodule.inclusion le_sup_left)` is injective, for
  the inclusion of `J` into `J ⊔ Ideal.span {x}`. Mathematically: if
  \(x\notin J\) and \(\mathfrak m x\subseteq J\), then
  \(M\otimes_R J\to M\otimes_R(J+Rx)\) is injective.
- `exists_not_mem_mul_mem_of_pow_le` (line 100) takes
  `IsLocalRing.maximalIdeal R ^ n ≤ J` and `J ≠ ⊤`. It produces `x ∉ J`
  with `a * x ∈ J` for every `a` in the maximal ideal.

## Implemented proof

`lTensor_top_subtype_injective`. The map
`LinearMap.lTensor M Submodule.topEquiv.symm` is a left inverse. After
`LinearMap.lTensor_comp_apply`, the composite of `topEquiv.symm` with the
subtype map is the identity by extensionality (`rfl`). `LinearMap.lTensor_id`
then gives the identity on \(M\otimes_R\top\).

`lTensor_inclusion_sup_span_injective`. Write \(J'=J+Rx\). The proof
constructs the \(R\)-linear maps
\[
f:\mathfrak m\to J\times R,\quad a\mapsto(ax,\,-a),
\qquad
g:J\times R\to J',\quad (j,r)\mapsto j+rx .
\]
In Lean, `f` is `f₁.prod (-m.subtype)`, where `f₁` restricts
`LinearMap.toSpanSingleton R R x` to \(\mathfrak m\) and corestricts it to
\(J\) using \(\mathfrak m x\subseteq J\). The map `g` is
`(Submodule.inclusion le_sup_left).coprod g₂`, where `g₂` corestricts
`toSpanSingleton R R x` to \(J'\).

- *Exactness at \(J\times R\)* (`Function.Exact f g`). Clearly
  \(g(f(a))=ax-ax=0\). Conversely, let \(j+rx=0\). If \(r\notin\mathfrak m\),
  then \(r\) is a unit (`IsLocalRing.notMem_maximalIdeal`), so
  \(x=-r^{-1}j\in J\). This contradicts \(x\notin J\). Hence
  \(r\in\mathfrak m\), and \((j,r)=f(-r)\) because \((-r)x=j\). This is the
  only use of the local hypothesis.
- *Surjectivity of \(g\)*. Every element of \(J'\) has the form \(y+ax\)
  with \(y\in J\) (`Submodule.mem_sup`, `Ideal.mem_span_singleton'`), and
  this equals \(g(y,a)\).

Mathlib's right exactness of the tensor product, `lTensor_exact M hexact
hsurj`, gives exactness of
\[
M\otimes_R\mathfrak m\xrightarrow{1\otimes f}M\otimes_R(J\times R)
\xrightarrow{1\otimes g}M\otimes_R J'.
\]
Let \(y\in M\otimes_R J\) map to zero in \(M\otimes_R J'\). Since
\(g\circ\iota_1\) is the inclusion \(J\to J'\) (`LinearMap.coprod_inl`),
\((1\otimes\iota_1)(y)\) lies in the kernel of \(1\otimes g\). So it equals
\((1\otimes f)(z)\) for some \(z\in M\otimes_R\mathfrak m\). Apply
\(1\otimes\mathrm{snd}\). Then \(\mathrm{snd}\circ f\) is minus the inclusion
of \(\mathfrak m\), and \(\mathrm{snd}\circ\iota_1=0\). Hence the inclusion of
\(\mathfrak m\) tensored with \(M\) sends \(z\) to zero, and `hm` gives
\(z=0\). Now apply \(1\otimes\mathrm{fst}\), using
\(\mathrm{fst}\circ\iota_1=\mathrm{id}\). It gives
\(y=(1\otimes(\mathrm{fst}\circ f))(z)=0\). The rewriting uses
`LinearMap.lTensor_comp_apply`, `snd_prod`, `snd_comp_inl`, `fst_comp_inl`,
`lTensor_neg`, `lTensor_zero` and `lTensor_id`.

`exists_not_mem_mul_mem_of_pow_le`. Induction on `n`. For `n = 0`, the
hypothesis says \(R=\mathfrak m^0\subseteq J\), contradicting `J ≠ ⊤`. For
`n = k + 1`, if \(\mathfrak m^k\subseteq J\) the induction hypothesis
applies. Otherwise choose \(x\in\mathfrak m^k\setminus J\). For
\(a\in\mathfrak m\), `Ideal.mul_mem_mul` and `pow_succ'` place \(ax\) in
\(\mathfrak m^{k+1}\subseteq J\).

`finiteColengthTensorInjectivity`. After the data, the hypothesis `hm`, the
ideal `J`, `n` and `hJ : 𝔪 ^ n ≤ J` are introduced, the proof uses
well-founded induction on `J` for the strict order `>` on `Ideal R`
(`WellFoundedGT.induction`). The induction also generalizes `hJ`. The
`WellFoundedGT (Ideal R)` instance comes from `IsNoetherianRing R`; this is
the only use of the Noetherian hypothesis. Hence the induction hypothesis
covers every strictly larger ideal containing \(\mathfrak m^n\).

- If `J = ⊤`, `lTensor_top_subtype_injective` concludes.
- Otherwise, `exists_not_mem_mul_mem_of_pow_le` gives \(x\notin J\) with
  \(\mathfrak m x\subseteq J\). Then \(J'=J+Rx\) strictly contains \(J\),
  because \(x\in J'\setminus J\), and \(\mathfrak m^n\subseteq J'\). The
  induction hypothesis makes \(M\otimes_R J'\to M\otimes_R R\) injective,
  and `lTensor_inclusion_sup_span_injective` makes
  \(M\otimes_R J\to M\otimes_R J'\) injective. The subtype map of \(J\)
  equals the subtype map of \(J'\) composed with the inclusion, by `rfl`.
  `LinearMap.lTensor_comp` and composition of injective maps finish.

All hypotheses of the statement are used: `IsNoetherianRing R` for the
well-founded induction, `IsLocalRing R` for the unit argument in the
one-step lemma (and to name \(\mathfrak m\)), `hJ` to produce the element
\(x\) at each step, and `hm` in the one-step lemma. No finiteness,
nontriviality or flatness of \(M\) is used. The proof uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Relation to the literature

The statement Markdown explains the target's provenance. It is the
finite-colength step in the proof of Stacks Project Lemma 10.99.7, tag
[00MK](https://stacks.math.columbia.edu/tag/00MK), obtained from Lemma
10.99.6, tag [00MJ](https://stacks.math.columbia.edu/tag/00MJ). The 00MK proof
identifies the kernel of \(J\otimes_R M\to M\) with
\(\mathrm{Tor}_1^R(M,R/J)\) (Remark 10.75.9). Then 00MJ shows that
\(\mathrm{Tor}_1^R(N,M)=0\) for every finite-length module \(N\), by
induction on the length of \(N\) and the long exact Tor sequence. The base
case \(N\cong\kappa\) is the hypothesis
\(\mathrm{Tor}_1^R(\kappa,M)=0\).

This Lean proof follows the same induction but avoids Tor completely.

- The hypothesis `hm`, injectivity of \(M\otimes_R\mathfrak m\to M\otimes_R R\),
  replaces \(\mathrm{Tor}_1^R(\kappa,M)=0\).
- The induction on the length of \(R/J\) becomes well-founded induction on
  ideals under reverse inclusion. In each step,
  \(\mathfrak m x\subseteq J\) and \(x\notin J\), so \((J+Rx)/J\cong\kappa\).
  This corresponds to splitting off a length-one submodule of \(R/J\).
- The long exact Tor sequence is replaced by the explicit right exact
  sequence \(\mathfrak m\to J\times R\to J+Rx\to 0\) and a diagram chase
  after tensoring with \(M\). Here \(J+Rx\) is the pushout of
  \(J\leftarrow\mathfrak m\to R\) along \(a\mapsto ax\) and the inclusion.

No formal comparison with categorical Tor, or with finite length, is made or
claimed. The source writes the ideal first, \(J\otimes_R M\), while the Lean
statement and proof use `LinearMap.lTensor M`, that is, \(M\otimes_R J\). The
two are related by tensor commutativity, which this proof does not need.

## Sources and attribution

The mathematics was read in registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`: file
`00MD.html`, Lemma 10.99.6, statement and proof; and file `00MK.html`,
Lemma 10.99.7, first paragraph of the proof. The statement pair records the
current-page source `stacks-flatness-00mk-00mj-current-2026-10-26`, content
SHA256 `867cdedaa7867ff53170db88408b2ad27481210df67727e5af2d3836ff0e5acb`.
The official 00MJ and 00MK pages were checked again on 27 October 2026. Their
statements and proofs were unchanged, and each had zero comments. No
Stacks-specific errata note is present in the project or Library notes.

Worker 844 wrote this proof independently. It uses only Mathlib, in the
pinned environment, and the published statement module. The task context
mentions the external lead `anthropic-flt-complete-lean-source-6e837e75`
(file `P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean`)
and the documentary audit `notes/reuse/anthropic-local-flatness-audit.md`.
No code from either was used or adapted, nothing from them is imported, and
the free-cover kernel-transport route described there is not used.
