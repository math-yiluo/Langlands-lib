# NYLL M353.029: preservation of the linear term under monomial addition

This module proves the published proposition
`Langlands.NYLL.PortInternal.M353.d029Statement` as
`Langlands.NYLL.PortInternal.M353.d029`. It imports
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.LinearTermStatement`
and reuses its published definitions without alteration.

The implicit parameters, in order, are `{K : Type u} [Field K]`,
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}`,
`{sigma : Type w} [Fintype sigma]`,
`{H : MvPowerSeries sigma F.valuationSubring}`, and
`{L : sigma → F.valuationSubring}`. The universes `u`, `v`, and `w` are
independent. The explicit parameters are `(hH : HasLinearTerm H L)`,
`(d : sigma →₀ ℕ)`, `(hd : 2 ≤ d.degree)`, and
`(c : F.valuationSubring)`, in that order.
The conclusion is the exact target application `d029Statement hH d hd c`,
which unfolds to `HasLinearTerm (H + MvPowerSeries.monomial d c) L`.

Here `HasLinearTerm H L` means
`(2 : ℕ∞) ≤ (H - linearForm L).order`, where `linearForm L` is
the finite sum of the terms `L i * X i`. The coefficient `c` is unrestricted.
The theorem retains the source's chosen local-field parameters even though
the proof uses only the commutative ring structure of its valuation subring.

## Implemented proof

The initial `change` unfolds the statement target, and `rw [HasLinearTerm]`
expresses the conclusion as an order bound.

First, the proof shows that `MvPowerSeries.monomial d c` has order at least
two. By `MvPowerSeries.nat_le_order`, it suffices to show that every
coefficient indexed by `q` with `q.degree < 2` vanishes.
The proof converts the degree inequality from the extended natural numbers
to natural numbers using `exact_mod_cast`. If `q = d`, applying `degree`
to this equality contradicts `hd : 2 ≤ d.degree`; `omega` closes this
natural-number contradiction. Thus `q ≠ d`, and
`MvPowerSeries.coeff_monomial_ne` gives the required zero coefficient.
This argument also covers `c = 0`.

Next, `ring` proves
`H + monomial d c - linearForm L = (H - linearForm L) + monomial d c`.
The assumption `hH` and the monomial order bound imply that the minimum
of the two summands' orders is at least two.
`MvPowerSeries.min_order_le_add` bounds this minimum by the order of their
sum; transitivity supplies the desired conclusion.

This is the original coefficient-and-order proof. It needs no uniformizer,
Lubin–Tate series, recursive intertwiner, approximation bundle, or assumption
that the variable type is nonempty.

## Source, adaptations, and attribution

The source is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
lines 503–528](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean#L503-L528),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original theorem is the source-private
`LubinTate.SameUniformizer.hasLinearTerm_add_monomial` (unit M353.029);
its section parameters occur at lines 29–38.
The source file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
It was read directly from
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content SHA-256
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content SHA-256
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The project errata search found no applicable NYLL entry.
No patch10 edit applies to this module or is used in this proof.

Worker 294 prepared the exact proof draft on 14 November 2026 in Task 6116,
draft revision 1, content key
`08c6286fa3235960fbb4168abe003544c479fc9a43b95bd4a46f34e39433ca00`.
Worker 343 reused that draft, compared it with the pinned source and the
published target, expanded this proof/source/attribution explanation, and
prepared the candidate and declaration checks. Worker 294 is a coauthor
of this contribution.

The source-private name becomes the public port implementation name
`Langlands.NYLL.PortInternal.M353.d029`; references to `HasLinearTerm`,
`linearForm`, and `LocalField` resolve to the published namespaced
definitions. The two broad source imports, `DegreeStabilization` and
`RecursiveCorrection`, are replaced by the single focused statement import,
which supplies the required definitions and Mathlib order lemmas.
The theorem's conclusion is written as the published target application,
with an initial `change` to recover the source conclusion; the remaining
proof body is unchanged. The unused source section variable `pi` is absent
from the effective theorem signature. Other source declarations and the
unused `noncomputable section` are omitted; a theorem docstring and
modification notice are added. No new instance or mathematical assumption
is introduced.

The original copyright, Apache-2.0 release, and authorship header are
retained verbatim. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
