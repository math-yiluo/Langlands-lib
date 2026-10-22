# Admissibility of actual normalized block parabolic induction

Authors: Worker 162 and Worker 172.

`Langlands.Parabolic.normalizedInductionAdmissibility` proves the published
`NormalizedInductionAdmissibilityClause` in
[`NormalizedInductionStatement`](NormalizedInductionStatement.md). Its parameters
are an arbitrary prime `p`, `F : PadicField.{uF} p`, compatible
`T : F.TopologicalData`, any rank `n`, any `B : GeneralLinear.BlockShape n`,
and any complex module `V : Type uV`. The field and representation universes are
independent, and rank zero is included.

For every admissible representation `sigma` of the actual product Levi
`B.Levi F.Carrier`, the theorem proves admissibility of

```
Induction.smoothInduced (B.parabolic F.Carrier)
  (twist (T.parabolicHalfModulus B)
    (sigma.comp (B.leviProjection F.Carrier)))
```

This is the target's right-translation action with its actual positive
half-modulus and diagonal-block projection, under `T.topology`.
Admissibility includes smoothness and finite-dimensional fixed spaces for
every open subgroup. There is no finite-dimensionality or irreducibility
assumption on the inducing module or representation.

## Implemented proof

The proof installs `T.topology` and `T.generalLinearTopologicalGroup n`, then
introduces `sigma` and its admissibility.

1. The reverse implication of
   [`leviInflationAdmissibility`](LeviInflationAdmissibilityProof.md) gives
   admissibility of `sigma.comp (B.leviProjection F.Carrier)`. This applies the
   published equivalence for the actual continuous, open, surjective Levi
   projection.
2. The reverse implication of
   [`isAdmissible_twist_iff`](../Twist/AdmissibilityProof.md) preserves
   admissibility after twisting by `T.parabolicHalfModulus B`.
   Its required open-kernel hypothesis is the published
   `T.isOpen_ker_parabolicHalfModulus B`, rather than an additional assumption.
3. [`parabolicQuotientCompact`](QuotientCompactProof.md) supplies compactness
   of the actual quotient with points `P g`, where `P = B.parabolic F.Carrier`.
   Apply
   [`Induction.compactQuotientClause_holds`](../Induction/CompactQuotientProof.md)
   to the twisted inflated representation, and select its second conclusion:
   admissibility of smooth induction.

The geometric and fixed-vector arguments are imported proofs. The quotient
module obtains a compact integral group in every rank and proves that its image
in the quotient is all of that quotient using the published Iwasawa theorem.
The generic induction module derives a finite double-coset cover for each
open subgroup and uses injective evaluation into finitely many fixed-vector
spaces of the inducing representation. This module composes those results;
it introduces no quotient-compactness or finite-cover premise. All ranks are
covered by the imported theorem families, with no separate positive-rank
restriction in the assembly.

## Sources and provenance

The proof is an internal composition of the published results named above.
The following registered originals were read directly for the target's
mathematical conventions and source correspondence:

- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter III, revision April 29, 2019, section 1, p.1: positive-half normalized
  induction, right translation, and admissibility from compactness of `P \ G`.
  Section 2, p.2 identifies admissible Levi representations with admissible
  parabolic representations trivial on the radical.
  Source `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977), sections 1.8–1.9, printed pp.444–445 (PDF pp.5–6),
  define normalized induction and state compact-quotient admissibility.
  Sections 2.2–2.3, printed p.446 (PDF p.7), identify the ordered block Levi
  subgroups of `GL_n` and specialize admissibility to parabolic induction.
  Source `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field* (1976), Lemma 3.6(b), p.30, gives
  compactness modulo the parabolic through Iwasawa decomposition. Definition
  3.12, p.32, inflates from the Levi before induction; Proposition 3.13(d),
  p.33, states preservation of admissibility. This source uses unnormalized
  induction, so the positive-half convention here comes from Casselman and
  Bernstein–Zelevinsky (1977) and is implemented by the open-kernel twist step.
  Source `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

The formal result specializes to standard block parabolics over the Library's
finite extensions of `Q_p`. The rank-zero case is included by the published
constructions and prerequisite proofs. The normalization is the explicit block
half-character already fixed by the target; no identification with Haar scaling
is assumed here. The contribution proves only the admissibility clause, leaving
the other clauses of `NormalizedInductionStatement` as separate obligations.
