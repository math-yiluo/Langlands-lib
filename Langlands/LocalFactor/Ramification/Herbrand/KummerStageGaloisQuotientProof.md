# Galois truncation quotients at finite Kummer stages

Module `Langlands.LocalFactor.Ramification.Herbrand.KummerStageGaloisQuotientProof`. The theorem

```lean
theorem Langlands.Ramification.Kummer.kummerStageGaloisQuotient :
    KummerStageGaloisQuotientStatement.{u}
```

proves `KummerStageGaloisQuotientStatement` (module `TruncationQuotientStatement`) in an
arbitrary universe `u`. Unfolded, the statement is

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
    IsKummerRootSystem F ϖ πs →
    ∀ (n : ℕ) (x : ℝ), -1 ≤ x → x ≤ kummerBreak F →
      GaloisTruncationIsoAt F (kummerStage F πs n) x
```

In words: let `F` be a `p`-adic field, `ϖ` a uniformizer and `πs` a compatible system of its
`p^n`-th roots (`IsKummerRootSystem`), and let `K_n` be the field of `kummerStage F πs n`, that
is `F(πs n)`. For every `n` and every `x` with `-1 ≤ x ≤ b`, where
`b = kummerBreak F = p e_F/(p - 1)`, the inclusion of `K_n` induces a topological isomorphism
`G_{K_n}/G_{K_n}^x ≃ G_F/G_F^x` of the quotients of the absolute Galois groups by their upper
ramification groups, compatible with `intermediateGaloisMap` and identifying the images of the
upper groups at every index `y` with `-1 ≤ y ≤ x` (`GaloisTruncationIsoAt`).

## Proof as implemented

Given `-1 ≤ x ≤ b`, transitivity of the order gives `-1 ≤ b`.

1. `kummerTowerUpperSup` (module `KummerTowerUpperSupProof`) proves
   `KummerTowerUpperSupStatement.{u}`. Applied at the index `b` it gives that the supremum of
   the fixing subgroup of `K_n` and the absolute upper group `G_F^b` is the whole absolute
   Galois group of `F`: `G_F^b` acts transitively on the embeddings of `K_n`.
2. This is the hypothesis of `truncationGaloisQuotient` (module `TruncationGaloisQuotientProof`),
   which proves `TruncationGaloisQuotientStatement.{u}` with transitivity index `b`. Applying it
   at `x` gives `GaloisTruncationIsoAt F (kummerStage F πs n) x`.

The two theorems apply to the endpoints and to stage zero as well. The Weil-group analogue is
`kummerStageWeilQuotient` (module `KummerStageWeilQuotientProof`), proved by the same
composition with `truncationWeilQuotient`.

## Declarations

- `kummerStageGaloisQuotient : KummerStageGaloisQuotientStatement.{u}` (theorem).

## Sources

- J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Ann. Sci. École Norm. Sup. (4) 16 (1983), registered as
  `wintenberger-1983-field-of-norms` (PDF page = printed page − 57). 1.1.2, printed p. 61 (PDF
  page 4): for a Galois extension with group `G` and `H = Gal(L/K')`, `(G/H)^u = G^u H/H` and
  `H^u = H ∩ G^{φ_{K'/K}(u)}`, the comparison of upper groups behind the truncation theorem.
  1.3.1, printed p. 64 (PDF page 7): `L/K` is elementary of level `i` if `G_K^i G_L = G_K` and
  `G_K^{i+ε} G_L = G_L` for `ε > 0`; the first condition is the transitivity hypothesis used
  here at the index `b`.
- J.-P. Serre, *Local Fields*, GTM 67 (1979), registered as `serre-1979-local-fields` (PDF page
  = printed page + 7). Chapter IV, §3, Lemma 5 (Herbrand's theorem) and Remarks 1–2, printed
  p. 75 (PDF page 82): the upper filtration of an infinite Galois extension, its left
  continuity, and the Herbrand function `φ_{E/K}` of a subextension.
