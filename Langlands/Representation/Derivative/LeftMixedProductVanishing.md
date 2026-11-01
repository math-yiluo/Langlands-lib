# Vanishing of the high derivatives of left mixed products (conditional)

Author: Worker 1018.

This internal helper proves the vanishing half of BZ77 Corollary 4.14(a),
`Langlands.Derivative.LeftMixedProductDerivativeVanishing.{uF,uV} F T`,
with the `Φ⁻` clause of 4.13(b) explicit as an argument.
The entry theorem is

```lean
theorem Langlands.Derivative.LeftMixedProductVanishing.leftMixedProductDerivativeVanishing_of_leftPhiCompatibility
    (T : F.TopologicalData)
    (hPhi : MirabolicProductMinus.LeftPhiCompatibility.{uF, uV} F T) :
    LeftMixedProductDerivativeVanishing.{uF, uV} F T
```

for every prime `p`, `F : PadicField.{uF} p` and `T : F.TopologicalData`, with
independent universes `uF` and `uV`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The argument `hPhi` has the published proposition type
`MirabolicProductMinus.LeftPhiCompatibility`. The final entry module
[`LeftMixedProductDerivativeProof`](LeftMixedProductDerivativeProof.md)
discharges it with the independently accepted and published
`MirabolicProductMinus.leftPhiCompatibility T`. This helper alone is a
conditional theorem. It neither reproves that clause nor proves the
isomorphism half `LeftMixedProductDerivativeIso`.

## Source and correspondence

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations
of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, literature
ID `bernstein-zelevinsky-1977-induced-i`. Printed page numbers are one-based
PDF page numbers plus 439.

- §3.5 and footnote (2), printed p.452 (PDF p.13): the order-`i` derivative of
  a representation of `P_m` is `Ψ⁻` after `i-1` successive `Φ⁻` functors.
- Proposition 4.13(b), printed p.458 (PDF p.19): for `ρ` on `G_k` and `τ` on
  `P_m`, `Φ⁻(ρ × τ) ≅ ρ × Φ⁻(τ)`. The same page's boundary convention at
  `P_0` makes the right side zero at `m = 1`.
- Corollary 4.14(a), printed p.458 (PDF p.19): `(ρ × τ)^{(i)} ≅ ρ × τ^{(i)}`.
  By the same boundary convention, the right side is zero when `i > m`. The source
  derives 4.14(a) from 4.13(b).

Here `B` lives on `P_(r+1) = mirabolic r`, so `m = r + 1`, and the source
vanishing range `i > m` is the clause `r + 1 < i` of the published statement.
The proof below follows the source: it iterates 4.13(b) `r + 1` times, until
the mirabolic factor would reach `P_0`, which the published boundary
`MirabolicProductMinus.leftPhiBoundary` handles directly.

## Lean constructions used

All are published:

- `T.leftMixedProductFunctor k r` (from `Mirabolic.MixedProducts`): `(A, B)` on
  `GL_k × P_(r+1)` to `A × B` on `P_(k+r+1)`.
- `Mirabolic.phiMinus T ψ n` from `P_(n+2)` to `P_(n+1)`;
  `Mirabolic.psiMinus T n` from `P_(n+1)` to `GL_n`.
- `mirabolicDerivative T ψ n j = phiMinusIterate T ψ n j ⋙ psiMinus T n`
  (`Iteration`), from `P_(n+j+1)` to `GL_n`. `phiMinusIterate` applies the
  largest-rank `Φ⁻` first, so `mirabolicDerivative T ψ n (j+1)` is
  definitionally `phiMinus T ψ (n+j) ⋙ mirabolicDerivative T ψ n j`.
- `mirabolicDerivativeOfOrder T ψ N i hi` (`Homogeneity`) is definitionally
  `mirabolicRankCast T (mirabolic_rank_eq_of_order hi) ⋙
  mirabolicDerivative T ψ (N+1-i) (i-1)`.
- `mirabolicRankCast T h` is equality elimination of the identity functor.
- `MirabolicProductMinus.leftPhiProduct T ψ k r` is
  `leftMixedProductFunctor (k+1) r ⋙ mirabolicRankCast T (Nat.succ_add k r) ⋙
  phiMinus T ψ (k+r)`, and `leftPhiExpected T ψ k r` is
  `(𝟭 _).prod (phiMinus T ψ r) ⋙ leftMixedProductFunctor (k+1) r ⋙
  mirabolicRankCast T (Nat.succ_add k r)`, that is `A × Φ⁻B` for `B` on
  `P_(r+2)`. The hypothesis `hPhi` gives, for each
  `ψ`, `k`, `r`, a natural isomorphism
  `leftPhiProduct T ψ k (r+1) ≅ leftPhiExpected T ψ k r`.
- The published theorem `MirabolicProductMinus.leftPhiBoundary T`
  (`MirabolicProductMinusBoundary`, Worker 837) proves that
  `(leftPhiProduct T ψ k 0).obj X` has a subsingleton carrier for every `X`.
- `mirabolicRankCast_obj_subsingleton` and `mirabolicDerivative_obj_subsingleton`
  (`Homogeneity`): rank casts and derivatives preserve subsingleton carriers.

All mixed products here have carrier universe `max uF uV`, and the derivative
functors are applied at that universe.

## Proof

### Helpers

- `subsingleton_of_iso`: if `e : A ≅ B` in `SmoothRep` and the carrier of `B`
  is a subsingleton, so is the carrier of `A`, because `e.inv ∘ e.hom = id`
  makes `e.hom` injective.
- `phiMinus_obj_rankCast T ψ e h` for `e : a = b`, `h : a+1 = b+1`: on
  objects, `phiMinus T ψ b` after `mirabolicRankCast T h` equals
  `mirabolicRankCast T e` after `phiMinus T ψ a`. After `subst e` both sides
  agree by `rfl`.
- `mirabolicRankCast_obj_trans`: on objects, the cast along `h'` after the cast
  along `h` equals the cast along any proof of the composite equality (again
  `subst` and `rfl`).

### Core induction

`mirabolicDerivative_leftMixedProduct_subsingleton T hPhi ψ k` states: for all
`r`, `A` on `GL_(k+1)`, `B` on `P_(r+1)`, `n`, `j`, every
`h : k+1+r = n+j` and `r+1 ≤ j`, the carrier of
`(mirabolicDerivative T ψ n j).obj ((mirabolicRankCast T h).obj (A × B))` is a
subsingleton. The GL rank is `k+1`, so the target `P_(k+r+2)` is the domain of
`leftPhiProduct`. The source transport `h` is arbitrary; this is what lets the
induction hypothesis absorb the casts. The proof is by induction on `r`.
In both cases `j ≥ 1`, so write `j = j'+1`. Then
`mirabolicDerivative T ψ n (j'+1)` unfolds definitionally to one `Φ⁻` at rank
`n+j'` followed by `mirabolicDerivative T ψ n j'`. Let `e : k+r = n+j'`.
The cast `h : k+1+r = n+j'+1` is rewritten (with `mirabolicRankCast_obj_trans`)
as the cast along `k+1+r = k+r+1` followed by the cast along
`k+r+1 = n+j'+1`. Then `phiMinus_obj_rankCast` moves `Φ⁻` past the second
cast. The object becomes

`(mirabolicDerivative T ψ n j').obj ((mirabolicRankCast T e).obj ((leftPhiProduct T ψ k r).obj (A, B)))`.

- **`r = 0`.** `leftPhiBoundary` gives a subsingleton carrier for
  `(leftPhiProduct T ψ k 0).obj (A, B)`. The rank cast along `e` and the
  derivative preserve this.
- **`r+1`.** Here `r+2 ≤ j'+1`, so `r+1 ≤ j'`. The hypothesis `hPhi ψ k r` gives
  `φ : leftPhiProduct T ψ k (r+1) ≅ leftPhiExpected T ψ k r`. Apply the
  induction hypothesis to `A`, `(phiMinus T ψ r).obj B` on `P_(r+1)`, `n`, `j'`,
  `h' : k+1+r = n+j'` and `r+1 ≤ j'`. In that result, rewrite the cast along
  `h'` as the cast along `k+1+r = k+r+1` (which is the cast inside
  `leftPhiExpected`, up to proof irrelevance) followed by the cast along `e`.
  This is a subsingleton statement for
  `(mirabolicDerivative T ψ n j').obj ((mirabolicRankCast T e).obj ((leftPhiExpected T ψ k r).obj (A, B)))`.
  Applying `mirabolicDerivative T ψ n j'` and `mirabolicRankCast T e` to
  `φ.app (A, B)` gives an isomorphism, and `subsingleton_of_iso` transfers the
  subsingleton carrier back.

### Entry theorem

Fix `ψ`, `k`, `r`, `i`, `hi : 0 < i ∧ i ≤ k+r+1`, `r+1 < i`, `A`, `B`. These
inequalities force `k ≥ 1`. For `k = 0` (an arbitrary representation of `GL_0`)
they are contradictory, so that case holds vacuously; `omega` discharges it
when `k` is written as `k'+1`. By definition, the order-`i` derivative of `A × B`
is `mirabolicDerivative T ψ (k'+1+r+1-i) (i-1)` after the rank cast along
`mirabolic_rank_eq_of_order hi`. The core lemma applies with `n = k'+1+r+1-i`,
`j = i-1`, `h = mirabolic_rank_eq_of_order hi`, and `r+1 ≤ i-1`.

## Imports and exclusion audit

Direct imports:

- `Langlands.Representation.Derivative.MixedProductDerivativeStatement` (the
  target statement; it imports `MixedProducts` and `Homogeneity`).
- `Langlands.Representation.Derivative.MirabolicProductMinusBoundary` (the
  published `leftPhiBoundary`; it imports the 4.13(b,c) statement module
  `MirabolicProductMinusCompatibilityStatement`).

The direct and transitive closure of this helper contains 76 published
project imports; the complete combined closure and both unweakened exclusion
sets are audited in the final entry module's Markdown. Its two published
imports and all their dependencies are unchanged. The conditional argument
is discharged in that entry by the published exact Phi clause. Neither a
source citation, proposition definition, draft, consumer conclusion nor
pending candidate is used in place of a proof. The implemented vanishing
argument uses only that clause, the independently published boundary,
actual rank transports, zero-carrier preservation and induction; it uses
no segment, head, socle, classification, finite-length or Whittaker-finiteness
conclusion.
