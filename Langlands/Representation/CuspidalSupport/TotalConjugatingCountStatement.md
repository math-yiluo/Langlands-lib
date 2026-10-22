# Total count of minimal conjugating block permutations

Author: Worker 204.

This pair states the count `l(M) = r!` from Bernstein–Zelevinsky (1977),
section 2.8. For an actual standard Levi of a general linear group over a
finite p-adic extension, the count runs over all minimal permutations that
conjugate it onto some standard Levi. The only declaration,
`Langlands.CuspidalSupport.TotalConjugatingCountTheorem.{uF}`, is a
Prop-valued definition. The pair proves nothing. It adds no definitions and
imports only the published `CuspidalSupport.LeviDefinitions`.

## Exact statement

```lean
def TotalConjugatingCountTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) (B : BlockShape n),
    Finite ((C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C) ∧
      Nat.card ((C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C) =
        Nat.factorial B.length
```

Write `S` for the dependent pair type
`(C : BlockShape n) × MinimalConjugatingPermutations (F := F.Carrier) B C`.
The proposition quantifies:

- every prime `p`;
- every actual `F : PadicField.{uF} p`, with field universe `uF` as the
  declaration's only universe parameter;
- every natural rank `n`, including `n = 0`;
- every ordered positive block shape `B : BlockShape n`.

It has no further hypotheses. In particular it takes no bijection, finite
instance, cardinal equation, coset parametrization or theorem-valued input.
No topology on `F.Carrier` is involved, because conjugation of Levis is
purely algebraic.

The conclusion has two conjuncts. The first is `Finite S`. The second is
`Nat.card S = Nat.factorial B.length`, where `B.length` is the number of
blocks. Mathlib's `Nat.card` is `0` on an infinite type. The factorial is
positive, so the second conjunct in fact implies the first. The first is
stated explicitly anyway, so that finiteness is part of the statement
rather than a consequence of the `Nat.card` convention. Each fiber
`MinimalConjugatingPermutations B C` already has a published `Finite`
instance. Finiteness of `S` is still a real claim, because the Library has
no `Finite` instance for the index type `BlockShape n`: only finitely many
target shapes may have nonempty fibers.

## The objects counted

An element of `S` is a pair `⟨C, w⟩`. Here `C : BlockShape n` is an ordered
positive target block shape and `w : MinimalConjugatingPermutations B C`.
This is the published subtype

```lean
{w : MinimalRepresentatives B C // ConjugatesLevi (F := F.Carrier) B C w.val}
```

so `w.val.val : Equiv.Perm (Fin n)` satisfies two conditions.

- `IsMinimalRepresentative B C`: the permutation is strictly increasing on
  each consecutive source block, and its inverse is strictly increasing on
  each consecutive target block. This is the Library's coordinate form of
  BZ77's set `W^{M,N}`.
- `ConjugatesLevi B C`: the image of the actual embedded block-diagonal
  subgroup `B.leviSubgroup F.Carrier` under conjugation
  `g ↦ P g P⁻¹` is exactly `C.leviSubgroup F.Carrier`. Here `P` is the
  actual permutation matrix `permutation n F.Carrier w.val.val`.

The sum runs over every ordered target shape. Pairs with different `C` are
different elements of `S`. Several permutations with the same target shape
are counted separately, including when block sizes coincide. For example,
with `B = (1, 1)` the only possible target is `C = (1, 1)`, and both the
identity and the transposition lie in the fiber. The count is `2 = 2!`.
It does not count distinct target shapes, which would give a multinomial
number. Rank zero is included: then `B` and every `C` have zero blocks,
and the statement asserts exactly one pair, matching `0! = 1`.

## Original source

The registered original is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472. Its literature ID is
`bernstein-zelevinsky-1977-induced-i`, with SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Printed pages 447–449 (PDF pages 8–10) were read directly. The project has
no errata note for this source.

- Section 2.6 (printed p. 447, PDF 8) sets
  `W(M,N) = {w ∈ W | w(M) = N}` for standard subgroups `M, N`. Here
  `w(g) = w g w⁻¹` for a representative of `w`. This is the direction of
  `ConjugatesLevi`.
- Example 2.7 (same page) treats `G = G_n` with `M`, `N` given by
  partitions. It says that `M ~ N` iff the two partitions have the same
  number of parts and are permutations of each other. It adds that these
  permutations correspond to the elements of `W(M,N)/W_M`.
- Section 2.8 (printed pp. 447–448, PDF 8–9) sets
  `W(M,*) = ∪_{N < G} W(M,N)`, the union over standard subgroups `N`. It
  defines `l(M)` as the cardinality of `W(M,*)/W_M`, and states: "if
  `M = G_{n_1} × ... × G_{n_r} < G = G_n`, then `l(M) = r!`." Theorem 2.8
  then bounds the length of cuspidal induction by `l(M)`.
- Lemma 2.11 (printed p. 448, PDF 9) defines the minimal representatives
  `W^{M,N}`.
- The proof of Corollary 2.13(c) (printed p. 449, PDF 10) uses
  `W(M,N) ∩ W^{M,N} = W_N \ W(M,N) / W_M = W(M,N) / W_M`.
- Step 2.14(2) (same page) computes
  `Σ_{L ~ M} |W(M,L)/W_M| = l(M)` using 2.13(c). This is the sum,
  over all associated standard Levis, of the number of minimal conjugating
  representatives.

## Derived formulation

For `G = GL_n`, standard subgroups `N < G` correspond exactly to ordered
positive compositions of `n`, that is, to `C : BlockShape n`. The Library
realizes `W` as `Equiv.Perm (Fin n)` acting through actual permutation
matrices. Since `w(M)` determines `N`, the union defining `W(M,*)` is
disjoint. By the 2.13(c) identification for each `N`, the cosets
`W(M,*)/W_M` correspond to the disjoint union over `N` of
`W(M,N) ∩ W^{M,N}`. The type `S` is the Library form of this disjoint
union, and `B.length` is BZ77's `r`. The statement therefore says that
`S` is finite of cardinality `l(M) = r!`. This is the form in which
2.14(2) uses the count.

BZ77 gives `l(M) = r!` without proof. The expected argument is as follows.
Distinct coordinate-block partitions have distinct block-diagonal
subgroups, since an elementary matrix `1 + E_{ab}` detects whether `a`
and `b` share a block. So `ConjugatesLevi B C w` holds exactly when the
permutation carries each source block onto a target block. That gives a
bijection `σ` of block indices with `C.size (σ i) = B.size i`. Minimality
forces the permutation to be the increasing map on each block. Conversely,
each `σ : Equiv.Perm (Fin B.length)` determines a unique target shape and
a unique such permutation. So `S ≃ Equiv.Perm (Fin B.length)`.

This explains the provenance and the future proof obligation only. This
pair establishes none of these facts: not the partition description of
`ConjugatesLevi`, not the bijection, and not the fixed-target coset
parametrization. The latter is the separate published proposition
`MinimalConjugatingCosetsTheorem` in
`CuspidalSupport.JacquetInductionStatement`. That proposition is stated
only for positive rank and is neither imported nor assumed here.
