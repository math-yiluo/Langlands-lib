# Coxeter systems from a length function with the exchange property

Module `Langlands.Group.CoxeterOfExchange`. It is a supporting module for the proof of
`Langlands.Group.RootPairingWeylCoxeterStatement` and contains one public theorem. All other
declarations are private.

## Public theorem

`Langlands.Group.exists_coxeterSystem_of_exchange`. Let `W` be a group, `B` a type,
`s : B → W` and `N : W → ℕ`. For a word `x : List B` write `π x = (x.map s).prod`. Assume:

- `mul_self`: `s b * s b = 1` for every `b`;
- `injective`: `s` is injective;
- `one`: `N 1 = 0`;
- `mul_simple`: for all `w` and `b`, either `N (w * s b) = N w + 1` or
  `N (w * s b) + 1 = N w`;
- `exchange` (right exchange property): if `N (π x * s b) < N (π x)`, then some index
  `k < x.length` satisfies `π x * s b = π (x.eraseIdx k)`;
- `generates`: every `w : W` is `π x` for some word `x`.

Then there are a Coxeter matrix `Mx : CoxeterMatrix B` and a Coxeter system
`cs : CoxeterSystem Mx W` such that

- `Mx a b = orderOf (s a * s b)` for all `a` and `b`;
- `cs.simple b = s b` for every `b`;
- `cs.length w = N w` for every `w`.

Unlike the textbook statement, the exchange hypothesis is not limited to reduced words. In the
application, the root-pairing proof establishes it for all words.

## Provenance

This is internal supporting content. It is a form of the classical characterization of Coxeter
systems by the exchange condition, proved with Matsumoto's argument; see Bourbaki, *Groupes et
algèbres de Lie*, Ch. IV §1. Neither Bourbaki nor any other Coxeter-group text is in the project
literature, so no numbered locator is claimed. The formulation was chosen to fit the
root-pairing application: a given function `N` replaces the word length, and the hypotheses
are those listed above.

## Proof as implemented

The hypotheses are bundled in the private structure `Hyp s N`, and `wp s x` denotes `π x`.

1. **Length estimates.** By induction on words, `N (w * π y) ≤ N w + y.length`, so
   `N (π x) ≤ x.length` (`mul_wp_le`, `wp_le`). Every `w` is `π y` for a word `y` with
   `y.length = N w` (`exists_word`). This uses induction from the right on a generating word:
   if `N` drops, the exchange property deletes a letter. Hence `N (u * v) ≤ N u + N v`. A word
   `x` is *reduced* (`Red`) when `N (π x) = x.length`. Prefixes and suffixes of reduced words
   are reduced (`red_append`).
2. **The Coxeter matrix.** `cmat` is the matrix `orderOf (s a * s b)`. It is symmetric because
   `(s a * s b)⁻¹ = s b * s a`. Its diagonal is `1` by `mul_self`, and off the diagonal it is
   `≠ 1` because `s` is injective.
3. **Matsumoto's lemma** (`good`). Let `πG` be the word product in the Coxeter group
   `(cmat h).Group`. Two reduced words of the same length `q` with the same product in `W` have
   the same product `πG`. The proof is by strong induction on `q`. A counterexample of length
   `q` is a pair `Bad q u v`. By the induction hypothesis, its two words cannot share their
   first or their last letter (`not_bad_cons`, `not_bad_append`).
   - `bad_tail` is the key step. From `Bad q u (v ++ [t])` it produces
     `Bad q (u.tail ++ [t]) u`. Since `π u * s t = π v` is shorter, exchange deletes a letter
     `k` of `u`. The word `u.eraseIdx k ++ [t]` is reduced, has product `π u`, and has a
     different `πG`-product from `u`. If `k ≠ 0` it would share its first letter with `u`, so
     `k = 0`.
   - `bad_iter` iterates `bad_tail`, starting from a counterexample `(x0 ++ [b], y0 ++ [a])`.
     After `q` steps both words are alternating words `altFrom a b q` and `altFrom b a q`.
   - `not_bad_alt` rules this out. Equal products give `(s a * s b) ^ q = 1`, so the order `m`
     of `s a * s b` divides `q`. If `q ≥ 2m`, the alternating word of length `q` would have the
     same product as a shorter one, contradicting reducedness. So `q = m = cmat a b`, and the
     two alternating words are the two sides of the braid relation
     (`CoxeterSystem.wordProd_braidWord_eq`, using `altFrom_eq_alternatingWord`).
4. **Every element of the Coxeter group has a reduced representative** (`exists_red`). The
   proof is by induction on a word. When `N` drops, exchange together with Matsumoto's lemma
   shows that the shorter word has the same `πG`-product.
5. **Assembly.** The lift `φ : (cmat h).Group →* W` with `φ (simple b) = s b` exists because
   `(s a * s b) ^ orderOf (s a * s b) = 1`. It is injective: if `φ g = 1`, write
   `g = πG z` with `z` reduced, so `z.length = N 1 = 0`. It is surjective by `generates`.
   The Coxeter system is `cs := ⟨(MulEquiv.ofBijective φ _).symm⟩`, so `cs.simple b = s b`.
   Finally `cs.length w = N w`. One inequality comes from a word of length `N w` given by
   `exists_word` together with `CoxeterSystem.length_wordProd_le`. The other comes from a
   `cs`-reduced word `ω` (`CoxeterSystem.exists_isReduced`) together with
   `N (π ω) ≤ ω.length`.
