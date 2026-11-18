# Adjoint lattices, the critical maximum and exactness (T2)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Lemma (1.4.4) and
Proposition (1.4.7), printed p. 36, and Corollary (1.4.10), printed p. 38
(PDF pp. 48 and 50). The field and order hypotheses are those at the start of
§1.4, printed p. 35.

`AdjointExactnessStatement` is an unproved proposition definition for all
nonarchimedean local fields `F`, finite-dimensional `F`-vector spaces `V`,
and field actions `E/F` on `V`, in independent universes. It assumes that
`β` generates `E/F`, that `β` is not a scalar in `F`, and that `Eˣ`
normalizes the order. Thus these are exactly `E = F[β] ≠ F` and the
normalization hypotheses of §1.4.

Writing `N k = 𝔑_k`, `P k = 𝔓^k`, `Q k = 𝔓^k ∩ B` and `Q 0 = 𝔅`, it
asserts that the intersection of the `N k` is `𝔅`, that `criticalIndexSet`
is nonempty and bounded above, and that it has a greatest integer `k₀`
equal to the defined `criticalExponent`.

For every tame corestriction, integers `m,k,r`, `k ≥ k₀` and `r ≥ 1`, it
states the exactness of all four sequences requested in T2:

1. `0 → N k / N (k+r) → P k / P (k+r) → Q k / Q (k+r) → 0`;
2. `0 → N k / 𝔅 → P k → Q k → 0`;
3. `0 → Q m · N k / Q m → P (m+k) → Q (m+k) → 0`;
4. `0 → Q m · N k / Q m · N (k+1) → P (m+k) / P (m+k+1)
   → Q (m+k) / Q (m+k+1) → 0`.

Products are products of submodules in `End_F(V)`, hence lattices spanned
by products. Both maps are explicit: the first is `adjointMap 𝒪[F] b`
for the image `b` of `β`, and the second is `x ↦ (s x).restrictScalars F`.
The latter identifies the codomain centralizer with its image in `A`.
No independently supplied centralizer filtration or exactness hypothesis
is used.

`QuotientLatticeExact` is internal notation, derived from the elementary
definition of exactness of additive quotient groups. Its six subgroup
parameters are `X,D,P,R,Q,T`. It states that `D ≤ X`, `R ≤ P`, `T ≤ Q`,
that both displayed maps carry numerator and denominator into the
corresponding numerator and denominator, that the preimage of `R` in `X`
is `D`, that every class of `Q/T` has a preimage in `P/R`, and that
`g(y) ∈ T` is equivalent to `y` lying in `f(X) + R`. These last three
conditions are respectively injectivity, surjectivity and middle
exactness. In every application here the specified maps are additive by
construction. Taking `R = T = 0` gives the unquotiented second and third
sequences. This formulation includes the full content of each sequence
without constructing quotient types.
