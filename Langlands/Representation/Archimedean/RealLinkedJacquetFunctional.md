# A Jacquet functional killed by a power of a lower root vector, and slow growth of a quotient

Lean module: `Langlands.Representation.Archimedean.RealLinkedJacquetFunctional`
(namespace `Langlands.Archimedean`; helper lemmas in
`Langlands.Archimedean.RealLinkedJacquetFunctional`).

This module defines one statement, `RealLinkedJacquetFunctionalStatement`. The statement is not
proved here. The module then proves `realLinkedQuotientGrowth_of_split`: this statement and the
statements of modules `RealLeftPolynomialGrowth` and `RealTaylorLeftPolynomial` together imply
`RealLinkedQuotientGrowthStatement` (module `RealLinkedQuotientGrowth`).

Notation:

- `𝔤 = ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ` and `U = U(𝔤)`; `U_d = degreeFiltration ℂ 𝔤 d`.
- `I(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`.
- `ρ = realStandardRep n ds` (right translation by `O(n)`) and `π = realStandardLie n ds`
  (right derivatives).
- `E = lowerRootMatrix n p hp`, the matrix unit `E_{p+1,p}`, and
  `e(t) = lowerRootElement n p hp t = 1 + t E` (module `RealLeftPolynomialGrowth`).

## The statement

```lean
def RealLinkedJacquetFunctionalStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
    ¬ IsRealMoeglinUnlinked ds →
      ∃ (ℓ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
        (a : Fin n → ℂ) (e : Fin n → Fin 2) (p k : ℕ) (hp : p + 1 < n),
        ℓ ≠ 0 ∧ IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e ∧
          a ⟨p, Nat.lt_of_succ_lt hp⟩ - a ⟨p + 1, hp⟩ = 1 - (k : ℂ) ∧
          ∀ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
            ℓ ((realStandardLie n ds (1 ⊗ₜ lowerRootMatrix n p hp) ^ k) v) = 0
```

The hypotheses on `ds` are those of `RealLinkedLanglandsQuotientNotLargeStatement`: total rank
`n`, Langlands order (`IsRealLanglandsOrdered`) and two linked Mœglin data
(`¬ IsRealMoeglinUnlinked ds`).

The conclusion asks for:

- a nonzero linear functional `ℓ` on `I(ds)`;
- exponents `a : Fin n → ℂ` and signs `e : Fin n → Fin 2` such that `ℓ` is a real Jacquet
  functional (`IsRealJacquetFunctional`, module `RealJacquetReduction`). That is, `ℓ` vanishes
  on `π(1 ⊗ X) v` for strictly upper triangular `X`;
  `ℓ(π(1 ⊗ E_jj) v) = a_j ℓ(v)`; and `ℓ(ρ(s_j) v) = (-1)^(e_j) ℓ(v)` for the sign reflections
  `s_j`;
- a position `p` with `p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and
  `ℓ(π(1 ⊗ E)^k v) = 0` for every `v`.

Since `ℓ ≠ 0`, the last condition fails for `k = 0`; so `k ≥ 1` in any witness.

## Provenance

This is an internal statement, introduced in Task 7070. No published reference states it in this
form. The following explains why it is expected to hold. It is a sketch; none of it is
formalised.

Notation for this section. `PS(x_1, …, x_m)` is the principal series of `GL_m(ℝ)` whose
characters have exponents `x_1, …, x_m` (and suitable signs). `D_p|det|^s` has infinitesimal
character `(u, v) = (s + p/2, s - p/2)`, and it is the irreducible submodule of `PS(u, v)` for
signs with the reducible parity (module `StandardModule`, `StandardModule.md`). `F_m` denotes an
`m`-dimensional irreducible representation of `GL_2(ℝ)`: `Sym^(m-1)` of the standard
representation, twisted by a character of `det`.

**Reformulation.** By the Frobenius reciprocity of `realJacquetFrobenius` (module
`RealJacquetFrobeniusProof`), `ℓ` gives the map `B v (b κ) = χ(b) ℓ(ρ(κ) v)` from `I(ds)` into
the principal series with characters `chars a e`. The condition on `ℓ` implies that the image
consists of functions `h` with `d^k/dt^k h(e(t) κ) = 0` at `t = 0` for every `κ ∈ O(n)`.
Conversely, let `T` be a nonzero `(𝔤, K)`-map from `I(ds)` into a module of the form
`Ind_{P_b}(F_k ⊗ σ)`, induced from the parabolic `P_b` of the simple root `b` at positions
`p, p + 1` (Levi `GL_2 × GL_1^(n-2)`), with `σ` a product of characters. Call such a module of
*F-type*. `Ind_{P_b}(F_k ⊗ σ)` lies in a principal series in which the characters at `p, p + 1`
are in increasing order and differ by `k`. In the Library's normalisation, its exponents
satisfy `a_p - a_{p+1} = 1 - k`. Its functions are polynomial of degree `< k` along
`t ↦ e(t) g`. Then `ℓ = ev_1 ∘ T` is a witness. It is nonzero because the image of `T` is a nonzero
`O(n)`-stable space of functions determined by their values on `O(n)`. So it is enough to find
a nonzero map from `I(ds)` into an F-type module.

**Rank one.** Let `x > y` with `x - y = m` a positive integer, and choose signs so that `PS(x, y)`
is reducible. The intertwining operator `PS(x, y) → PS(y, x)` converges. Its image is the
Langlands quotient `F_m`, which sits in `PS(y, x)` as the functions polynomial along the lower
unipotent group.

**Key lemma.** Let `A_w = A_{s_b} A_{w'}` be a product of absolutely convergent intertwining
operators between principal series of `GL_n(ℝ)` (the lengths add). Its last factor `A_{s_b}`
crosses two adjacent exponents `x > y` that are integral and of reducible parity. If the
restriction of `A_w` to a submodule `I` is nonzero, then `A_w(I)` is a nonzero submodule of
`A_{s_b}(…)`. By induction in stages and the rank-one case, this lies in the F-type module
`Ind_{P_b}(F_{x-y} ⊗ σ)`. Signs: `D_p ⊗ sgn(det) ≅ D_p`, so the signs of the two characters of a
discrete-series block in its principal series can be flipped together. This changes the parity of
every crossing between one of them and another entry. So the parity of a chosen crossing with a
discrete-series entry can be arranged.

**Reduction to an adjacent pair.** A weight-`0` block is induced from two characters
(`realBlockMoeglinData`). Choose a linked pair of Mœglin data at minimal distance in
`realMoeglinData ds`. The data between them are unlinked to each other and to both ends. By
Mœglin 1997, Theorem 10b, `Ind(a ⊗ c)` is irreducible for unlinked `a, c`, hence isomorphic to
`Ind(c ⊗ a)`. So the pair can be moved next to each other without changing `I(ds)` up to
isomorphism. Induction in stages reduces to the pair alone in `GL_m(ℝ)`, `m ∈ {2, 3, 4}`, in
Langlands order. The image `J` of its Langlands intertwining operator is the Langlands quotient
(Knapp 1986, Theorem 7.24). If `J` lies in an F-type module of `GL_m(ℝ)`, inducing up, and
embedding the other discrete-series blocks in their principal series, gives a nonzero map
from `I(ds)` into an F-type module of `GL_n(ℝ)`. The cases follow. Linked data have real exponent
differences, and only differences matter, so the exponents are written as real numbers.

- *Two characters* `x > y`, linked: `J = F_{x-y}` inside `PS(y, x)`; `k = x - y`.
- *Discrete series then character*, `D_p|det|^s` and exponent `w`: linkage gives
  `s - w - p/2 ∈ {1, 2, …}`, so `w < v < u`. Embed `I` in `PS(u, v, w)`. The Langlands operator
  is the restriction of the crossings `(v, w)` and then `(u, w)`, both convergent. The last
  crossing `(u, w)` is integral; arrange its parity. `k = u - w`.
- *Character then discrete series*, `w > u > v`: crossings `(w, u)` and then `(w, v)`;
  `k = w - v`.
- *Two discrete series* `D_p|det|^s`, `D_q|det|^t`, `s > t`, `s - t - |p - q|/2 ∈ {1, 2, …}`.
  Write `u_1 = s + p/2`, `v_1 = s - p/2`, `u_2 = t + q/2`, `v_2 = t - q/2`. All differences
  are integers.
  (a) If `s - t > q/2`, embed `D_q|det|^t` in `PS(u_2, v_2)`, so
  `I ⊆ Ind(D_p|det|^s ⊗ u_2 ⊗ v_2)`. The block operator is the restriction of `A_2 A_1`.
  `A_1` moves `D_p|det|^s` past `u_2`; it converges since `s - u_2 = s - t - q/2 > 0`. `A_2`
  moves it past `v_2` (convergent, `s - v_2 > 0`). Embedding `D_p|det|^s` in `PS(u_1, v_1)`,
  `A_2` is the restriction of the crossings `(v_1, v_2)` and then `(u_1, v_2)`, both
  convergent because `v_1 - v_2 = s - t - (p - q)/2 > 0`. The last crossing `(u_1, v_2)` gives
  `k = u_1 - v_2 = s - t + (p + q)/2`. This includes singular cases such as `u_2 = v_1`.
  For `D_5|det|^(11/2) × D_2` (infinitesimal character `{8, 3, 1, -1}`) it gives `k = 9`.
  (b) If `s - t > p/2`, embed `D_p|det|^s` in `PS(u_1, v_1)` instead. Move `v_1` past
  `D_q|det|^t` (convergent, `v_1 - t > 0`), then `u_1`; the latter is the crossings `(u_1, u_2)`
  and then `(u_1, v_2)`. The last crossing is again `(u_1, v_2)`.
  (c) Otherwise `|p - q|/2 < s - t ≤ min(p, q)/2`, and `u_1 > u_2 > v_1 > v_2`, a regular
  integral infinitesimal character. The point `λ' = v_2 + (4, 2, 1, 0)` is that of
  `D_3|det|^(s') × D_2|det|^(t')` with `s' - t' = 3/2 > 1`, which is case (a). It lies in the same
  Weyl chamber as `λ = (u_1, u_2, v_1, v_2)`, and `λ - λ'` is integral. The translation functor
  `T` from `λ'` to `λ` is an equivalence of categories (Bernstein–Gelfand 1980, Theorem 4.1 and
  Remark 4.2(a)). By the tensor identity `Ind_P(τ) ⊗ F ≅ Ind_P(τ ⊗ F|_P)` and a filtration
  of `F|_P`, `T` carries the standard module at `λ'` to the one at `λ`. So it carries the
  Langlands quotient `J'` to `J`. Applied to an F-type module, the same two facts and the
  Clebsch–Gordan decomposition of `F_k ⊗ F_j` give a filtration whose subquotients are F-type
  modules or zero. The irreducible module `J = T(J')` embeds in one of these subquotients.

For equal `p = q` and `s - t = 1` (Speh's case, inside (a) for `p = 1` and (c) for `p ≥ 2`),
Sahi and Stein 1990 realise the Langlands quotient inside a module induced from characters of
`GL_2 × GL_2` composed with the determinant. That module lies in an F-type module with `k = 1`.
This is a cross-check only.

## Helper lemmas (namespace `RealLinkedJacquetFunctional`)

- `finrank_map_le_of_eqOn`: if `g x = Φ (f x)` for `x` in a finite-dimensional subspace `P`, then
  `dim g(P) ≤ dim f(P)`. Proof: `g(P) ≤ Φ(f(P))` (`Submodule.finrank_mono`), and
  `dim Φ(f(P)) ≤ dim f(P)` (`Submodule.finrank_map_le`).
- `finrank_quotient_ker_le`: let `B : X → V` intertwine Lie algebra actions `σ` and `π`, and let
  `P` be a finite-dimensional subspace of `U(L)`. Then the operators of `P` on `X / ker B` span a
  space of dimension at most that of their restrictions `range B → V`. Proof: `ker B.liftQ` is
  trivial, so `X / ker B → V` has a left inverse `L'` (`LinearMap.exists_leftInverse_of_injective`).
  By `envelopingAction_intertwine` (module `RealLargeLanglandsQuotientReduction`),
  `mkQ ∘ σ(u) = L' ∘ π(u)|_{range B} ∘ B.rangeRestrict`. Apply the previous lemma.
- `charFun_of_pos`: `charFun e t x = x^t` for `x > 0`.
- `frobFun_apply_one`: the Frobenius function of `v` takes the value `ℓ(v)` at `1`. This is
  `frobFun_eq` with `b = k = 1`.
- `iterate_rightDerivative_frobFun`: `R(X)^k (B v) = B(π(1 ⊗ X)^k v)`, by induction on `k` from
  `frobFun_rightDerivative`.
- `frobLin_codRestrict_lie` and `frobLin_codRestrict_rep`: when `frobLin` takes values in the
  `O(n)`-finite functions of a standard module `ds'`, its corestriction carries `π` to
  `realStandardLie n ds'` and `ρ` to `realStandardRep n ds'`. The first holds on pure tensors by
  `frobFun_rightDerivative`, using `c ⊗ M = c • (1 ⊗ M)`, and extends by additivity. The second
  is `frobFun_rightTranslation`.

## The combination

`realLinkedQuotientGrowth_of_split : RealLeftPolynomialGrowthStatement →
RealTaylorLeftPolynomialStatement → RealLinkedJacquetFunctionalStatement →
RealLinkedQuotientGrowthStatement`.

Fix `n` and `ds` satisfying the hypotheses. Take `ℓ, a, e, p, k` from the Jacquet functional
statement. The steps follow.

1. **The Frobenius map.** `I(ds)` is a real `(𝔤, K)`-module (`isRealGKModule_realStandardModule`).
   As in the proof of `realJacquetFrobenius`, each `B v = frobFun ρ ℓ a e v` lies in the
   principal series `principalSeries ℝ n (posChar a e)`; this uses `contMDiff_frobFun` and
   `frobFun_left`. It is also `O(n)`-finite (`frobFun_mem_kFiniteVectors`). The standard module
   of the character list `chars a e` has no induced blocks, so `B v` lies in its `O(n)`-finite
   functions. Let `B` be the corestriction of `frobLin` to these functions. By the helper lemmas,
   `B` intertwines `ρ, π` with the actions on that standard module.
2. **Exponent condition.** By `posChar_apply` and `charFun_of_pos`, for `x > 0`,
   `posChar a e j x = x^(expo a j)`, where `expo a j = a_j - (n - 1)/2 + j`. From
   `a_p - a_{p+1} = 1 - k` we get `expo a (p + 1) = expo a p + k`. Hence
   `χ_{p+1}(x) = x^k χ_p(x)` for `χ = posChar a e` (`Complex.cpow_add`, `Complex.cpow_natCast`).
3. **Taylor condition.** For `κ ∈ O(n)`, the right translate of `B v` by `κ` is `B(ρ(κ) v)`
   (`frobFun_rightTranslation`). So `R(E)^k` of it at `1` is `B(π(1 ⊗ E)^k ρ(κ) v)(1)`, which is
   `ℓ(π(1 ⊗ E)^k ρ(κ) v) = 0`.
4. **Polynomiality.** By the Taylor statement, applied with `χ = posChar a e`, every function in
   `range B` is polynomial of degree `< k` along `t ↦ e(t) g`.
5. **Growth.** The growth statement for `Y = range B` gives `C` with
   `dim { u|_{range B} : u ∈ U_d } ≤ C (d + 1)^(n (n - 1) - 1)`.
6. **The submodule.** Take `W = ker B`. It is a `(𝔤, K)`-submodule because `B` intertwines both
   actions. It is proper: if `ker B = ⊤`, then `ℓ(v) = B v (1) = 0` for all `v`
   (`frobFun_apply_one`), contradicting `ℓ ≠ 0`. By `finrank_quotient_ker_le`, the operators of
   `U_d` on `I(ds) / W` span a space of dimension at most that in step 5. This is the bound
   required by `RealLinkedQuotientGrowthStatement`.

Sources (provenance sketch only):

- C. Mœglin, Representations of GL(n) over the real field, in: T. N. Bailey and A. W. Knapp
  (eds.), Representation Theory and Automorphic Forms, Proc. Sympos. Pure Math. 61 (1997),
  157–166 (`bailey-knapp-1997-pspm61`), Theorems 10a and 10b, printed p. 164.
- A. W. Knapp, Representation Theory of Semisimple Groups: An Overview Based on Examples,
  Princeton University Press, 1986 (`provided-40cace9c0f8c2361e7b3d7459f7908362f819b68114945405f1c16d968b21855`),
  Theorem 7.24, p. 200 (PDF page 214): the Langlands quotient is the image of the intertwining
  operator.
- J. N. Bernstein and S. I. Gelfand, Tensor products of finite and infinite dimensional
  representations of semisimple Lie algebras, Compositio Math. 41 (1980), 245–285
  (`bernstein-gelfand-1980-tensor-products`), Theorem 4.1 and Remark 4.2(a), pp. 268–269.
- S. Sahi and E. M. Stein, Analysis in matrix space and Speh's representations, Invent. Math.
  101 (1990), 379–393 (`sahi-stein-1990-matrix-speh`), cross-check for Speh's case only.

The factorisation of intertwining operators along reduced decompositions, the rank-one facts
and the translation of standard modules are standard. They are used here without a precise
locator.
