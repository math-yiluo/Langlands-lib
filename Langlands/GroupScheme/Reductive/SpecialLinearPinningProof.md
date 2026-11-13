# The split pinning of the special linear group

Proof of `Langlands.GroupScheme.SpecialLinearSimplyConnectedPinningStatement`
(module `Langlands.GroupScheme.Reductive.SpecialLinearPinningStatement`):

```lean
theorem specialLinearSimplyConnectedPinning :
    SpecialLinearSimplyConnectedPinningStatement.{u}
```

Proof author: Worker 61 (Task 5703); prepared for publication by Worker 235
(Task 6032), using the five-module proof from Task 5703 public draft revision 2.
Worker 235 placed the helper declarations in the `SpecialLinear.FinSucc` namespace
to allow joint import with the Library's arbitrary-pivot `SpecialLinearTorus` API.
The statement says that for every field `k` and every `n`,
the Library's `SL_{n+1}` over `k` has a split pinning `p` with two properties. Its coroots
span the cocharacter lattice (`p.rootDatum.corootSpan ℤ = ⊤`). There is a bijection
`e : p.base.support ≃ Fin n` under which the pairings of the simple roots are the entries of
the Cartan matrix `CartanMatrix.A n` of type `A_n`.

The theorem has exactly the published statement as its type at every universe
parameter `u`, with no additional premise. The field is arbitrary, including all
positive characteristics. For `n = 0` the same construction has a rank-zero torus,
zero cocharacter lattice and empty simple-root support; its bijection is with
`Fin 0`. No separate positive-rank assumption is used.

The auxiliary declarations are in namespace
`Langlands.GroupScheme.SpecialLinear.FinSucc`. Their module paths remain under
`Langlands.GroupScheme.Reductive`. The published
`Langlands.GroupScheme.SpecialLinear` declarations, including its arbitrary-pivot
diagonal torus, can be imported alongside these modules. Worker 243 proposed the
fixed-torus export `exists_coordinateRootDatum` for coordinate-dependent consumers.
Notation is as in `Reductive.SpecialLinearCoroots`: `𝔻` is the split torus of rank `n` over `k`,
`w(p)` is `weightCoord n p`, `rootChar n k p q` has coordinates `w(p) - w(q)`, and
`delta p q y = [y = p] - [y = q]`.

## Integer coordinates

- `regularCoord n x = n - 2x` for `x : Fin (n + 1)`.
- `sum_range_two_mul`: `∑_{i < m} 2i = m(m - 1)`. With it, `sum_regularCoord` shows that
  the `regularCoord n x` sum to `0`.
- `regularCoord_sub`: `regularCoord n x - regularCoord n y = 2(y - x)`.
- `delta_sub_delta_eq_cartan`: for `a, b : Fin n`,
  `delta b b' a - delta b b' a' = CartanMatrix.A n a b`. Here `a = a.castSucc` and
  `a' = a.succ`, and likewise for `b`. This is the Cartan matrix of type `A_n`: `2` on the
  diagonal, `-1` for `|a - b| = 1`, and `0` otherwise.
- `eq_of_cartan_eq_two`: `CartanMatrix.A n a b = 2` forces `a = b`.

## Simple roots over a field

- `regularCochar n k = cochar n k (regularCoord n)`, the cocharacter
  `t ↦ diag(t^n, t^(n-2), …, t^(-n))`.
  `latticePairing_rootChar_regularCochar`: the root `rootChar n k x y` pairs with it to
  `2(y - x)`, which is nonzero for `x ≠ y`.
- `rootChar_castSucc_succ_injective`: the characters `rootChar n k a.castSucc a.succ`,
  `a : Fin n`, are pairwise distinct. Pair them with `corootChar n k b.castSucc b.succ` and
  use `delta_sub_delta_eq_cartan` and `eq_of_cartan_eq_two`.

For the next lemmas, `P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻)`
satisfies `hP : IsRootDatumOf (diagonalTorus n (CommRingCat.of k)) P`.

- `exists_root_eq hP j`: each root of `P` is `rootChar n k x y` for some `x ≠ y`.
- `root'_regularCochar`: if `P.root j = rootChar n k x y`, then
  `P.root' j (regularCochar n k) = 2(y - x)`. `root'_regularCochar_ne_zero`: this value is
  never `0`, so the regular cocharacter is regular for `P`.
- `pairing_eq_delta` (with `[Finite J]`): if `P.root i = rootChar n k x y` and
  `P.root j = rootChar n k p q`, then `P.pairing i j = delta p q x - delta p q y`. This uses
  the coroot formula `coroot_eq_corootChar` of `Reductive.SpecialLinearCoroots`.
- `mem_baseOf_iff hP j`: **simple roots.** Let `f` be the linear form
  `⟨-, regularCochar n k⟩` on characters. Then `j` lies in Mathlib's
  `IsAddIndecomposable.baseOf P.root f` if and only if
  `P.root j = rootChar n k a.castSucc a.succ` for some `a : Fin n`. Membership in `baseOf`
  means `f(P.root j) > 0`, and in every decomposition `P.root j = P.root j1 + P.root j2`
  with `f`-positive summands one summand is `0`.
  - Forward: a positive root `rootChar x y` has `x < y`. If `y ≠ x + 1`, then with
    `z = x + 1` it decomposes as `rootChar x z + rootChar z y` into two positive roots,
    neither `0` (`P.ne_zero`).
  - Backward: `rootChar a.castSucc a.succ` has `f`-value `2`. Every positive root has
    `f`-value at least `2`, so a sum of two positive roots has value at least `4`. Hence no
    decomposition exists.

## The pinning

`exists_coordinateRootDatum n k` exposes the root datum on the fixed torus `𝔻`
with inclusion `FinSucc.diagonalTorus n (CommRingCat.of k)`. It returns a finite
index type `J`, a reduced root datum `P` satisfying `IsRootDatumOf` for that
inclusion, a base `B`, and a bijection `e : B.support ≃ Fin n`. In addition to the
coroot span and Cartan pairing conclusions, it retains the coordinate equations

```lean
∀ a : B.support,
  P.root a.val = rootChar n k (e a).castSucc (e a).succ
```

The proof proceeds as follows:

1. `SL_{n+1}` over `k` is connected reductive (the Library's
   `SpecialLinear.isConnectedReductive`). The diagonal torus is a split maximal torus
   (`isSplitTorus_diagonalTorus`, `isMaximalTorus_diagonalTorus` of
   `Reductive.SpecialLinearRoots`).
2. The Library's theorem `rootDatumExistence` gives a finite index type `J`, a reduced root
   datum `P` and `hP : IsRootDatumOf (diagonalTorus n k) P`.
3. The Library's `RootDatumCoweightFace.exists_base_support`, applied to the regular
   cocharacter (`root'_regularCochar_ne_zero`), gives a base `B` of `P` with support
   `baseOf P.root f`. By `mem_baseOf_iff`, every simple index `j` has
   `P.root j = rootChar n k (g j).castSucc (g j).succ` for some `g j : Fin n`.
4. The map `g : B.support → Fin n` is bijective. It is injective because `P.root` is
   injective. It is surjective because each `rootChar n k a.castSucc a.succ` is a root
   (`mem_range_root_iff`), and that root is simple by `mem_baseOf_iff`. Then
   `rootChar_castSucc_succ_injective` identifies its `g`-value as `a`.
5. Return `P`, its base `B` and the bijection `Equiv.ofBijective g` together with
   the coordinate equations already proved for `g`. The coroot span condition is
   `corootSpan_eq_top` of `Reductive.SpecialLinearCoroots`. The Cartan condition follows
   from `pairing_eq_delta` and `delta_sub_delta_eq_cartan`.

`exists_splitPinning n k` uses these fixed-torus data to construct a split pinning
with torus `𝔻`, inclusion `diagonalTorus n k`, root datum `P` and base `B`. Its root
pinning is the Library's `RootPinning.ofSplitMaximalTorus`. The returned coroot span,
bijection and Cartan equations establish the required conclusions directly.

`Langlands.GroupScheme.specialLinearSimplyConnectedPinning` applies
`FinSucc.exists_splitPinning`.
Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

`SL_{n+1}` is split simply connected of type `A_n`. Its simple roots for the diagonal torus
and the ordering defined by `diag(t^n, t^(n-2), …, t^(-n))` are `ε_a - ε_{a+1}`. Both facts
are standard. The source for the mathematical result is J. S. Milne,
*Algebraic Groups* (2017), Example 23.61, printed p.502 (PDF p.518), and
§24.c, printed p.517 (PDF p.533), registered as
`milne-2017-algebraic-groups` (source SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The official 2017 errata snapshot dated 2026-11-02 has no correction to these
two passages; it does correct the indexing of some earlier type `A_n` examples.
Here the index is consistently `SL_{n+1}`.

The proof here is derived for this project. It does not write down the root
datum explicitly. It takes the abstract root datum supplied by the Library's existence
theorem, and computes its roots (`Reductive.SpecialLinearRoots`) and coroots
(`Reductive.SpecialLinearCoroots`) in coordinates. The final pinning uses the
actual Library group scheme `SpecialLinear.groupScheme (Fin (n + 1))
(CommRingCat.of k)`. The construction and its imports do not use
`InnerTypeANormOneStatement` or the downstream inner-form proof.

## Module chain

`SpecialLinearLieMatrix` → `SpecialLinearTorus` → `SpecialLinearRoots` →
`SpecialLinearCoroots` → `SpecialLinearPinningProof`. All are in
`Langlands/GroupScheme/Reductive/`.
