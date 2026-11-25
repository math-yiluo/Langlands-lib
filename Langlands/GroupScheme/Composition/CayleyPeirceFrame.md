# The Peirce frame of an isotropic Cayley datum and its ℤ²-grading

Let `c : CayleyDatum K` be a Cayley datum over a field `K`, in any
characteristic. This module shows how an isotropic norm gives a vector
`e` with `N(e) = 0` and `T(e) = 1`. It then shows that such an `e`,
together with dual triples in its two Peirce spaces, gives a weighted
self-dual frame in the sense of
`Langlands.GroupScheme.Composition.CayleyFrameGrading`, and hence a
grading by `ℤ²` whose degrees generate `ℤ²`. Here `b` is `form`, the
polar form of the norm `N`, `T` is `trace`, and `μ` (written as
juxtaposition) is the multiplication. The identities used are those of
`Langlands.GroupScheme.Composition.CayleyIdentities`.

## An idempotent from an isotropic vector

`exists_norm_eq_zero_trace_eq_one`: if `x ≠ 0` and `N(x) = 0`, there is
`e` with `N(e) = 0` and `T(e) = 1`.

Proof: first suppose `T(xy) = 0` for every `y`. Since
`T(xy) = T(x) T(y) - b(x, y)`, the vector `T(x) 1 - x` is orthogonal to
everything, so `x = T(x) 1`. Then `0 = N(x) = T(x)²` gives `x = 0`, a
contradiction. So some `y` has `T(xy) ≠ 0`. Put
`e = x (T(xy)⁻¹ y)`. It has `N(e) = N(x) N(…) = 0` and `T(e) = 1`.

## Peirce spaces

- `InPeirce e z` means `ez = z`, `T(z) = 0` and `b(z, e) = 0`. This is
  membership in the Peirce space `U(e)`.
- `IsPeircePair e f` means `N(e) = 0`, `T(e) = 1` and `e + f = 1`.
- `form_mul_self_eq_zero`, `form_mul_left_self_eq_zero` and
  `form_mul_right_self_eq_zero` show that if `N(z) = 0` then
  `b(zw, z) = b(wz, z) = 0`, and `b(zz, w) = 0` if moreover `T(z) = 0`.
  These follow from (I1), (I1') and `z² = T(z) z - N(z) 1`.

For a Peirce pair `P : IsPeircePair e f` the following hold:

- Basic facts: `eq_sub` (`f = 1 - e`), `form_left_left` (`b(e, e) = 0`),
  `trace_right` and `norm_right`, so `symm` makes `(f, e)` a Peirce pair
  too.
- Products and pairings of `e` and `f`: `mul_left_left` (`ee = e`),
  `mul_left_right` (`ef = 0`), `form_left_right` (`b(e, f) = 1`),
  `mul_right_apply` and `form_right_apply`.
- `inPeirce_right_iff` describes `U(f)` through `e`:
  `ew = 0`, `T(w) = 0` and `b(w, e) = 0`.
- For `z ∈ U(e)`: `norm_eq_zero` (`N(z) = 0`), `mul_right_left`
  (`ze = 0`, from `ez + ze = T(e) z + T(z) e - b(e, z) 1`),
  `mul_right_right` (`zf = z`), `mul_left_of` (`fz = 0`) and
  `form_right` (`b(z, f) = 0`).
- `form_eq_zero`: `U(e)` is totally isotropic, by (I1) with `x = e`.
- `mul_mem`: `U(e) U(e) ⊆ U(f)`. The condition `e(zz') = 0` comes from
  the linearized identity (I4L). The trace condition comes from
  `trace_mul` and isotropy. The condition `b(zz', e) = 0` comes from
  (I3) and `ze = 0`.
- `form_mul_mul_mem`, `form_mul_mem_mul` and `form_mem_mul_mul`: for
  `z, z' ∈ U(e)` and `w ∈ U(f)`, the trilinear values `b(zz', w)`,
  `b(zw, z')` and `b(wz, z')` vanish. The first follows from `mul_mem`
  and isotropy of `U(f)`. The other two reduce to the first through
  (I3) and (I3').

## Peirce frames

`PeirceFrame` bundles the data that `exists_peirceFrame`
(module `Langlands.GroupScheme.Composition.CayleyPeirceExistence`)
produces:

- a vector `e` with `norm_e : N(e) = 0` and `trace_e : T(e) = 1`;
- `u v : Fin 3 → CayleyVector K` with `mem_u` (`e(u a) = u a`,
  `T(u a) = 0` and `b(u a, e) = 0`) and `mem_v` (`e(v a) = 0`,
  `T(v a) = 0` and `b(v a, e) = 0`);
- `form_uv : b(u a, v b) = δ_ab`.

The index type is `PeirceIndex = Bool ⊕ (Bool × Fin 3)`. The frame
vectors are `vec (inl true) = e`, `vec (inl false) = 1 - e`,
`vec (inr (true, a)) = u a` and `vec (inr (false, a)) = v a` (through
`E` and `F`). The involution `peirceDual` swaps `e ↔ 1 - e` and
`u a ↔ v a`. For `ε : Fin 3 → M`, `peirceWeight ε` is `0` on `e` and
`1 - e`, `ε a` on `u a`, and `-ε a` on `v a`. The helpers `peirceSide`
and `peirceRightSide` record the sides of the Peirce spaces. Further
results: `peirceDual_dual`, `peirceWeight_dual`, `eq_not_of_ne_bool`,
and `sum_eps_eq_zero` (if `ε 0 + ε 1 + ε 2 = 0`, then
`ε a + ε b + ε d = 0` for pairwise distinct `a, b, d`).

For a Peirce frame `D` the following hold:

- `pair`, `pair'` and `pair_true`: `(E s, E (!s))` is a Peirce pair.
  `mem`: `F s a ∈ U(E s)`. `trace_F`: `T(F s a) = 0`.
- Multiplication tables: `E_mul_E`, `E_mul_F` and `F_mul_E`, and in frame
  form `mul_vec_left` and `mul_vec_right`.
- Pairings: `form_E_E`, `form_E_F`, `form_F_E` and `form_F_F`, which
  combine into `form_vec`: `b(vec i, vec j) = 1` if `j = peirceDual i`
  and `0` otherwise.
- `form_F_F_F`: `b(F s a · F t b, F r d) = 0` unless `s = t = r` and
  `a, b, d` are pairwise distinct. Mixed sides vanish by
  `form_mul_mul_mem` and its variants. A repeated index vanishes because
  Peirce vectors have `N = T = 0`.
- `trace_vec_of_weight`: frame vectors of nonzero weight are orthogonal to
  `1`.
- `form_mul_vec`: if `ε 0 + ε 1 + ε 2 = 0`, then
  `b(vec i · vec j, vec l) = 0` whenever the three weights do not sum to
  zero. If one of the first two vectors is `E s`, the product is `0` or
  the other vector, by the multiplication tables, and `form_vec` applies.
  If the third vector is `E r`, (I3') moves `E r` into a product with the
  second vector, and the same argument applies. If all three are Peirce
  vectors, `form_F_F_F` leaves only the case of one side and pairwise
  distinct indices. There the weights sum to `±(ε a + ε b + ε d) = 0`.
- `weightedFrame ε hε : c.WeightedFrame PeirceIndex M` assembles these
  facts.
- `stdEps : Fin 3 → (ULift (Fin 2) → ℤ)` is `e₀, e₁, -(e₀ + e₁)`, and
  `stdEps_sum` says that these sum to zero.
- **`exists_grading`**: a Peirce frame gives a grading
  `g : c.Grading (ULift (Fin 2) → ℤ)` whose support generates the group.
  The grading is `(weightedFrame stdEps stdEps_sum).toGrading`. Its
  support contains the weights `e₀` and `e₁` of `u 0` and `u 1`, which
  generate `ℤ²`.

## Provenance

The Peirce decomposition of a split Cayley algebra along an isotropic
idempotent `e` uses `e`, `1 - e` and two totally isotropic three-dimensional
spaces in duality. This decomposition, and the grading by the weight
lattice of a maximal split torus of `G₂` that it carries, are standard
(Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*, Section 33.C,
printed pp.459–462 / PDF pp.482–485, as cited in the target statement's
Markdown). That source does not spell out the Peirce decomposition. It
identifies an isotropic Cayley algebra with the split model and its
automorphism group with split `G₂`. The Lean proofs here are direct
consequences of the composition identities. They do not use any
classification of composition algebras or of `G₂`. The
weight-vanishing argument through the trilinear form `b(xy, z)` is the
route chosen for this development.
