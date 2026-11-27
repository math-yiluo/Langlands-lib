# Elements commuting with the centralizer filtration up to one step

Let `E` be a field acting on `V` with `F ⊆ E`, such that `E^×` normalizes the
`𝔬_F`-lattice chain `𝓛 = (L_i)`. Write `𝔓^j = 𝓛.endFiltration j` and
`𝔄 = 𝔓^0`. The module proves that an element `b ∈ 𝔄` whose commutator with
every `E`-linear element of `𝔓^j` lies in `𝔓^{j+1}`, for every `j ∈ ℤ`, is
congruent modulo `𝔓` to an element of `𝔬_E`. All results are proved.

## Results

- `CriticalDerived.rankOne_mem_endFiltration`: let `w` be a basis of `V` over
  `E` splitting `𝓛` (`RelativeSplits`), and let `c • w_k` have exact depth `0`.
  For `y ∈ L_j`, the `E`-linear rank-one map `v ↦ w_k^*(v) c⁻¹ y`
  (`StratumEquivalence.rankOne`) lies in `𝔓^j`.
- `StratumEquivalence.exists_integer_sub_mem_of_commutator`: let `b ∈ 𝔄` satisfy
  `b y − y b ∈ 𝔓^{j+1}` for every `j ∈ ℤ` and every `E`-linear `y ∈ 𝔓^j`. Then
  there is `a ∈ 𝔬_E` with `b − a ∈ 𝔓`. Here `F` is a nonarchimedean local field
  and `V`, `E` are finite-dimensional over `F`.

## Proof

Take a splitting basis `w` and a vector `u = c • w_k` of exact depth `0`
(`StratumEquivalence.exists_basis_depth_zero`). Put `μ = w_k^*(b u) c⁻¹ ∈ E`.
For `y ∈ L_j`, the rank-one map `R_y : v ↦ w_k^*(v) c⁻¹ y` lies in `𝔓^j` and is
`E`-linear. It sends `u` to `y` and `b u` to `μ y`. The hypothesis applied to
`R_y` and evaluated at `u ∈ L_0` gives `b y − μ y ∈ L_{j+1}`. As `j` and `y` are
arbitrary, `b − μ ∈ 𝔓`.

It remains to see that `μ ∈ 𝔬_E`. The coordinate `w_k^*(b u) w_k = μ u` of
`b u ∈ L_0` lies in `L_0`, because `w` splits `𝓛`. Since `u` has exact depth
`0`, the shift of `μ` is nonnegative, and `StratumEquivalence.mem_integers_iff`
gives `μ ∈ 𝔬_E`.

## Origin

The result is an internal device. It plays the role of two facts used by
Bushnell and Kutzko in the proof of Lemma (5.2) of *Simple types in GL(N):
computing conjugacy classes* (1994), printed p. 134 (PDF p. 147), literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. These are
that the centre of `U(𝔅)/U¹(𝔅)` is the image of `k_E^×`, where
`𝔅 = 𝔄 ∩ End_E(V)`, and that the fixed points of the conjugation action of
`U(𝔅)` on `(𝔔^m + 𝔓^{m+1})/𝔓^{m+1}`, for `m = e(𝔅)` and `𝔔 = rad(𝔅)`, form
the image of `𝔭_E`. Those facts are used there only when `𝔄` is maximal among
the hereditary orders normalized by `E^×`, that is, when `e(𝔅) = 1`. The
present statement needs no maximality assumption.
