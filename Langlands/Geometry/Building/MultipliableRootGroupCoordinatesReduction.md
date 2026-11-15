# Scheme-level unitary coordinates from coherent algebraic SU3 coordinates

This module reduces `MultipliableRootGroupCoordinatesExistenceStatement` (module
`MultipliableRootGroupCoordinates`) to two statements:

- `AlgebraicSU3RootCoordinatesExistenceStatement`: coherent algebraic SU3 coordinates `C` with
  Weyl normalization at every multipliable relative root;
- `UnitaryChartUpgradeStatement` (module `RootHeisenbergUnitaryChart`): a rational homomorphism from the unitary parameters to a
  multipliable root group that has chart form comes from a homomorphism of group schemes
  representing the root group.

The main theorem `multipliableRootGroupCoordinatesExistence_of_algebraicSU3` takes both
statements as explicit hypotheses. It does not assert that either of them holds.

Provenance: the module is internal. The record `ValuedUnitaryRootGroupCoordinates` models the
isomorphism `R_{E/K} U_{L/E} → U_a` of Kaletha–Prasad, *Bruhat–Tits theory: a new approach*,
Construction 2.9.16, together with the valuation of Construction 6.1.17. The proof here only
assembles published or separately staged Lean results, listed below.

## Split coroot points and scaling

Namespace `Langlands.Geometry.Building.AlgebraicSU3RootCoordinates`. Fix a field `k`.

- `gmPoint c`: the rational point of `𝔾_m` over `Spec k` with value `c : kˣ`.
- `rationalUnitsEquiv_scalar_gmPoint L c`: the scalar inclusion `WeilGm.scalar : 𝔾_m → R_{L/k} 𝔾_m`
  sends `gmPoint c` to the point corresponding to `c ∈ Lˣ` (through `WeilGm.rationalUnitsEquiv`).

For the next three statements, `C : AlgebraicSU3RootCoordinates i j s b` with
`i : S ⟶ G` and `s : S ⟶ Z`.

- `exists_map_eq_corootPoint hi hs c`: if `i` is a maximal split torus, `s ≫ j = i` and `j` is
  a monomorphism, then for every `c : kˣ` there is a rational point `t` of `S` with
  `s(t) = C.corootPoint c`, where `c` is read in `C.extensionˣ`. Proof: the composite
  `𝔾_m → R_{L/k} 𝔾_m → Z → G` (scalar inclusion, `C.coroot`, `j`) commutes with `i`
  because `Z` is commutative and `s ≫ j = i`. Since `𝔾_m` is a split torus
  (`isSplitTorus_gm`), it factors through `S` (`IsMaximalSplitTorus.exists_factor_of_commute`).
  Take `t` to be the image of `gmPoint c`.
- `rationalCharacterEval_extend_map t`: the positive character of `C`, evaluated on the
  extension to `L` of `s(t)`, is the value `b(t)` read in `Lˣ`. The proof uses
  `GaloisPointComparison.rationalExtend_map`, `rationalCharacterEval_characterRestrict`,
  the field `C.positive.restriction` and `GaloisPointComparison.rationalCharacterEval_extend`.
- `exists_conj_eq_scale hi hs c`: for every `c : kˣ` there is a rational point `t` of `S` with
  `b(t) = c` and
  `i(t) · C.positive.equiv p · i(t)⁻¹ = C.positive.equiv (scale c p)` for every parameter `p`,
  where `scale c (u, v) = (c u, c² v)`. Proof: take `t` from `exists_map_eq_corootPoint`. By
  `character_corootPoint`, the positive character takes the value
  `diagonalRootScalar c = c · c / σ(c) = c` on `C.corootPoint c`, since `σ` fixes `k`.
  With `rationalCharacterEval_extend_map` this gives `b(t) = c`. The conjugation formula is
  the field `C.positive.conjugation` at the point `s(t)` of `Z`, with `j(s(t)) = i(t)`.
- `exists_act_eq_scale hi hs jU hjU φ hφ c hc`: let `jU : U ⟶ G` represent the root subgroup
  of `b`, and let `φ` be a map from the parameters to `U(k)` with `φ p ≫ jU = C.positive.equiv p`.
  Then for every nonzero `c : k` there is a rational point `t` of `S` with `b(t) = c` and
  `t · φ(p) = φ(scale c p)` for the torus action `RelativeRoot.subgroupAction i b jU hjU`.
  Proof: `exists_conj_eq_scale`, then cancel the monomorphism `jU` using
  `RelativeRoot.subgroupAction_act_comp`.

## The reduction

Namespace `Langlands.Geometry.Building`.

`multipliableRootGroupCoordinatesExistence_of_algebraicSU3 hc hu`, for
`hc : AlgebraicSU3RootCoordinatesExistenceStatement.{u}` and
`hu : UnitaryChartUpgradeStatement.{u}`, proves
`MultipliableRootGroupCoordinatesExistenceStatement.{u}`.

**Proof.** Let `F` be a nonarchimedean local field, `K` its maximal unramified field
(`inertiaFixedField F`), `G` an affine group scheme over `K` with building data `B`, and `b` a
relative root with `2 • b` a relative root.

1. *Setup.* `G` is connected reductive and `B.i` is a maximal split torus. `G` is quasi-split
   (`MaximalUnramified.isQuasiSplit`), so the centralizer `Z` of the torus is a torus
   (`isTorus_of_quasiSplit_torusCentralizer`). The torus has opposite factor pairs
   (`rootRankOneFactorization`), so `b` is indivisible
   (`mem_indivisibleRoots_of_double_mem`). Applying `hc` gives
   `C : AlgebraicSU3RootCoordinates B.i Z.j Z.s b` with Weyl normalization `hn`.
2. *Root group chart.* Smooth closed representatives `jU : U ⟶ G` of `U_b` and
   `j₂ : U₂ ⟶ G` of `U_{2b}` come from `subgroup_has_smooth_closed_representative`. The
   relative root system (`relativeRootSystem`) excludes `n • b` for `n ≥ 3`. Then
   `nonempty_doubleRootCommutatorPairing` gives a commutator pairing `D` with weight vector
   coordinates `e` on its quotient `V`. `weightVectorCoordinatesOfNoHigherRoots` gives weight
   vector coordinates `e'` on `U₂`, and `heisenbergNormalForm` gives a normal form `N`.
3. *Rational coordinates on `U`.* `φe` is `C.positive.equiv` pulled back to `U(K)` along
   `jU`. It sends exactly the parameters with `u = 0` into `U₂`: by `D.isFppfQuotient` the
   kernel of the quotient map is the doubled root group, and `C.positive.double` identifies
   the parameters landing there. For every nonzero `c ∈ K`, `exists_act_eq_scale` gives a torus
   point with root value `c` acting on `φe` by `scale c`.
4. *Chart form and upgrade.* `HeisenbergNormalForm.exists_unitaryChartForm` (module
   `RootHeisenbergUnitaryChartForm`) gives `A`, `B`, `H` with
   `φe(u, v) = incl(B v + H(u, u)) · sec(A u)`, with `A` bijective and `B` bijective on
   trace-zero elements. `K` is infinite (`LocalField.infinite_of_isNonarchimedeanLocalField`,
   then injectivity of `F → K`). So `hu` gives `ψ : R_{E/K} U_{L/E} ⟶ U`, with `E = C.base`
   and `L = C.extension`. It agrees with `φe` on rational points, and `ψ ≫ jU` represents the
   root subgroup of `b`.
5. *Depth.* The origin is `C.coordinateOrigin Z hZ B.apartment hn` (module
   `ValuedSU3CoordinateAssembly`). `coordinateOrigin_depths` (with `B.isOmegaCompatible`, the
   norm-calibrated Henselian valuation of `L` from
   `IntegerValuation.isNormCalibrated_henselianSeparableAddValuation`, and its invariance under
   conjugation `SU3Root.henselianSeparableAddValuation_quadratic_bar`) gives
   `origin.val b (C.positive.equiv p) = towerDepth p`. The rational point of `ψ ≫ jU` at `p` is
   `φe p ≫ jU = C.positive.equiv p`, so the record `ValuedUnitaryRootGroupCoordinates B b` is
   `⟨C.base, C.extension, ψ ≫ jU, _, origin, _⟩`.

The proof is elaborated with `maxHeartbeats 400000`.
