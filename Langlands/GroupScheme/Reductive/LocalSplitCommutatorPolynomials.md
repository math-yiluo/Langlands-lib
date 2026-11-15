# Universal commutator polynomials of positive cell factors

This module proves that the commutator of two positive cell factors is given by
universal polynomials. Let `u` be a family of additive-group maps into a group scheme
`G` over a commutative ring `R`. Assume `u` is equivariant for a coordinate split
torus with exponent characters `ch`, and that the big-cell map of `u` is an open
immersion. Then for any two positions `k`, `l` there are polynomials
`E_p ∈ R[S][T]` with the following property. Over every ring `B` over `R` and for all
`x, y ∈ B`, the commutator of `u_{pos k}(x)` and `u_{pos l}(y)` is the ordered product
of the positive cell factors with coordinates `E_p(x, y)`. These polynomials are
bihomogeneous of the expected weights. Every monomial `S ^ dS T ^ dT` that occurs in
`E_p` has `dS ≥ 1`, `dT ≥ 1` and `dS • ch (pos k) + dT • ch (pos l) = ch (pos p)`.

As a consequence, the commutator relations of the imported
`Langlands.GroupScheme.Reductive.LocalSplitCommutatorLaws` hold for two groups whose
Weyl families have the same universal polynomials
(`commutatorRelations_of_isUnivComm`). The base ring is arbitrary and may have
nilpotents.

## Conventions

`R[S][T]` is `Polynomial (Polynomial R)`, with `S = C X` and `T = X`. The coefficient
of `S ^ dS T ^ dT` in `F` is `(F.coeff dT).coeff dS`. Elements of a ring `B` are
viewed as global functions on `Spec B` through the inverse of `Scheme.ΓSpecIso`.

For a family `v : J → (𝔾ₐ ⟶ G)`, positions `pos : Fin n → J` and an object `Z` over
`Spec R`, the imported `orderedProduct v pos Z e` is `P(e) = ∏_q v_{pos q}(e q)` in
the order of the positions. The imported `posComm v pos Z k l x y` is
`(v_k(x) · v_l(y))⁻¹ · (v_l(y) · v_k(x))`, where `v_k = v (pos k)`.

For `s : Spec B → Spec R` and `x, y ∈ B`, `lineEval s x y : R[S][T] → B` is the ring
map that restricts to the ring map `R → B` of `s` on `R` and sends `S ↦ x` and
`T ↦ y`.

## Statement

`LocalSplitUniversalCommutatorStatement.{u}` concerns:

- a commutative ring `R`, a finite type `I` and a type `J`, all in universe `u`;
- a group scheme `G` over `Spec R` and a coordinate split torus
  `i : T_I → G`;
- exponent characters `ch : J → I → ℤ` and a family `u : J → (𝔾ₐ ⟶ G)`;
- index families `neg : Fin m → J` and `pos : Fin n → J`.

It assumes that the underlying scheme morphism of `cellMap i u neg pos` is an open
immersion, and that `u` is torus equivariant with characters `ch`
(`TorusEquivariant i ch u`). It also assumes a cocharacter `ν : I → ℤ` with
`coPairing (ch (neg k)) ν < 0` for every `k` and `0 < coPairing (ch (pos k)) ν` for
every `k`.

The conclusion is that for all positions `k`, `l` (with no order condition) there
is `E : Fin n → R[S][T]` with two properties:

1. **Specialization.** For every commutative ring `B : Type u`, every
   `s : Spec B → Spec R` and all `x, y ∈ B`,
   `posComm u pos (Over.mk s) k l x y = orderedProduct u pos (Over.mk s) (fun q => lineEval s x y (E q))`;
2. **Weights.** For every position `p` and all `dS, dT : ℕ`, if the coefficient of
   `S ^ dS T ^ dT` in `E p` is nonzero, then `1 ≤ dS`, `1 ≤ dT` and
   `(dS : ℤ) • ch (pos k) + (dT : ℤ) • ch (pos l) = ch (pos p)` in `I → ℤ`.

The module proves this proposition at full universe as
`localSplitUniversalCommutator`.

The namespace `LocalSplitCell` also contains:

- `scaleS`, `scaleST` and `laurentST`: the substitution `S ↦ U ^ a S`,
  `T ↦ U ^ b T` from `R[S][T]` to `R[U, U⁻¹][S][T]`, and the coefficient inclusion
  `R[S][T] → R[U, U⁻¹][S][T]`. `scaleS_monomial`, `scaleST_monomial`,
  `coeff_coeff_scaleST`, `coeff_coeff_laurentST`, `scaleST_comp_C_C`, `scaleST_C_X`
  and `scaleST_X` compute them. `coeff_coeff_scaleST` says that the coefficient of
  `S ^ i T ^ j` in `scaleST a b E` is that of `E` times `U ^ (i a + j b)`;
- `val_zpow_isUnit_T`: the integer powers of the unit `U` of `R[U, U⁻¹]` are the
  monomials `T z`;
- `weight_eq_of_scaleST_eq`: if `scaleST a b E = U ^ c · laurentST E`, then every
  monomial `S ^ i T ^ j` that occurs in `E` has `i a + j b = c`;
- `lineBase R : Spec R[S][T] → Spec R`, and the predicate `IsUnivComm u pos k l E`.
  It says that over `lineBase R`, the commutator of `u_k(S)` and `u_l(T)` equals the
  ordered product with coordinates `E`;
- `exists_isUnivComm` and `IsUnivComm.unique`: existence of universal coordinates
  under the hypotheses above, and their uniqueness when the cell map is an open
  immersion;
- `lineEval`, `lineEval_C_X`, `lineEval_X`, `specMap_lineEval` and
  `specMap_ofHom_comp`: the evaluation map and its compatibility with the structure
  maps;
- `IsUnivComm.posComm_eq` and `IsUnivComm.posComm_map`: specialization of the
  universal identity along `lineEval s x y` and along any ring map out of `R[S][T]`;
- `posComm_transfer_of_isUnivComm`: let the big-cell map of `u` in `G` be an open
  immersion, and let the same `E` be universal both for `u` and for a family `u'`
  into another group scheme `H` over `Spec R`. Then over every ring over `R`, each
  expression `posComm u … k l x y = P(e)` in `G` gives
  `posComm u' … k l x y = P'(e)` in `H`;
- `IsUnivComm.eval_zero`, `IsUnivComm.map_eval_zero` and `IsUnivComm.one_le`: the
  universal coordinates vanish at `T = 0` and at `S = 0`, so only monomials with
  `dS ≥ 1` and `dT ≥ 1` occur;
- `val_units_map_zpow`, `torusChar_cocharPoint_T`, `laurentLineBase`,
  `IsUnivComm.posComm_scaleST`, `IsUnivComm.posComm_laurent_conj`,
  `IsUnivComm.scaleST_eq` and `IsUnivComm.weight`: the torus-scaling argument below;
- `IsUnivComm.eq_zero_of_forall_ne` and `posComm_eq_one_of_forall_ne`: suppose no
  `dS, dT ≥ 1` satisfy `dS • ch (pos k) + dT • ch (pos l) = ch (pos p)`. Then the
  universal coordinate at `p` is zero, since by the weight condition no monomial can
  occur in it. If this holds for every position `p`, all coordinates are zero. Then
  the factors at `k` and `l` commute over every ring over `R`, because
  `P(0) = 1`;
- `commutatorRelations_of_isUnivComm`: let `G` be reductive with a fibrewise maximal
  coordinate split torus `i` and fibrewise root datum `P`. Take a base `b`, words `W`,
  and a family `u` whose simple-root members are root parametrizations with Weyl
  points. Let `neg` and `pos` enumerate the non-positive and the positive roots. If,
  for every pair of positions `k < l`, the Weyl families `weylFamily P W u` and
  `weylFamily P W u'` have the same universal coordinates, then
  `CommutatorRelations b W u u' pos` holds. The family `u'` maps into any group
  scheme `H` over `Spec R`. No hypothesis on `H` is needed.

## Proof

**Existence and specialization.** The imported `exists_posComm_eq_ring` applies over
the ring `R[S][T]` with structure map `lineBase R` and gives `E` with
`IsUnivComm u pos k l E`. For `s : Spec B → Spec R` and `x, y ∈ B`, the ring map
`lineEval s x y` satisfies `Spec.map (lineEval s x y) ≫ lineBase R = s`
(`specMap_lineEval`, from Mathlib's `Spec.map_preimage`). It sends `S` to `x` and `T`
to `y`. Pulling the universal identity back along it (imported `posComm_specHom`)
gives the specialization property.

**Axes.** Pull the universal identity back along `T ↦ 0`. The commutator becomes
`posComm … S 0`, which is `1` (imported `posComm_zero_right`), and `1 = P(0)`
(imported `orderedProduct_zero`). Uniqueness of coordinates (imported
`coord_eq_of_orderedProduct_eq`) gives `E_p(S, 0) = 0`. The same argument along
`S ↦ 0` with `posComm_zero_left` gives `E_p(0, T) = 0`. So every monomial that occurs
in `E_p` has `dS ≥ 1` and `dT ≥ 1`.

**Weights.** Fix a cocharacter `ν'`, and let `a`, `b`, `c` be the pairings of
`ch (pos k)`, `ch (pos l)`, `ch (pos p)` with `ν'`. Work over `R[U, U⁻¹][S][T]` with
structure map `laurentLineBase R`.

1. Pulling the universal identity back along `scaleST a b` shows that the commutator
   of `u_k(U ^ a S)` and `u_l(U ^ b T)` is the product with coordinates
   `scaleST a b (E q)` (`IsUnivComm.posComm_scaleST`).
2. Pull it back along `laurentST` instead, and conjugate by the torus point `ν'(U)`,
   the cocharacter point of the unit `U`. Its characters take the values
   `U ^ ⟨χ, ν'⟩` (`torusChar_cocharPoint_T`, from the imported
   `torusChar_cocharPoint`). The imported `torus_mul_posComm_mul_inv` and
   `torus_mul_orderedProduct_mul_inv` show that the same commutator is the product
   with coordinates `U ^ ⟨ch (pos q), ν'⟩ · laurentST (E q)`
   (`IsUnivComm.posComm_laurent_conj`).
3. Uniqueness of coordinates (imported `orderedProduct_pos_injective`) gives
   `scaleST a b (E p) = U ^ c · laurentST (E p)` (`IsUnivComm.scaleST_eq`).
4. Compare the coefficients of `S ^ dS T ^ dT`. By `coeff_coeff_scaleST`, the left
   side has `U ^ (dS a + dT b)` times the coefficient of `E p`, and the right side
   has `U ^ c` times the same coefficient. If that coefficient is nonzero, Mathlib's
   `AddMonoidAlgebra.single_left_inj` gives `dS a + dT b = c`
   (`weight_eq_of_scaleST_eq`).

Taking `ν' = Pi.single t 1` for every `t ∈ I` gives the equality
`dS • ch (pos k) + dT • ch (pos l) = ch (pos p)` coordinatewise (`IsUnivComm.weight`).
This step needs no sign condition on `ν'`.

**Transfer.** Suppose `posComm u … k l x y = P(e)` in `G` over `s : Spec B → Spec R`.
Write `x` and `y` as elements of `B`. Specialization gives
`posComm u … k l x y = P(E(x, y))`, so `e = E(x, y)` by the imported
`orderedProduct_pos_injective`. Specialization for `u'` then gives
`posComm u' … k l x y = P'(E(x, y)) = P'(e)`. For the Weyl families, the imported
`isRootParametrization_weylFamily` and `LocalSplitBigCell.isOpenImmersion_cellMap`
make the big-cell map of `weylFamily P W u` an open immersion. The transfer lemma
then gives `CommutatorRelations` for test rings over `R`.

## Provenance and scope

This is an internal derived result toward the Isomorphism Theorem over an arbitrary
local ring. In the proofs of the Isomorphism and Isogeny Theorems, the group law on
the product of the positive root groups is described by commutation relations. Their
structure constants are polynomial in the coordinates and are shown to depend only on
the pinned root datum (B. Conrad, *Reductive group schemes*, in *Autour des schémas
en groupes*, Panoramas et Synthèses 42–43, 2014, Proposition 5.1.14 with formula
(5.1.5), and Lemma 6.2.8; SGA 3, Exp. XXIII, 3.1–3.4). This module constructs the
universal polynomials of such commutators for positive cell factors, directly from
the open big cell. Their weight condition is an integral form of the shape of the
commutator formula. The construction and the torus-scaling proof of the weights are
explicit arguments of this module, not transcriptions of a published proof.

The module does not compute the polynomials `E_p`, and it does not show that they
agree for two groups with the same root datum. That comparison of structure
constants (Conrad, Lemma 6.2.8) remains open here, as do the negative simple
relations and the construction of Weyl-normalized simple-root data. The module does
not prove the local split Isomorphism Theorem.
