# Stable-pairing asymptotics with a threshold controlled by a dimension

Module `Langlands.Representation.Jacquet.StablePairingDimensionThreshold`, namespace
`Langlands.Jacquet.StablePairingData`. Helper module of the proof of
`Langlands.HarishChandraSchwartz.RationalOrbitConstantTermThresholdStatement`
(entry module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermThresholdProof`).

## Mathematical content

This is the abstract source of uniformity in Waldspurger's Proposition I.4.3 and I.5
(J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, literature id
`waldspurger-2003-plancherel`, printed pp. 245–247, PDF pp. 11–13). In the proof of the I.5
analogue of Théorème I.4.1, Waldspurger needs one compact open subgroup `U_c` of `U` that kills
all of `V^H ∩ Ker(j_P)` (his property (3), printed p. 246), and obtains it from the finite
generation of `V^H ∩ Ker(j_P)` over the Noetherian base ring. Here the same uniformity is
obtained from Casselman's Fitting argument instead: the exponent of the compression by `D.g⁻¹`
that kills the relevant power kernels depends only on a bound `d` for the dimension of the
`K`-fixed vectors. This module proves the abstract step; the uniformity in the representation
is obtained only in the standard specialization (module `StandardCasselmanDimensionThreshold`),
see the remark after the statement.

Let `D` be the Library's stable-pairing data (`StablePairingData`), `ρ` a smooth representation
admitted by `D` (`D.Admits ρ hρ`), `b` a stable pairing, and `K` a good subgroup such that the
`K`-fixed vectors are finite-dimensional of dimension at most `d`. Write `C(a)` for the
compression `v ↦ e_K ρ(a) v` on `K`-fixed vectors (`compressedAction`).

- `powerKernelSup_le_ker_pow`: the union of the kernels of the powers of `C(g)` is contained in
  the kernel of `C(g)^d` (Mathlib's `Module.End.ker_pow_eq_ker_pow_finrank_of_le` and
  `Module.End.ker_pow_le_ker_pow_finrank`).
- `IsStablePairing.asymptotics_of_finrank_le`: for `K`-fixed `v` and `ℓ`, and every `a` with
  (i) `a⁻¹ (K ∩ N) a ⊆ K`, (ii) `C(a)` commuting with `C(D.g⁻¹)`, and (iii)
  `C(a) = X ∘ C(D.g⁻¹)^d` for some endomorphism `X`, one has
  `ℓ(ρ(a) v) = b(ǰ(ℓ), j(ρ(a) v))`.

Condition (i) is a condition on `a`, `K` and `D.N` only. Conditions (ii) and (iii), however,
are conditions on the compressions `C(a)` and `C(D.g⁻¹)` of the given representation `ρ`, and in
general they depend on `ρ` even when `D`, `a`, `K`, `d` and `dim V^K` are fixed. (For example,
take the discrete group `S₃` with `N = Nbar = M = K = {1}`, `D.g = (12)`, `a = (23)` and `d = 2`:
for both the two-dimensional trivial representation and the two-dimensional standard
representation, `C(x) = ρ(x)` and (iii) holds with `X = ρ(a)`, but (ii) holds only for the
trivial one.) None of the conditions depends on `v`, `ℓ` or `b`. Compared with the Library's
`exists_finset_asymptotics_of_commute`, the gain is that the finite set of conjugation
conditions produced from the particular vector `v` is replaced by the fixed exponent `d`.

The uniformity in the representation is supplied by the standard specialization
`exists_dimension_threshold_standardCasselmanPairing` (module
`StandardCasselmanDimensionThreshold`): there `a = ϖ^λ` is a dominant lattice point, and (ii) and
(iii) are derived from facts about the group alone, namely the Iwahori factorization of `K`
relative to `P_∅`, the contraction properties of dominant lattice points, commutativity of the
lattice, and the factorization `ϖ^λ = ϖ^{λ − d z} g^d` (Casselman's multiplicativity of the
compressions on dominant elements). Those facts hold for every admissible `ρ` with
`dim V^K ≤ d` simultaneously, so one threshold serves all such `ρ`.

## Proof of the main lemma

As in the Library's `IsStablePairing.exists_finset_asymptotics_of_commute`, choose a stable
`t` with `j(t) = j(v)` (`exists_stable_mk_eq`). Then `v − t` lies in the kernel of the Jacquet
map on `K`-fixed vectors, hence in the power kernels of `C(D.g⁻¹)` (`Admits.lower_kernel`), hence
in the kernel of `C(D.g⁻¹)^d` by the first lemma. By (iii), `C(a)(v − t) = 0`, so
`e_K ρ(a) v = C(a) t`. By (ii), `C(a) t` lies in the stable image (`mem_stableImage_of_commute`),
where `b` computes the pairing (definition of `IsStablePairing`). Finally `ℓ` is `K`-fixed
(`smoothDualPairing_averageMap`) and `ρ(a) v` is fixed by `K ∩ N` by (i), so the class of its
`K`-average pairs like its own class (`IsStablePairing.apply_mk_averageMap`). The only
difference from the Library's lemma is that the finite set of conjugation conditions is replaced
by condition (iii).

## Check

Development check: 0 errors, 0 warnings.
