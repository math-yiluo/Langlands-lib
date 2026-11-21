# Herbrand's subgroup formula in either characteristic

This module contains three proposition definitions in
`Langlands.Ramification.Local`. They are statements only. Their proofs belong
to successor tasks. They use the following published constructions:

- the finite Herbrand functions `herbrandPhi`, `herbrandPsi` and the finite
  upper groups `upperRamificationGroup` from `Herbrand.GeneralFinite`;
- the absolute upper groups `absoluteUpperRamificationGroup` from
  `Herbrand.GeneralAbsolute`;
- `relativeIndex`, `galoisClosure` and `relativeHerbrandPsi` from
  `Herbrand.GeneralSubextension`.

None of the statements has a characteristic hypothesis.

## `FiniteHerbrandSubgroupFormula`

The base `K₀` carries `[Field K₀] [ValuativeRel K₀] [TopologicalSpace K₀]`,
the structure required by `LocalField.TopologicalData`. Fields `K`, `E` and `M`
form compatible towers \(K\to E\to M\), \(K_0\to K\to M\) and
\(K_0\to E\to M\), and \(M\) is finite over \(K_0\). One realization
`T : LocalField.TopologicalData K₀ M` supplies the integer ring of \(M\) for
both upper groups and both Herbrand functions.

The statement says that for every real \(u\) and every
\(\sigma\in\operatorname{Aut}_E(M)\), `σ.restrictScalars K` lies in
`upperRamificationGroup T K u` exactly when \(\sigma\) lies in
`upperRamificationGroup T E (herbrandPhi T E (herbrandPsi T K u))`. In
Serre's notation this is
\[
  H\cap G^{u}=H^{\varphi_{M/E}(\psi_{M/K}(u))},\qquad
  G=\operatorname{Aut}_K(M),\ H=\operatorname{Aut}_E(M),
\]
where \(H\) is embedded in \(G\) by restriction of scalars. The Library's finite
upper groups are subgroups of the full automorphism groups, so the statement
does not assume that \(M/K\) or \(M/E\) is Galois.

## `RelativeHerbrandPsiIndependence`

The base `K₀` is a nontrivially normed, ultrametric, complete and locally
compact field with a valuative relation. The hypothesis
`hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b` says that the relation
agrees with norm comparison. The field `K` is finite over `K₀`. The field `Ω` is a
separable closure of `K` (`[IsSepClosure K Ω]`) with compatible tower
\(K_0\to K\to\Omega\). The field `E : IntermediateField K Ω` is finite over
`K`. The field `M : FiniteGaloisIntermediateField K Ω` is any finite Galois
intermediate field, and `h` says that it contains the image of `E`.

The statement says that for every real \(u\),
`relativeHerbrandPsi K₀ K Ω hbase E u = relativeIndex K₀ K hbase M h u`. The
left side is \(\varphi_{N/E}(\psi_{N/K}(u))\) for the chosen normal closure
\(N\) of \(E/K\) in \(\Omega\). The right side is
\(\varphi_{M/E}(\psi_{M/K}(u))\), computed in the canonical realization of
\(M\) over the norm of \(K_0\). The `haveI` supplies the tower
\(K_0\to E\to\Omega\) by definitional equality of algebra maps, exactly as in
the definition of `relativeHerbrandPsi`.

## `AbsoluteHerbrandSubgroupFormula`

The data `K₀`, `hbase`, `K`, `Ω` and `E` are the same as in the previous
statement. The statement says that for every real \(u\ge -1\) and every
\(\tau\in\operatorname{Aut}_E(\Omega)\), `τ.restrictScalars K` lies in
`absoluteUpperRamificationGroup K₀ K Ω hbase u` exactly when \(\tau\) lies in
`absoluteUpperRamificationGroup K₀ E Ω hbase (relativeHerbrandPsi K₀ K Ω hbase E u)`.
Restriction of scalars identifies \(G_E=\operatorname{Aut}_E(\Omega)\) with a
subgroup of \(G_K=\operatorname{Aut}_K(\Omega)\) acting on the same \(\Omega\).
The statement is therefore
\[
  G_K^{u}\cap G_E=G_E^{\psi_{E/K}(u)}\qquad(u\ge -1).
\]

Both absolute groups use the published construction in the same \(\Omega\),
over the same base \(K_0\) and the same `hbase`. Each is the intersection of the
restriction preimages of the canonical finite upper groups of the finite Galois
intermediate fields. The second group needs three instances, supplied by
`haveI`:

- \(E\) is finite over \(K_0\) by transitivity;
- the tower \(K_0\to E\to\Omega\) holds by definitional equality;
- `IsSepClosure E Ω` holds because \(\Omega\) is separably closed, and
  \(\Omega/E\) is separable because \(\Omega/K\) is Galois
  (`IsGalois.tower_top_of_isGalois`).

For a nonarchimedean local field \(K\), either characteristic, the hypotheses
include \(K_0=K\) with `LocalGalois.localNormedField` and its norm comparison.
This is the choice made by `localRelativeHerbrandPsi` and
`localAbsoluteUpperRamificationGroup`.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979), Chapter IV, §3. The registered source is
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

- Proposition 15, printed p. 74 (PDF p. 81), proved p. 75: the transitivity
  formulas \(\varphi_{L/K}=\varphi_{K'/K}\circ\varphi_{L/K'}\) and
  \(\psi_{L/K}=\psi_{L/K'}\circ\psi_{K'/K}\).
- Remark 1, printed p. 75 (PDF p. 82): for an infinite Galois extension,
  \(G^v=\varprojlim G(L'/K)^v\) over the finite Galois subextensions \(L'\).
  An element lies in this limit exactly when each of its finite restrictions
  lies in the finite upper group. That is the intersection used by
  `absoluteUpperRamificationGroup`.
- Remark 2, printed p. 75 (PDF p. 82): for a subextension \(E\) of a finite
  Galois \(L/K\), \(\varphi_{E/K}=\varphi_{L/K}\circ\psi_{L/E}\), independently
  of \(L\) by Proposition 15. The inverse function is
  \(\psi_{E/K}=\varphi_{L/E}\circ\psi_{L/K}\), the relative index of
  `GeneralSubextension`. `RelativeHerbrandPsiIndependence` states this
  independence for the inverse function, with \(L\) ranging over the finite
  Galois intermediate fields of the fixed \(\Omega\).
- Remark 3, printed pp. 75–76 (PDF pp. 82–83): with the indexing
  \(G(t)=G_{t_L}=G^{t_{L'}}\) for \(G=G(L/L')\), a subgroup \(H\) satisfies
  \(H(t)=H\cap G(t)\). Take \(t_K=u\). Then \(t_M=\psi_{M/K}(u)\) and
  \(t_E=\varphi_{M/E}(t_M)\), which is `FiniteHerbrandSubgroupFormula`.
  `AbsoluteHerbrandSubgroupFormula` is the profinite form of Remark 3, using
  the definition of Remark 1 and the relative function of Remark 2. Serre does
  not state it separately.

Serre defines the Herbrand functions on \([-1,\infty)\), the image of
\(T_L\) in Remark 3. The finite statements here hold at every real argument, using
the Library's continuation of \(\varphi\) and \(\psi\) by the identity at
nonpositive arguments. The absolute statement keeps Serre's range
\(u\ge -1\). Serre's standing hypotheses in Chapter IV are complete discrete
valuations and separable residue extensions. They hold for finite extensions
of the locally compact base used in the last two statements, whose residue
fields are finite.

The Library proves p-adic analogues in `Langlands.Ramification.HerbrandBridge`
(`Herbrand.SubextensionProof`):

- `restrictScalars_mem_upperRamificationGroup_iff`;
- `relativeIndex_eq_of_le`;
- `restrictScalars_mem_upperGroupIn_iff`;
- `intermediateGaloisMap_mem_absoluteUpperRamificationGroup_iff`.

The statements here concern the characteristic-free definitions above.
