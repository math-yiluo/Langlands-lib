# Orthogonality of wave packets of non-associate parabolics on `G(F) \ G(𝔸)`

Module `Langlands.Global.AdelicNonAssociateWavePacketOrthogonality` states Lapid's
Proposition 2 in the case `Ω(P, P') = ∅` and proves it from the published
`Langlands.Global.WavePacketInnerProductStatement` (Lapid's Proposition 2 in general), which
the theorem takes as a hypothesis. It does not prove `WavePacketInnerProductStatement`.

| Declaration | Kind | Provenance |
| --- | --- | --- |
| `IsParabolicWavePacket` | definition | Lapid 2011, §3, p.314 (`W_P`, `Θ_{P,φ}`), in the data of `WavePacketInnerProductStatement` |
| `NonAssociateWavePacketOrthogonalityStatement` | statement | Lapid 2011, Proposition 2, (4), with `Ω(P, P') = ∅` |
| `weylParameterSet_eq_empty_of_not_weylConjugation` | theorem (proved) | internal |
| `nonAssociateWavePacketOrthogonality_of_innerProduct` | theorem (proved) | derived from `WavePacketInnerProductStatement` |

It is a step toward `Langlands.Global.RelativeWavePacketOrthogonalityStatement`,
the corresponding statement on `[G] = A_G G(F) \ G(𝔸)` with parameters in `i(𝔞_M^G)^*`. The
passage from `G(F) \ G(𝔸)` to `[G]` is not part of this module.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated Eisenstein series*, Clay
Math. Proc. 13 (2011), registered as `lapid-2011-asymptotic-inner-product-truncated-eisenstein`
(volume PDF page = printed page + 9).

- §2, printed pp.311–312 (PDF pp.320–321): `A^2_P`, the Eisenstein series `E_P(g, φ, λ)`, which
  converge for `Re λ` sufficiently regular, and the intertwining operators `M(w, λ)` for
  `w ∈ Ω(P, Q)`; `Ω(P, Q)` is taken from Arthur 1980.
- §3, printed p.314 (PDF p.323): `W_P` is the space of compactly supported smooth functions on
  `i𝔞_P^*` with values in a finite-dimensional subspace of `A^2_P` whose Eisenstein series are
  smooth on `i𝔞_P^*`; `Θ_{P,φ}(g) = ∫_{i𝔞_P^*} E_P(g, φ(λ), λ) dλ`. Proposition 2: for
  `φ ∈ W_P`, `Θ_{P,φ} ∈ L²(G \ G(𝔸))`, and for `φ' ∈ W_{P'}`
  `(Θ_{P,φ}, Θ_{P',φ'}) = ∫_{i𝔞_P^*} ∑_{w ∈ Ω(P,P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ` (4).

When `Ω(P, P')` is empty the sum in (4) is empty and the inner product is `0`.

## `IsParabolicWavePacket`

`IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ`, for a presented parabolic
`p : P → G` with Levi `l`, subgroup `iU`, presentation `r` and `hK : IsIwasawaCompact p K`,
says: there are coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, finitely many `v j ∈ A^2_P`
(`IsSquareIntegrableInducedForm`), smooth compactly supported `c j : ℝⁿ → ℂ`, and functions
`E j` on `X^*(P) ⊗ ℂ` with one set `D ⊇ i𝔞_P^*` such that each `λ ↦ E j λ g` is meromorphic in
coordinates with domain of holomorphy `D` and `E j` equals `hK.eisensteinSeries (v j)` for
`Re λ` sufficiently regular, and
`Θ(g) = ∫ ∑ j, c j x · E j (i e(x)) g d(spectralMeasure n)(x)`.

These are exactly the conditions that `WavePacketInnerProductStatement` imposes on each of its
two wave packets, and `Θ = Θ_{P,φ}` for `φ(i e(x)) = ∑ j, c j x · v j` (Lapid's `W_P`; the
Eisenstein series of the values of `φ` are holomorphic near `i𝔞_P^*` because the `E j` are).
The predicate is `IsRelativeWavePacket` (module `Langlands.Global.AdelicParabolicSpectrum`)
with coordinates on all of `X^*(P) ⊗ ℝ` in place of `relativeParameterSpace p`, and it is the
data part of `IsWavePacket` (module `Langlands.Global.AdelicWavePacketCompletenessReduction`) for
one fixed presented parabolic instead of an existentially quantified one. Fixing the parabolic is
what the orthogonality statement needs: its hypothesis is about the Levi subgroups of the two
given parabolics.

## `NonAssociateWavePacketOrthogonalityStatement`

Data: a number field `F : Type`; `G` with `IsAffineHom G.X.hom`, `IsAffine G.X.left`,
`LocallyOfFiniteType G.X.hom` and `IsConnectedReductive G`; two presented parabolics
`(P, M, U, A, p, iU, l, a, r, hA, hT)` and `(P', M', U', A', p', iU', l', a', r', hA', hT')`
with the instance arguments of `WavePacketInnerProductStatement` (except
`IsClosedImmersion (iU ≫ p)`, which follows from the radical hypothesis) and geometric
unipotent radicals `iU`, `iU'`; a subgroup `K` with `IsIwasawaCompact p K`,
`IsIwasawaCompact p' K` and `IsMaximalCompactSubgroup F G K`; `rho` with
`IsClosedSubgroup rho`; `hsmooth`, `hcalc`.

Hypothesis: no rational point `w` of `G` and no `c : M' ⟶ M` satisfy
`IsWeylConjugation p l p' l' w c`.

Conclusion: for all `Θ`, `Θ'` with `IsParabolicWavePacket` for `P` and `P'`, and `μG` the
quotient of Mathlib's Haar measure on `G(𝔸)` by counting measure on `G(F)`
(`LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) _ Measure.haar`, the measure of
`WavePacketInnerProductStatement`), `y ↦ Θ(y.out)` and `y ↦ Θ'(y.out)` are in `L²(μG)` and
`∫ y, Θ y.out * conj (Θ' y.out) ∂μG = 0`.

Correspondence. Lapid's `Ω(P, P')` is enumerated in the Library by `weylParameterSet p l p' l' π'`
(module `Langlands.Global.AdelicInducedInnerProduct`), the set of maps `λ ↦ wλ` given by pairs
`(w, c)` with `IsWeylConjugation p l p' l' w c`. The hypothesis says that there is no such
pair, so this set is empty for every Levi projection `π'`. Lapid works with standard parabolics
and their standard Levi subgroups; like `WavePacketInnerProductStatement`, the statement here
allows presented parabolics standard for possibly different minimal parabolics and any maximal
compact `K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)`; the Markdown of
`Langlands.Global.AdelicWavePacketInnerProductStatement` ("Regions and parabolics", "The compact
subgroup") explains the reduction to Lapid's setting. The statement asserts nothing
about associate pairs.

## Proof of `nonAssociateWavePacketOrthogonality_of_innerProduct`

`weylParameterSet_eq_empty_of_not_weylConjugation`: an element of
`weylParameterSet p l q l' π'` comes with a pair `(w, c)` satisfying
`IsWeylConjugation p l q l' w c`, which the hypothesis excludes.

The theorem `nonAssociateWavePacketOrthogonality_of_innerProduct` takes
`WavePacketInnerProductStatement` and proves `NonAssociateWavePacketOrthogonalityStatement`.
After unpacking the two `IsParabolicWavePacket` hypotheses, it supplies the remaining data of
`WavePacketInnerProductStatement`:

1. the instances `IsClosedImmersion (iU ≫ p)` and `IsClosedImmersion (iU' ≫ p')`, from
   `IsClosedSubgroup.comp` and the closed-subgroup part of the radical hypotheses;
2. a Levi projection `π' : P' ⟶ M'` with `l' ≫ π' = 𝟙 M'`, from
   `IsRationalLeviSubgroup.exists_unipotentRadical_retraction` applied to
   `r'.isCompatible.levi`;
3. a Haar measure `μM'` on `M'(𝔸)` with `IsIwasawaCompatibleMeasure`, from the published
   theorem `iwasawaCompatibleMeasureExistence`;
4. the weight `β'`, the normalized bump function `ContDiffBump.normed volume` with radii `1`
   and `2` on `ℝ^{n'}`, which is continuous, compactly supported and has integral `1`;
5. the enumeration of `Ω(P, P')` by the empty type `T = Empty` with `m = 0`, empty families
   `w`, `cw`, `ψ`, `coeff` and `DM = Set.univ`. The injectivity and all hypotheses indexed by
   `T` hold vacuously; the surjectivity onto `weylParameterSet p l p' l' π'` holds because that
   set is empty.

`WavePacketInnerProductStatement` then gives the two `L²` memberships and the inner product as
the integral over `ℝⁿ` of a sum indexed by `Empty`, which `simp` evaluates to `0`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

- The theorem is conditional on `WavePacketInnerProductStatement`, which is not proved in the
  Library.
- The statement is on `G(F) \ G(𝔸)` with parameters in all of `i𝔞_P^*`. The statement on `[G]`
  with parameters in `i(𝔞_M^G)^*`, `RelativeWavePacketOrthogonalityStatement`, needs in
  addition the comparison between the two quotients and the two kinds of wave packets; this
  module does not provide it.
