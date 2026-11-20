# The actual opposite-radical level-volume bound

`Langlands.HarishChandraSchwartz.RationalOppositeLevelSetMeasureBoundStatement.{u}`
states Waldspurger's Lemma II.4.1 for actual rational points. Let `F` be a
nonarchimedean local field with residue cardinality `q`, `G` a connected
reductive affine group of finite type, `i` a maximal split torus, `ν` a generic
cocharacter, and `ζ` standard for `J`. At the supplied compact open `K0` assume
`SimultaneousStandardBasisAt i ν K0` and `FiniteCartanCovering F i ν K0`.

The bound applies to each compact open minimal Iwasawa factor `K`, each Haar
measure `μ` on `U = oppositeUnipotent i ζ`, and each measurable integer function
`L` identifying the actual Iwasawa half-weight by

```text
w(u) = q^(-L(u)/2),
w(u) = iwasawaWeight hPK (rationalMinimalModulus i ν) u.
```

The conclusion `LevelSetMeasureBound μ L q` gives real constants `C` and `d`
such that for all natural `n ≥ 1`,

```text
μ {u | L(u) = n} ≤ ofReal (C * q^(n/2) * n^d).
```

The source takes `C > 0` and `d` natural. The Library's real-constant formulation
suffices for the subsequent convergence argument. The supplied function `L`
indexes the intrinsic levels of the minimal modulus, and the conclusion
estimates their Haar volumes on the inverse-cocharacter radical.

Waldspurger fixes a special compact and obtains the bound using contraction,
the opposite-cell coefficient integral, and the spherical upper bound of
Lemma II.1.1. The formulation for an arbitrary compact open Iwasawa factor is
derived. The two compact factors give comparable half-weights by
`exists_iwasawaWeight_le_mul` in both directions. For integer levels this bounds
the difference between their indices. A bounded number of neighboring positive
levels obey the same exponential and polynomial bound after increasing the
constant. The remaining levels are contained in a compact height sublevel by
the modulus-height comparison. Changing Haar normalization rescales the constant.
The statement uses the structural inputs supplied by the downstream
`RationalUnipotentWeightIntegrabilityStatement`.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), Lemma II.4.1, printed pp. 259–261.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
