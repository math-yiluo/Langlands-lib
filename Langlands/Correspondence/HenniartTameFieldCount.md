# Wild inertia of a tame totally ramified extension and the fixed-point formula

This module derives the fixed-point formula `WeilTameFieldFixedPointStatement`
(module `Langlands.Correspondence.HenniartTameOrbitFormula`) from the Frobenius
parametrization of tame fields `TameWeilFrobeniusParametrizationStatement`, as
`weilTameFieldFixedPoint_of_parametrization`. Over a tame totally ramified
field `E` of degree `m`, the orbit formula with `m = 1` is transported to `K`:
wild inertia of `E` and of `K` agree, upper indices are rescaled by `m`, and
`q_E = q_K`. Compare H. Koch, *Bemerkungen zur numerischen lokalen
Langlands-Vermutung* (1984), registered as
`koch-1984-numerical-langlands-remarks`, §8, Lemma 8 (PDF p. 6), which counts
the representations attached to a fixed tame field with fixed restriction to
the first ramification group; the rescaling of upper indices is Herbrand's
theory of J.-P. Serre, *Local Fields* (1979), registered as
`serre-1979-local-fields`, IV §3, Propositions 12–15 and Remark 2 (printed
pp. 73–75, PDF pp. 80–82).

Throughout, `E` is a finite subextension of the algebraic closure of `K`,
`L = E.asPadicField`, `ι = intermediateWeilMap K E : W_L → W_K`, and the
hypotheses are `hdeg` (degree `m`), `hres` (residue degree one) and `hker`
(wild inertia of `K` lies in the image of `ι`).

## Herbrand function and upper groups

- `relativeHerbrandPsi_eq`: `ψ_{E/K}(v) = m v` for `v ≥ 0`. For every `v₀ > 0`
  the upper group `W_K^{v₀}` lies in wild inertia, hence in the image of `ι`
  (`intermediateWeilMap_range`), so the published
  `relativeHerbrandPsi_sub_eq_of_upperGroup_le` makes `ψ_{E/K}` affine on
  `[v₀, ∞)` with slope `e_L / e_K`, which is `m` by
  `PadicField.ramificationIndex_mul_extensionResidueDegree` and `hres`. Letting
  `v₀ → 0` and using continuity and `ψ_{E/K}(0) = 0` gives the formula.
- `map_mem_upperGroup_iff`: for `v > 0`, `ι w ∈ W_K^v` exactly when
  `w ∈ W_L^{m v}`, by the published `intermediateWeilEquiv_mem_upperGroup_iff`.
- `isClosed_weilWildInertia`, `degree_pos` and the instance
  `weilWildInertia_normal_field` are auxiliary.

## Wild inertia

- `map_mem_weilWildInertia`: `ι` maps wild inertia of `L` into wild inertia of
  `K`. The preimage of `P_K` is closed and contains every positive upper group
  of `L` (`map_mem_upperGroup_iff`), so it contains `P_L`
  (`wildIn_le_of_isClosed`, module
  `Langlands.Correspondence.HenniartTameOrbitCount`).
- `exists_weilWildInertia_preimage`: every element of `P_K` is the image of an
  element of `P_L`. The image of `P_L` is compact, hence closed (the Weil group
  is Hausdorff, `localWeilGroup_t2Space`), and it contains every positive upper
  group of `K`: such an element lies in `P_K`, hence (by `hker`) is `ι w`, and
  `w` lies in a positive upper group of `L`, hence in `P_L`.
- `wildHom`, `wildHom_bijective`, `wildIso` and `wildIso_apply`: `ι` restricts
  to an isomorphism of topological groups `P_L ≃ P_K`; it is inducing because
  `ι` is an embedding (`intermediateWeilMap_isEmbedding`), so its inverse is
  continuous (`Equiv.toHomeomorphOfIsInducing`).

## Classes

- `fieldW` transports wild classes of `L` to wild classes of `K` along
  `wildIso` (`classMap` of `Langlands.Correspondence.HenniartTameOrbitCount`);
  it is bijective (`fieldW_injective`, `fieldW_surjective`) and preserves rank.
- `fieldW_smul`: conjugation by `w ∈ W_L` corresponds to conjugation by `ι w`.
- `wildClassTrivialAt_fieldW`: for `v > 0`, a class is trivial at index `m v`
  over `L` exactly when its transport is trivial at index `v` over `K`.
- `mem_iff`: if `J` is an open normal subgroup of `W_K` with
  `range ι ∩ I_K = J` and `ι φ_L = ψ`, then a class `c` of `L` lies in
  `tameOrbitClasses L I_L r 1 j` and is fixed by `φ_L` exactly when
  `fieldW c` lies in `tameOrbitClasses K J r m j` and is fixed by `ψ`. Here
  `J`-fixed corresponds to `I_L`-fixed because `ι` maps `I_L` onto `J`
  (`intermediateWeilMap_mem_localInertia`), and
  `j / p^r < m v ↔ j / (p^r m) < v`.

## The fixed-point formula

- `inertiaOpenNormal F` is inertia as an open normal subgroup of the Weil group
  (`localInertia_isOpen`, `localInertia_normal`).
- `fixed_count`: under `hdeg`, `hres`, `p ∤ m`, `[I_K : J ∩ I_K] = m`,
  `range ι ∩ I_K = J`, and `ψ ∈ range ι` of degree one,
  `C_L(p^r, j) = (q_K - 1) · #{c ∈ tameOrbitClasses K J r m j : ψ • c = c}`.
  Wild inertia of `K` lies in `J` (`wildIn_le_of_coprime`), hence in the image
  of `ι`. The preimage `φ_L` of `ψ` has degree one
  (`intermediateWeilEquiv_degree` with `hres`). The orbit formula
  `TameOrbit.orbitFormula` over `L` with `m = 1` and `J = I_L`, with the open
  subgroups of `exists_index_of_parametrization` over `L`, gives
  `C_L(p^r, j) = (q_L - 1) · #(frobeniusStableTameOrbits L I_L r 1 j φ_L)`.
  Then `q_L = q_K` by `extensionResidueCardinality`; the `I_L`-orbits of
  `I_L`-fixed classes are single points, so the stable orbits correspond to the
  `φ_L`-fixed tame classes of `L`; and `mem_iff` with `fieldW` matches these
  with the `ψ`-fixed tame classes of `K`.
- `weilTameFieldFixedPoint_of_parametrization`:
  `TameWeilFrobeniusParametrizationStatement.{uK}` implies
  `WeilTameFieldFixedPointStatement.{uK, uW}`. For a datum `D` and `g ∈ I_K`,
  the field `E` indexed by the coset of `g` is tame totally ramified of degree
  `m` with residue degree one (the definition of
  `TameTotallyRamifiedExtensions`), `D.inertiaIntersection` gives
  `range ι ∩ I_K = D.kernel`, `D.cosetEquiv` gives the index `m`, and
  `D.frobenius_mem` places `ψ = g φ`, of degree one, in the image of `ι`.
