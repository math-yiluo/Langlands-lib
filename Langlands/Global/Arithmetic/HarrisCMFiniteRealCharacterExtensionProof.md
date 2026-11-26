# Extending a finite real-subfield character to a CM field

`Langlands.Global.Harris.cmFiniteRealCharacterExtension` proves
`Langlands.Global.Harris.CMFiniteRealCharacterExtensionStatement` from
`Langlands.Global.Arithmetic.HarrisCyclicDescentCorrectionStatement`, for a CM
number field `E : Type u` in an arbitrary universe. Write `F` for
`maximalRealSubfield E` and `c` for `IsCMField.complexConj E`. Given a Hecke
character `η₀` of `F` with `η₀ ^ n = 1` for some `n > 0` and
`η₀.atInfinity = 1`, the theorem constructs a Hecke character `α` of `E` with
`α ^ m = 1` for some `m > 0`, with `α ∘ ideleClassInclusion = η₀`, and with
`α * α.complexConj = η₀ ∘ ideleClassNorm`.

The source is Michael Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210, proof of Lemma 1.6,
printed p. 189, PDF p. 13 (registered source `harris-1998-local-langlands`; arXiv TeX
`math_9611226v1.tex`, lines 766–789). Harris extends `η₀` as a character of the
compact group `E^×_A / E^× E_∞^×` from the closed subgroup coming from `F`, and
derives the product identity from `α(a) α(a^c) = α(N_{E/F}(a))`. The Lean proof
replaces the compactness and closed-subgroup argument by an explicit open
subgroup of finite index, built from the same arithmetic: fixed valuations and
the CM involution force the conjugate ratio of a principal factor to be a root
of unity, and a local condition at one finite place forces it to be one.

## Notation in the module

`ideleConj` is `ideleEquiv c.toRingEquiv`, the CM involution on the actual
ideles of `E`. `ideleConj_ideleConj` proves it is an involution,
`ideleConj_ideleInclusion` proves it fixes the image of `ideleInclusion` from
`F` (by `adeleInclusion_adeleEquiv` with the identity of `F`), and
`ideleConj_diagonalUnits` computes it on principal ideles.

## Local and place lemmas

- `exists_openSubgroup_subset`: every neighbourhood of one in the unit group of a
  finite completion contains an open subgroup. The completion is a
  nonarchimedean local field, its unit group is locally profinite, and the van
  Dantzig theorem `Langlands.Topology.LocallyProfiniteProof.vanDantzig` gives the
  subgroup.
- `exists_openSubgroup_pullback`: for a place `q` of `E` over a place `p` of `F`
  and a neighbourhood `t` of one in `F_pˣ`, there is an open subgroup `B` of
  `E_qˣ` whose preimage under the completed unit inclusion lies in `t`. This
  uses `CMHalfWeight.isEmbedding_completionUnitInclusion`.
- `mem_integralIdeles_of_ideleInclusion`: an idele of `F` whose inclusion is
  integral is integral. At each place `p` choose `placeAbove E p`; by
  `CMHalfWeight.ideleCoordinate_ideleInclusion` and
  `FiniteExtension.valuation_completionMap`, the valuation above is the
  valuation below raised to the positive ramification index.
- `nonempty_finitePlace`: the ring of integers is not a field, so it has a
  nonzero prime ideal.
- `unitCoordinate E w ζ` is the coordinate at `w` of the principal idele of a
  global unit `ζ`, and `unitCoordinate_injective` shows it is injective.
- `exists_torsion_separating`: there are a finite place `w₀` and an open
  subgroup `B₀` of `E_{w₀}ˣ` containing the coordinate of no root of unity other
  than one. The roots of unity form the finite group `Units.torsion E`; the
  coordinates of the nontrivial ones form a finite set not containing one, whose
  complement is a neighbourhood of one.

## The box lemma

`exists_integral_box` takes an open subgroup `U` of the ideles of a number field
containing the whole archimedean factor. It returns a finite set `I` of finite
places and neighbourhoods `t p` of one such that every integral idele whose
coordinates at the places of `I` lie in the `t p` belongs to `U`. The proof uses
the topological group isomorphism `SUnitIdeleTopology.productEquiv K ∅` between
the integral ideles and the product of the archimedean units with all local
valuation units. The preimage of `U` is a neighbourhood of one in this product,
so by `nhds_prod_eq`, `nhds_pi` and `Filter.mem_pi` it contains a box restricting
finitely many finite coordinates. An integral idele is its archimedean part,
which lies in `U`, times the idele with the same finite coordinates and trivial
archimedean part, which lies in the box.

## Finite index

`finiteIndex_map_of_isOpen` proves that the image in the idele classes of an open
subgroup `V` of the ideles containing the whole archimedean factor has finite
index. By `NormOneIdeleClass.exists_integral_mul_principal` every idele is an
integral idele times a principal idele times a representative of its class in
the finite group `IntegralIdeleClassQuotient`, finite by
`integralIdeleClassQuotientFinite`. By `exists_infinite_mul_mem_ideleBox` an
integral idele is an archimedean idele times an element of the compact set
`NormOneIdeleClass.ideleBox K 1` (`NormOneIdeleClass.isCompact_ideleBox`).
Finitely many translates `z V` cover this compact set. The classes of the
products `z * r`, for these `z` and the representatives `r`, then exhaust the
quotient of the idele classes by the image of `V`.

## The separating subgroup

Let `U` be an open subgroup of the ideles of `F` containing the archimedean
factor. `exists_separating_subgroup` constructs an open subgroup `W` of the
ideles of `E` with the following properties.

1. `W` consists of integral ideles and contains the whole archimedean factor.
2. `W` is stable under `ideleConj`.
3. If the principal idele of a root of unity `ζ` lies in `W`, then `ζ = 1`.
4. If `ideleInclusion r ∈ W` for an idele `r` of `F`, then `r ∈ U`.

Take `I` and `t` from the box lemma for `U`, and for `p ∈ I` take the open
subgroup `B p` of `exists_openSubgroup_pullback` at `placeAbove E p`. Let `W₀` be
the integral ideles whose coordinate at `w₀` lies in `B₀` and whose coordinate at
`placeAbove E p` lies in `B p` for each `p ∈ I`, and let `W` be the ideles `x`
with `x` and `ideleConj x` in `W₀`. Archimedean ideles and their conjugates
have trivial finite coordinates (`ideleCoordinate_ideleConj_infinite`), so they
lie in `W`. Property 4 combines `mem_integralIdeles_of_ideleInclusion`,
`CMHalfWeight.ideleCoordinate_ideleInclusion` and the box lemma.

## Descent

`mem_of_ideleInclusion_eq` is the arithmetic core. Suppose `U` also contains the
principal ideles of `F`, and `ideleInclusion y = diag(e) * w` with `e ∈ Eˣ` and
`w ∈ W`. Applying `ideleConj` and using `ideleConj_ideleInclusion` gives
`diag(c(e) / e) = w * (ideleConj w)⁻¹ ∈ W`. As `W` is integral,
`principalIdeleUnitCriterion` makes `c(e) / e` a unit of the ring of integers.
Its absolute value at every infinite place is one by
`IsCMField.infinitePlace_complexConj`, so it is a root of unity by
`Units.mem_torsion`, and property 3 gives `c(e) = e`. By
`IsCMField.complexConj_eq_self_iff`, `e` comes from `f ∈ Fˣ`, and
`ideleInclusion_diagonal` gives `ideleInclusion (y * diag(f)⁻¹) = w`. Property 4
puts `y * diag(f)⁻¹` in `U`, hence `y ∈ U`.

## Assembly

In `exists_extension`, let `U` be the preimage in the ideles of `F` of the kernel
of `η₀`. This kernel is open by `complexCharacterOpenKernel`, `U` contains the
archimedean factor because `η₀.atInfinity = 1`, and it contains the principal
ideles. Let `N` be the image in the idele classes of `E` of `W ⊔ U'`, where `U'`
is the image of `U` under `ideleInclusion`. It is open, being the image of an
open subgroup under the open quotient map, and it has finite index by
`finiteIndex_map_of_isOpen`. `character_eq_one_of_mem` shows that every idele
class of `F` whose inclusion lies in `N` is in the kernel of `η₀`: a
representative `y` satisfies `ideleInclusion y = w * ideleInclusion u * diag(e)`
with `w ∈ W` and `u ∈ U`, and the descent lemma applied to `y * u⁻¹` gives
`y ∈ U`. `Langlands.Topology.exists_character_of_open_finite_quotient`, with
exponent the index of `N` (`Subgroup.pow_index_mem`), then gives a continuous
character `α` of the idele classes of `E` with `α ^ [C_E : N] = 1` and
`α ∘ ideleClassInclusion = η₀`.

`ideleClassInclusion_ideleClassNorm` proves that the inclusion of the norm of an
idele class `x` of `E` is `x * ideleClassComplexConj x`. It applies
`ideleClassNormGaloisProduct` to the quadratic Galois extension `E / F`, whose
automorphism group is `{1, c}` since it has two elements and
`IsCMField.complexConj_ne_one`. Then `mul_complexConj_eq` evaluates
`α x * α (ideleClassComplexConj x) = α (ideleClassInclusion (ideleClassNorm x))
= η₀ (ideleClassNorm x)`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
