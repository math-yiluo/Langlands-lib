# The kernel of a torus map with even cocharacter image

Authors: Worker 146.

This internal helper unit supports the proof of
`Langlands.GroupScheme.Quaternionic.SpinKernel.SpinKernelGeneratorStatement`
(Task 5870). It contains the lattice part of the following standard fact.
Let `t : T → 𝔻` be a map from a split torus to the split diagonal torus
`𝔻 = 𝔾_m^l` whose cocharacter image is the even-sum lattice. Then the kernel of
`t` is the image of `μ₂` under a cocharacter `c` with `t ∘ c = 2 e_{i₀}`.
This is the familiar description of the kernel of `Spin → SO` on maximal tori.
The unit is derived from the Library's lattice APIs and cites no outside source.

## Hypotheses

`k` is an arbitrary field, `l` a finite type, `T` a commutative group scheme over
`Spec k`, and `t : T ⟶ 𝔻` a map into
`splitTorus.commGroupScheme (Spec k) (ULift l)`. Cocharacter coordinates are taken
with `GeneralLinear.cocharacterCoordEquiv l k`. The structure
`EvenImage T t c i₀` bundles four hypotheses on `t`, a cocharacter `c` of `T` and
an index `i₀ : l`:

- `injective`: pushforward `ν ↦ ν ≫ t` is injective on cocharacters;
- `even`: every pushed-forward cocharacter has even coordinate sum;
- `exists_single_sub`: every vector `eᵢ - e_{i₀}` is the image of some cocharacter;
- `coord_c`: the image of `c` is `2 e_{i₀}`.

Together these say that `t_*` is an isomorphism from `X_*(T)` onto the even-sum
lattice, and that `c` is the preimage of `2 e_{i₀}`. The results that use characters
also assume `IsSplitTorus T.toGrp`.

## Lattice constructions

- `halfForm f h` is half of a `ℤ`-linear form `f` whose values are all even.
  `two_mul_halfForm` records `2 * halfForm f h x = f x`.
- `vector_decomp` writes an integer vector `v` with coordinate sum `2s` as
  `∑ᵢ vᵢ (eᵢ - e_{i₀}) + s · 2e_{i₀}`.
- `coordSum t` is the linear form `ν ↦ ∑ᵢ (t_* ν)ᵢ` on `X_*(T)`.
- `EvenImage.halfSum` is half of `coordSum t`. Its value on `c` is one
  (`halfSum_c`).

## The half-sum character

The Library's perfect lattice pairing of a split torus
(`IsSplitTorus.isPerfPair_latticePairing`) makes every linear form on `X_*(T)` the
pairing with a unique character. `EvenImage.halfChar hT` is the character that
pairs to `halfSum` (`latticePairing_halfChar`). `character_ext` is the
injectivity of characters into linear forms. Proved results:

- `latticePairing_comp`: the pairing of `t ≫ φ` with `ν` is the coordinate dot
  product of `φ` and `t_* ν` (from `GeneralLinear.latticePairing_coord`).
- `c_comp_halfChar`: `c ≫ halfChar = 𝟙 𝔾_m`, since the pairing value is one.
- `two_smul_halfChar`: twice `halfChar` is the pullback by `t` of the
  coordinate-sum character `(1, …, 1)` of `𝔻`.
- `exists_eq_comp_add`: every character `ψ` of `T` is `t ≫ φ + ⟨ψ, c⟩ · halfChar`
  for some character `φ` of `𝔻`. Its coordinates are `φᵢ = ⟨ψ, νᵢ⟩`, where `νᵢ`
  is a preimage of `eᵢ - e_{i₀}`. The proof checks the equality on every
  cocharacter `w`. By injectivity and `vector_decomp`,
  `w = ∑ᵢ (t_* w)ᵢ νᵢ + halfSum(w) c`.

## Points of the kernel

All results hold on arbitrary relative test objects `U` over `Spec k`.

- `EvenImage.exists_comp_eq`: if a point `x : U ⟶ T` satisfies
  `x ≫ t = 1`, then `u = x ≫ halfChar` satisfies `u * u = 1` and
  `u ≫ c = x`. The square of `u` is the value at `x` of the pullback of the
  coordinate-sum character by `t`, which is one. For `u ≫ c = x`, the
  Library's character separation for split tori
  (`IsSplitTorus.point_ext_characters`) reduces the claim to each character
  `ψ`. There `exists_eq_comp_add` gives `ψ(x) = u^{⟨ψ, c⟩}`, and the left side
  is `u^{⟨ψ, c⟩}` by `eq_gmEndEquiv_zsmul` and `Gm.comp_zsmul_id`.
- `EvenImage.comp_injective`: the map `u ↦ u ≫ c` on points of `𝔾_m` is
  injective, because composing with `halfChar` recovers `u`
  (`c_comp_halfChar`).

So, on every test object, `u ↦ u ≫ c` is a bijection from the square roots of
unity onto the points of `T` that `t` sends to one, and its inverse is
`x ↦ x ≫ halfChar`. Nothing here assumes the characteristic of `k`.

The half-form helpers reuse `IndexTwoKernel.halfForm` and
`IndexTwoKernel.two_mul_halfForm`; the compatibility names preserve the
original interface without duplicating the integer-halving construction.
