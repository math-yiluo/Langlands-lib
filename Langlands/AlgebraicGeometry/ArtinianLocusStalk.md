# Local maps factoring through a locally Artinian closed subscheme

Author: Worker 372.

This internal helper module proves that a local point of a scheme `X` at `x` which factors
through a locally Artinian closed subscheme kills a fixed power of the maximal ideal of the stalk
at `x`.

## Declarations

- `map_mem_maximalIdeal_pow`: a local homomorphism `ψ : R →+* S` of local rings maps
  `𝔪_R ^ c` into `𝔪_S ^ c`. Proof: `Ideal.map_pow` and `IsLocalRing.map_maximalIdeal_le`.
- `isArtinianRing_stalk`: every stalk of a locally Artinian scheme is an Artinian ring. It is a
  localization of the Artinian ring of sections over an affine open neighbourhood.
- `exists_maximalIdeal_pow_eq_bot`: the maximal ideal of such a stalk is nilpotent
  (`IsArtinianRing.isNilpotent_jacobson_bot`, with the Jacobson radical equal to the maximal ideal).
- `exists_uniform_pow_eq_bot`: let `j : Z ⟶ X` be a closed immersion with `Z` locally Artinian,
  and let `x : X`. There is one `c` such that `𝔪_{Z,z} ^ c = ⊥` for every `z` with `j z = x`.
  Since `j` is injective there is at most one such `z`.
- `map_eq_zero_of_factor`: assume the conclusion of `exists_uniform_pow_eq_bot` holds for `c`.
  Let `R` be a local ring and `φ : 𝒪_{X,x} ⟶ R` a local homomorphism. Suppose that
  `Spec.map φ ≫ X.fromSpecStalk x` factors as `g ≫ j` with `g : Spec R ⟶ Z`. Then `φ` kills
  `𝔪_{X,x} ^ c`.

## Proof of `map_eq_zero_of_factor`

`SpecToEquivOfLocalRing` describes morphisms `Spec R ⟶ X` from a local ring by a point and a
local map out of its stalk. Applied to `g ≫ j = Spec.map φ ≫ X.fromSpecStalk x`, it shows that
`g ≫ j` sends the closed point of `Spec R` to `x`. It also shows that `φ` equals
`Scheme.stalkClosedPointTo (g ≫ j)` after the stalk identification `ρ` (`stalkCongr`). So the
point `z = g (closedPoint R)` satisfies `j z = x`.
`Scheme.stalkClosedPointTo_comp` factors `stalkClosedPointTo (g ≫ j)` through the stalk map
`j.stalkMap z : 𝒪_{X,x} → 𝒪_{Z,z}`. That map is local, so it sends `𝔪_{X,x} ^ c` into
`𝔪_{Z,z} ^ c = ⊥`. Hence `φ a = 0` for every `a ∈ 𝔪_{X,x} ^ c`.

## Provenance

Internal, standard commutative algebra and scheme theory. These are the local consequences
of a finite (hence Artinian) locus that the lower bound in
`Langlands.AbelianScheme.FieldH1LowerBound` needs.
