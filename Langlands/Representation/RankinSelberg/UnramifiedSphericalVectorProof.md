# Proof: normalized spherical Whittaker vectors

Author: Worker 1797. Module
`Langlands.Representation.RankinSelberg.UnramifiedSphericalVectorProof`.

The theorem `Langlands.RankinSelberg.unramifiedSphericalVector` proves the published
proposition `Langlands.RankinSelberg.UnramifiedSphericalVectorStatement.{uF, uV}` of
`Langlands.Representation.RankinSelberg.UnramifiedPairStatement`, unchanged, with
independent field and carrier universes. The helper lemmas are in the namespace
`Langlands.RankinSelberg.UnramifiedWhittaker`; the helper modules
`UnramifiedWhittakerCells` and `UnramifiedRecursionUniqueness` are described in their
own Markdown files.

## What is proved

For every prime `p`, every `F : PadicField p`, every `r`, every complex
representation `π` of `GL_(r+1)(F)` (carrier in universe `uV`) and every unitary
additive character `ψ` with conductor `O` (`HasIntegerConductor ψ`): if `π` is generic
for `ψ` (irreducible, admissible, with a nonzero standard Whittaker functional) and has
a nonzero `GL_(r+1)(O)`-fixed vector, then

- for every nonzero `ℓ` in `glFunctionals ψ r π`, the type `SphericalTest π ℓ` has an
  element `w` with every other element equal to `w`;
- the same for every nonzero `ℓ` in `glInverseFunctionals ψ r π` (character `ψ⁻¹`).

`SphericalTest π ℓ` is the published type of right `GL_(r+1)(O)`-invariant vectors
`W` of the coefficient model of `ℓ` with `W(1) = 1`.

## Correspondence with the source

Jacquet–Shalika, *On Euler products and the classification of automorphic forms II*,
§1.3, printed page 780 (registered as `jacquet-shalika-1981-euler-products-ii`): "up
to scalars there exists exactly one element `W_0` in `𝒲(π; ψ)` invariant under `K` on
the right. Moreover `W_0(e) ≠ 0`". The source cites Casselman–Shalika and Shintani for
this. The Lean proof follows Shintani's mechanism: the spherical Hecke operators act
on the spherical line by scalars, the minuscule ones give a triangular recursion for
the values on the dominant torus, and the recursion determines the function from its
value at the identity. Uniqueness up to scalars is `sphericalFixedLine`.

## Hecke scalars on a fixed line (section `Line`)

Here `ρ` is any complex representation of `GL_(r+1)(F)` (canonical topology), and the
fixed space `ρ^K`, `K = sphericalSubgroup F r = GL_(r+1)(O)`, is assumed spanned by a
given vector `v` (`∀ w ∈ ρ^K, ∃ c, c • v = w`).

- `exists_labelledRep_sum_eq_smul`: for smooth `ρ` and each `i : Fin (r + 2)`,
  `∑_α ρ(x_α) v = c • v` for some `c`, where `x_α` runs over the published labelled
  representatives `labelledRep ϖ (residueLift F) α` of the double coset
  `K diag(ϖ,…,ϖ,1,…,1) K` (`ϖ` the canonical uniformizer). The published
  `standardHecke_cornerAction_eq_sum` identifies this sum with the integrated action of
  `standardHeckeElement F r i`, which lies in `ρ^K`.
- `exists_central_smul`: an element `z` commuting with all of `GL_(r+1)(F)` sends `v`
  into `ρ^K`, hence to a multiple of `v`.
- `torus_const_commute`: `torus ϖ (fun _ => c)` is central.

## Functions satisfying the Hecke relations (section `Functions`)

`eq_zero_of_hecke_relations`. Let `θ` be integrally trivial and nontrivial on
`1 + x E_(i,i+1)` for some `x ∈ ϖ⁻¹ O`, for every `i`. Let `f` be `θ`-equivariant and
right `K`-invariant, suppose that for each `1 ≤ k ≤ r + 1` there is `c` with
`∑_α f(x · x_α) = c f(x)` for all `x`, that `x ↦ f(x ϖ⁻¹)` is a multiple of `f`, and that
`f(1) = 0`. Then `f = 0`.

Proof. Put `d lam = f(ϖ^lam)`. It vanishes off antitone `lam`
(`eval_torus_eq_zero_of_not_antitone`), `d 0 = f 1 = 0`, and by
`sum_eval_torus_mul_labelledRep` it satisfies `SatisfiesHeckeRecursion` with weights
`q^(#radical pairs of S)` (`q` the residue cardinality, nonzero). So
`eq_zero_of_satisfiesHeckeRecursion` gives `d = 0` on partition exponents. The central
relation gives `d (lam - j) = c'^j d lam` for the constant vector `j`, and every antitone
`lam` is a partition exponent minus a constant vector, so `d = 0` everywhere. Finally
every `g` is `u ϖ^lam k` (published `exists_eq_unipotentPart`), so
`f g = θ(u) d(lam) = 0`.

## Matrix coefficients of spherical vectors (section `Coefficients`)

- `coefficient_eq_zero_of_eval_one`: if `π` is smooth, `π^K` is spanned by each of its
  nonzero vectors, `ℓ` is a `θ`-equivariant functional (with `θ` as above) and
  `v ∈ π^K` has `ℓ v = 0`, then `ℓ(π g v) = 0` for all `g`. For `v ≠ 0`, the function
  `g ↦ ℓ(π g v)` satisfies the hypotheses of `eq_zero_of_hecke_relations`: the coset sum
  and central relations follow from `exists_labelledRep_sum_eq_smul` and
  `exists_central_smul` after applying `w ↦ ℓ(π x w)`.
- `mem_fixedVectors_of_model`: if the coefficient map of `ℓ` is injective and the
  coefficient function of `v` is right `K`-invariant, then `v ∈ π^K`.
- `existsUnique_sphericalTest`: for irreducible smooth `π`, nonzero `ℓ` and `π^K ≠ 0`,
  `SphericalTest π ℓ` has exactly one element. The coefficient map is injective
  (published `modelEquiv`). Existence: for nonzero `v ∈ π^K` the model vector of `v` is
  spherical, and its value `ℓ v` at the identity is nonzero, since otherwise `v = 0` by
  the previous lemma; the published `normalizeSphericalTest` rescales it. Uniqueness:
  two tests come from `u, u' ∈ π^K` with `ℓ u = ℓ u' = 1`; then `ℓ(u' - u) = 0`, so
  `u' - u = 0`.

## Characters of conductor `O` (section `Conductor`)

- `standardCharacter_adjacentUnit`: the standard character takes the value `ψ(x)` on
  `1 + x E_(i,i+1)`.
- `exists_conductor_witness`: if `ψ` has conductor `O`, then `ψ(x) ≠ 1` for some
  `x ∈ ϖ⁻¹ O`. Since `ϖ⁻¹ ∉ O`, the second clause of `HasIntegerConductor` gives an
  integral `y` with `ψ(ϖ⁻¹ y) ≠ 1`.
- `standardCharacter_nondegenerate`, `inverseStandardCharacter_nondegenerate`: hence
  both the standard character and its inverse satisfy the nondegeneracy hypothesis
  above. Integral triviality is the published `isIntegrallyTrivial_standardCharacter`
  and `isIntegrallyTrivial_inverseStandardCharacter`.

## The statement

`fixedLine_of_isGeneric`: an irreducible admissible `π` with `π^K ≠ 0` is bundled as an
`AutomorphicObject` (`SmoothRep.of π`), and the published `sphericalFixedLine` gives
`finrank π^K = 1`; hence `π^K` is spanned by each nonzero vector.

`unramifiedSphericalVector` unpacks genericity into irreducibility and admissibility
and applies `existsUnique_sphericalTest` twice, with `θ = standardCharacter ψ r` and
`θ = inverseStandardCharacter ψ r`. The functional hypothesis in `IsGeneric` is not
needed beyond what the statement already supplies (a nonzero `ℓ`).
