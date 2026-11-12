# The minimal modulus on `U₀(F)` and the lower bound of Lemma II.1.1 for the actual `Ξ`

Author: Worker 19, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiLowerBound`, namespace
`Langlands.HarishChandraSchwartz`. It is a companion of
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights` (same author and candidate), whose
definitions `rationalMinimalModulus` (`δ₀`) and `rationalXi` (`Ξ`) and whose setting and local
instances it uses.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`), printed page numbers:

- II.1, printed pp. 250–251: `Ξ(g) = ∫_K δ₀(m₀(kg))^{1/2} dk` with `g = u₀(g) m₀(g) k₀(g)`.
- Lemme II.1.1, printed p. 251, as quoted in the Library's `TemperedExponentCone.md`: "Il existe
  `C_1, C_2 > 0` et `d ∈ ℕ` tels que pour tout `m ∈ M̄_0^+`, on ait
  `C_1 δ_0(m)^{1/2} ⩽ Ξ(m) ⩽ C_2 δ_0(m)^{1/2}(1 + σ(m))^d`." The Library's `SphericalBounds.md`
  records Waldspurger's proof of the lower bound through a factorization `H = (H ∩ P₀) V` with
  `V = H ∩ Ū₀` and `m⁻¹ V m ⊆ K`, which is the route used here.

The present author could not open the PDF in this session and relies on these Library quotations.

## Hypotheses

In addition to the data of `RationalWeights` (a compact open `K` with `hKo`, `hKc`, and
`hPK : IsIwasawaPair P₀(F) K`):

- a subgroup `H ≤ K` (`hHK`) satisfying the Library predicate
  `StandardParabolicBasisMember i ν ∅ q H` (`hH`) for a split subtorus `q : A → S`: the ordered
  Iwahori factorization `H = (H ∩ Ū₀)(H ∩ M₀)(H ∩ U₀)` and the contraction and cofinality clauses
  of Renard V.5.2 (rows S20–S23 of `notes/renard/chapter-v-structural-inputs.md`) for the minimal
  standard parabolic, with the chambers of `A(F)`. This is one member of a basis as in
  `SimultaneousStandardBasisAt` (structural, unproved in general);
- for the results on `U₀(F)`: `hi : IsMaximalSplitTorus i` and
  `hA : IsCompatibleStandardSplitComponent i ν ∅ A q` (the split component of `M₀`), which supply a
  strict element of `A(F)` (the Library's `exists_strict_element`, with the standard cocharacter
  `ν` of the empty face);
- for the lower bound: `H` open (`hHo`).

## Results

- `rationalMinimalModulus_eq_one_of_mem_unipotent`: `δ₀(u) = 1` for every `u ∈ U₀(F)`. By strict
  exhaustion `U₀(F) = ⋃_n g^{-n} (H ∩ U₀(F)) g^n` for the strict element `g ∈ M₀(F) ⊆ P₀(F)`, so
  `u = a x a⁻¹` with `a = g^{-n} ∈ P₀(F)` and `x ∈ H ∩ U₀(F) ⊆ P₀(F) ∩ K`; then
  `δ₀(u) = δ₀(a) δ₀(x) δ₀(a)⁻¹ = δ₀(x) = 1` (`rationalMinimalModulus_eq_one`).
- `rationalMinimalModulus_mul_of_mem_unipotent`: `δ₀(u m) = δ₀(m)` for `u ∈ U₀(F)`, `m ∈ M₀(F)`.
- `iwasawaWeight_rationalMinimalModulus`: for `g = u m k` with `u ∈ U₀(F)`, `m ∈ M₀(F)`, `k ∈ K`,
  the integrand of `rationalXi` at `g` is `δ₀(m)^{1/2}`. Hence, under these hypotheses,
  `rationalXi` is exactly Waldspurger's `∫_K δ₀(m₀(kg))^{1/2} dk` (closing the correspondence point
  noted in `RationalWeights.md`, whenever every point of `P₀(F)` is a product `u m`).
- **`rationalXi_lowerBound`** (lower bound of Lemme II.1.1): the Library's
  `XiLowerBound (rationalXi hKc hPK) (standardComponentCAplus i ν ∅ q) φ` with
  `φ(p k) = δ₀(p)^{1/2}`, i.e. `φ(a) ≤ C Ξ(a)` on the weak chamber `C_A^+` of the split component
  (with `C = mes(H)⁻¹` for the Haar probability measure of `K`). Proof: the Library's
  `xiLowerBound_of_factorization` with `V = H ∩ Ū₀(F)`; the factorization `h = p v` with
  `p ∈ H ∩ P₀(F)`, `v ∈ V` comes from the ordered factorization of `h⁻¹ = l m n`
  (`h = (n⁻¹ m⁻¹) l⁻¹`), and `a⁻¹ V a ⊆ H ⊆ K` for `a ∈ C_A^+` is the weak chamber contraction.
- `exists_sqrt_rationalMinimalModulus_le_rationalXi`: the same in explicit form,
  `δ₀(a)^{1/2} ≤ C Ξ(a)` for `a ∈ P₀(F) ∩ C_A^+`.

## Scope

- The lower bound is proved on the lattice chamber `C_A^+` of the split component of `M₀` (images of
  points `c(ϖ)` of `A(F)` that are dominant), not on all of Waldspurger's `M̄₀⁺`.
- The upper bound of Lemme II.1.1 is not treated.
- The decomposition `P₀(F) = U₀(F) M₀(F)` on rational points is not proved here; the identification
  of the integrand applies to points written as `u m k`.
