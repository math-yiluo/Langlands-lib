# Square-summability of unitary Whittaker functions on mirabolic cells

Author: Worker 1797. Module `Langlands.Representation.RankinSelberg.UnitaryCellBound`,
namespace `Langlands.RankinSelberg.UnramifiedUnitary`.

This helper module serves the proof of
`Langlands.RankinSelberg.UnramifiedUnitaryPoleFreeStatement` (see
`UnramifiedUnitaryPoleFreeProof.md`). It is an algebraic version of the proof of
Jacquet–Shalika, *On Euler products and the classification of automorphic
representations I*, Amer. J. Math. 103 (1981), Proposition (1.3), printed pp. 505–507
(literature id `provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`).
That proposition shows that for a unitary generic `π`, the Hermitian product on the compact
part `𝒦₀` of the Kirillov model is `c ∫_{N\P} φ₁ φ̄₂`, with the constant coming from
Bernstein–Zelevinsky's uniqueness of invariant forms. It then derives
`∫_{N\P} |W|² < ∞`. The source works with a Hilbert space. The implementation has no
completion and no topology on the carrier: it uses an algebraic invariant positive form,
the smooth dual and finite sums of cell functions. The conclusion is the finite-sum bound
below. Its proof route is internal.

## Notation

`P = mirabolic n F ⊆ GL_(n+1)(F)` is the last-row mirabolic group and
`N = Mirabolic.upperUnipotent n F` is its full upper unipotent subgroup. `θ` is the standard
character `mirabolicCharacter ψ n`. `ρ` is a representation of `GL_(n+1)(F)` on `V`, and
`ℓ` is a standard Whittaker functional (`glFunctionals ψ n ρ`). The compact model is the
published `mirabolicCompactInduced ψ n` (compactly supported mod `N`, left `(N, θ)`-covariant
functions, with right translation). The Kirillov map is the published
`mirabolicCoefficientMap ψ ρ hρ ℓ : v ↦ (p ↦ ℓ(ρ(p) v))`.

## The inverse Kirillov map (section `KirillovSection`)

Assume the Kirillov map is injective (`hinj`) and its image contains the compact model
(`hmin`). `kirillovSection` (`ι`) sends a compact function `f` to the unique vector with
Kirillov function `f` (`kirillovSection_spec`, `kirillovSection_eval`). It is linear by
injectivity. It is `P`-equivariant (`kirillovSection_equivariant`), because the Kirillov map
intertwines `ρ|_P` with right translation.

## The two invariant forms (section `Forms`)

- `dualRestriction ρ` is the smooth contragredient restricted to `P`.
- `kirillovForm ψ ρ ι` is `B₁(f, λ) = λ(ι f)`. `kirillovForm_mem`: it is a `P`-invariant
  bilinear form on (compact model) × (restricted smooth dual), with trivial character.
- `mirabolicFunctional` views `ℓ` as an `(N, θ)`-functional on `ρ|_P`.
  `mem_glFunctionals_of_mirabolic` is the converse. `norm_mirabolicCharacter`,
  `norm_mirabolicCharacter_inv` and `mirabolicCharacter_inv_mul` record that `θ` is unitary
  and `θ⁻¹θ = 1`.
- `dualFunctional ψ ρ E hE ℓ` is the published `conjugateFunctional` of `ℓ` along an
  equivariant conjugate-linear equivalence `E : V ≃ₗ⋆ SmoothDual ρ`. It is an
  `(N, θ⁻¹)`-functional on the restricted smooth dual, with
  `dualFunctional (E v) = conj ℓ(v)` (`dualFunctional_apply`).
- `eq_smul_dualFunctional`: if every standard Whittaker functional of `ρ` is a multiple of
  `ℓ`, then every `(N, θ⁻¹)`-functional `μ` on the restricted smooth dual is a multiple of
  `dualFunctional ℓ`. Proof: `μ ∘ E`, conjugated, is a `θ`-functional on `ρ|_P` (apply
  `conjugateFunctional` to `E.symm`). Hence it is a standard Whittaker functional, hence
  `c ℓ`. Unwinding gives `μ = c̄ · dualFunctional ℓ`.
- `exists_eq_smul_of_injective_line`: if `L : Y → Z` is linear and injective and `Z` is
  spanned by one vector, then for any `B₁, B₂ ∈ Y` either `B₁ = κ B₂` or `B₂ = 0`.

## Cells (sections `Cells`, `CellPairing`)

The setting is a general topological group `G` with subgroup `H` and character
`θ : H →* ℂˣ`.

- `conjSub g K` is the open subgroup `g K g⁻¹` (`mem_conjSub`, `conj_mem_conjSub`). It is
  compact when `K` is (`isCompact_conjSub`, preimage under a homeomorphism).
- `cell_admissible`: suppose `λ` is a `θ`-functional, `v` is fixed by `K` and
  `λ(π(g) v) ≠ 0`. Then `θ` is trivial on `H ∩ g K g⁻¹`. Indeed, for `u` there,
  `π(u)π(g)v = π(g)v`, so `θ(u) λ(π(g)v) = λ(π(g)v)`.
- `cellFunction H θ K hK g hv` is the right translate by `g⁻¹` of the published
  `compactDoubleCosetSection` for `g K g⁻¹` at the identity with value `1`. Its value at `y`
  is the section's value at `y g⁻¹` (`cellFunction_eval`). It equals `1` at `g`
  (`cellFunction_self`) and vanishes at any `y ∉ H g K` (`cellFunction_other`, from
  `compactDoubleCosetSection_support_subset`). It is fixed by right translation by `K`
  (`cellFunction_fixed`, from `compactDoubleCosetSection_mul`).
- `pairing_cellFunction`. Let `B₂` be the published integral pairing
  `CompactFunctionalPairing.pairing H θ θ' σ hσ μ hθ' ν`, i.e. `∫_{H\G} f(x) μ(σ(x) w) dν`,
  for a right-invariant `ν`. For `x` fixed by `K`,
  `B₂(cellFunction, x) = ν(orbit of g K g⁻¹) · μ(σ(g) x)`. Proof: invariance of `B₂`
  (`pairing_mem`) moves the translation by `g⁻¹` to `σ(g) x`, and `pairing_section`
  evaluates the pairing of the unit section.

## The bound (section `Bound`)

- `norm_inner_sq_le`: Cauchy–Schwarz for an `InvariantPositiveForm`, namely
  `|b(x,y)|² ≤ Re b(x,x) · Re b(y,y)`, from Mathlib's `InnerProductSpace.Core`.
- `le_of_norm_sq_le_re`: for `κ ≠ 0`, `S ≥ 0` and `R ≥ 0`, if `‖κS‖² ≤ R · Re(κS)` then
  `S ≤ ‖κ‖⁻¹ R`.
- `evalAt y` is evaluation at `y`, as a linear functional on the compact model.
- `cell_admissible_mirabolic` is `cell_admissible` for `ℓ`. `mirabolicCell` is
  `cellFunction` typed in the compact model. Its evaluation and fixedness lemmas are
  `evalAt_mirabolicCell_self`, `evalAt_mirabolicCell_other` and `mirabolicCell_fixed`.
  `cellFamily ψ ρ ℓ K hK v hv g i` is the cell function of `g i` when `ℓ(ρ(g i) v) ≠ 0`,
  and `0` otherwise (`cellFamily_of_eq_zero`, `cellFamily_of_ne_zero`).
- `bound_of_cell_formula`. Its inputs are an equivariant section `ι` of the Kirillov map, a
  nonnegative mass function `M`, and a scalar `κ` with
  `b(u, ι(cell of g, K)) = κ · M(g K g⁻¹) · conj ℓ(ρ(g) u)` for every `K`-fixed `u`. Then,
  for `v` fixed by `K` and points `g_i` (`i ∈ s`) with `g_i ∉ N g_j K` for `i ≠ j`,
  `∑_i M(g_i K g_i⁻¹) |ℓ(ρ(g_i) v)|² ≤ C Re b(v,v)`, where `C = 0` if `κ = 0` and
  `C = ‖κ‖⁻¹` otherwise.
  Proof. Put `φ = ∑_i W(g_i) f_i`, with `W(g) = ℓ(ρ(g)v)` and `f_i` the cell family. Each
  `f_i` is `K`-fixed, so `ιφ` is `K`-fixed. By disjointness of the cells,
  `ℓ(ρ(g_i) ιφ) = φ(g_i) = W(g_i)`. The cell formula, linearity, and
  `W · conj W = |W|²` give `b(v, ιφ) = b(ιφ, ιφ) = κ S`, where
  `S = ∑ M_i |W(g_i)|²`. If `κ = 0` then `b(ιφ, ιφ) = 0`, so `ιφ = 0` and every
  `W(g_i) = 0`. Otherwise Cauchy–Schwarz gives `‖κS‖² ≤ Re b(v,v) · Re(κS)`, and
  `le_of_norm_sq_le_re` concludes.
- `cellBound_core`. Its inputs are injectivity of the Kirillov map, `hmin`, multiplicity
  one for `ℓ`, an invariant positive form `b`, an equivalence `E` equal to the published
  `b.toSmoothDual`, a compact-open basis of `P`, smoothness of the character
  representation, and a measure `ν` on `N\P` that is finite on compacts, right invariant,
  and gives compact-open orbits positive finite mass. The conclusion is the bound of
  `bound_of_cell_formula` with `M(J) = ν(orbit of J)`.
  Proof. The published `FormsFunctional.exists_injective_formsFunctional` gives an
  injective linear map `L` from invariant forms to `(N, θ⁻¹)`-functionals on the
  restricted smooth dual. That space is a line spanned by `dualFunctional ℓ`
  (`eq_smul_dualFunctional`). Hence either `B₁ = κ B₂` or `B₂ = 0`, where `B₁` is the
  Kirillov form and `B₂` the integral pairing with `dualFunctional ℓ`. In the first case,
  `b(u, ιf) = B₁(f, E u)` (`smoothDualPairing_toSmoothDual`), and
  `pairing_cellFunction` together with `dualFunctional_apply` gives the cell formula.
  In the second case, `pairing_cellFunction` and positivity of orbit masses force
  `W(g_i) = 0` for every `i`.

## The p-adic case (section `Padic`)

`padicCellBound F n ψ ρ`: let `F` be a p-adic field with its canonical topology, and `ρ` an
admissible, irreducible, unitarizable representation of `GL_(n+1)(F)` with a nonzero
standard Whittaker functional `ℓ`. Let `ν` be as above. For every `v` fixed by a compact
open subgroup `K` of `P` there is `C` such that
`∑_{i∈s} ν(orbit of g_i K g_i⁻¹) |ℓ(ρ(g_i) v)|² ≤ C` for every finite family of pairwise
distinct cells. The hypotheses of `cellBound_core` are discharged as follows:

- multiplicity one by the published `Whittaker.multiplicityOne`;
- injectivity by `kirillov_injective` (module `UnramifiedKirillovInjectivity`);
- `hmin` by the published `Whittaker.mirabolicCompactMinimality` (BZ76, Proposition
  5.15(c)) applied to `mirabolicCoefficientImage`, which is nonzero by
  `mirabolicCoefficientImage_ne_bot`;
- `E` by the published `InvariantPositiveForm.smoothDualEquiv`, with cofinality
  `GeneralLinear.compactOpen_cofinal`;
- the topological instances, the compact-open basis and the character smoothness as in
  the published proof of `Whittaker.mirabolicCompactTwistedPairing`.
