# The Gelfand–Kazhdan contragredient over every nonarchimedean local field

Author: Worker 5089.

The published theorems `Langlands.generalLinearConjugationDistributionTranspose`
(module `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof`) and
`Langlands.gelfandKazhdanContragredient` (module
`Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`, assembled in
`GelfandKazhdanAssembly`) prove statements that quantify over `PadicField` only. Their
proofs use the p-adic structure only to install topological instances: Hausdorffness,
local compactness and total disconnectedness of the field, and local compactness,
sigma-compactness, Hausdorffness and the nonarchimedean property of the general linear
group. The lemmas they apply are stated for general topological fields and groups.

This module repeats the two proofs for an arbitrary nonarchimedean local field

```lean
variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
```

of any characteristic. The topological facts come from
`Langlands.Group.GL.LocalFieldTopology`, installed with `attribute [local instance]`:
Hausdorffness and total disconnectedness of `F`, and Hausdorffness, local compactness,
second countability, sigma-compactness, the nonarchimedean property and total
disconnectedness of `Matrix.GeneralLinearGroup (Fin (n + 1)) F`. Local compactness of
`F` itself is part of Mathlib's `IsNonarchimedeanLocalField`. Each proof is otherwise
the published p-adic proof with `F.Carrier` replaced by `F`.

## Declarations

Both theorems are in the namespace `Langlands.LocalField`, with the field `F`
explicit and universes `uF` (field) and `uV` (carrier).

```lean
theorem generalLinearConjugationDistributionTranspose (n : ℕ)
    (D : Distribution (Matrix.GeneralLinearGroup (Fin (n + 1)) F))
    (hD : IsConjugationInvariant D) : IsTransposeInvariant (n + 1) F D

theorem gelfandKazhdanContragredient (n : ℕ) (V : Type uV) [AddCommGroup V]
    [Module ℂ V]
    (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F) V)
    (hρ : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) :
    ∃ E : V ≃ₗ[ℂ] SmoothDual ρ, ∀ g v,
      E (ρ (GeneralLinear.inverseTranspose (n + 1) F g) v) =
        smoothContragredient ρ g (E v)
```

The first says that a complex algebraic distribution on `GL_(n+1)(F)` that is invariant
under every inner automorphism is invariant under the transpose map
`transposeHomeomorph (n + 1) F`. It is the content of
`GeneralLinearConjugationDistributionTransposeStatement` for every nonarchimedean local
field. The second says that for an admissible irreducible complex representation `ρ` of
`GL_(n+1)(F)` there is a complex linear equivalence `E` from its carrier to its smooth
dual that intertwines `ρ ∘ (inverse transpose)` with the smooth contragredient. It is
the content of `GelfandKazhdanContragredientStatement` for every nonarchimedean local
field.

## Proof of `generalLinearConjugationDistributionTranspose`

This repeats the published proof of
`HarmonicAnalysis.Distribution.generalLinearConjugationDistributionTranspose_of_prerequisites`,
with its four hypotheses replaced by the published theorems
`HarmonicAnalysis.Distribution.equivariantLocalization`,
`HarmonicAnalysis.Distribution.finiteOrbitAntiInvariantVanishing`,
`Langlands.matrixTransposeConjugate` and `Langlands.matrixCharpolyFiniteConjugacy`. It
uses the published helpers `charpolyCoeffs`, `charpolyCoeffs_conj`,
`charpolyCoeffs_transpose`, `continuous_charpolyCoeffs`, `charpoly_eq_of_coeff_eq` and
`conjugationInvariant_finiteOrbit_vanishing` of that module, all of which are stated for
general fields and groups. Write `τ` for the transpose and `q` for `charpolyCoeffs (n + 1)`.

1. Every `z` is conjugate to `τ z` (`matrixTransposeConjugate`, lifted from matrices to
   units), and `τ.symm = τ` because `τ` is an involution.
2. `D' = D - τ_* D` is conjugation invariant
   (`IsConjugationInvariant.pushforward_transpose`) and satisfies `τ_* D' = -D'`
   (`pushforward_transpose_involutive`).
3. `equivariantLocalization` is applied with `X = GL_(n+1)(F)`,
   `Y = Fin (n + 1) → F`, the map `q`, the index type `GL_(n+1)(F) ⊕ Unit`, the
   homeomorphisms `conjugationHomeomorph a` and `τ`, and the characters `1` and `-1`.
   The space `Y` is Hausdorff, locally compact and totally disconnected as a finite power
   of `F`; the p-adic proof obtained these properties from a proper ultrametric norm on
   `F.Carrier`, and here they come from the local instances above.
4. Each nonempty fibre `q ⁻¹' {y}` is the closed union of the conjugacy classes of a
   finite set `s`: take `g₀` in the fibre, the finite set of matrices given by
   `matrixCharpolyFiniteConjugacy` for its characteristic polynomial, and keep the units
   among them with `q` value `y`. An empty fibre is the empty union.
5. On such a fibre, a conjugation-invariant `T` with `τ_* T = -T` vanishes by
   `conjugationInvariant_finiteOrbit_vanishing` with `σ = τ`, since by step 1 both `τ`
   and `τ.symm` preserve each conjugacy class.
6. Localization gives `D' = 0`, that is `D = τ_* D`.

## Proof of `gelfandKazhdanContragredient`

This repeats the published conditional assembly
`gelfandKazhdanContragredient_of_character_inputs`, applied as in `GelfandKazhdanProof`
to `Langlands.characterSeparation` (at universes `uF, uV, uV`) and to the all-field
transpose theorem above instead of the p-adic one.

Let `G = Matrix.GeneralLinearGroup (Fin (n + 1)) F` with its Borel measurable space, and
let `μ = RankinSelberg.generalLinearHaar F n`, which is stated for every nonarchimedean
local field. `RankinSelberg.generalLinearHaarSymmetries F n` gives inversion invariance,
preservation by inverse transpose and preservation by every inner automorphism. Let
`e = GeneralLinear.inverseTransposeContinuous (n + 1) F`.

- `characterTransport` gives admissibility and the character formulas of the smooth
  dual `smoothContragredient ρ` and of the pullback `ρ ∘ e`.
- Compact open subgroups are cofinal among open subgroups of `G`
  (`Hecke.TestFunction.commonCompactOpenBiInvariance`). With
  `smoothBidual_injective_of_compact_cofinal` and
  `smoothBidual_surjective_of_compact_cofinal`, the transfer
  `isIrreducible_smoothContragredient_iff_of_bidual` makes the smooth dual irreducible.
  The pullback is irreducible by `isIrreducible_comp_continuousMulEquiv_iff`.
- The character distribution of `ρ` is conjugation invariant
  (`Character.distribution_isConjugationInvariant_of_measurePreserving`), hence
  transpose invariant by the first theorem of this module.
- Testing transpose invariance on the inverted test function identifies the two
  character formulas: the pullback of `f` along `e.symm` is the pullback along the
  transpose of `g ↦ f g⁻¹`. So the characters of `ρ ∘ e` and of the smooth dual agree.
- `characterSeparation` turns equal characters of the two irreducible admissible
  representations into the required equivalence `E`.

## Relation to the original source

The source is I. N. Bernstein and A. V. Zelevinsky, *Representations of the group
GL(n,F), where F is a non-Archimedean local field (survey)*, Russian Math. Surveys 31:3
(1976), 1–68 (registered `bernstein-zelevinsky-1976-representations-gln`), Theorem 7.3
and its proof, printed pp.57–58. The source works over an arbitrary non-Archimedean
local field. Its Theorem 7.3 states that `π^s` and the contragredient of `π` are
equivalent, where `s` is the automorphism `g ↦ s_n (gᵗ)⁻¹ s_n⁻¹` of 7.1. The theorem
here uses ordinary inverse transpose instead, as the published p-adic statement does.
The two automorphisms differ by the inner automorphism `g ↦ s_n g s_n⁻¹`; this module
neither uses nor proves the conversion between the two forms.

The proofs here follow the published p-adic modules, whose Markdown records how their implementation follows and adapts that argument: in
particular, transpose invariance is proved by localization along the characteristic
polynomial and finite-orbit vanishing, not through the constructiveness results of the
source's §6. This module is an internal generalization of those proofs to every
nonarchimedean local field. It introduces no new transcription from the literature and
keeps the published argument unchanged apart from the source of the topological
instances. It supports `Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof`.
