# The Leray splitting of `U(ν, ν)` and its Weil representation

**GKT §11.2** (Theorem 11.6, p. 318; Corollary 11.7, p. 325) and **§12.4** (Proposition 12.27 (1),
p. 372; Proposition 12.29, p. 375; Proposition 13.16, p. 399) for the unitary dual pair in Case
`3₊` with `W` split, proved directly by generators and relations (not by the book's computation of
the Leray cocycle).

The module `Langlands.Theta.DualPair.Unitary.Splitting` constructs the Weil representation of the
quasi-split unitary group `U(ν, ν)` for the Leray splitting with data `(χ, ψ)` (GKT p. 317) in the
Schrödinger model, and proves that it is smooth, unitary, normalizes the Schrödinger
representation and acts on the Siegel Levi subgroup by the character `χ(det) |N det|^{|α|/2}`.

## Content

Hypotheses of the public theorems: `F` a nonarchimedean local field of characteristic zero; `E` a
field, `[Algebra F E]` with the module topology and `[Algebra.IsQuadraticExtension F E]`;
`hE : IsQuadraticInvolution c δ` (`c` the conjugation, `c δ = -δ`); `Q` an `α × α` matrix over `E`
with `hQ : Matrix.IsHermitianFor c Q` and `hQu : IsUnit Q.det`; `ψ : UnitaryAdditiveCharacter F`;
`χ : Eˣ →* Circle` continuous (`hχ`) with
`hres : ∀ a : Fˣ, χ(a) = (LocalClassField.normResidueSign F E a)^{|α|}` (the restriction of `χ` to
`Fˣ` is the `|α|`-th power of the quadratic character of `E / F`: the condition (11.2), GKT
p. 317; Harris–Kudla–Sweet, *Theta dichotomy for unitary groups*, J. AMS 9 (1996), section 1).

- `IsLerayWeil c ψ χ Q μ κ ω` (a structure): `ω : Representation ℂ U(ν, ν) (SchwartzBruhat M_{α×ν}(E))`
  acts on the Siegel parabolic by the operators `siegelParabolicOp`
  (`apply_of_mem_siegelParabolic`) and at the Weyl element by `κ • hermitianFourier c ψ Q μ`
  (`weylElement_apply`): the three formulas of GKT Proposition 12.27 (1) with
  `β(m(a) n(b)) = χ(det a)` (Proposition 12.29), the scalar `κ` standing for `β(w)` and the
  normalization of the Haar measure `μ`. Since the Siegel parabolic and the Weyl element generate
  `U(ν, ν)` (`UnitaryGroup.eq_top_of_siegelParabolic_le_of_weylElement_mem`), `ω` is determined by
  `κ`.
- `exists_isLerayWeil`: for every Haar measure `μ` such `κ` and `ω` exist (Theorem 11.6 and
  Corollary 11.7 in this case). The operators of the Siegel parabolic form a representation of it;
  the Weyl element's operator `κ ℱ` is invertible (`ℱ² = C · reflection`); `κ = s(det(-1)) / γ₀` is
  chosen with `γ₀` the constant of the Hermitian Gauss integrals, which is non-zero
  (`gauss_const_ne_zero`), so that every relation `w p w = p₁ w p₂` of the big cell holds for the
  operators (`weyl_cell_relation`, from the braid relation), and the relations `w p = q w` hold
  (`fou_parFun_levi`). The extension to `U(ν, ν)` is `Group.exists_monoidHom_of_bigCell_relations`
  (`Langlands/Group/BigCellHom.lean`), applicable because every finite set of `U(ν, ν)` has a
  translate in the big cell.
- `IsLerayWeil.isSmooth`: `ω` is smooth (`Langlands.IsSmooth`; GKT Proposition 13.16 for this pair).
  The stabilizer of a vector contains the elements near `1` of the Siegel parabolic
  (`parFun_fixed_near_one`) and of its conjugate by the Weyl element, hence is open
  (`UnitaryGroup.isOpen_of_eventually_mem_siegelParabolic`; `isSmooth_iff_forall_isOpen`).
- `IsLerayWeil.lintegral_enorm_sq`: `∫ ‖ω(g) φ‖² dμ' = ∫ ‖φ‖² dμ'` for every Haar measure `μ'`. The
  subgroup of the `g` preserving the norm contains the Siegel parabolic; the Weyl element multiplies
  the norm by `k = |κ|² C` (Plancherel, `lintegral_enorm_bicharacterFourier_sq`), and `k² = 1` since
  `w² ∈ P`, so `k = 1`.
- `IsLerayWeil.normalizes`: `HeisenbergGroup.Normalizes (hermitianSchrodinger c ν Q ψ)
  (UnitaryGroup.heisenbergAction c hE.involutive hQ) ω`, that is
  `ω(g) ρ(w, t) = ρ(w g⁻¹, t) ω(g)` for the Schrödinger representation `ρ` of the Heisenberg group of
  `M_{α×2ν}(E)` (`Langlands/Theta/DualPair/Unitary/Schrodinger.lean`): relation (2.2) of GKT p. 47,
  so that `(g ⊗ 1, ω(g))` is in the metaplectic group of pairs. It holds on the Siegel parabolic
  and at the Weyl element (`heisFun_parFun`, `heisFun_fou`), and the elements where it holds form a
  subgroup.
- `IsLerayWeil.siegelLevi_apply`: `ω(diag(a, c(a)⁻ᵀ)) φ (x) = χ(det a) |N_{E/F} det a|_F^{|α|/2} φ(x a)`.

The proofs are internal (namespace `Langlands.Theta.Unitary.Internal`: `Exist.exists_isLerayWeil`,
`weyl_cell_relation`, `weil_heis_intertwine`, `weil_representation_preserves_L2`,
`isSmooth_of_isLerayWeil`); the public theorems restate them with the Library's hypotheses.

Literature: S. Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87
(1994), §3, Theorem 3.1, p. 378, Corollary 3.3, p. 380, §5, pp. 399–400; R. Ranga Rao, *On some
explicit formulas in the theory of Weil representation*, Pacific J. Math. 157 (1993). The book's
treatment (Theorem 11.6) follows Kudla (1994) and Harris–Kudla–Sweet (1996), appendix.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean`, lines 134–138
(`IsKW`); under `Proofs/DivisorProofs/`: `ExistsWeilRepresentationBigCellRelationFourier.lean`,
`ExistsWeilRepresentationSplitUnitarySchwartzBruh.lean`, `WeilRepresentationIntertwinesHeisenberg.lean`,
`WeilRepresentationPreservesL2Space.lean`, `SplitUnitaryWeilRepresentationIsSmooth.lean`,
`KudlaSplittingSplitUnitary.lean` (each whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- The source's published statement `KudlaSplittingSplitUnitary` (an existence statement with four
  consequences) is replaced by the structure `IsLerayWeil` (the source's `KSp.IsKW`, with fields
  `apply_of_mem_siegelParabolic`, `weylElement_apply`), the existence theorem `exists_isLerayWeil`
  and four theorems about any `ω` satisfying it.
- Hypotheses in the Library's notions: `ψ : UnitaryAdditiveCharacter F` (the source: an
  `AddChar F ℂ` with three hypotheses); `IsHerm c Q` split into `Matrix.IsHermitianFor c Q` and
  `IsUnit Q.det`; `ResEtaPow ⊥ χ |α|` written with `LocalClassField.normResidueSign`, which needs the
  instance `Algebra.IsQuadraticExtension F E` (provided by `hE.isQuadraticExtension`); `IsSmoothRep`
  → `Langlands.IsSmooth`; `SB` → `SchwartzBruhat`; `nabs` → `distribHaarChar`; the third clause, with
  the source's operators `Heisenberg₂`, → `HeisenbergGroup.Normalizes` for
  `hermitianSchrodinger` and `UnitaryGroup.heisenbergAction` (the action of `g` is right
  multiplication by `g⁻¹`, so that it is a left action).
- The 48 statement wrappers of the source are not taken: each call of a wrapper is a call of the
  lemma it wraps; their implementations are internal.
- No file-level `open scoped Classical`.

## Declarations

- `Langlands.Theta.IsLerayWeil` (fields `apply_of_mem_siegelParabolic`, `weylElement_apply`)
- `Langlands.Theta.exists_isLerayWeil`
- `Langlands.Theta.IsLerayWeil.isSmooth`, `.lintegral_enorm_sq`, `.normalizes`, `.siegelLevi_apply`
- Deprecated aliases (since 2026-11-23): `IsKudlaWeil` (with `IsKudlaWeil.mk`, the two fields and
  the four theorems) for `IsLerayWeil`, and `exists_isKudlaWeil` for `exists_isLerayWeil`.

## Dependencies

`Langlands.Theta.DualPair.Unitary.WeylElement`, `Langlands.Theta.DualPair.TensorInvariants`,
`Langlands.Group.BigCellHom`, `Langlands.Representation.Smooth.OpenStabilizer`; Mathlib:
`Topology.LocallyConstant.Algebra`.
