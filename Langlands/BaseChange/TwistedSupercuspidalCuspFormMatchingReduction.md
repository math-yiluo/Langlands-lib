# Matching cusp forms for a σ-stable supercuspidal: a reduction

The module `Langlands.BaseChange.TwistedSupercuspidalCuspFormMatchingReduction` states and proves

- `TwistedSupercuspidalCuspFormMatchingReductionStatement.{u, v, uV, uW}`: the implication

  ```
  CuspFormOrbitalVanishingStatement.{u} →
    CuspFormSigmaOrbitalVanishingStatement.{u, v} →
    SigmaStableSupercuspidalDescentStatement.{u, v, uV, uW} →
    SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
    SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW} →
    TwistedSupercuspidalCuspFormMatchingStatement.{u, v, uW}
  ```

  for every universe `uV` (the space of the representation of `GL_n(F)` produced by the
  descent);
- `twistedSupercuspidalCuspFormMatchingReduction`, its proof.

The premises are, in words (each module states its proposition; this module proves none of
them):

1. `CuspFormOrbitalVanishingStatement` and `CuspFormSigmaOrbitalVanishingStatement` (module
   `Langlands.BaseChange.CuspFormOrbitalVanishingStatement`): for `0 < n`, a Schwartz–Bruhat
   function with vanishing constant terms has vanishing orbital integrals at the regular
   semisimple elements of `GL_n(F)` that are not regular elliptic, resp. vanishing σ-orbital
   integrals at the σ-regular elements of `GL_n(E)` that are not σ-elliptic.
2. `SigmaStableSupercuspidalDescentStatement` (module of the same name): a σ-stable
   irreducible supercuspidal `τ` of `GL_n(E)`, with any σ-intertwiner, is a σ-lift
   (`IsSigmaLift`) of an irreducible supercuspidal `π` of `GL_n(F)`.
3. `SigmaLiftCharacterIdentityStatement` (module of the same name, Henniart–Lemaire 2011,
   II.2.9): for irreducible admissible `π` and `τ`, `IsSigmaLift` is equivalent to the identity
   of character values at associated regular pairs (`IsShintaniLift`).
4. `SupercuspidalCoefficientEllipticMatchingStatement` (module of the same name): given the
   identity `Θ_τ^{A⁻¹}(δ⁻¹) = c Θ_π(γ⁻¹)`, `c ≠ 0`, at the associated pairs `(δ, γ)` with `γ`
   regular elliptic, there are cusp forms `φ`, `f` with `f = 0` at the regular elliptic
   non-norms, concordant at those pairs, and with `tr(τ(φ) ∘ A) ≠ 0`.

## Auxiliary lemmas

- `IsCyclicAlgebra.symm`: `σ⁻¹` generates the same cyclic algebra (`orderOf σ⁻¹ = orderOf σ`;
  an element fixed by `σ⁻¹` is fixed by `σ`).
- `mul_entrywiseAut_cyclicNorm`: `δ · N_k(δ)^σ = N_{k+1}(δ)` for the twisted norms
  `N_k(δ) = δ δ^σ ⋯ δ^{σ^{k-1}}` (`cyclicNorm`).
- `entrywiseAut_pow_cyclicNorm_symm_inv`: `(N_{σ⁻¹,k}(δ⁻¹))^{σ^k} = (N_{σ,k}(δ)^σ)⁻¹`, by
  induction on `k`.
- `cyclicNorm_symm_inv`: for `σ^l = 1`, `N_{σ⁻¹}(δ⁻¹) = δ⁻¹ N_σ(δ)⁻¹ δ`.
- `IsNormAssociated.symm_inv`: if `δ` and `γ` are associated for `σ` (`N_σ(δ)` conjugate in
  `GL_n(E)` to `γ`), then `δ⁻¹` and `γ⁻¹` are associated for `σ⁻¹`.
- `squarefree_mirror` and `isRegularSemisimple_inv`: in characteristic zero the inverse of a
  regular semisimple `γ` is regular semisimple; the characteristic polynomial of `γ⁻¹` is a unit
  times the reverse of that of `γ` (`Matrix.charpoly_inv`, `Matrix.reverse_charpoly`), and the
  mirror of a squarefree polynomial over a field is squarefree.
- `IsNormAssociated.charpoly_eq`, `IsNormAssociated.isRegularElliptic_iff`: two elements of
  `GL_n(F)` associated with the same `δ` are conjugate in `GL_n(E)`, hence have the same
  characteristic polynomial (`charpoly_conj`, module `Langlands.BaseChange.LeviClassSystem`, and
  injectivity of `F[X] → E[X]`), and are regular elliptic together.
- `IsNorm.of_conj`: being a norm is invariant under conjugation.

## Proof of `twistedSupercuspidalCuspFormMatchingReduction`

Let `F`, `E`, `σ`, `l`, `n`, `τ`, `A`, `μF`, `μE` be as in
`TwistedSupercuspidalCuspFormMatchingStatement`.

1. *Inverse generator and inverse intertwiner.* `A⁻¹` satisfies
   `A⁻¹ τ(g) = τ(g^{σ⁻¹}) A⁻¹`, since `A τ(g^{σ⁻¹}) = τ(g) A`; it is packaged as
   `A' : SigmaIntertwiner σ⁻¹ n τ` (`LinearEquiv.isIntertwining_symm_isIntertwining`).
2. *Descent and character identity.* The descent for `σ⁻¹` (`IsCyclicAlgebra.symm`) and `A'`
   gives `π` and `c` with `IsSigmaLift σ⁻¹ l π _ τ _ A' c`; the character identity turns this into
   `c ≠ 0` and, at every pair `(δ', γ')` associated for `σ⁻¹` with `γ'` regular semisimple, a
   value `a` of the character of `π` at `γ'` with `c a` the value at `δ'` of
   `φ ↦ tr(τ(φ) ∘ A⁻¹)`.
3. *The hypothesis of the elliptic matching.* For `(δ, γ)` associated for `σ` with `γ` regular
   elliptic, `(δ⁻¹, γ⁻¹)` is associated for `σ⁻¹` (`IsNormAssociated.symm_inv`) and `γ⁻¹` is
   regular semisimple (`isRegularSemisimple_inv`); step 2 at `(δ⁻¹, γ⁻¹)` is the required
   identity `Θ_τ^{A⁻¹}(δ⁻¹) = c Θ_π(γ⁻¹)`. The elliptic matching gives `φ` and `f` with vanishing
   constant terms, `f = 0` at the regular elliptic non-norms, concordance at the elliptic
   associated pairs and `tr(τ(φ) ∘ A) ≠ 0`.
4. *Concordance* (`AreConcordant`, HL I.2.5) has two clauses.
   - *Vanishing off norms* (`VanishesOffNorms`): at a regular semisimple non-norm `γ`, if `γ`
     is regular elliptic then so is every conjugate `x⁻¹ γ x` (`isRegularElliptic_conj_iff`,
     module `Langlands.BaseChange.EllipticLocusClopen`), and no conjugate is a norm
     (`IsNorm.of_conj`), so the integrand `x ↦ f(x⁻¹ γ x)` of the orbital integral is identically
     `0`; if `γ` is not regular elliptic, `CuspFormOrbitalVanishingStatement` applies.
   - *Concordance at associated regular pairs*: if `γ` is regular elliptic this is step 3;
     otherwise `δ` is not σ-elliptic (any regular elliptic `γ'` associated with `δ` would make
     `γ` regular elliptic by `IsNormAssociated.isRegularElliptic_iff`), and both orbital
     integrals vanish by the two vanishing statements.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8): I.2.5, printed pp. 17–18 (association, concordance); II.2.7–II.2.9,
  printed pp. 66–70 (σ-lifts and the character identity); II.6.3–II.6.4, printed pp. 119–121
  (cusp forms at an auxiliary place).

## Derived content

The implication is formulated for this Library. It isolates the analytic input (premises 1
and 4) from the representation-theoretic input (premises 2 and 3) of the matching of cusp
forms at the auxiliary place of the comparison of the simple trace formula with its twisted
form.
