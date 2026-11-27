# Orbital integrals of cusp forms vanish off the elliptic set

The module `Langlands.BaseChange.CuspFormOrbitalVanishingStatement` states two propositions on
`GL_n` over a nonarchimedean local field `F` of characteristic zero, for `0 < n`:

- `CuspFormOrbitalVanishingStatement.{u}`: every Schwartz–Bruhat function on `GL_n(F)` with
  vanishing constant terms has vanishing orbital integrals at the regular semisimple elements
  that are not regular elliptic;
- `CuspFormSigmaOrbitalVanishingStatement.{u, v}`: for a field `E` that is a cyclic `F`-algebra
  with generator `σ`, every Schwartz–Bruhat function on `GL_n(E)` with vanishing constant terms
  has vanishing σ-orbital integrals at the σ-regular elements that are not σ-elliptic.

The module states the two propositions and does not prove them.

## Notation (Library and Mathlib)

- `HasVanishingConstantTerms f` (module `Langlands.BaseChange.CuspForm`): for every proper
  standard block parabolic subgroup with unipotent radical `U`, every Haar measure on `U` and all
  `x, y`, the function `u ↦ f(x u y)` is integrable on `U` with integral `0`.
- `OrbitalIntegralsVanishOffElliptic μF f` and `SigmaOrbitalIntegralsVanishOffElliptic σ l μE φ`
  (module `Langlands.BaseChange.EllipticOrbitalIntegral`): the orbital integral
  `∫ f(x⁻¹ γ x) dνγ(x)` vanishes at every regular semisimple `γ` that is not regular elliptic, and
  the σ-orbital integral `∫ φ(x⁻¹ δ x^σ) dνδ(x)` vanishes at every σ-regular `δ` that is not
  σ-elliptic, for every right Haar measure on the (σ-)centralizer and every quotient measure
  compatible with it and with `μF`, resp. `μE`. Henniart–Lemaire call such functions
  *elliptique*, resp. *σ-elliptique* (II.4.10, printed p. 93).
- `IsSigmaRegular σ l δ` and `IsSigmaElliptic σ l δ` (module `Langlands.BaseChange.Norm`): `δ`
  is associated with some regular semisimple, resp. regular elliptic, element of `GL_n(F)`.
- `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`); `SchwartzBruhat` (module
  `Langlands.HarmonicAnalysis.Basic`).

## Statements

`CuspFormOrbitalVanishingStatement.{u}` quantifies over `F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`
and `n : ℕ` with `0 < n`. With the topological instances on `GL_n(F)`
(`LocalFieldTopology.generalLinear_*`) and the Borel σ-algebra, it asserts: for every Haar
measure `μF` on `GL_n(F)` and every `f : SchwartzBruhat (GeneralLinear n F)` with
`HasVanishingConstantTerms f`, `OrbitalIntegralsVanishOffElliptic μF f`.

`CuspFormSigmaOrbitalVanishingStatement.{u, v}` quantifies over the same `F`, a field
`E : Type v` with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`, `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l` and `0 < n`.
With the topological instances on `GL_n(E)` (`generalLinear_*_of_finite`) and the Borel
σ-algebra, it asserts: for every Haar measure `μE` on `GL_n(E)` and every
`φ : SchwartzBruhat (GeneralLinear n E)` with `HasVanishingConstantTerms φ`,
`SigmaOrbitalIntegralsVanishOffElliptic σ l μE φ`.

The hypothesis `0 < n` is needed: for `n = 0` the identity of the trivial group `GL_0(F)` is
regular semisimple (its characteristic polynomial `1` is separable) and not regular elliptic
(`1` is a unit, hence not irreducible), every function on `GL_0(F)` has vanishing constant
terms (there is no block shape with two blocks), and the orbital integral at the identity is
`f(1)` times the total mass of the quotient measure on a point. For `n = 1` every regular
semisimple element is regular elliptic, so both statements hold trivially.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL. II.2.2–II.2.3, printed pp. 62–64: association,
  σ-regular and σ-elliptic elements; if `N(δ) = γ` with `γ` regular then `G^σ_δ(F) = G_γ(F)` and
  `δ ∈ G_γ(E)` (p. 63); `γ` is closed when `F[γ]` is a product of fields, and `δ` is σ-closed
  when every element associated with it is closed (p. 63); the (σ-)orbital integrals
  `Λ^{G(E)}_σ(φ, δ) = ∫ φ(g⁻¹ δ g^σ) dḡ^σ_δ` (p. 64). II.4.5, printed pp. 86–88: with the Haar
  measures `dg_E` on `G(E)`, `dm_E` on `M(E)` and `du_E` on `U(E)` giving volume `1` to
  `K_E = G(o_E)`, `M(o_E) = M(E) ∩ K_E` and `U(o_E) = U(E) ∩ K_E`, and `dk_E` the restriction of
  `dg_E` to `K_E`, the map `φ ↦ φ_{P,σ}`,
  `φ_{P,σ}(m) = δ_{P(E)}(m)^{1/2} ∫_{U(E) × K_E} φ(k⁻¹ m u k^σ) du_E dk_E`, and, for `δ ∈ M(E)`
  σ-closed with σ-centralizer contained in `M`, the descent formula
  `Λ^{G(E)}_σ(φ, δ) = |D_{G/M,σ}(δ)|_F^{-1/2} Λ^{M(E)}_σ(φ_{P,σ}, δ)` (formula (1), after
  Laumon, Prop. 4.4.9), where the two sides use the quotients of `dg_E` and of `dm_E` by the same
  Haar measure on the σ-centralizer; the case `E = F`, `σ = id` is the ordinary descent formula
  (p. 88, after formula (3)). II.4.10, printed p. 93: the definition of elliptic and σ-elliptic
  functions. II.5.14, Proposition 2 (2) and its proof, printed pp. 115–116: the same reduction
  (σ-conjugate a σ-regular non-σ-elliptic `δ` into a proper Levi subgroup and apply formula (1)
  of II.4.5) for pseudo-coefficients of σ-discrete series.

## Derivation from parabolic descent

Let `δ ∈ GL_n(E)` be σ-regular and not σ-elliptic, associated with a regular semisimple `γ`.

1. *A proper Levi subgroup.* Since `γ` is not elliptic, its characteristic polynomial is
   reducible; it is separable, so `F[γ]` is a product of at least two fields and `γ` is
   conjugate in `GL_n(F)` into a proper standard block Levi subgroup `M(F)`, with centralizer, a
   maximal torus, contained in `M`. Replacing `γ` by a conjugate does not change σ-regularity or
   σ-ellipticity of `δ`.
2. *A σ-conjugate of `δ` in `M(E)`.* By the norm lemma (HL I.2.2) `δ` is σ-conjugate to some
   `δ'` with `N(δ') = γ`; then `δ' γ = δ' N(δ')^σ = N(δ') δ' = γ δ'`, so `δ'` lies in the
   centralizer of `γ` in `GL_n(E)`, which is contained in `M(E)`, and so does the σ-centralizer
   `G^σ_{δ'}(F) = G_γ(F)` (HL II.2.2). Every element associated with `δ'` is conjugate to `γ`,
   hence closed, so `δ'` is σ-closed (HL II.2.3).
3. *Descent with the normalized measures.* For the Haar measures of HL II.4.5 (volume `1` on
   `K_E`, `M(o_E)`, `U(o_E)`) and any Haar measure on the σ-centralizer, formula (1) expresses
   the σ-orbital integral of `φ` at `δ'` as a multiple of `Λ^{M(E)}_σ(φ_{P,σ}, δ')`. The
   hypothesis `HasVanishingConstantTerms φ`, applied with `x = k⁻¹ m`, `y = k^σ` and the Haar
   measure `du_E`, makes the inner integral `∫_U φ(k⁻¹ m u k^σ) du_E` vanish for every `m` and
   `k`, so `φ_{P,σ} = 0` and the σ-orbital integral at `δ'` is `0`.
4. *Arbitrary measures and the original `δ`.* The σ-orbital integral at `δ` equals the one at
   `δ'` for the measures transported by the σ-conjugation (HL II.2.4, last display). For the
   measures in the statement (any Haar measure `μE` on `GL_n(E)`, any right Haar measure on the
   σ-centralizer and any compatible quotient measure), Haar uniqueness gives positive scalars
   `a`, `b` relating them to the measures of step 3, and the compatible quotient measures are
   then related by the scalar `a / b` (the Library's `IsCompatible.smul_eq_smul`, module
   `Langlands.Analysis.Local.QuotientCompatibleScaling`). The σ-orbital integral is multiplied
   by the same scalar, so it is still `0`.

The ordinary statement is the same argument with `E = F` and `σ = id`.

## Derived content

The two statements are formulated for this Library; HL state the descent formula and not these
consequences. They are the local facts on cusp forms that the comparison of the simple trace
formula with its twisted form uses at a place where a cusp form is taken: the non-elliptic
(σ-)orbital integrals of a cusp form vanish, so that only elliptic terms remain to be matched.
