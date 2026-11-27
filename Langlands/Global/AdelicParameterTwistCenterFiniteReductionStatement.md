# Center finiteness of twists from the finite Harish-Chandra transfer to a Levi

Module `Langlands.Global.AdelicParameterTwistCenterFiniteReductionStatement`. It contains one
statement, `Langlands.Global.ParameterTwistCenterFiniteReductionStatement`, and no proof. The
module `Langlands.Global.AdelicParameterTwistCenterFiniteReduction` proves it
(`Langlands.Global.parameterTwistCenterFiniteReduction`).

## Statement

`ParameterTwistCenterFiniteReductionStatement.{u}` is the implication

`ParabolicLeviCenterRestrictionStatement.{u} → ParameterTwistCenterFiniteStatement.{u}`.

- The premise `Langlands.Automorphic.GroupSchemeFunctions.ParabolicLeviCenterRestrictionStatement`
  (module `GroupSchemeLeviCenterRestriction`) concerns a connected reductive `G` over a number
  field, a parabolic `q : Q → G` with geometric unipotent radical `iV`, a rational Levi
  `l : M → Q` with `M × V ≅ Q`, smooth structures on `G` and `M`, and a point `a` of `G(F_∞)`.
  It asserts a module-finite complex algebra homomorphism `p` from the center of the complex
  enveloping algebra of `G(F_∞)` to that of `M(F_∞)`. For every plot-smooth `f` on `G(F_∞)` left
  invariant under `V(F_∞)` and every central `z`, the restriction `m ↦ (z f)(l(m) a)` equals
  `p(z)` applied to `m ↦ f(l(m) a)`.
- The conclusion `Langlands.Global.ParameterTwistCenterFiniteStatement` (module
  `AdelicParameterTwistCenterFiniteStatement`) concerns a standard parabolic family `fam`, a
  standard index `I` and a maximal compact `K` of `G(𝔸)` with `P_I(𝔸) K = G(𝔸)`. It asserts that
  for every smooth `𝔷`-finite function `φ` on `G(𝔸)` left invariant under `U_I(𝔸)` and every
  `λ ∈ X^*(P_I) ⊗ ℂ`, the twist `φ_λ(g) = φ(g) m_{P_I}(g)^λ` is again `𝔷`-finite.

## Sources and provenance

Derived. The conclusion is the `𝔷`-finiteness part of the assertion "`φ_λ ∈ 𝒜_P`" of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), §2.2, p. 191 (before (2.1)). The premise is a finite transfer of enveloping centers to a
Levi subgroup, in the unnormalized convention of the Library. Its source is Mœglin–Waldspurger,
*Spectral decomposition and Eisenstein series* (1995), I.2.17, printed pp. 37–38 (chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, PDF pp. 20–21). There a
Harish-Chandra homomorphism `i : 𝔷 → 𝔷_M`, with `𝔷_M` a finitely generated `i(𝔷)`-module, is
used to compare `𝔷`-finiteness of a function on `U(𝔸)M(k) \ G` with `𝔷_M`-finiteness of its
normalized restrictions to `M`, and the inverse image of a cofinite ideal of `𝔷_M` kills the
function.

The implication adapts this finite center transfer to the twist of Bernstein–Lapid. Besides the
transfer, the argument uses right-translation covariance of the center action, the
multiplicativity of `m_P^λ` along `P(𝔸)` and its splitting over pairs `(a, b)` for a maximal
compact `K`, and the change of the center action of the Levi under multiplication by the
character `m ↦ m_P(m)^λ` of `M(F_∞)`. The last step follows from the Leibniz rule and the
universal property of the enveloping algebra. The proof module derives these from Library
results.
