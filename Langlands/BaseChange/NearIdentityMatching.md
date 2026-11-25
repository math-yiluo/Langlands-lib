# Matching of test functions near the identity for cyclic base change

`Langlands.BaseChange.NearIdentityMatching`. Namespace `Langlands.BaseChange`.

Proves `NearIdentityMatchingStatement` (`nearIdentityMatching`), and the two directions in a
sharper form with an explicit radius and an explicit transferred function.

## Statements

Hypotheses of the two directions: `F` a nonarchimedean local field (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`), `E` a field with `[Algebra F E]
[FiniteDimensional F E] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`,
`σ : E ≃ₐ[F] E` with `IsCyclicAlgebra σ l`, Borel σ-algebras and Haar measures `μF`, `μE` on
`GL_n(F)`, `GL_n(E)`, and `r : ℝ` with `0 < r`. The norms are `LocalGalois.localNormedField F` on
`F` and the spectral norm `LocalGalois.finiteExtensionNormedField F E` on `E` (installed by `letI`
in the statements); `normCongruence 𝕂 n s` is `{g | ‖g i j - δ i j‖ ≤ s}`.

- `exists_concordant_ordinary_of_support_normCongruence`: if `r < ‖(l : F)‖`, every
  `φ : SchwartzBruhat (GL_n(E))` with `Function.support φ ⊆ normCongruence E n (r * ‖(l : F)‖)`
  has `f : SchwartzBruhat (GL_n(F))` with `AreConcordant σ l μF μE φ f`,
  `f (u ^ l) = μF(normCongruence F n r)⁻¹ * ∫ κ in normCongruence E n r,
  φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) ∂μE` for `u ∈ normCongruence F n r`, and
  `f γ = 0` for `γ ∉ normCongruence F n (r * ‖(l : F)‖)`.
- `exists_concordant_twisted_of_support_normCongruence`: if `r < ‖(l : F)‖`, every
  `f : SchwartzBruhat (GL_n(F))` with `Function.support f ⊆ normCongruence F n (r * ‖(l : F)‖)`
  has `φ : SchwartzBruhat (GL_n(E))` with `AreConcordant σ l μF μE φ f`,
  `φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) = μE(normCongruence E n r)⁻¹ *
  ∫ κ' in normCongruence F n r, f (κ'⁻¹ * u ^ l * κ') ∂μF` for `κ ∈ normCongruence E n r`,
  `u ∈ normCongruence F n r`, and `φ = 0` off these σ-conjugates.
- `nearIdentityMatching : NearIdentityMatchingStatement.{u, v}`, with
  `U = normCongruence E n (r ‖l‖)`, `V = normCongruence F n (r ‖l‖)`, `r = ‖l‖ / 2` (`l > 0`
  and characteristic zero give `‖(l : F)‖ > 0`).

## Proofs

Let `K = normCongruenceSubgroup E n` of radius `r` and `K_F = K ∩ GL_n(F)`, which is
`normCongruence F n r` (`baseChange_mem_normCongruence_iff`). `K` is a compact open descent
subgroup (`isTwistedDescentSubgroup_normCongruence`), so both directions are applications of
`areConcordant_of_integral_eq`.

- From `GL_n(E)`: `A(g) = ∫_K φ(κ⁻¹ g κ^σ) dμE` is locally constant; `f` is defined on `l`-th powers
  of `K_F` by `f(u^l) = μF(K_F)⁻¹ A(u)` (well defined: roots in `K_F` are unique,
  `eq_of_pow_eq`) and by `0` elsewhere. It is Schwartz–Bruhat because the image of `K_F` under
  `u ↦ u^l` is the open compact set `normCongruence F n (r‖l‖)` (`pow_image_normCongruence`).
  The support of `φ` lies in the σ-conjugates `κ⁻¹ u κ^σ` by the twisted descent
  (`exists_twistedConj_baseChange_mul_eq`, centre `1`), and `A(κ⁻¹ u κ) = A(u)` for `κ ∈ K_F` by
  left invariance of `μE` on `K`, which gives the integral identity of
  `areConcordant_of_integral_eq`.
- From `GL_n(F)`: `A_F(γ) = ∫_{K_F} f(κ⁻¹ γ κ) dμF`; `φ(κ⁻¹ u κ^σ) = μE(K)⁻¹ A_F(u^l)` on the
  image `P` of `K × K_F`, `0` elsewhere. It is well defined by rigidity of σ-conjugacy
  (`IsTwistedDescentSubgroup.rational_of_twistedConj`) and conjugation invariance of `A_F`, and
  Schwartz–Bruhat because `P` is open (`isOpen_twistedConj_normCongruence`) and compact. The
  support of `f` consists of `l`-th powers of `K_F` (`pow_image_normCongruence`).

Private helpers: `mem_schwartzBruhat_of_image` (a function given by a locally constant function on
the open image of a compact set and zero elsewhere is Schwartz–Bruhat),
`isLocallyConstant_setIntegral`, `setIntegral_mul_left_of_mem`.

## Declarations, in order

private `mem_schwartzBruhat_of_image`, `isLocallyConstant_setIntegral`,
`setIntegral_mul_left_of_mem`; `exists_concordant_ordinary_of_support_normCongruence`,
`exists_concordant_twisted_of_support_normCongruence`, `nearIdentityMatching`.

## Literature

J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), Chapter 1, §3: Proposition 3.1, p. 20; the proof of Lemma 3.4, pp. 22–25 (for
`δ₀ = 1`: the function `ψ(m) = ∫ α(g) φ(g⁻¹ m g^σ) dg`, p. 23, here `α` is `μF(K_F)⁻¹` times the
indicator of `K`, and the transfer of germs near `γ₀ = 1` through `m ↦ m^l`, p. 24); the reverse
construction, p. 25. G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011), §I.2.5, p. 17 (concordance).

## Source and licence

Port of `UpperTheory.ConvolutionTheory.Loc.nearDown` and `…Loc.nearUp` of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>)
at commit `f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`, under
`src/Development/AutomorphicArithmetic/Foundations/Convolution/TwistedLocalOrbits/`:
`NearDown.lean` lines 26–67 (`sb_of_push`, `avg_locConst`), 200–235 (`exists_push`) and
241–277 (`nearDown`, the construction of `f`); `NearUp.lean` lines 25–76 (`sb_of_push`,
`avg_locConst`, `set_left`) and 116–209 (`nearUp`). The repository has no licence file; its text
is used with attribution (see
`licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- The conclusion `Match` becomes `AreConcordant` through `areConcordant_of_integral_eq`; the source's
  `nearDown` repeats the proof of `nearCore`, here it is applied like `nearUp` does.
- Radii are real numbers for the spectral norm of `E` and the norm of `F` instead of elements of the
  value group of `E`; the source's `small` (radius in `F` from a radius in `E`) is not needed since
  `algebraMap F E` is isometric.
- The neighbourhoods are produced as `nhds 1`-members for the end statement, and the transferred
  functions are described in the statements.
- The source's Galois hypotheses become `IsCyclicAlgebra σ l` with `E` a field.
