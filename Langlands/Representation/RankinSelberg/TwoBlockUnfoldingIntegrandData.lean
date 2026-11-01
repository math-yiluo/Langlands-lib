import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# The integrand of the first Section 4.6 unfolding

JPSS (1983), Section 4.6, equation (4) on printed page 411 and the first integral on
printed page 412: after substituting the Jacquet integral (4.6.2) into the outer integral
over `N_r \ G_r^m`, the iterated integrand is unfolded to the integral of
`W(g) f[g; e, e] Φ(η g)` over `N_(t_1,t_2) \ G_r^m`, where `N_(t_1,t_2)` is the
block-diagonal upper-unipotent group (5).

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, actual block
functionals `ℓ_i` in the inverse-character spaces, a lower normalized section `f`, a test
function `W` in the standard-character space and a Schwartz–Bruhat function `Φ`, this
module constructs the scalar function

`[g]_H ↦ W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)`

on the published quotient `H \ GL_(t+1)`, `H = blockUnipotent h F.Carrier`, by actual
quotient descent. It proves the block covariance of the scalar section, the left
`H`-invariance, the representative formula, the fiber formula through the positive
Jacquet kernel, and the identities of the total fiber integral and the radical average
with `W(g) J(f)(g) Φ(lastRow g)`. No integrability, measurability or Fubini statement is
asserted.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockUnfolding

open GeneralLinear TwoBlockJacquet TwoBlockDeformation TwoBlockUnipotentQuotient
  QuotientIntegration Whittaker HarmonicAnalysis

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

/-! ### Block covariance of the scalar section -/

section Covariance

variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))

/-- Left translation by `diag(n_0, n_1)` multiplies the scalar section at the Levi identity
by the product of the two block inverse standard characters `ψ⁻¹(n_0) ψ⁻¹(n_1)`. -/
theorem scalarSection_blockEmbedding_mul (f : Sections F h σ) (n : BlockUnipotents m F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    scalarSection (fun i => (ell i).val) f (blockEmbedding h F.Carrier n * g) 1 =
      (∏ i, (inverseStandardCharacter ψ (m i) (n i) : ℂ)) *
        scalarSection (fun i => (ell i).val) f g 1 := by
  let := F.canonicalTopologicalData.topology
  rw [scalarSection_one, scalarSection_one, blockEmbedding_apply,
    sectionEval_leviEmbedding_mul F h σ f _
      (fun i => determinantNorm_eq_one_of_mem_upperUnipotent F _ (n i).property) g,
    tensorContraction_blockTensor F h σ ψ _ (fun i => (ell i).property) _
      (fun i => (n i).property)]

/-- The product of the two block inverse standard characters of `(n_0, n_1)` is the
ambient inverse standard character of `diag(n_0, n_1)`: the corner block vanishes. -/
theorem inverseStandardCharacter_blockEmbedding (n : BlockUnipotents m F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    (inverseStandardCharacter ψ t
        ⟨blockEmbedding h F.Carrier n, blockEmbedding_mem_upperUnipotent h F.Carrier n⟩ : ℂ) =
      ∏ i, (inverseStandardCharacter ψ (m i) (n i) : ℂ) := by
  let := F.canonicalTopologicalData.topology
  rw [inverseStandardCharacter_eq_prod F h ψ]
  have hlevi : ∀ i, (⟨unipotentLevi h
      ⟨blockEmbedding h F.Carrier n, blockEmbedding_mem_upperUnipotent h F.Carrier n⟩ i,
        unipotentLevi_mem h _ i⟩ : upperUnipotent (m i + 1) F.Carrier) = n i :=
    fun i => Subtype.ext (unipotentLevi_blockEmbedding h F.Carrier n i)
  have hcorner : unipotentCorner h
      ⟨blockEmbedding h F.Carrier n, blockEmbedding_mem_upperUnipotent h F.Carrier n⟩
        (Fin.last (m 0)) 0 = 0 :=
    blockEmbedding_index_zero_one h F.Carrier n _ _
  simp only [hlevi, hcorner, AddChar.map_zero_eq_one, inv_one, mul_one]

/-- Left translation by `diag(n_0, n_1)` multiplies the scalar section at the Levi identity
by the ambient inverse standard character of `diag(n_0, n_1)`. -/
theorem scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter (f : Sections F h σ)
    (n : BlockUnipotents m F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    scalarSection (fun i => (ell i).val) f (blockEmbedding h F.Carrier n * g) 1 =
      (inverseStandardCharacter ψ t
          ⟨blockEmbedding h F.Carrier n, blockEmbedding_mem_upperUnipotent h F.Carrier n⟩ : ℂ) *
        scalarSection (fun i => (ell i).val) f g 1 := by
  rw [inverseStandardCharacter_blockEmbedding, scalarSection_blockEmbedding_mul]

end Covariance

/-! ### The scalar function and its descent -/

section Integrand

variable (ell : letI := F.canonicalTopologicalData.topology
  ∀ i, Whittaker.glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : letI := F.canonicalTopologicalData.topology
  RankinSelberg.WhittakerFunctions ψ t)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

/-- The scalar function `g ↦ W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)` on `GL_(t+1)`, before
descent. -/
def groupIntegrand (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  letI := F.canonicalTopologicalData.topology
  Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g)

theorem groupIntegrand_def (g : GeneralLinear (t + 1) F.Carrier) :
    groupIntegrand ell f Wtest Φ g =
      letI := F.canonicalTopologicalData.topology
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g) :=
  rfl

/-- Left `H`-invariance: the standard character of `diag(n_0, n_1)` from `W` cancels the
inverse character from the scalar section, and the last row is unchanged. -/
theorem groupIntegrand_blockUnipotent_mul (u : blockUnipotent h F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    groupIntegrand ell f Wtest Φ (u.val * g) = groupIntegrand ell f Wtest Φ g := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨_, n, rfl⟩ := u
  let v : upperUnipotent (t + 1) F.Carrier :=
    ⟨blockEmbedding h F.Carrier n, blockEmbedding_mem_upperUnipotent h F.Carrier n⟩
  have hW : Wtest.val (blockEmbedding h F.Carrier n * g) =
      (standardCharacter ψ t v : ℂ) * Wtest.val g :=
    Wtest.property v g
  have hrow : RankinSelberg.lastRow (blockEmbedding h F.Carrier n * g) =
      RankinSelberg.lastRow g :=
    RankinSelberg.lastRow_unipotent_mul v g
  have hchar : (standardCharacter ψ t v : ℂ) * (inverseStandardCharacter ψ t v : ℂ) = 1 :=
    Units.mul_inv (standardCharacter ψ t v)
  change Wtest.val (blockEmbedding h F.Carrier n * g) *
      scalarSection (fun i => (ell i).val) f (blockEmbedding h F.Carrier n * g) 1 *
        Φ (RankinSelberg.lastRow (blockEmbedding h F.Carrier n * g)) =
    Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g)
  rw [hW, hrow, scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter ell f n g]
  calc (standardCharacter ψ t v : ℂ) * Wtest.val g *
        ((inverseStandardCharacter ψ t v : ℂ) * scalarSection (fun i => (ell i).val) f g 1) *
          Φ (RankinSelberg.lastRow g) =
        ((standardCharacter ψ t v : ℂ) * (inverseStandardCharacter ψ t v : ℂ)) *
          (Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 *
            Φ (RankinSelberg.lastRow g)) := by ring
    _ = _ := by rw [hchar, one_mul]

/-- The integrand of the first Section 4.6 unfolding on the actual quotient
`N_(t_1,t_2) \ GL_(t+1)`: the actual descent of `groupIntegrand`. No coset representative
is chosen. -/
def integrand : BlockQuotient h F.Carrier → ℂ :=
  descend (blockUnipotent h F.Carrier) (groupIntegrand ell f Wtest Φ)
    (groupIntegrand_blockUnipotent_mul ell f Wtest Φ)

/-- Representative formula: `integrand [g]_H = W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)`. -/
@[simp]
theorem integrand_mk (g : GeneralLinear (t + 1) F.Carrier) :
    integrand ell f Wtest Φ (Quotient.mk _ g) =
      letI := F.canonicalTopologicalData.topology
      Wtest.val g * scalarSection (fun i => (ell i).val) f g 1 * Φ (RankinSelberg.lastRow g) :=
  rfl

/-- The fiber formula: at `[u(x) g]_H` the standard covariance of `W` on the upper
radical `u(x)` supplies the positive kernel `ψ(x_(m 0, 0))` of the raw Jacquet integrand. -/
theorem integrand_fiberPoint (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    integrand ell f Wtest Φ (fiberPoint h F.Carrier x g) =
      letI := F.canonicalTopologicalData.topology
      Wtest.val g * TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x *
        Φ (RankinSelberg.lastRow g) := by
  let := F.canonicalTopologicalData.topology
  let v : upperUnipotent (t + 1) F.Carrier :=
    ⟨upperRadical h F.Carrier x, upperRadical_mem_upperUnipotent h F.Carrier x⟩
  have hW : Wtest.val (upperRadical h F.Carrier x * g) = positiveKernel ψ x * Wtest.val g := by
    rw [positiveKernel_eq_superdiagonal_upperRadical ψ h x]
    exact Wtest.property v g
  have hrow : RankinSelberg.lastRow (upperRadical h F.Carrier x * g) =
      RankinSelberg.lastRow g :=
    RankinSelberg.lastRow_unipotent_mul v g
  rw [fiberPoint_def, integrand_mk, hW, hrow, TwoBlockJacquet.integrand_def]
  ring

/-! ### The fiber integral and the radical average -/

variable [MeasurableSpace F.Carrier]

/-- The total fiber integral of the integrand over the rectangle, at a representative `g`,
is `W(g) J(f)(g) Φ(lastRow g)` for the ordinary Bochner integral `J(f)(g)` of (4.6.2)
against the same measure. This is an identity of total integrals: no integrability is
assumed. -/
theorem fiberIntegral_integrand
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (g : GeneralLinear (t + 1) F.Carrier) :
    fiberIntegral F h μ (integrand ell f Wtest Φ) g =
      letI := F.canonicalTopologicalData.topology
      Wtest.val g * jacquetFunction ψ (fun i => (ell i).val) μ f g *
        Φ (RankinSelberg.lastRow g) := by
  let := F.canonicalTopologicalData.topology
  simp only [fiberIntegral_def, integrand_fiberPoint, jacquetFunction_def]
  rw [integral_mul_const, integral_const_mul]

/-- The published radical average of the integrand at `[g]_N` is
`W(g) J(f)(g) Φ(lastRow g)`, for every Borel additive Haar measure on the rectangle.
This is an identity of total integrals: no integrability is assumed. -/
theorem radicalAverage_integrand_mk :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace F.Carrier]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (g : GeneralLinear (t + 1) F.Carrier),
      radicalAverage F h μ (integrand ell f Wtest Φ) (Quotient.mk _ g) =
        Wtest.val g * jacquetFunction ψ (fun i => (ell i).val) μ f g *
          Φ (RankinSelberg.lastRow g) := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ g
  rw [radicalAverage_mk, ← fiberIntegral_def, fiberIntegral_integrand]

end Integrand

end Langlands.RankinSelberg.TwoBlockUnfolding
