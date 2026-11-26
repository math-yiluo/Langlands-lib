import Langlands.Global.AdelicEisensteinConvolutionIdentity
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphy
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicWavePacketTranslationReduction
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Compact conditions for the normalized adelic convolution -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "Ad" => AdelicGroupPoints F G
local notation "dh" => (Measure.haar : Measure Ad)
local notation "Λ" => ComplexCharacterParameter F P
local notation "K∞" => K.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G))
local notation "Kf" => K.comap (ContinuousMonoidHom.toMonoidHom (ofFinite F G))
omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Normalized convolution is right convolution of the twisted input followed by untwisting. -/
theorem IsIwasawaCompact.integral_translate_eq_heightPower_mul_rightConvolution
    (kernel v : Ad → ℂ) (lam : Λ) (g : Ad) :
    hK.inducedConvolution lam kernel v g = hK.heightPower (-lam) g *
      rightConvolution F G kernel (hK.parameterTwist v lam) g := by
  rw [IsIwasawaCompact.inducedConvolution, rightConvolution, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  change kernel h * (hK.heightPower (-lam) g * hK.parameterTwist v lam (g * h)) = _
  rw [mul_left_comm]

/-- The left-compact-translate span of the kernel bounds the right-compact-translate span of
the normalized convolution. Each translate is in the image of one linear map from the
left-translate span. -/
theorem IsIwasawaCompact.integral_translate_isInfiniteSubgroupFiniteFunction
    {kernel v : Ad → ℂ} (hk : IsLeftFiniteTestFunction F G K∞ kernel)
    (hv : Continuous v) (lam : Λ) :
    IsInfiniteSubgroupFiniteFunction F G K∞ (hK.inducedConvolution lam kernel v) := by
  let S := range fun k : K∞ => fun h : Ad => kernel (ofInfinite F G k * h)
  let V := Submodule.span ℂ S
  let : FiniteDimensional ℂ V := hk.2.2.1
  have hcs (ψ : Ad → ℂ) (hψ : ψ ∈ V) : Continuous ψ ∧ HasCompactSupport ψ := by
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨k, rfl⟩ := hψ
      exact ⟨hk.1.comp (continuous_const.mul continuous_id),
        hk.2.1.comp_homeomorph (Homeomorph.mulLeft _)⟩
    | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
    | add ψ χ _ _ hψ hχ => exact ⟨hψ.1.add hχ.1, hψ.2.add hχ.2⟩
    | smul c ψ _ hψ => exact ⟨continuous_const.mul hψ.1, hψ.2.smul_left⟩
  have hInt (ψ : V) (g : Ad) : Integrable
      (fun h => ψ.1 h * hK.inducedRightTranslate lam h v g) dh := by
    have hprod : Continuous (fun h => ψ.1 h * hK.inducedRightTranslate lam h v g) :=
      (hcs _ ψ.2).1.mul (continuous_const.mul
        ((hK.continuous_parameterTwist hv lam).comp (continuous_const.mul continuous_id)))
    exact hprod.integrable_of_hasCompactSupport (hcs _ ψ.2).2.mul_right
  let L : V →ₗ[ℂ] (Ad → ℂ) :=
    { toFun := fun ψ => hK.inducedConvolution lam ψ.1 v
      map_add' := fun ψ χ => by
        funext g
        change (∫ h, (ψ.1 h + χ.1 h) * hK.inducedRightTranslate lam h v g ∂dh) = _
        simp only [add_mul, integral_add (hInt ψ g) (hInt χ g)]
        rfl
      map_smul' := fun a ψ => by
        funext g
        change (∫ h, (a * ψ.1 h) * hK.inducedRightTranslate lam h v g ∂dh) = _
        simp only [mul_assoc, integral_const_mul]
        rfl }
  change FiniteDimensional ℂ (Submodule.span ℂ _)
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ : _ ≤ LinearMap.range L)
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨_, Submodule.subset_span ⟨k⁻¹, rfl⟩⟩, funext fun g => ?_⟩
  have hk_mem : ofInfinite F G (k : InfiniteAdelicGroupPoints F G) ∈ K := k.property
  have hpow : hK.heightPower (-lam) (g * ofInfinite F G k) = hK.heightPower (-lam) g := by
    simp only [IsIwasawaCompact.heightPower, hK.height_mul_right g hk_mem]
  change hK.inducedConvolution lam
    (fun h => kernel (ofInfinite F G ((k⁻¹ : K∞) : InfiniteAdelicGroupPoints F G) * h)) v g =
      hK.inducedConvolution lam kernel v (g * ofInfinite F G k)
  simp only [hK.integral_translate_eq_heightPower_mul_rightConvolution, hpow, Subgroup.coe_inv, map_inv]
  rw [rightConvolution_mul_right]

/-- An open subgroup of the finite adelic points fixes the normalized convolutions on the
right at every parameter. Intersect the left level of the kernel with the finite Iwasawa
compact, where the height is right invariant. -/
theorem IsIwasawaCompact.integral_translate_has_finite_level
    (hmax : IsMaximalCompactSubgroup F G K) {kernel : Ad → ℂ}
    (hk : IsLeftFiniteTestFunction F G K∞ kernel) :
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
      ∀ l ∈ L, ∀ v lam g,
        hK.inducedConvolution lam kernel v (g * ofFinite F G l) = hK.inducedConvolution lam kernel v g := by
  obtain ⟨L, hLo, hL⟩ := hk.2.2.2
  have hKf : Kf = K.map (finite F G).toMonoidHom := by
    ext b
    constructor
    · intro hb
      exact ⟨ofFinite F G b, hb, by simp⟩
    · rintro ⟨g, hg, rfl⟩
      have hg' : g ∈ factorSubgroup F G K∞ Kf := by
        rw [← hmax.eq_factorSubgroup]
        exact hg
      exact (mem_factorSubgroup.mp hg').2
  have hKo : IsOpen (Kf : Set (FiniteAdelicGroupPoints F G)) := by
    rw [hKf]
    exact IsMaximalCompactSubgroup.isOpen_finite F G K hmax
  refine ⟨L ⊓ Kf, hLo.inter hKo, fun l hl v lam g => ?_⟩
  have hlK : ofFinite F G l ∈ K := hl.2
  have hpow : hK.heightPower (-lam) (g * ofFinite F G l) = hK.heightPower (-lam) g := by
    simp only [IsIwasawaCompact.heightPower, hK.height_mul_right g hlK]
  simp only [hK.integral_translate_eq_heightPower_mul_rightConvolution, hpow]
  rw [rightConvolution_mul_right, ← map_inv]
  simp_rw [hL l⁻¹ (L.inv_mem hl.1)]

/-- The normalized convolution preserves a left equivariance relation at a parabolic point.
The addition of its logarithmic height cancels in the normalized translate. -/
theorem IsIwasawaCompact.integral_translate_left_equivariant
    (kernel v : Ad → ℂ) (lam : Λ) (q : AdelicGroupPoints F P) (α : ℂ)
    (heq : ∀ g, v (map F P G p q * g) = α * v g) (g : Ad) :
    hK.inducedConvolution lam kernel v (map F P G p q * g) =
      α * hK.inducedConvolution lam kernel v g := by
  have hp (z : Λ) (x : Ad) : hK.heightPower z (map F P G p q * x) =
      parameterPower F P z q * hK.heightPower z x := by
    rw [IsIwasawaCompact.heightPower, hK.height_map_mul, map_add, Complex.exp_add]
    rfl
  have hcancel : parameterPower F P (-lam) q * parameterPower F P lam q = 1 := by
    simp only [parameterPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero]
  rw [IsIwasawaCompact.inducedConvolution, IsIwasawaCompact.inducedConvolution, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [IsIwasawaCompact.inducedRightTranslate, IsIwasawaCompact.parameterTwist,
    mul_assoc (map F P G p q), heq, hp]
  calc
    _ = (parameterPower F P (-lam) q * parameterPower F P lam q) *
        (α * (kernel h * (hK.heightPower (-lam) g * (v (g * h) * hK.heightPower lam (g * h))))) := by ring
    _ = _ := by rw [hcancel, one_mul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Normalized convolution by a left-finite test function gives right archimedean compact
finiteness and one open right finite level for all parameters and all continuous inputs. -/
def NormalizedConvolutionCompactConditionsStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact p K),
    IsMaximalCompactSubgroup F G K →
    ∀ kernel : AdelicGroupPoints F G → ℂ,
      let Ki := K.comap (ofInfinite F G).toMonoidHom
      IsLeftFiniteTestFunction F G Ki kernel →
      (∀ (v : AdelicGroupPoints F G → ℂ), Continuous v →
        ∀ lam, IsInfiniteSubgroupFiniteFunction F G Ki (hK.inducedConvolution lam kernel v)) ∧
      ∃ L : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∀ l ∈ L, ∀ v lam g, hK.inducedConvolution lam kernel v (g * ofFinite F G l) =
          hK.inducedConvolution lam kernel v g

theorem normalizedConvolutionCompactConditions : NormalizedConvolutionCompactConditionsStatement := by
  intro F _ _ G P _ _ _ p _ K hK hmax kernel Ki hk
  exact ⟨fun _ hv lam => hK.integral_translate_isInfiniteSubgroupFiniteFunction hk hv lam,
    hK.integral_translate_has_finite_level hmax hk⟩

end Langlands.Global
