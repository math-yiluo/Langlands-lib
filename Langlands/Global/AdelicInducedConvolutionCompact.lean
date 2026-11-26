import Langlands.Global.AdelicInducedConvolutionFiniteSpanStatement
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.EisensteinConstantTerm.Height

/-! # Compact types and finite level of the integrated induced action -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

local notation "H" => AdelicGroupPoints F G
local notation "Kinf" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K
local notation "haar" => (Measure.haar : Measure H)

/-- Each integrand of the integrated induced action is continuous and supported on the
compact support of its kernel. -/
theorem IsIwasawaCompact.integrable_inducedConvolution_integrand (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) {φ v : H → ℂ} (hφ : Continuous φ)
    (hsupp : HasCompactSupport φ) (hv : Continuous v) (g : H) :
    Integrable (fun h => φ h * hK.inducedRightTranslate lam h v g) haar := by
  have hcont : Continuous (fun h : H => hK.inducedRightTranslate lam h v g) :=
    continuous_const.mul ((hK.continuous_parameterTwist hv lam).comp (continuous_const.mul continuous_id))
  exact (hφ.mul hcont).integrable_of_hasCompactSupport hsupp.mul_right

/-- Right translation of the output by a compact point becomes inverse left translation of the
kernel under the Haar integral. -/
theorem IsIwasawaCompact.inducedConvolution_mul_right_of_mem (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (φ v : H → ℂ) {k : H} (hk : k ∈ K) (g : H) :
    hK.inducedConvolution lam φ v (g * k) =
      hK.inducedConvolution lam (fun h => φ (k⁻¹ * h)) v g := by
  change (∫ h, φ h * hK.inducedRightTranslate lam h v (g * k) ∂haar) = _
  simp_rw [← hK.inducedRightTranslate_of_mem lam hk, hK.inducedRightTranslate_mul]
  simpa only [inv_mul_cancel_left, IsIwasawaCompact.inducedConvolution] using
    integral_mul_left_eq_self («μ» := haar)
    (fun h => φ (k⁻¹ * h) * hK.inducedRightTranslate lam h v g) k

private def leftKernelOrbit (φ : H → ℂ) : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ (Set.range fun k : Kinf => fun h : H => φ (ofInfinite F G k * h))

omit [LocallyOfFiniteType G.X.hom] in
private theorem continuous_and_compactSupport_of_mem_leftKernelOrbit {φ : H → ℂ}
    (hφ : Continuous φ) (hcomp : HasCompactSupport φ) {f : H → ℂ}
    (hf : f ∈ leftKernelOrbit (K := K) φ) : Continuous f ∧ HasCompactSupport f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    exact ⟨hφ.comp (continuous_const.mul continuous_id),
      hcomp.comp_homeomorph (Homeomorph.mulLeft (ofInfinite F G k))⟩
  | zero => exact ⟨continuous_const, HasCompactSupport.zero⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  | smul a f _ hf => exact ⟨continuous_const.smul hf.1, hf.2.smul_left⟩

private def inducedConvolutionKernelMap (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) {φ v : H → ℂ} (hφ : Continuous φ)
    (hsupp : HasCompactSupport φ) (hv : Continuous v) : leftKernelOrbit (K := K) φ →ₗ[ℂ] (H → ℂ) where
  toFun ψ := hK.inducedConvolution lam (ψ : H → ℂ) v
  map_add' ψ ψ' := by
    funext g
    obtain ⟨hc, hcs⟩ := continuous_and_compactSupport_of_mem_leftKernelOrbit hφ hsupp ψ.property
    obtain ⟨hc', hcs'⟩ := continuous_and_compactSupport_of_mem_leftKernelOrbit hφ hsupp ψ'.property
    simp only [IsIwasawaCompact.inducedConvolution, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (hK.integrable_inducedConvolution_integrand lam hc hcs hv g)
      (hK.integrable_inducedConvolution_integrand lam hc' hcs' hv g)
  map_smul' c ψ := by
    funext g
    simp only [IsIwasawaCompact.inducedConvolution, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul, RingHom.id_apply]

/-- The compact data of a left finite kernel bound the right compact data of the whole
convolution family. -/
def InducedConvolutionCompactDataStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsIwasawaCompact p K), IsMaximalCompactSubgroup F G K →
    ∀ φ v : AdelicGroupPoints F G → ℂ,
    let KArch := K.comap (ofInfinite F G).toMonoidHom
    IsLeftFiniteTestFunction F G KArch φ → Continuous v →
    ∃ (L : Subgroup (FiniteAdelicGroupPoints F G)), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
    ∃ (E : Submodule ℂ (KArch → ℂ)), FiniteDimensional ℂ E ∧
      ∀ lam : ComplexCharacterParameter F P,
        (∀ b ∈ L, ∀ g : AdelicGroupPoints F G,
          hK.inducedConvolution lam φ v (g * ofFinite F G b) = hK.inducedConvolution lam φ v g) ∧
        IsInfiniteSubgroupFiniteFunction F G KArch (hK.inducedConvolution lam φ v) ∧
        ∀ g : AdelicGroupPoints F G,
          (fun k : KArch => hK.inducedConvolution lam φ v (g * ofInfinite F G k)) ∈ E

/-- Use the left translates of the kernel to control the right action of the compact on each
output, uniformly for every complex parameter. -/
theorem inducedConvolutionCompactData : InducedConvolutionCompactDataStatement := by
  intro F _ _ G P _ _ _ _ p _ K hK hmax φ v KArch hφ hv
  let Kf := K.comap (ofFinite F G).toMonoidHom
  have hKf : IsOpen (Kf : Set (FiniteAdelicGroupPoints F G)) := by
    have heq : Kf = K.map (finite F G).toMonoidHom := by
      ext b
      constructor
      · intro hb
        exact ⟨ofFinite F G b, hb, finite_ofFinite F G b⟩
      · rintro ⟨g, hg, rfl⟩
        exact ((hmax.mem_iff g).mp hg).2
    rw [heq]
    exact hmax.isOpen_finite
  obtain ⟨L, hL, hfix⟩ := hφ.2.2.2
  let W := leftKernelOrbit (K := K) φ
  let : FiniteDimensional ℂ W := hφ.2.2.1
  let basis := Module.finBasis ℂ W
  let kernel (k : KArch) : W := ⟨fun h => φ (ofInfinite F G (k⁻¹ : KArch) * h),
    Submodule.subset_span ⟨k⁻¹, rfl⟩⟩
  let c (i : Fin (Module.finrank ℂ W)) (k : KArch) : ℂ := basis.repr (kernel k) i
  let E := Submodule.span ℂ (Set.range c)
  refine ⟨L ⊓ Kf, hL.inter hKf, E, FiniteDimensional.span_of_finite ℂ (Set.finite_range c),
    fun lam => ?_⟩
  let T := inducedConvolutionKernelMap hK lam hφ.1 hφ.2.1 hv
  have htranslate (k : KArch) (g : AdelicGroupPoints F G) :
      hK.inducedConvolution lam φ v (g * ofInfinite F G k) = T (kernel k) g := by
    have hk : ofInfinite F G (k : InfiniteAdelicGroupPoints F G) ∈ K := k.property
    rw [hK.inducedConvolution_mul_right_of_mem lam φ v hk]
    change hK.inducedConvolution lam (fun h => φ ((ofInfinite F G k)⁻¹ * h)) v g =
      hK.inducedConvolution lam (fun h => φ (ofInfinite F G (k⁻¹ : KArch) * h)) v g
    simp only [Subgroup.coe_inv, map_inv]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb g
    have hbK : ofFinite F G b ∈ K := hb.2
    rw [hK.inducedConvolution_mul_right_of_mem lam φ v hbK]
    have heq : (fun h => φ ((ofFinite F G b)⁻¹ * h)) = φ := by
      funext h
      rw [← map_inv]
      exact hfix b⁻¹ (L.inv_mem hb.1) h
    rw [heq]
  · apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨kernel k, (funext (htranslate k)).symm⟩
  · intro g
    have heq : (fun k : KArch => hK.inducedConvolution lam φ v (g * ofInfinite F G k)) =
        ∑ i, T (basis i) g • c i := by
      funext k
      rw [htranslate]
      have hk : T (kernel k) = ∑ i, basis.repr (kernel k) i • T (basis i) := by
        conv_lhs => rw [← basis.sum_repr (kernel k)]
        simp only [map_sum, map_smul]
      rw [hk]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [heq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Langlands.Global.AdelicGroupPoints
