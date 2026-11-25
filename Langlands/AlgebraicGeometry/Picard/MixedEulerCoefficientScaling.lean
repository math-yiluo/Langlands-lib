import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler
import Langlands.AlgebraicGeometry.Modules.CoherentEulerTopTwist
import Langlands.Algebra.RationalPolynomialDifferenceComparisonProof

/-! # Tensor additivity and power scaling of actual mixed Euler coefficients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules QuasicoherentLocal

local instance {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (N : Picard.LineBundle X) :
    (tensorObj M N.obj).IsQuasicoherent :=
  isQuasicoherent_tensor_lineBundle M N.obj N.property

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The kernel-cokernel Euler relation also holds after a line-bundle twist. -/
theorem coherentEulerSequence_sub_tensor [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L B : Picard.LineBundle X) :
    letI := isQuasicoherent_kernel φ
    letI := isQuasicoherent_cokernel φ
    coherentEulerSequence f (tensorObj M B.obj) (hM.tensor_lineBundle B.property) L -
        coherentEulerSequence f (tensorObj N B.obj) (hN.tensor_lineBundle B.property) L =
      coherentEulerSequence f (tensorObj (kernel φ) B.obj)
          ((hM.kernel φ).tensor_lineBundle B.property) L -
        coherentEulerSequence f (tensorObj (cokernel φ) B.obj)
          ((hN.cokernel φ).tensor_lineBundle B.property) L := by
  have := isQuasicoherent_image φ
  have := isQuasicoherent_kernel φ
  have := isQuasicoherent_cokernel φ
  let p := factorThruImage φ
  let i := image.ι φ
  have := isQuasicoherent_kernel p
  have := isQuasicoherent_cokernel i
  have hI : HasFiniteAffineSections (image φ) := hM.of_epi p
  let S₁ := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  let S₂ := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  have h₁ := coherentEulerSequence_add_tensor f S₁ hS₁ (hM.kernel p) hM hI L B
  have h₂ := coherentEulerSequence_add_tensor f S₂ hS₂ hI hN (hN.cokernel i) L B
  let eK : kernel φ ≅ kernel p :=
    (kernelIsoOfEq (image.fac φ)).symm ≪≫ kernelCompMono p i
  let eC : cokernel φ ≅ cokernel i :=
    (cokernelIsoOfEq (image.fac φ)).symm ≪≫ cokernelEpiComp p i
  have hK := coherentEulerSequence_iso f
    ((hM.kernel φ).tensor_lineBundle B.property)
    ((hM.kernel p).tensor_lineBundle B.property) L
    ((tensorBy B.obj).mapIso eK)
  have hC := coherentEulerSequence_iso f
    ((hN.cokernel φ).tensor_lineBundle B.property)
    ((hN.cokernel i).tensor_lineBundle B.property) L
    ((tensorBy B.obj).mapIso eC)
  change coherentEulerSequence f (tensorObj M B.obj) _ L = _ at h₁
  change coherentEulerSequence f (tensorObj N B.obj) _ L = _ at h₂
  rw [h₁, h₂, hK, hC]
  abel

/-- Smaller-support graph errors cancel in the first line-bundle twist difference. -/
theorem iterate_fwdDiff_twist_sub_of_graph [IsNoetherian X] [X.IsSeparated]
    (d : ℕ) (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L B : Picard.LineBundle X) (T : IrreducibleCloseds X) (hT : height T ≤ d + 1)
    (U : X.Opens) (hU : IsAffineOpen U) (hTU : ((T : Set X) ∩ U).Nonempty)
    (hMT : VanishesOn M ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hNT : VanishesOn N ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (e : N.restrict U.ι ≅ M.restrict U.ι) :
    (fwdDiff 1)^[d]
      ((coherentEulerSequence f (tensorObj N B.obj) (hN.tensor_lineBundle B.property) L -
          coherentEulerSequence f N hN L) -
        (coherentEulerSequence f (tensorObj M B.obj) (hM.tensor_lineBundle B.property) L -
          coherentEulerSequence f M hM L)) = 0 := by
  have := CoherentGraph.isQuasicoherent M N U e hU
  obtain ⟨hK₁, hC₁, hK₂, hC₂⟩ := CoherentGraph.isQuasicoherent_errors M N U e hU
  obtain ⟨hFK₁, hFC₁, hFK₂, hFC₂⟩ :=
    CoherentGraph.hasFiniteAffineSections_errors M N U e hU hM hN
  obtain ⟨hDK₁, hDC₁, hDK₂, hDC₂⟩ :=
    CoherentGraph.lowerSupportErrors M N U e T hT hTU hMT hNT
  have hG := CoherentGraph.hasFiniteAffineSections M N U e hM hN
  have h₁ := coherentEulerSequence_sub f (CoherentGraph.fst M N U e) hG hM L
  have h₂ := coherentEulerSequence_sub f (CoherentGraph.snd M N U e) hG hN L
  have ht₁ := coherentEulerSequence_sub_tensor f (CoherentGraph.fst M N U e) hG hM L B
  have ht₂ := coherentEulerSequence_sub_tensor f (CoherentGraph.snd M N U e) hG hN L B
  have hEq :
      (coherentEulerSequence f (tensorObj N B.obj) (hN.tensor_lineBundle B.property) L -
          coherentEulerSequence f N hN L) -
        (coherentEulerSequence f (tensorObj M B.obj) (hM.tensor_lineBundle B.property) L -
          coherentEulerSequence f M hM L) =
      ((coherentEulerSequence f (tensorObj (kernel (CoherentGraph.fst M N U e)) B.obj)
            (hFK₁.tensor_lineBundle B.property) L -
          coherentEulerSequence f (kernel (CoherentGraph.fst M N U e)) hFK₁ L) -
        (coherentEulerSequence f (tensorObj (cokernel (CoherentGraph.fst M N U e)) B.obj)
            (hFC₁.tensor_lineBundle B.property) L -
          coherentEulerSequence f (cokernel (CoherentGraph.fst M N U e)) hFC₁ L)) -
      ((coherentEulerSequence f (tensorObj (kernel (CoherentGraph.snd M N U e)) B.obj)
            (hFK₂.tensor_lineBundle B.property) L -
          coherentEulerSequence f (kernel (CoherentGraph.snd M N U e)) hFK₂ L) -
        (coherentEulerSequence f (tensorObj (cokernel (CoherentGraph.snd M N U e)) B.obj)
            (hFC₂.tensor_lineBundle B.property) L -
          coherentEulerSequence f (cokernel (CoherentGraph.snd M N U e)) hFC₂ L)) := by
    linear_combination ht₁ - h₁ - ht₂ + h₂
  have hk₁ := iterate_fwdDiff_tensor_sub_eq_zero f d _ hFK₁ L B hDK₁
  have hc₁ := iterate_fwdDiff_tensor_sub_eq_zero f d _ hFC₁ L B hDC₁
  have hk₂ := iterate_fwdDiff_tensor_sub_eq_zero f d _ hFK₂ L B hDK₂
  have hc₂ := iterate_fwdDiff_tensor_sub_eq_zero f d _ hFC₂ L B hDC₂
  rw [hEq]
  simp only [iterate_fwdDiff_sub] at hk₁ hc₁ hk₂ hc₂ ⊢
  linear_combination hk₁ - hc₁ - hk₂ + hc₂

end Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

private local instance (X : Scheme.{u}) : (structureSheaf X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

private local instance {X : Scheme.{u}} (N : LineBundle X) : N.obj.IsQuasicoherent :=
  N.property.isQuasicoherent

local instance {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (N : LineBundle X) :
    (tensorObj M N.obj).IsQuasicoherent :=
  QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M N.obj N.property

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Additivity of the actual mixed coefficient in its coefficient line bundle. -/
def MixedEulerCoefficientTensorAdditive (L : LineBundle X) (g : ℕ) : Prop :=
  ∀ M N : LineBundle X,
    mixedLineBundleEulerCoefficient f L (LineBundle.tensor pullbackTensorComparisonIsIso M N) g =
      mixedLineBundleEulerCoefficient f L M g + mixedLineBundleEulerCoefficient f L N g

/-- On an integral scheme of bounded positive dimension, the actual mixed
Euler coefficient is additive under tensor products of coefficient bundles. -/
theorem mixedEulerCoefficientTensorAdditive [IsNoetherian X] [X.IsSeparated] [IsIntegral X]
    (L : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d + 1) :
    MixedEulerCoefficientTensorAdditive f L (d + 1) := by
  intro M N
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨W, hxW, ⟨t⟩⟩ := M.property x
  obtain ⟨U, hU, hxU, hUW⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxW
  change X.Opens at U
  let e : M.obj.restrict U.ι ≅ (structureSheaf X).restrict U.ι :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M.obj ≪≫
      pullbackTrivializationOfLE hUW M.obj t ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hOT : QuasicoherentLocal.VanishesOn (structureSheaf X)
      ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩ := by
    apply (NoetherianVanishing.VanishesOn.bot _).mono
    intro y hy
    exact (hy (Set.mem_univ y)).elim
  have hMT : QuasicoherentLocal.VanishesOn M.obj
      ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩ := by
    apply (NoetherianVanishing.VanishesOn.bot _).mono
    intro y hy
    exact (hy (Set.mem_univ y)).elim
  have he := iterate_fwdDiff_twist_sub_of_graph f d (structureSheaf X) M.obj
    (hasFiniteAffineSections_structureSheaf X) (hasFiniteAffineSections_lineBundle M)
    L N T (NoetherianVanishing.height_le_of_topologicalKrullDim_le hX T)
    U hU ⟨x, Set.mem_univ x, hxU⟩ hOT hMT e
  have hO := coherentEulerSequence_iso f
    ((hasFiniteAffineSections_structureSheaf X).tensor_lineBundle N.property)
    (hasFiniteAffineSections_lineBundle N) L (tensorLeftUnitor N.obj)
  rw [hO] at he
  let MN := LineBundle.tensor pullbackTensorComparisonIsIso M N
  have hp := Langlands.Algebra.RationalPolynomial.coeff_eq_of_iterate_fwdDiff_sub_eq_zero
    (mixedLineBundleEulerPolynomial f L M (d + 1) +
      mixedLineBundleEulerPolynomial f L N (d + 1))
    (mixedLineBundleEulerPolynomial f L MN (d + 1)) 1 d
  have hseq :
      ((fun n : ℕ => (mixedLineBundleEulerPolynomial f L MN (d + 1)).eval (n : ℚ)) -
        fun n : ℕ => 1 * (mixedLineBundleEulerPolynomial f L M (d + 1) +
          mixedLineBundleEulerPolynomial f L N (d + 1)).eval (n : ℚ)) =
      (coherentEulerSequence f (tensorObj M.obj N.obj)
          ((hasFiniteAffineSections_lineBundle M).tensor_lineBundle N.property) L -
        coherentEulerSequence f M.obj (hasFiniteAffineSections_lineBundle M) L) -
      (coherentEulerSequence f N.obj (hasFiniteAffineSections_lineBundle N) L -
        coherentEulerSequence f (structureSheaf X)
          (hasFiniteAffineSections_structureSheaf X) L) := by
    ext n
    simp only [Pi.sub_apply, Polynomial.eval_add, one_mul,
      mixedLineBundleEulerPolynomial_eval f L MN (d + 1) hX,
      mixedLineBundleEulerPolynomial_eval f L M (d + 1) hX,
      mixedLineBundleEulerPolynomial_eval f L N (d + 1) hX]
    dsimp only [MN, LineBundle.tensor]
    ring
  have hc := hp (by rw [hseq]; exact he)
  simpa only [mixedLineBundleEulerCoefficient, Nat.add_sub_cancel,
    Polynomial.coeff_add, one_mul] using hc

/-- Positive and zero tensor powers scale the actual mixed coefficient by
the exponent. -/
theorem mixedLineBundleEulerCoefficient_tensorPow [IsNoetherian X]
    [X.IsSeparated] [IsIntegral X]
    (L N : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d + 1) (n : ℕ) :
    mixedLineBundleEulerCoefficient f L
        ⟨tensorPow N.obj n, tensorPow_isLocallyFreeRankOne X N n⟩ (d + 1) =
      (n : ℚ) * mixedLineBundleEulerCoefficient f L N (d + 1) := by
  induction n with
  | zero =>
      simpa only [tensorPow, LineBundle.trivial, structureSheaf, Nat.cast_zero, zero_mul] using
        mixedLineBundleEulerCoefficient_trivial f L (d + 1)
  | succ n ih =>
      let Nn : LineBundle X := ⟨tensorPow N.obj n, tensorPow_isLocallyFreeRankOne X N n⟩
      have ha := mixedEulerCoefficientTensorAdditive f L d hX N Nn
      change mixedLineBundleEulerCoefficient f L
        (LineBundle.tensor pullbackTensorComparisonIsIso N Nn) (d + 1) = _
      rw [ha, ih, Nat.cast_add, Nat.cast_one]
      ring

end Langlands.AlgebraicGeometry.Picard
