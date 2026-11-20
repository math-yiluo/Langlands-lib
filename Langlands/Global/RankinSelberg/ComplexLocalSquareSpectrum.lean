import Langlands.Global.RankinSelberg.ComplexUnitarySkewPairing
import Langlands.Representation.Archimedean.ComplexLocalEllipticAnnihilator
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Langlands.HarmonicAnalysis.Distribution.RenardHeckeCompactHaar
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Eigenvector decomposition for the complex coordinate square operator -/

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean
open ComplexDuality.LieInvariance (skewRe skewIm star_skewRe star_skewIm)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Std" => Automorphic.complexStandardKFinite n

local instance (j : ℕ) : MeasurableSpace (unitaryCompact ℂ j) := borel _
local instance (j : ℕ) : BorelSpace (unitaryCompact ℂ j) := ⟨rfl⟩

variable {ds : List ComplexCharacterData}
  (μ : Measure (unitaryCompact ℂ n)) [μ.IsHaarMeasure]

private def standardUnitaryPairing (f g : Std ds) : ℂ :=
  complexUnitaryPairing μ (f : G → ℂ) (g : G → ℂ)

local notation "P" => standardUnitaryPairing μ

private theorem standardUnitaryPairing_integrable (f g : Std ds) :
    Integrable (fun k : K => star ((f : G → ℂ) k.val) * (g : G → ℂ) k.val) μ :=
  (((f.property.1.1.continuous.comp continuous_subtype_val).star).mul
    (g.property.1.1.continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

omit [μ.IsHaarMeasure] in
private theorem standardUnitaryPairing_conj (f g : Std ds) : star (P f g) = P g f := by
  unfold standardUnitaryPairing complexUnitaryPairing
  change (starRingEnd ℂ) (∫ k, star ((f : G → ℂ) k.val) * (g : G → ℂ) k.val ∂μ) = _
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun k => by
    change star (star ((f : G → ℂ) k.val) * (g : G → ℂ) k.val) =
      star ((g : G → ℂ) k.val) * (f : G → ℂ) k.val
    rw [star_mul, star_star]

private theorem standardUnitaryPairing_add_left (f g h : Std ds) :
    P (f + g) h = P f h + P g h := by
  unfold standardUnitaryPairing complexUnitaryPairing
  simp only [Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  exact integral_add (standardUnitaryPairing_integrable μ f h)
    (standardUnitaryPairing_integrable μ g h)

omit [μ.IsHaarMeasure] in
private theorem standardUnitaryPairing_smul_left (c : ℂ) (f g : Std ds) :
    P (c • f) g = star c * P f g := by
  unfold standardUnitaryPairing complexUnitaryPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun k => by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul]
    ring

private theorem standardUnitaryPairing_re (f : Std ds) :
    (P f f).re = ∫ k : K, ‖(f : G → ℂ) k.val‖ ^ 2 ∂μ := by
  unfold standardUnitaryPairing complexUnitaryPairing
  change RCLike.re (∫ k, star ((f : G → ℂ) k.val) * (f : G → ℂ) k.val ∂μ) = _
  rw [← integral_re (standardUnitaryPairing_integrable μ f f)]
  exact integral_congr_ae (ae_of_all _ fun k => by
    let z := (f : G → ℂ) k.val
    change ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re])

private theorem standardUnitaryPairing_definite (f : Std ds) (hf : P f f = 0) : f = 0 := by
  apply Subtype.ext
  apply ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary f.property.1 (Submodule.zero_mem _)
  intro k hk
  by_contra hne
  have hcont : Continuous (fun u : K => ‖(f : G → ℂ) u.val‖ ^ 2) :=
    ((f.property.1.1.continuous.comp continuous_subtype_val).norm).pow 2
  have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ)
    (x := ⟨k, hk⟩) (HasCompactSupport.of_compactSpace _) (fun _ => sq_nonneg _)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))
  rw [← standardUnitaryPairing_re μ f, hf] at hpos
  exact lt_irrefl 0 hpos

@[instance_reducible]
private def unitaryPairingCore (V : Submodule ℂ (Std ds)) : InnerProductSpace.Core ℂ V where
  inner f g := P f.val g.val
  conj_inner_symm f g := standardUnitaryPairing_conj μ g.val f.val
  re_inner_nonneg f := by
    change (P f.val f.val).re ≥ 0
    rw [standardUnitaryPairing_re]
    exact integral_nonneg fun _ => sq_nonneg _
  add_left f g h := standardUnitaryPairing_add_left μ f.val g.val h.val
  smul_left f g c := standardUnitaryPairing_smul_left μ c f.val g.val
  definite f hf := Subtype.ext (standardUnitaryPairing_definite μ f.val hf)

private theorem standardUnitaryPairing_generator_skew [μ.IsInvInvariant]
    {X : M} (hX : X.conjTranspose = -X) (f g : Std ds) :
    let A := envelopingAction (complexStandardLie n ds) (realGenerator n X)
    P (A f) g + P f (A g) = 0 := by
  dsimp only
  let A := envelopingAction (complexStandardLie n ds) (realGenerator n X)
  have hD (v : Std ds) :
      Continuous (rightDerivative (matrixModel ℂ n) X (v : G → ℂ)) :=
    (realGenerator_action ds X v) ▸ (A v).property.1.1.continuous
  unfold standardUnitaryPairing
  rw [realGenerator_action, realGenerator_action]
  exact complexUnitaryPairing_rightDerivative_add_eq_zero μ hX f.property.1.1
    g.property.1.1 (hD f) (hD g)

omit [μ.IsHaarMeasure] in
private theorem standardUnitaryPairing_smul_right (c : ℂ) (u v : Std ds) :
    P u (c • v) = c * P u v := by
  rw [← standardUnitaryPairing_conj μ (c • v) u, standardUnitaryPairing_smul_left,
    star_mul, star_star, standardUnitaryPairing_conj]
  exact mul_comm _ _

private theorem standardUnitaryPairing_add_right (u v w : Std ds) :
    P u (v + w) = P u v + P u w := by
  rw [← standardUnitaryPairing_conj μ (v + w) u, standardUnitaryPairing_add_left,
    star_add, standardUnitaryPairing_conj, standardUnitaryPairing_conj]

private def standardSymmetricEndomorphisms (ds : List ComplexCharacterData) :
    AddSubmonoid (Module.End ℂ (Std ds)) where
  carrier := {T | ∀ f g, P (T f) g = P f (T g)}
  zero_mem' := by
    intro f g
    change P 0 g = P f 0
    simp [standardUnitaryPairing, complexUnitaryPairing]
  add_mem' := by
    intro S T hS hT f g
    change P (S f + T f) g = P f (S g + T g)
    exact (standardUnitaryPairing_add_left μ _ _ _).trans
      ((congrArg₂ (· + ·) (hS f g) (hT f g)).trans
        (standardUnitaryPairing_add_right μ _ _ _).symm)

private theorem compactGenerator_square_mem [μ.IsInvInvariant]
    {X : M} (hX : X.conjTranspose = -X) :
    envelopingAction (complexStandardLie n ds) (realGenerator n X ^ 2) ∈
      standardSymmetricEndomorphisms μ ds := by
  let A := envelopingAction (complexStandardLie n ds)
  change ∀ f g, P (A (realGenerator n X ^ 2) f) g = P f (A (realGenerator n X ^ 2) g)
  intro f g
  rw [map_pow, pow_two, Module.End.mul_apply, Module.End.mul_apply]
  have h₁ := standardUnitaryPairing_generator_skew μ hX (A (realGenerator n X) f) g
  have h₂ := standardUnitaryPairing_generator_skew μ hX f (A (realGenerator n X) g)
  linear_combination h₁ - h₂

private theorem standardUnitaryPairing_compactSquare_symm [μ.IsInvInvariant] (f g : Std ds) :
    let T := envelopingAction (complexStandardLie n ds) (compactSquareSum n)
    P (T f) g = P f (T g) := by
  let A := envelopingAction (complexStandardLie n ds)
  let U := ∑ i : Fin n, ∑ j : Fin n,
    (realGenerator n (skewRe i j) ^ 2 + realGenerator n (skewIm i j) ^ 2)
  let S := standardSymmetricEndomorphisms μ ds
  have hU : A U ∈ S := by
    simp only [U, map_sum, map_add]
    refine S.sum_mem fun i _ => S.sum_mem fun j _ => S.add_mem ?_ ?_
    · exact compactGenerator_square_mem μ (star_skewRe i j)
    · exact compactGenerator_square_mem μ (star_skewIm i j)
  have heq : P (A U f) g = P f (A U g) := hU f g
  change P (A ((1 / 4 : ℂ) • U) f) g = P f (A ((1 / 4 : ℂ) • U) g)
  rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, standardUnitaryPairing_smul_left,
    standardUnitaryPairing_smul_right, heq]
  rw [show star (1 / 4 : ℂ) = 1 / 4 by
    change (starRingEnd ℂ) _ = _
    simp [map_ofNat]]

/-- Each unitary-finite vector is a finite linear combination of eigenvectors
of the real coordinate square sum. -/
theorem exists_coordinateSquare_eigenvector_expansion (ds : List ComplexCharacterData)
    (f : Std ds) :
    ∃ (m : ℕ) (v : Fin m → Std ds) (a c : Fin m → ℂ),
      f = ∑ j, a j • v j ∧ ∀ j, coordinateSquareOperator ds (v j) = c j • v j := by
  classical
  let μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  let : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let : IsProbabilityMeasure μ :=
    Langlands.HarmonicAnalysis.Distribution.RenardHecke.isProbabilityMeasure_haarMeasure_top
  let : μ.IsInvInvariant :=
    Langlands.HarmonicAnalysis.Distribution.RenardHecke.isInvInvariant_of_compact μ
  obtain ⟨V, hVfin, hf, hV⟩ := exists_invariant_coordinateSquareOperator_submodule ds f
  let : FiniteDimensional ℂ V := hVfin
  let C := envelopingAction (complexStandardLie n ds) (compactSquareSum n)
  obtain ⟨b, hb⟩ := complexStandardLie_hasInfinitesimalCharacter n ds (matrixCasimir n)
    (matrixCasimir_mem_center n)
  have hC (v : Std ds) :
      coordinateSquareOperator ds v = b • v + (2 : ℂ) • C v := by
    simp only [coordinateSquareOperator, coordinateSquareSum_eq_casimir_add_compact, map_add,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, hb, Module.algebraMap_end_apply, C]
  have hCV (v : Std ds) (hv : v ∈ V) : C v ∈ V := by
    have hv' := V.sub_mem (hV v hv) (V.smul_mem b hv)
    rw [hC, add_sub_cancel_left] at hv'
    exact (V.smul_mem_iff (by norm_num : (2 : ℂ) ≠ 0)).mp hv'
  let T := C.restrict hCV
  let core := unitaryPairingCore μ V
  let : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ core
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hT : T.IsSymmetric := fun v w => standardUnitaryPairing_compactSquare_symm μ v.val w.val
  let basis := hT.eigenvectorBasis (n := Module.finrank ℂ V) rfl
  let u : V := ⟨f, hf⟩
  refine ⟨Module.finrank ℂ V, fun j => (basis j : V).val, fun j => basis.toBasis.repr u j,
    fun j => b + (2 : ℂ) * (hT.eigenvalues rfl j : ℂ), ?_, fun j => ?_⟩
  · simpa only [Submodule.coe_sum, Submodule.coe_smul, basis.coe_toBasis, u] using
      congrArg Subtype.val (basis.toBasis.sum_repr u).symm
  · rw [hC]
    have hj := congrArg Subtype.val (hT.apply_eigenvectorBasis rfl j)
    change C (basis j).val = (hT.eigenvalues rfl j : ℂ) • (basis j).val at hj
    rw [hj, add_smul, mul_smul]

end Langlands.Global.RankinSelbergGlobal
