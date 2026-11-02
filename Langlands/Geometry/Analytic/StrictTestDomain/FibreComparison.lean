import Langlands.Geometry.Analytic.StrictTestDomain.PairTest
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Lift
import Langlands.Analysis.NonarchimedeanCompletedTensorStatement
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Fibres of strict-test representations -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.Analytic

namespace FieldTensor

/-- The completed tensor statement for normed field extensions given by
isometric algebra maps. -/
theorem exists_embedding
    (hT : Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u})
    {F : Type u} [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (hF : ∃ c : F, 1 < ‖c‖)
    {E : Type u} [NormedField E] [IsUltrametricDist E] [Algebra F E]
    (hE : ∀ c : F, ‖algebraMap F E c‖ = ‖c‖)
    {E' : Type u} [NormedField E'] [IsUltrametricDist E'] [Algebra F E']
    (hE' : ∀ c : F, ‖algebraMap F E' c‖ = ‖c‖) :
    ∃ (W : Type u) (_ : NormedCommRing W) (_ : NormedAlgebra F W)
      (_ : IsUltrametricDist W) (_ : CompleteSpace W) (τ : E ⊗[F] E' →ₐ[F] W),
      Function.Injective τ ∧ ∀ (e : E) (e' : E'), ‖τ (e ⊗ₜ[F] e')‖ ≤ ‖e‖ * ‖e'‖ := by
  let : NontriviallyNormedField F := { ‹NormedField F› with non_trivial := hF }
  let : NormedAlgebra F E :=
    { ‹Algebra F E› with
      norm_smul_le := fun c e => by rw [Algebra.smul_def, norm_mul, hE] }
  let : NormedAlgebra F E' :=
    { ‹Algebra F E'› with
      norm_smul_le := fun c e => by rw [Algebra.smul_def, norm_mul, hE'] }
  exact hT F E E'

/-- If a tensor product of normed fields maps to a nonzero normed ring
contractively on pure tensors, then `h ⊗ 1 = 1 ⊗ h'` forces `‖h‖ ≤ ‖h'‖`. -/
theorem norm_le_of_tmul_eq {F E E' W : Type*} [Field F] [NormedField E] [NormedField E']
    [Algebra F E] [Algebra F E'] [NormedRing W] [Nontrivial W] [Algebra F W]
    (τ : E ⊗[F] E' →ₐ[F] W) (hτ : ∀ (e : E) (e' : E'), ‖τ (e ⊗ₜ[F] e')‖ ≤ ‖e‖ * ‖e'‖)
    {h : E} {h' : E'} (hh : h ⊗ₜ[F] (1 : E') = (1 : E) ⊗ₜ[F] h') : ‖h‖ ≤ ‖h'‖ := by
  rcases eq_or_ne h 0 with rfl | h0
  · rw [norm_zero]
    exact norm_nonneg _
  have h1 : (1 : W) = τ (h⁻¹ ⊗ₜ[F] (1 : E')) * τ ((1 : E) ⊗ₜ[F] h') := by
    rw [← hh, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ h0, mul_one,
      ← Algebra.TensorProduct.one_def, map_one]
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr h0
  have h2 : 1 ≤ ‖h‖⁻¹ * ‖h'‖ := by
    calc (1 : ℝ) ≤ ‖(1 : W)‖ := one_le_norm_one W
      _ ≤ ‖τ (h⁻¹ ⊗ₜ[F] (1 : E'))‖ * ‖τ ((1 : E) ⊗ₜ[F] h')‖ := by
          rw [h1]
          exact norm_mul_le _ _
      _ ≤ (‖h⁻¹‖ * ‖(1 : E')‖) * (‖(1 : E)‖ * ‖h'‖) :=
          mul_le_mul (hτ _ _) (hτ _ _) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖h‖⁻¹ * ‖h'‖ := by rw [norm_one, norm_one, norm_inv, mul_one, one_mul]
  calc ‖h‖ = ‖h‖ * 1 := (mul_one _).symm
    _ ≤ ‖h‖ * (‖h‖⁻¹ * ‖h'‖) := mul_le_mul_of_nonneg_left h2 hpos.le
    _ = ‖h'‖ := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- If `h ⊗ 1 = 1 ⊗ h` in `E ⊗[F] E` for a field extension `E` of `F`, then
`h` lies in `F`. -/
theorem mem_range_of_tmul_eq {F E : Type*} [Field F] [Field E] [Algebra F E] {h : E}
    (hh : h ⊗ₜ[F] (1 : E) = (1 : E) ⊗ₜ[F] h) : h ∈ Set.range (algebraMap F E) := by
  by_contra hne
  have hmem : h ∉ Submodule.span F {(1 : E)} := by
    intro hs
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs
    exact hne ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmem inferInstance
  have hf1 : f 1 = 0 := by
    have h1 : f 1 ∈ (Submodule.span F {(1 : E)}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rwa [hmap, Submodule.mem_bot] at h1
  have key := congrArg ((TensorProduct.lid F E).toLinearMap ∘ₗ f.rTensor E) hh
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, hf1, zero_smul] at key
  apply hf
  rwa [← Algebra.algebraMap_eq_smul_one, map_eq_zero] at key

end FieldTensor

namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  {K : Type v} [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]

/-- Finitely many elements of a completed residue field are simultaneously
approximated by fractions with a common denominator. -/
theorem exists_common_denominator (x : BanachSpectrum A) {m : ℕ}
    (z : Fin m → CompletedResidueField K x) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : A) (f : Fin m → A), 0 < x g ∧
      ∀ k, ‖completedResidueMap K x g * z k - completedResidueMap K x (f k)‖ < ε * x g := by
  have hd := Metric.denseRange_iff.mp (denseRange_residueCompletionMap K x)
  choose w hw using fun k => hd (z k) ε hε
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (ResidueDomain x)) (fun k => (w k).ofAbs)
  choose r hr using fun k => RingHom.mem_rangeS.mp (hb k)
  obtain ⟨g, hg⟩ : ∃ g, residueQuotient x g = (b : ResidueDomain x) :=
    Ideal.Quotient.mk_surjective _
  choose f hf using fun k => (Ideal.Quotient.mk_surjective (r k) :
    ∃ a, residueQuotient x a = r k)
  have hgpos : 0 < x g := by
    rcases (apply_nonneg x.toMulRingSeminorm g).lt_or_eq with h | h
    · exact h
    · exfalso
      apply nonZeroDivisors.ne_zero b.2
      rw [← hg]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h.symm
  refine ⟨g, f, hgpos, fun k => ?_⟩
  have hkey : completedResidueMap K x (f k) =
      completedResidueMap K x g * residueCompletionMap K x (w k) := by
    change residueCompletionMap K x (residueFieldMap K x (f k)) =
      residueCompletionMap K x (residueFieldMap K x g) * residueCompletionMap K x (w k)
    rw [← map_mul (residueCompletionMap K x)]
    congr 1
    apply WithAbs.ofAbs_injective
    change algebraMap (ResidueDomain x) (ResidueFraction x) (residueQuotient x (f k)) =
      algebraMap (ResidueDomain x) (ResidueFraction x) (residueQuotient x g) * (w k).ofAbs
    have hfk : residueQuotient x (f k) = r k := hf k
    rw [hfk, hg, ← Algebra.smul_def, hr k]
  rw [hkey, ← mul_sub, norm_mul, norm_completedResidueMap, ← dist_eq_norm, mul_comm ε]
  exact mul_lt_mul_of_pos_left (hw k) hgpos

end BanachSpectrum

namespace StrictTestDomain

open BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- For a point `y` of `M(Q)` over a point `x` of `M(P)`, the isometric
embedding of completed residue fields `H(x) → H(y)` induced by `i`. -/
def fibreEmbedding {P Q : PresentedStrictAffinoidAlgebra K} (i : BoundedAlgHom K P Q)
    {x : BanachSpectrum P} {y : BanachSpectrum Q} (hy : comap i.toBoundedRingHom y = x) :
    BoundedAlgHom K (CompletedResidueField K x) (CompletedResidueField K y) :=
  completedResidueLift K x ((completedResidueMap K y).comp i).toAlgHom fun a => by
    rw [← hy]
    exact norm_completedResidueMap K y (i a)

theorem norm_fibreEmbedding {P Q : PresentedStrictAffinoidAlgebra K} (i : BoundedAlgHom K P Q)
    {x : BanachSpectrum P} {y : BanachSpectrum Q} (hy : comap i.toBoundedRingHom y = x)
    (z : CompletedResidueField K x) : ‖fibreEmbedding i hy z‖ = ‖z‖ :=
  (isometry_completedResidueLift K x _ _).norm_map_of_map_zero
    (map_zero (fibreEmbedding i hy).toAlgHom) z

theorem fibreEmbedding_map {P Q : PresentedStrictAffinoidAlgebra K} (i : BoundedAlgHom K P Q)
    {x : BanachSpectrum P} {y : BanachSpectrum Q} (hy : comap i.toBoundedRingHom y = x)
    (a : P) : fibreEmbedding i hy (completedResidueMap K x a) = completedResidueMap K y (i a) :=
  completedResidueLift_map K x _ _ a

/-- The algebra structure of `H(y)` over `H(x)` given by `fibreEmbedding`. -/
abbrev fibreAlgebra {P Q : PresentedStrictAffinoidAlgebra K} (i : BoundedAlgHom K P Q)
    {x : BanachSpectrum P} {y : BanachSpectrum Q} (hy : comap i.toBoundedRingHom y = x) :
    Algebra (CompletedResidueField K x) (CompletedResidueField K y) :=
  (fibreEmbedding i hy).toAlgHom.toRingHom.toAlgebra

variable [CompleteSpace K]

/-- Temkin's tensor argument: if `i` represents a subset for strict tests and
`y, y'` lie over the same point `x`, then the residue values of every element
of `Q` agree in `H(y) ⊗[H(x)] H(y')`. The algebra structures over `H(x)` are
arbitrary instances agreeing with `fibreEmbedding`. -/
theorem tmul_eq_of_represents
    (hT : Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u})
    (hK : ∃ c : K, 1 < ‖c‖) {P Q : PresentedStrictAffinoidAlgebra K}
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)} (hU : Represents K i U)
    {x : BanachSpectrum P} {y y' : BanachSpectrum Q}
    (hy : comap i.toBoundedRingHom y = x) (hy' : comap i.toBoundedRingHom y' = x)
    [Algebra (CompletedResidueField K x) (CompletedResidueField K y)]
    [Algebra (CompletedResidueField K x) (CompletedResidueField K y')]
    (hE : ∀ z, algebraMap (CompletedResidueField K x) (CompletedResidueField K y) z =
      fibreEmbedding i hy z)
    (hE' : ∀ z, algebraMap (CompletedResidueField K x) (CompletedResidueField K y') z =
      fibreEmbedding i hy' z) (q : Q) :
    completedResidueMap K y q ⊗ₜ[CompletedResidueField K x]
        (1 : CompletedResidueField K y') =
      (1 : CompletedResidueField K y) ⊗ₜ[CompletedResidueField K x]
        completedResidueMap K y' q := by
  obtain ⟨c, hc⟩ := hK
  have hF : ∃ c : CompletedResidueField K x, 1 < ‖c‖ :=
    ⟨algebraMap K _ c, by rwa [norm_algebraMap']⟩
  obtain ⟨W, _, _, _, _, τ, hτ, hτn⟩ := FieldTensor.exists_embedding hT hF
    (fun z => by rw [hE]; exact norm_fibreEmbedding i hy z)
    (fun z => by rw [hE']; exact norm_fibreEmbedding i hy' z)
  let instKW : Algebra K W :=
    ((algebraMap (CompletedResidueField K x) W).comp
      (algebraMap K (CompletedResidueField K x))).toAlgebra
  let : NormedAlgebra K W :=
    { instKW with
      norm_smul_le := fun k w => by
        change ‖algebraMap (CompletedResidueField K x) W
            (algebraMap K (CompletedResidueField K x) k) * w‖ ≤ ‖k‖ * ‖w‖
        rw [← Algebra.smul_def]
        exact (norm_smul_le _ _).trans_eq (by rw [norm_algebraMap']) }
  let u : BoundedAlgHom K Q W :=
    { toRingHom := τ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom.comp
        (completedResidueMap K y).toAlgHom.toRingHom)
      commutes' := fun k => by
        change τ ((completedResidueMap K y).toAlgHom (algebraMap K Q k) ⊗ₜ[_]
            (1 : CompletedResidueField K y')) =
          algebraMap (CompletedResidueField K x) W (algebraMap K (CompletedResidueField K x) k)
        rw [(completedResidueMap K y).toAlgHom.commutes,
          ← (fibreEmbedding i hy).toAlgHom.commutes, ← hE,
          ← Algebra.TensorProduct.algebraMap_apply]
        exact τ.commutes _
      bounded := ⟨1, one_pos, fun q => by
        change ‖τ ((completedResidueMap K y).toAlgHom q ⊗ₜ[_]
          (1 : CompletedResidueField K y'))‖ ≤ 1 * ‖q‖
        refine (hτn _ _).trans ?_
        rw [norm_one, mul_one, one_mul]
        exact (norm_completedResidueMap K y q).trans_le (y.le_norm q)⟩ }
  let v : BoundedAlgHom K Q W :=
    { toRingHom := τ.toRingHom.comp
        ((Algebra.TensorProduct.includeRight :
          CompletedResidueField K y' →ₐ[CompletedResidueField K x]
            CompletedResidueField K y ⊗[CompletedResidueField K x]
              CompletedResidueField K y').toRingHom.comp
        (completedResidueMap K y').toAlgHom.toRingHom)
      commutes' := fun k => by
        change τ ((1 : CompletedResidueField K y) ⊗ₜ[_]
            (completedResidueMap K y').toAlgHom (algebraMap K Q k)) =
          algebraMap (CompletedResidueField K x) W (algebraMap K (CompletedResidueField K x) k)
        rw [(completedResidueMap K y').toAlgHom.commutes,
          ← (fibreEmbedding i hy').toAlgHom.commutes, ← hE',
          ← Algebra.TensorProduct.algebraMap_apply']
        exact τ.commutes _
      bounded := ⟨1, one_pos, fun q => by
        change ‖τ ((1 : CompletedResidueField K y) ⊗ₜ[_]
          (completedResidueMap K y').toAlgHom q)‖ ≤ 1 * ‖q‖
        refine (hτn _ _).trans ?_
        rw [norm_one, one_mul, one_mul]
        exact (norm_completedResidueMap K y' q).trans_le (y'.le_norm q)⟩ }
  have huv : u.comp i = v.comp i := by
    apply BoundedAlgHom.ext
    intro a
    change τ ((completedResidueMap K y).toAlgHom (i a) ⊗ₜ[_]
        (1 : CompletedResidueField K y')) =
      τ ((1 : CompletedResidueField K y) ⊗ₜ[_] (completedResidueMap K y').toAlgHom (i a))
    rw [← fibreEmbedding_map i hy a, ← fibreEmbedding_map i hy' a, ← hE, ← hE',
      ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  have heq := eq_of_comp_eq hU u v huv
  apply hτ
  exact congrArg (fun φ : BoundedAlgHom K Q W => φ q) heq

/-- Temkin, Prop. 2.1, injectivity: a map representing a subset for strict tests
is injective on Banach spectra. -/
theorem comap_injective_of_represents
    (hT : Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u})
    (hK : ∃ c : K, 1 < ‖c‖) {P Q : PresentedStrictAffinoidAlgebra K}
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)} (hU : Represents K i U) :
    Function.Injective (comap i.toBoundedRingHom) := by
  have key : ∀ y y' : BanachSpectrum Q,
      comap i.toBoundedRingHom y = comap i.toBoundedRingHom y' → ∀ q, y q ≤ y' q := by
    intro y y' h q
    let instE := fibreAlgebra i h
    let instE' := fibreAlgebra i (rfl : comap i.toBoundedRingHom y' = _)
    have htm := tmul_eq_of_represents hT hK hU h rfl (fun _ => rfl) (fun _ => rfl) q
    obtain ⟨c, hc⟩ := hK
    have hF : ∃ c : CompletedResidueField K (comap i.toBoundedRingHom y'), 1 < ‖c‖ :=
      ⟨algebraMap K _ c, by rwa [norm_algebraMap']⟩
    obtain ⟨W, _, _, _, _, τ, hτ, hτn⟩ := FieldTensor.exists_embedding hT hF
      (norm_fibreEmbedding i h) (norm_fibreEmbedding i rfl)
    have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
      (CompletedResidueField K (comap i.toBoundedRingHom y'))
      (CompletedResidueField K y) (CompletedResidueField K y')
      (algebraMap (CompletedResidueField K (comap i.toBoundedRingHom y'))
        (CompletedResidueField K y)).injective
      (algebraMap (CompletedResidueField K (comap i.toBoundedRingHom y'))
        (CompletedResidueField K y')).injective
    have : Nontrivial W := hτ.nontrivial
    have hle := FieldTensor.norm_le_of_tmul_eq τ hτn htm
    rwa [norm_completedResidueMap, norm_completedResidueMap] at hle
  intro y y' h
  exact BanachSpectrum.ext fun q => le_antisymm (key y y' h q) (key y' y h.symm q)

/-- Temkin, Prop. 2.1, residue fields: if `i` represents a subset for strict
tests, then the residue value at `y` of every element of `Q` lies in the image
of the completed residue field of the point below. -/
theorem mem_range_of_represents
    (hT : Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u})
    (hK : ∃ c : K, 1 < ‖c‖) {P Q : PresentedStrictAffinoidAlgebra K}
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)} (hU : Represents K i U)
    {x : BanachSpectrum P} {y : BanachSpectrum Q} (hy : comap i.toBoundedRingHom y = x)
    (q : Q) : completedResidueMap K y q ∈ Set.range (fibreEmbedding i hy) := by
  let instE := fibreAlgebra i hy
  obtain ⟨z, hz⟩ := FieldTensor.mem_range_of_tmul_eq
    (tmul_eq_of_represents hT hK hU hy hy (fun _ => rfl) (fun _ => rfl) q)
  exact ⟨z, hz⟩

/-- Temkin, Prop. 2.1, approximation form: finitely many elements of `Q` are
simultaneously approximated at `y` by fractions of elements of `P` with a
common denominator. -/
theorem exists_fraction_approximation
    (hT : Langlands.Analysis.NonarchimedeanCompletedTensorStatement.{u})
    (hK : ∃ c : K, 1 < ‖c‖) {P Q : PresentedStrictAffinoidAlgebra K}
    {i : BoundedAlgHom K P Q} {U : Set (BanachSpectrum P)} (hU : Represents K i U)
    (y : BanachSpectrum Q) {m : ℕ} (t : Fin m → Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : P) (f : Fin m → P), 0 < comap i.toBoundedRingHom y g ∧
      ∀ k, y (i g * t k - i (f k)) < ε * comap i.toBoundedRingHom y g := by
  choose z hz using fun k => mem_range_of_represents hT hK hU rfl (t k)
  obtain ⟨g, f, hg, hgf⟩ := exists_common_denominator (comap i.toBoundedRingHom y) z hε
  refine ⟨g, f, hg, fun k => ?_⟩
  have h := hgf k
  rw [← norm_fibreEmbedding i rfl, map_sub, map_mul, fibreEmbedding_map, fibreEmbedding_map,
    hz k, ← map_mul, ← map_sub, norm_completedResidueMap] at h
  exact h

end StrictTestDomain

end Langlands.Analytic
