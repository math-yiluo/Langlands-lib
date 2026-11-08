import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.TensorProduct.Finite
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Lift
import Langlands.Geometry.Analytic.Affinoid

/-! # Finite fibres of finite bounded algebra maps -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Polynomial TensorProduct

section AbsoluteValues

variable {F : Type u} {E : Type v} [NormedField F] [Field E] [Algebra F E]

/-- Over a trivially normed field, a nonarchimedean absolute value extending
the norm is at most `1` on every integral element. -/
theorem absoluteValue_le_one_of_trivial (htriv : ∀ c : F, c ≠ 0 → ‖c‖ = 1)
    (f : AbsoluteValue E ℝ) (hna : IsNonarchimedean f)
    (hext : ∀ c : F, f (algebraMap F E c) = ‖c‖) {x : E} (hx : IsIntegral F x) :
    f x ≤ 1 := by
  by_contra h
  push Not at h
  have hp : (minpoly F x).Monic := minpoly.monic hx
  have hn : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hx
  have h0 : aeval x (minpoly F x) = 0 := minpoly.aeval F x
  rw [hp.as_sum] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have heq : x ^ (minpoly F x).natDegree =
      -∑ i ∈ Finset.range (minpoly F x).natDegree,
        algebraMap F E ((minpoly F x).coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left h0
  have hne : (Finset.range (minpoly F x).natDegree).Nonempty :=
    Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i, hi, hle⟩ := hna.finset_image_add_of_nonempty
    (fun i => algebraMap F E ((minpoly F x).coeff i) * x ^ i) hne
  have hcoeff : f (algebraMap F E ((minpoly F x).coeff i)) ≤ 1 := by
    rw [hext]
    by_cases hc : (minpoly F x).coeff i = 0
    · rw [hc, norm_zero]
      exact zero_le_one
    · exact (htriv _ hc).le
  have h1 : f x ^ (minpoly F x).natDegree ≤ f x ^ i := by
    rw [← map_pow, heq, AbsoluteValue.map_neg]
    calc _ ≤ f (algebraMap F E ((minpoly F x).coeff i) * x ^ i) := hle
      _ = f (algebraMap F E ((minpoly F x).coeff i)) * f x ^ i := by rw [map_mul, map_pow]
      _ ≤ 1 * f x ^ i := by gcongr
      _ = f x ^ i := one_mul _
  have h2 : f x ^ i < f x ^ (minpoly F x).natDegree :=
    pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  linarith

/-- Over a trivially normed field, a nonarchimedean absolute value extending
the norm is `1` on every nonzero algebraic element. -/
theorem absoluteValue_eq_one_of_trivial (htriv : ∀ c : F, c ≠ 0 → ‖c‖ = 1)
    (f : AbsoluteValue E ℝ) (hna : IsNonarchimedean f)
    (hext : ∀ c : F, f (algebraMap F E c) = ‖c‖) {x : E} (hx : IsAlgebraic F x)
    (hx0 : x ≠ 0) : f x = 1 := by
  have h1 := absoluteValue_le_one_of_trivial htriv f hna hext hx.isIntegral
  have h2 := absoluteValue_le_one_of_trivial htriv f hna hext hx.inv.isIntegral
  rw [map_inv₀] at h2
  have hpos : 0 < f x := f.pos hx0
  have : 1 ≤ f x := by
    rw [inv_le_one₀ hpos] at h2
    exact h2
  linarith

/-- Two nonarchimedean absolute values on an algebraic extension of a complete
ultrametric normed field that both extend its norm are equal. -/
theorem absoluteValue_eq_of_extends [IsUltrametricDist F] [CompleteSpace F]
    [Algebra.IsAlgebraic F E] (f g : AbsoluteValue E ℝ)
    (hfna : IsNonarchimedean f) (hgna : IsNonarchimedean g)
    (hf : ∀ c : F, f (algebraMap F E c) = ‖c‖) (hg : ∀ c : F, g (algebraMap F E c) = ‖c‖) :
    f = g := by
  ext x
  by_cases hnt : ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1
  · let : NontriviallyNormedField F := NontriviallyNormedField.ofNormNeOne hnt
    exact (spectralNorm_unique_field_norm_ext (K := F) (L := E) hf x).trans
      (spectralNorm_unique_field_norm_ext (K := F) (L := E) hg x).symm
  · push Not at hnt
    by_cases hx0 : x = 0
    · rw [hx0, map_zero, map_zero]
    · have hx : IsAlgebraic F x := Algebra.IsAlgebraic.isAlgebraic x
      rw [absoluteValue_eq_one_of_trivial hnt f hfna hf hx hx0,
        absoluteValue_eq_one_of_trivial hnt g hgna hg hx hx0]


end AbsoluteValues

section Family

/-- An absolute value pulled back along a ring map from a field to a normed
field. -/
def pullbackAbsoluteValue {Q : Type u} {L : Type v} [Field Q] [NormedField L]
    (φ : Q →+* L) : AbsoluteValue Q ℝ where
  toFun q := ‖φ q‖
  map_mul' a b := by rw [map_mul, norm_mul]
  nonneg' _ := norm_nonneg _
  eq_zero' a := by rw [norm_eq_zero, map_eq_zero_iff φ φ.injective]
  add_le' a b := by
    rw [map_add]
    exact norm_add_le _ _

/-- Let `T` be a finite algebra over a complete ultrametric normed field `H`.
A family of ring maps from `T` to ultrametric normed fields, each isometric on
`H`, and pairwise distinguished by the norms of their values, is finite. -/
theorem finite_of_isometric_family {H : Type u} [NormedField H] [IsUltrametricDist H]
    [CompleteSpace H] {T : Type v} [CommRing T] [Algebra H T] [Module.Finite H T]
    {ι : Type w} {L : ι → Type z} [∀ i, NormedField (L i)] [∀ i, IsUltrametricDist (L i)]
    (Φ : ∀ i, T →+* L i) (hΦ : ∀ i c, ‖Φ i (algebraMap H T c)‖ = ‖c‖)
    (hinj : ∀ i j, (∀ b, ‖Φ i b‖ = ‖Φ j b‖) → i = j) : Finite ι := by
  have : IsArtinianRing T := IsArtinianRing.of_finite H T
  let P : ι → PrimeSpectrum T := fun i => ⟨RingHom.ker (Φ i), RingHom.ker_isPrime _⟩
  refine Finite.of_injective P fun i j hij => hinj i j ?_
  have hker : RingHom.ker (Φ i) = RingHom.ker (Φ j) := congrArg PrimeSpectrum.asIdeal hij
  let I : Ideal T := RingHom.ker (Φ i)
  have : I.IsPrime := RingHom.ker_isPrime _
  have : I.IsMaximal := IsArtinianRing.isMaximal_of_isPrime I
  let : Field (T ⧸ I) := Ideal.Quotient.field I
  have : Module.Finite H (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ H I).toLinearMap
      Ideal.Quotient.mk_surjective
  let φi : T ⧸ I →+* L i := Ideal.Quotient.lift I (Φ i) fun a ha => ha
  let φj : T ⧸ I →+* L j := Ideal.Quotient.lift I (Φ j) fun a ha => by
    have ha' : a ∈ RingHom.ker (Φ j) := hker ▸ ha
    exact ha'
  have hext : ∀ {k : ι} (φ : T ⧸ I →+* L k),
      (∀ a, φ (Ideal.Quotient.mk I a) = Φ k a) →
        ∀ c : H, pullbackAbsoluteValue φ (algebraMap H (T ⧸ I) c) = ‖c‖ := by
    intro k φ hφ c
    change ‖φ (Ideal.Quotient.mk I (algebraMap H T c))‖ = ‖c‖
    rw [hφ, hΦ]
  have hna : ∀ {k : ι} (φ : T ⧸ I →+* L k), IsNonarchimedean (pullbackAbsoluteValue φ) := by
    intro k φ a b
    change ‖φ (a + b)‖ ≤ max ‖φ a‖ ‖φ b‖
    rw [map_add]
    exact IsUltrametricDist.norm_add_le_max _ _
  have heq := absoluteValue_eq_of_extends (F := H) (E := T ⧸ I)
    (pullbackAbsoluteValue φi) (pullbackAbsoluteValue φj) (hna φi) (hna φj)
    (hext φi fun a => Ideal.Quotient.lift_mk _ _ _)
    (hext φj fun a => Ideal.Quotient.lift_mk _ _ _)
  intro b
  have hb := congrArg (fun v : AbsoluteValue (T ⧸ I) ℝ => v (Ideal.Quotient.mk I b)) heq
  change ‖φi (Ideal.Quotient.mk I b)‖ = ‖φj (Ideal.Quotient.mk I b)‖ at hb
  have e1 : φi (Ideal.Quotient.mk I b) = Φ i b := Ideal.Quotient.lift_mk _ _ _
  have e2 : φj (Ideal.Quotient.mk I b) = Φ j b := Ideal.Quotient.lift_mk _ _ _
  rwa [e1, e2] at hb

end Family

namespace BanachSpectrum

section ResidueOver

variable (K : Type u) [NormedField K] [IsUltrametricDist K] (R : Type v) [CommRing R]

/-- The completed residue field of a point of an `R`-algebra `A`, regarded as
an `R`-algebra through the residue map. -/
def ResidueOver {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [Algebra R A]
    (x : BanachSpectrum A) : Type w :=
  CompletedResidueField K x

namespace ResidueOver

variable {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [Algebra R A]
  (x : BanachSpectrum A)

instance : NormedField (ResidueOver K R x) :=
  inferInstanceAs (NormedField (CompletedResidueField K x))

instance : IsUltrametricDist (ResidueOver K R x) :=
  inferInstanceAs (IsUltrametricDist (CompletedResidueField K x))

instance : CompleteSpace (ResidueOver K R x) :=
  inferInstanceAs (CompleteSpace (CompletedResidueField K x))

/-- The residue map of `x`, with values in `ResidueOver`. -/
def residue : A →+* ResidueOver K R x :=
  (completedResidueMap K x).toAlgHom.toRingHom

theorem norm_residue (a : A) : ‖residue K R x a‖ = x a :=
  norm_completedResidueMap K x a

instance : Algebra R (ResidueOver K R x) :=
  ((residue K R x).comp (algebraMap R A)).toAlgebra

end ResidueOver

end ResidueOver

section Fibre

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {R : Type v} [NormedCommRing R] [NormedAlgebra K R]
  {S : Type w} [NormedCommRing S] [NormedAlgebra K S] [Algebra R S]

/-- The residue embedding at a point lying over `t`. -/
def fibreResidueEmbedding (t : BanachSpectrum R) (s : BanachSpectrum S)
    (hs : ∀ a, s (algebraMap R S a) = t a) :
    ResidueOver K R t →ₐ[R] ResidueOver K R s where
  toRingHom := completedResidueLiftRingHom K t
    ((ResidueOver.residue K R s).comp (algebraMap R S))
    (fun a => (ResidueOver.norm_residue K R s (algebraMap R S a)).trans (hs a))
  commutes' a := completedResidueLiftRingHom_map K t _ _ a

theorem isometry_fibreResidueEmbedding (t : BanachSpectrum R) (s : BanachSpectrum S)
    (hs : ∀ a, s (algebraMap R S a) = t a) :
    Isometry (fibreResidueEmbedding (K := K) t s hs) :=
  isometry_completedResidueLiftRingHom K t
    ((ResidueOver.residue K R s).comp (algebraMap R S))
    (fun a => (ResidueOver.norm_residue K R s (algebraMap R S a)).trans (hs a))

/-- The residue map of a point as an `R`-algebra map. -/
def residueAlgHom (s : BanachSpectrum S) : S →ₐ[R] ResidueOver K R s where
  toRingHom := ResidueOver.residue K R s
  commutes' _ := rfl

/-- The map from the base change of `S` to the completed residue field at `t`
into the completed residue field of a point over `t`. -/
def fibreTensorMap (t : BanachSpectrum R) (s : BanachSpectrum S)
    (hs : ∀ a, s (algebraMap R S a) = t a) :
    ResidueOver K R t ⊗[R] S →ₐ[R] ResidueOver K R s :=
  Algebra.TensorProduct.productMap (fibreResidueEmbedding t s hs) (residueAlgHom s)

variable (K) in
include K in
/-- For a finite `R`-algebra `S`, only finitely many points of the spectrum of
`S` lie over a given point of the spectrum of `R`. -/
theorem finite_setOf_over [Module.Finite R S] (t : BanachSpectrum R) :
    {s : BanachSpectrum S | ∀ a, s (algebraMap R S a) = t a}.Finite := by
  let ι := {s : BanachSpectrum S | ∀ a, s (algebraMap R S a) = t a}
  have hfin : Finite ι := by
    refine finite_of_isometric_family (H := ResidueOver K R t)
      (T := ResidueOver K R t ⊗[R] S) (L := fun s : ι => ResidueOver K R s.1)
      (fun s => (fibreTensorMap t s.1 s.2).toRingHom) (fun s c => ?_) (fun s s' h => ?_)
    · change ‖fibreTensorMap t s.1 s.2 (c ⊗ₜ 1)‖ = ‖c‖
      rw [fibreTensorMap, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
      exact (isometry_fibreResidueEmbedding t s.1 s.2).norm_map_of_map_zero (map_zero _) c
    · apply Subtype.ext
      apply BanachSpectrum.ext
      intro a
      have ha := h (1 ⊗ₜ a)
      change ‖fibreTensorMap t s.1 s.2 (1 ⊗ₜ a)‖ = ‖fibreTensorMap t s'.1 s'.2 (1 ⊗ₜ a)‖ at ha
      rw [fibreTensorMap, fibreTensorMap, Algebra.TensorProduct.productMap_apply_tmul,
        Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, one_mul, one_mul] at ha
      change ‖ResidueOver.residue K R s.1 a‖ = ‖ResidueOver.residue K R s'.1 a‖ at ha
      rwa [ResidueOver.norm_residue, ResidueOver.norm_residue] at ha
  exact Set.toFinite ι

end Fibre

end BanachSpectrum

namespace BoundedAlgHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {R : Type v} {S : Type w} [NormedCommRing R] [NormedCommRing S]
  [NormedAlgebra K R] [NormedAlgebra K S]

/-- The fibre of the spectrum map of `f` over a point `t`. -/
def fibre (f : BoundedAlgHom K R S) (t : BanachSpectrum R) : Set (BanachSpectrum S) :=
  {s | BanachSpectrum.comap f.toBoundedRingHom s = t}

omit [IsUltrametricDist K] in
/-- Fibres are closed: the spectrum map is continuous and the spectrum is
Hausdorff. -/
theorem isClosed_fibre (f : BoundedAlgHom K R S) (t : BanachSpectrum R) :
    IsClosed (f.fibre t) :=
  isClosed_singleton.preimage (BanachSpectrum.comapContinuous f.toBoundedRingHom).continuous

/-- The fibres of the spectrum map of a bounded algebra map that is finite as a
ring map are finite. -/
theorem finite_fibre (f : BoundedAlgHom K R S) (hf : f.toAlgHom.toRingHom.Finite)
    (t : BanachSpectrum R) : (f.fibre t).Finite := by
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  have : Module.Finite R S := hf
  refine (BanachSpectrum.finite_setOf_over K t).subset fun s hs a => ?_
  rw [← hs]
  rfl

end BoundedAlgHom

end Langlands.Analytic
