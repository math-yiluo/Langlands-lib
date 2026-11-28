import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Analysis.SeveralComplex.RankWitness
import Langlands.Analysis.Meromorphic.ScalarIdentity
import Mathlib.Analysis.Complex.Convex

/-! # The regularized integral along translated coordinate faces -/

noncomputable section

open MeasureTheory Set Filter

set_option autoImplicit false

namespace Langlands.Global

variable {n : ℕ} {J : Type*} [Fintype J]

local notation "Spectral" => (Fin n → ℂ)

private def facePolynomialTemplate (i : J ↪ Fin n) (p : MvPolynomial (Fin n) ℂ) :
    MvPolynomial J (MvPolynomial (Fin n) ℂ) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun a => MvPolynomial.C (MvPolynomial.X a) +
      ∑ j ∈ Finset.univ.filter (fun j => i j = a), MvPolynomial.X j) p

/-- Substitute a base point and a coordinate face into the given ambient polynomial.
The coefficients in the face variables are evaluated polynomials in the base point. -/
def translatedFacePolynomial (i : J ↪ Fin n) (p : MvPolynomial (Fin n) ℂ) (b : Fin n → ℝ) :
    MvPolynomial J ℂ :=
  MvPolynomial.map (MvPolynomial.eval (fun a => (b a : ℂ))) (facePolynomialTemplate i p)

theorem eval_translatedFacePolynomial (i : J ↪ Fin n) (p : MvPolynomial (Fin n) ℂ)
    (b : Fin n → ℝ) (u : J → ℝ) :
    (translatedFacePolynomial i p b).eval (fun j => (u j : ℂ)) =
      p.eval (fun a => (b a : ℂ) + ∑ j ∈ Finset.univ.filter (fun j => i j = a), (u j : ℂ)) := by
  rw [translatedFacePolynomial, MvPolynomial.eval_map]
  change MvPolynomial.eval₂Hom _ _ (facePolynomialTemplate i p) = _
  rw [facePolynomialTemplate, MvPolynomial.map_eval₂Hom]
  congr 2
  · ext c
    simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, RingHom.id_apply]
  · funext a
    simp only [map_add, map_sum, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]

private theorem negativeOrthantRegularizedIntegral_map_eval (i : J ↪ Fin n)
    (p : MvPolynomial (Fin n) ℂ) (b : Fin n → ℝ) (z : Spectral) :
    negativeOrthantRegularizedIntegral (fun j => z (i j)) (translatedFacePolynomial i p b) =
      ∑ k ∈ (facePolynomialTemplate i p).support,
        ((facePolynomialTemplate i p).coeff k).eval (fun a => (b a : ℂ)) *
          ∏ j, orthantFactor (k j) (z (i j)) := by
  let q := facePolynomialTemplate i p
  let f := MvPolynomial.eval (fun a => (b a : ℂ))
  let r := MvPolynomial.map f q
  change (∑ k ∈ r.support, r.coeff k * ∏ j, orthantFactor (k j) (z (i j))) = _
  rw [Finset.sum_subset (MvPolynomial.support_map_subset f q)
    (fun k _ hk => by rw [MvPolynomial.notMem_support_iff.mp hk, zero_mul])]
  exact Finset.sum_congr rfl fun k _ => by rw [MvPolynomial.coeff_map]

/-- The part of the regularized integral over a translated coordinate face, integrated
against the measure of base points. The base measure can be a restriction to a bounded
cell by taking the base space to be a compact closure. -/
def regularizedAffineFaceIntegral {Y : Type*} [MeasurableSpace Y] (dy : Measure Y)
    (i : J ↪ Fin n) (b : Y → Fin n → ℝ) (p : MvPolynomial (Fin n) ℂ) (z : Spectral) : ℂ :=
  ∫ y, Complex.exp (∑ a, z a * (b y a : ℂ)) *
    negativeOrthantRegularizedIntegral (fun j => z (i j)) (translatedFacePolynomial i p (b y)) ∂dy

/-- An ordinary iterated integral over a translated negative orthant, or over a translated
coordinate face when the embedding only selects part of the coordinates. -/
def affineFaceIntegral (i : J ↪ Fin n) (b : Fin n → ℝ) (p : MvPolynomial (Fin n) ℂ) (z : Spectral) : ℂ :=
  ∫ u in univ.pi (fun _ : J => Iic (0 : ℝ)),
    let x (a : Fin n) := b a + ∑ j ∈ Finset.univ.filter (fun j => i j = a), u j
    Complex.exp (∑ a, z a * (x a : ℂ)) * p.eval (fun a => (x a : ℂ))

/-- In the positive real chamber this is the convergent iterated integral over the
translated face. -/
theorem regularizedAffineFaceIntegral_eq_integral_pos {Y : Type*} [MeasurableSpace Y] (dy : Measure Y)
    (i : J ↪ Fin n) (b : Y → Fin n → ℝ) (p : MvPolynomial (Fin n) ℂ) (z : Spectral)
    (hz : ∀ a, 0 < (z a).re) :
    regularizedAffineFaceIntegral dy i b p z = ∫ y, affineFaceIntegral i (b y) p z ∂dy := by
  unfold regularizedAffineFaceIntegral affineFaceIntegral
  apply integral_congr_ae
  filter_upwards with y
  rw [negativeOrthantRegularizedIntegral_eq_integral (fun j => hz (i j)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  dsimp only
  rw [eval_translatedFacePolynomial]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, mul_add, Finset.sum_add_distrib,
    Complex.exp_add, ← mul_assoc]
  congr 2
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply congrArg Complex.exp
  apply Finset.sum_congr rfl
  intro j _
  simp [eq_comm]

private theorem isOpen_coordinateNonzero (n : ℕ) : IsOpen {z : Fin n → ℂ | ∀ a, z a ≠ 0} := by
  have he : {z : Fin n → ℂ | ∀ a, z a ≠ 0} = ⋂ a : Fin n, {z : Fin n → ℂ | z a ≠ 0} := by
    ext z
    simp
  rw [he]
  exact isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_apply a) continuous_const

/-- Holomorphy of a regularized translated face on the common nonzero-coordinate locus.
Compactness and the fixed polynomial support provide bounds on compact spectral sets. -/
def RegularizedAffineFaceHolomorphyStatement : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (dy : Measure Y) [IsFiniteMeasure dy] (i : J ↪ Fin n) (b : Y → Fin n → ℝ)
    (p : MvPolynomial (Fin n) ℂ), Continuous b →
    DifferentiableOn ℂ (regularizedAffineFaceIntegral dy i b p) {z | ∀ a, z a ≠ 0}

set_option maxHeartbeats 3600000 in
theorem regularizedAffineFaceHolomorphy : RegularizedAffineFaceHolomorphyStatement (n := n) (J := J) := by
  intro Y _ _ _ _ dy _ i b p hb
  let D : Set Spectral := {s | ∀ a, s a ≠ 0}
  let q := facePolynomialTemplate i p
  let term (y : Y) (s : Spectral) := Complex.exp (∑ a, s a * (b y a : ℂ)) *
    ∑ k ∈ q.support, (q.coeff k).eval (fun a => (b y a : ℂ)) * ∏ j, orthantFactor (k j) (s (i j))
  have hD : IsOpen D := isOpen_coordinateNonzero n
  have hEq : regularizedAffineFaceIntegral dy i b p = fun s => ∫ y, term y s ∂dy := by
    funext s
    simp only [regularizedAffineFaceIntegral, term, negativeOrthantRegularizedIntegral_map_eval, q]
  have hd (y : Y) : DifferentiableOn ℂ (term y) D := by
    unfold term
    refine (Differentiable.fun_sum fun a _ => (differentiable_apply a).mul_const _).cexp.differentiableOn.mul ?_
    refine DifferentiableOn.fun_sum fun k _ => DifferentiableOn.const_mul ?_ _
    apply Langlands.Analysis.SeveralComplex.differentiableOn_finset_prod_apply Finset.univ
    intro j hj
    simp only [orthantFactor, div_eq_mul_inv]
    have hi : DifferentiableOn ℂ (fun s : Spectral => (s (i j) ^ (k j + 1))⁻¹) D :=
      ((differentiable_apply (i j)).pow (k j + 1)).differentiableOn.inv
        (fun s hs => pow_ne_zero _ (hs (i j)))
    exact hi.const_mul _
  have hc : ContinuousOn (fun x : Spectral × Y => term x.2 x.1) (D ×ˢ univ) := by
    unfold term
    refine (Complex.continuous_exp.comp (continuous_finsetSum _ fun a _ =>
      ((continuous_apply a).comp continuous_fst).mul (Complex.continuous_ofReal.comp
        ((continuous_apply a).comp (hb.comp continuous_snd))))).continuousOn.mul ?_
    refine continuousOn_finsetSum _ fun k _ => ?_
    refine ((MvPolynomial.continuous_eval _).comp
      (continuous_pi fun a => Complex.continuous_ofReal.comp ((continuous_apply a).comp
        (hb.comp continuous_snd)))).continuousOn.mul ?_
    refine continuousOn_finsetProd _ fun j _ => ?_
    simp only [orthantFactor, div_eq_mul_inv]
    exact ((((continuous_apply (i j)).comp continuous_fst).pow _).continuousOn.inv₀
      fun s hs => pow_ne_zero _ (hs.1 (i j))).const_mul _
  rw [hEq]
  refine Langlands.Analysis.SeveralComplex.differentiableOn_integral_of_bounded dy
    (fun s y => term y s) hD hd (fun s hs => ?_) ?_
  · let m (y : Y) : Spectral × Y := (s, y)
    have hm : Continuous m := continuous_const.prodMk continuous_id
    have hmaps : MapsTo m (univ : Set Y) (D ×ˢ univ) := fun y _ => ⟨hs, mem_univ y⟩
    have hCm : ContinuousOn ((fun x : Spectral × Y => term x.2 x.1) ∘ m) (univ : Set Y) :=
      hc.comp hm.continuousOn hmaps
    exact (continuousOn_univ.mp hCm).aestronglyMeasurable
  · intro K hKD hK
    obtain ⟨B, hB⟩ := (hK.prod isCompact_univ).bddAbove_image (hc.mono
      (Set.prod_mono hKD subset_rfl)).norm
    exact ⟨B, fun s hs y => hB ⟨(s, y), ⟨hs, mem_univ y⟩, rfl⟩⟩

private theorem translatedFacePolynomial_refl (p : MvPolynomial (Fin n) ℂ) (t : Fin n → ℝ) :
    translatedFacePolynomial (Function.Embedding.refl (Fin n)) p t = polynomialShift t p := by
  rw [translatedFacePolynomial, facePolynomialTemplate, MvPolynomial.map_eval₂Hom]
  unfold polynomialShift
  change MvPolynomial.eval₂Hom _ _ p = MvPolynomial.eval₂Hom _ _ p
  congr 2
  · ext c
    simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C, MvPolynomial.algebraMap_eq]
  · funext a
    simp only [Function.Embedding.refl_apply, map_add, MvPolynomial.map_C, MvPolynomial.map_X,
      MvPolynomial.eval_X, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_comm]

private theorem isPreconnected_coordinateNonzero (n : ℕ) : IsPreconnected {z : Fin n → ℂ | ∀ a, z a ≠ 0} := by
  have he : {z : Fin n → ℂ | ∀ a, z a ≠ 0} = univ.pi (fun _ : Fin n => ({0} : Set ℂ)ᶜ) := by
    ext z
    simp [Set.mem_pi]
  rw [he]
  have hC : IsPathConnected (({0} : Set ℂ)ᶜ) := by
    apply (isPathConnected_iff_pathConnectedSpace (F := ({0} : Set ℂ)ᶜ)).mpr
    exact (unitsHomeomorphNeZero (G₀ := ℂ)).surjective.pathConnectedSpace
      (unitsHomeomorphNeZero (G₀ := ℂ)).continuous
  have hP : IsPathConnected (univ.pi (fun _ : Fin n => ({0} : Set ℂ)ᶜ)) :=
    IsPathConnected.pi fun _ => hC
  exact hP.isConnected.isPreconnected

/-- Given a finite recombination of ordinary translated-face integrals in the positive chamber,
the same equality holds for the regularized values where all ambient coordinates are nonzero.
The base measures are finite on compact spaces, so bounded split domains can be represented by
restrictions of measures on their closures. -/
def RegularizedAffineFaceRecombinationStatement : Prop :=
  ∀ {m : ℕ} (J : Fin m → Type) [∀ k, Fintype (J k)] (Y : Fin m → Type)
    [∀ k, TopologicalSpace (Y k)] [∀ k, CompactSpace (Y k)]
    [∀ k, MeasurableSpace (Y k)] [∀ k, BorelSpace (Y k)]
    (dy : ∀ k, Measure (Y k)) [∀ k, IsFiniteMeasure (dy k)]
    (i : ∀ k, J k ↪ Fin n) (b : ∀ k, Y k → Fin n → ℝ) (t : Fin n → ℝ)
    (p : MvPolynomial (Fin n) ℂ), (∀ k, Continuous (b k)) →
    (∀ z : Spectral, (∀ a, 0 < (z a).re) →
      affineFaceIntegral (Function.Embedding.refl (Fin n)) t p z =
        ∑ k, ∫ y, affineFaceIntegral (i k) (b k y) p z ∂dy k) →
    ∀ z : Spectral, (∀ a, z a ≠ 0) →
      Complex.exp (∑ a, z a * (t a : ℂ)) * negativeOrthantRegularizedIntegral z (polynomialShift t p) =
        ∑ k, regularizedAffineFaceIntegral (dy k) (i k) (b k) p z

set_option maxHeartbeats 2600000 in
theorem regularizedAffineFaceRecombination : RegularizedAffineFaceRecombinationStatement (n := n) := by
  intro m labels _ Y _ _ _ _ dy _ i b t p hb hsum
  let F₀ := regularizedAffineFaceIntegral (Measure.dirac ()) (Function.Embedding.refl (Fin n))
    (fun _ => t) p
  let F₁ (z : Spectral) := ∑ k, regularizedAffineFaceIntegral (dy k) (i k) (b k) p z
  let D : Set Spectral := {z | ∀ a, z a ≠ 0}
  let U : Set Spectral := {z | ∀ a, 0 < (z a).re}
  have hD : IsOpen D := isOpen_coordinateNonzero n
  have hU : IsOpen U := by
    have he : U = ⋂ a : Fin n, {z : Spectral | 0 < (z a).re} := by ext z; simp [U]
    rw [he]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply a))
  have hF₀ : DifferentiableOn ℂ F₀ D :=
    regularizedAffineFaceHolomorphy Unit (Measure.dirac ()) (Function.Embedding.refl (Fin n))
      (fun _ => t) p continuous_const
  have hF₁ : DifferentiableOn ℂ F₁ D :=
    DifferentiableOn.fun_sum fun k _ => regularizedAffineFaceHolomorphy (Y k) (dy k) (i k) (b k) p (hb k)
  have hEq : EqOn F₀ F₁ U := by
    intro z hz
    have h₀ : F₀ z = affineFaceIntegral (Function.Embedding.refl (Fin n)) t p z := by
      rw [show F₀ z = _ from regularizedAffineFaceIntegral_eq_integral_pos (Measure.dirac ())
        (Function.Embedding.refl (Fin n)) (fun _ => t) p z hz]
      simp [Measure.real]
    have h₁ (k : Fin m) : regularizedAffineFaceIntegral (dy k) (i k) (b k) p z =
        ∫ y, affineFaceIntegral (i k) (b k y) p z ∂dy k :=
      regularizedAffineFaceIntegral_eq_integral_pos (dy k) (i k) (b k) p z hz
    rw [h₀, hsum z hz]
    exact Finset.sum_congr rfl fun k _ => (h₁ k).symm

  have hsub : U ⊆ D := by
    intro z hz a hza
    have hp := hz a
    simp [hza] at hp
  have hne : U.Nonempty := ⟨fun _ => 1, by simp [U]⟩
  have hzero : EqOn (fun z => F₀ z - F₁ z) 0 U := fun z hz => sub_eq_zero.mpr (hEq hz)
  have h := Langlands.Analysis.Meromorphic.differentiableOn_eqOn_zero_of_isPreconnected
    (hF₀.sub hF₁) hD (isPreconnected_coordinateNonzero n) hU hsub hne hzero
  intro z hz
  have he : F₀ z = F₁ z := sub_eq_zero.mp (h (show z ∈ D from hz))
  simpa [F₀, F₁, regularizedAffineFaceIntegral, Measure.real, Function.Embedding.refl_apply,
    translatedFacePolynomial_refl] using he

end Langlands.Global
