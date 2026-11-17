import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantStatement
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeStatement
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceStatement
import Langlands.AbelianScheme.Tate.GeometricPrimeAdicRankProof
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityReduction
import Langlands.CategoryTheory.RationalizationDenominators
import Langlands.AbelianScheme.IntegralInverseIsogeny
import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphismRosati
import Langlands.AlgebraicGeometry.Picard.DualMapRational
import Langlands.AlgebraicGeometry.FiniteFlatConstantRankCompositionProof
import Langlands.AlgebraicGeometry.Modules.CoherentEulerTopTwist
import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Polynomial.Roots

/-! # Reduction of the Mumford Rosati trace formula to degree statements

`MumfordMixedEulerTraceReductionStatement` says that the degree statement
`IsogenyDegreeTateDeterminantStatement` and the Euler-degree statement
`MumfordEulerDegreeStatement` imply `MumfordMixedEulerTraceStatement`.
`mumfordMixedEulerTraceReduction` proves it by comparing the coefficients of `n ^ (2g)`
and `n ^ (2g - 1)` in two expressions for the degree of
`(n • lam + f ≫ lam ≫ f^∨) ≫ μ`, where `μ` is an integral multiple of the inverse of `lam`.
-/

noncomputable section

universe u

open Polynomial CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati.MumfordTraceReduction

/-- If `r Q² = c D` with `D` monic of degree `2g`, `Q` of degree at most `g` and
`c ≠ 0`, then `2 Q_{g-1} = Q_g · nextCoeff D`. -/
theorem two_mul_coeff_pred_eq {K : Type*} [Field K] {g : ℕ} (hg : 0 < g)
    {D Q : K[X]} {r c : K} (hc : c ≠ 0) (hD : D.Monic) (hDdeg : D.natDegree = 2 * g)
    (hQ : Q.natDegree ≤ g) (h : C r * Q ^ 2 = C c * D) :
    2 * Q.coeff (g - 1) = Q.coeff g * D.nextCoeff := by
  have h2g : (C r * Q ^ 2).coeff (2 * g) = (C c * D).coeff (2 * g) := by rw [h]
  rw [coeff_C_mul, coeff_C_mul, coeff_pow_of_natDegree_le hQ, ← hDdeg,
    ← Polynomial.leadingCoeff, hD.leadingCoeff, mul_one] at h2g
  set q := Q.coeff g with hqdef
  have hq : q ≠ 0 := by
    intro h0
    rw [h0] at h2g
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2g
    exact hc h2g.symm
  have hQdeg : Q.natDegree = g := le_antisymm hQ (le_natDegree_of_ne_zero hq)
  obtain ⟨Q', hQ'def⟩ : ∃ Q' : K[X], Q' = C q⁻¹ * Q := ⟨_, rfl⟩
  have hQ'deg : Q'.natDegree = g := by
    rw [hQ'def, natDegree_C_mul (inv_ne_zero hq), hQdeg]
  have hQ'monic : Q'.Monic := by
    rw [Monic, hQ'def, leadingCoeff_mul, leadingCoeff_C, Polynomial.leadingCoeff, hQdeg,
      inv_mul_cancel₀ hq]
  have hQeq : Q = C q * Q' := by
    rw [hQ'def, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hq, C_1, one_mul]
  have hsq : Q' ^ 2 = D := by
    have hcd : C c * Q' ^ 2 = C c * D := by
      calc C c * Q' ^ 2 = C (r * q ^ 2) * Q' ^ 2 := by rw [h2g]
        _ = C r * (C q * Q') ^ 2 := by rw [mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
        _ = C r * Q ^ 2 := by rw [← hQeq]
        _ = C c * D := h
    exact mul_left_cancel₀ (C_ne_zero.mpr hc) hcd
  have hnext : D.nextCoeff = 2 * Q'.nextCoeff := by
    rw [← hsq, hQ'monic.nextCoeff_pow, nsmul_eq_mul, Nat.cast_ofNat]
  have hQ'next : Q'.nextCoeff = q⁻¹ * Q.coeff (g - 1) := by
    rw [nextCoeff_of_natDegree_pos (by omega), hQ'deg, hQ'def, coeff_C_mul]
  rw [hnext, hQ'next]
  field_simp

/-- A polynomial over a characteristic-zero field whose values at all natural
numbers are rational has rational coefficients. -/
theorem coeff_mem_range_of_eval_natCast {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (p : K[X]) (h : ∀ n : ℕ, p.eval (n : K) ∈ Set.range (algebraMap ℚ K)) (i : ℕ) :
    p.coeff i ∈ Set.range (algebraMap ℚ K) := by
  classical
  choose v hv using h
  set d := p.natDegree
  let s : Finset ℚ := (Finset.range (d + 1)).image (fun n : ℕ => (n : ℚ))
  let w : ℚ → ℚ := fun x => v x.num.toNat
  let R : ℚ[X] := Lagrange.interpolate s id w
  have hinj : Set.InjOn (id : ℚ → ℚ) s := Set.injOn_id _
  have hscard : s.card = d + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  let t : Finset K := (Finset.range (d + 1)).image (fun n : ℕ => (n : K))
  have htcard : t.card = d + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hpR : p = R.map (algebraMap ℚ K) := by
    apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq t
    · rw [htcard]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self d)
      · rw [degree_map]
        have := Lagrange.degree_interpolate_lt (s := s) (v := id) w hinj
        rwa [hscard] at this
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
      have hns : (n : ℚ) ∈ s := Finset.mem_image.mpr ⟨n, hn, rfl⟩
      have hR : R.eval (n : ℚ) = v n := by
        have := Lagrange.eval_interpolate_at_node (s := s) (v := id) w hinj hns
        simpa only [id, w, Rat.num_natCast, Int.toNat_natCast] using this
      rw [← hv n, Polynomial.eval_map, ← map_natCast (algebraMap ℚ K) n,
        Polynomial.eval₂_at_apply, hR]
  rw [hpR, Polynomial.coeff_map]
  exact ⟨_, rfl⟩

/-- The next coefficient of the characteristic polynomial of `-T` is the trace of `T`. -/
theorem nextCoeff_charpoly_neg {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V) :
    (LinearMap.charpoly (-T)).nextCoeff = LinearMap.trace K V T := by
  have h := Matrix.trace_eq_neg_charpoly_nextCoeff
    (LinearMap.toMatrix (Module.Free.chooseBasis K V) (Module.Free.chooseBasis K V) (-T))
  rw [← LinearMap.trace_eq_matrix_trace, map_neg, ← LinearMap.charpoly_def] at h
  linear_combination h

/-- Evaluating the characteristic polynomial of `-T` gives `det (t + T)`. -/
theorem eval_charpoly_neg {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V) (t : K) :
    (LinearMap.charpoly (-T)).eval t = LinearMap.det (algebraMap K (Module.End K V) t + T) := by
  rw [LinearMap.eval_charpoly, sub_neg_eq_add]

section Tate

variable {k : Type u} [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))

/-- On an actual integral endomorphism, the rational action is its actual Tate map. -/
theorem rationalEndAction_homToHom0 (p : ℕ) [Fact p.Prime] (α : A ⟶ A) :
    Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A (homToHom0 α) =
      Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α := by
  rw [Tate.PrimeAdic.rationalEndAction_apply, homToHom0_apply,
    Tate.PrimeAdic.rationalHomMap_tmul, one_smul]

/-- The prime trace is the trace of the rational action. -/
theorem primeEndomorphismTrace_eq (p : ℕ) [Fact p.Prime] (a : End0 A) :
    primeEndomorphismTrace A p a =
      LinearMap.trace ℚ_[p] _ (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A a) :=
  rfl

/-- In characteristic zero every nonzero integer is a unit of the global sections. -/
theorem isUnit_intCast_global [CharZero k] (n : ℤ) (hn : n ≠ 0) :
    IsUnit (n : Γ(Scheme.Spec.obj (Opposite.op (CommRingCat.of k)), ⊤)) := by
  have hn' : (n : k) ≠ 0 := Int.cast_ne_zero.mpr hn
  simpa using (Ne.isUnit hn').map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- The rational `2`-adic Tate module has dimension `2g`. -/
theorem rational_two_finrank [IsAlgClosed k] [CharZero k] (g : ℕ)
    (hA : A.HasRelativeDimension g) :
    FiniteDimensional ℚ_[2] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) 2) ∧
      Module.finrank ℚ_[2] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) 2) = 2 * g := by
  have h2 : IsUnit ((2 : ℕ) : Γ(Scheme.Spec.obj (Opposite.op (CommRingCat.of k)), ⊤)) := by
    simpa using isUnit_intCast_global (k := k) 2 two_ne_zero
  obtain ⟨-, hfin, hrank⟩ := Tate.PrimeAdic.geometricPrimeAdicRank _ A g hA 2 h2 k (𝟙 _)
  exact ⟨hfin, hrank⟩

/-- An abelian scheme over a field has a point. -/
theorem nonempty_left : Nonempty A.X.left := by
  let pt : Scheme.Spec.obj (Opposite.op (CommRingCat.of k)) := IsLocalRing.closedPoint k
  exact ⟨(MonObj.one (X := A.X)).left pt⟩

/-- Under the degree statement, the actual `2`-adic trace of every integral
endomorphism is rational. -/
theorem trace_rationalMap_mem_range (hS1 : IsogenyDegreeTateDeterminantStatement.{u})
    [IsAlgClosed k] [CharZero k] (g : ℕ) (hA : A.HasRelativeDimension g) (α : A ⟶ A) :
    LinearMap.trace ℚ_[2] _ (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) 2 α) ∈
      Set.range (algebraMap ℚ ℚ_[2]) := by
  obtain ⟨hfin, -⟩ := rational_two_finrank A g hA
  obtain ⟨y⟩ := nonempty_left A
  have h2 : ((2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr two_ne_zero
  have hdet : ∀ n : ℕ, (LinearMap.charpoly
      (-Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) 2 α)).eval (n : ℚ_[2]) ∈
        Set.range (algebraMap ℚ ℚ_[2]) := by
    intro n
    rw [eval_charpoly_neg]
    have hmap : algebraMap ℚ_[2] (Module.End ℚ_[2] _) (n : ℚ_[2]) +
        Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) 2 α =
          Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) 2 (n • 𝟙 A + α) := by
      rw [← rationalEndAction_homToHom0 A 2 (n • 𝟙 A + α), map_add homToHom0,
        map_nsmul homToHom0, homToHom0_id,
        map_add (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) 2 A),
        map_nsmul (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) 2 A),
        rationalEndAction_homToHom0, Algebra.algebraMap_eq_smul_one, Nat.cast_smul_eq_nsmul]
      congr 2
      exact (map_one (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) 2 A)).symm
    rw [hmap]
    by_cases hiso : IsIsogeny (n • 𝟙 A + α)
    · rw [← ((hS1 k A 2 h2 (n • 𝟙 A + α)).1 hiso y)]
      exact ⟨_, map_natCast _ _⟩
    · rw [(hS1 k A 2 h2 (n • 𝟙 A + α)).2 hiso]
      exact ⟨0, map_zero _⟩
  rw [← nextCoeff_charpoly_neg, Polynomial.nextCoeff]
  split_ifs
  · exact ⟨0, map_zero _⟩
  · exact coeff_mem_range_of_eval_natCast _ hdet _

/-- Under the degree statement, the actual `2`-adic trace of every rational
endomorphism is rational. -/
theorem primeEndomorphismTrace_mem_range (hS1 : IsogenyDegreeTateDeterminantStatement.{u})
    [IsAlgClosed k] [CharZero k] (g : ℕ) (hA : A.HasRelativeDimension g) (a : End0 A) :
    primeEndomorphismTrace A 2 a ∈ Set.range (algebraMap ℚ ℚ_[2]) := by
  obtain ⟨N, hN, α, hα⟩ := Rationalization.exists_integral_multiple a
  obtain ⟨q, hq⟩ := trace_rationalMap_mem_range A hS1 g hA α
  have hα' : homToHom0 α = N • a := hα
  have htr : primeEndomorphismTrace A 2 (homToHom0 α) =
      (N : ℚ_[2]) * primeEndomorphismTrace A 2 a := by
    rw [hα', map_zsmul, zsmul_eq_mul]
  rw [primeEndomorphismTrace_eq, rationalEndAction_homToHom0, ← hq] at htr
  have hN' : (N : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr hN
  refine ⟨q / N, ?_⟩
  rw [map_div₀, map_intCast, htr, mul_div_cancel_left₀ _ hN']

/-- Under the degree statement, the chosen geometric trace is the rational lift of
the actual `2`-adic trace. -/
theorem algebraMap_geometricEndomorphismTrace
    (hS1 : IsogenyDegreeTateDeterminantStatement.{u})
    [IsAlgClosed k] [CharZero k] (g : ℕ) (hA : A.HasRelativeDimension g) (a : End0 A) :
    algebraMap ℚ ℚ_[2] (geometricEndomorphismTrace A a) = primeEndomorphismTrace A 2 a := by
  choose t ht using primeEndomorphismTrace_mem_range A hS1 g hA
  let T : End0 A →ₗ[ℚ] ℚ :=
    { toFun := t
      map_add' := fun a b => (algebraMap ℚ ℚ_[2]).injective (by
        rw [map_add, ht, ht, ht, map_add])
      map_smul' := fun q a => (algebraMap ℚ ℚ_[2]).injective (by
        rw [ht, map_smul, RingHom.id_apply, smul_eq_mul, map_mul, ht, Algebra.smul_def]) }
  rw [geometricEndomorphismTrace_eq A T ht]
  exact ht a

end Tate

section Polarization

open Langlands.AlgebraicGeometry.Picard

variable (P : Prerequisites.{u}) {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)

/-- The actual dual endomorphism formed with the witnesses of `W` on both sides. -/
abbrev dualMap (f : A ⟶ A) : W.dual P ⟶ W.dual P :=
  dualAbelianSchemeMapFromEvaluation W.hasDual W.geometry P.preservation
    W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry W.hasDual W.geometry W.inversePoincare
    W.evaluation f

theorem dual0_homToHom0 (f : A ⟶ A) :
    W.dual0 P hadd (homToHom0 f) = homToHom0 (dualMap P W f) :=
  dualHom0_homToHom0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f

variable [HasRationalInverse P W lam]

/-- A positive integral multiple of the rational inverse of `lam` is an actual isogeny. -/
theorem exists_integral_inverse [CharZero k] :
    ∃ (N : ℤ) (μ : W.dual P ⟶ A), 0 < N ∧
      homToHom0 μ = N • polarizationInverse P W lam ∧ IsIsogeny μ := by
  obtain ⟨n, hn, μ₀, hμ₀⟩ := Rationalization.exists_integral_multiple (polarizationInverse P W lam)
  have hμ₀' : homToHom0 μ₀ = n • polarizationInverse P W lam := hμ₀
  have hμ : homToHom0 (n • μ₀) = (n * n) • polarizationInverse P W lam := by
    rw [map_zsmul homToHom0 n μ₀, hμ₀', smul_smul]
  refine ⟨n * n, n • μ₀, mul_self_pos.mpr hn, hμ, ?_⟩
  have hlm : lam ≫ (n • μ₀) = (n * n) • 𝟙 A := by
    apply homToHom0_injective_of_charZero A A
    rw [← comp0_homToHom0, hμ, map_zsmul, polarization_comp_inverse, map_zsmul homToHom0,
      homToHom0_id]
  have hml : (n • μ₀) ≫ lam = (n * n) • 𝟙 (W.dual P) := by
    apply homToHom0_injective_of_charZero _ _
    rw [← comp0_homToHom0, hμ, map_zsmul (comp0 _ _ _), LinearMap.smul_apply,
      inverse_comp_polarization, map_zsmul homToHom0, homToHom0_id]
  let d : Rationalization.IntegralInverseData A (W.dual P) :=
    { multiple := n * n
      multiple_ne_zero := mul_ne_zero hn hn
      hom := lam
      inv := n • μ₀
      hom_inv := hlm
      inv_hom := hml }
  exact (integralInverseData_finiteEtaleIsogenies d (mul_self_pos.mpr hn)
    (isUnit_intCast_global _ (mul_ne_zero hn hn))).2.2.1

/-- The rational class of `(n • lam + f ≫ lam ≫ f^∨) ≫ μ`. -/
theorem homToHom0_comp_inverse (N : ℤ) (μ : W.dual P ⟶ A)
    (hμ : homToHom0 μ = N • polarizationInverse P W lam) (f : A ⟶ A) (n : ℕ) :
    homToHom0 ((n • lam + (f ≫ lam ≫ dualMap P W f : A ⟶ W.dual P)) ≫ μ) =
      (N : ℚ) • ((n : End0 A) + involution P W hadd lam (homToHom0 f) * endToEnd0 A f) := by
  rw [← comp0_homToHom0, hμ, map_add homToHom0, map_nsmul homToHom0, ← comp0_homToHom0,
    ← comp0_homToHom0, ← dual0_homToHom0 P W hadd, end0_mul, involution_apply,
    map_zsmul (comp0 _ _ _ _), map_add (comp0 _ _ _), LinearMap.add_apply,
    map_nsmul (comp0 _ _ _), LinearMap.smul_apply, polarization_comp_inverse,
    endToEnd0_apply, ← comp0_assoc, ← comp0_assoc, comp0_assoc (homToHom0 f) (homToHom0 lam),
    Int.cast_smul_eq_zsmul, show (n : End0 A) = n • id0 A from (nsmul_one n).symm]

/-- Determinant of the Tate map of `(n • lam + f ≫ lam ≫ f^∨) ≫ μ`. -/
theorem det_rationalMap_comp_inverse (g : ℕ)
    [FiniteDimensional ℚ_[2] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) 2)]
    (hrank : Module.finrank ℚ_[2] (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) 2) = 2 * g)
    (N : ℤ) (μ : W.dual P ⟶ A) (hμ : homToHom0 μ = N • polarizationInverse P W lam)
    (f : A ⟶ A) (n : ℕ) :
    LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) 2
        ((n • lam + (f ≫ lam ≫ dualMap P W f : A ⟶ W.dual P)) ≫ μ)) =
      (N : ℚ_[2]) ^ (2 * g) * (LinearMap.charpoly
        (-Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) 2 A
          (involution P W hadd lam (homToHom0 f) * endToEnd0 A f))).eval (n : ℚ_[2]) := by
  rw [← rationalEndAction_homToHom0, homToHom0_comp_inverse P W hadd lam N μ hμ f n, map_smul,
    map_add, map_natCast, eval_charpoly_neg, map_natCast (algebraMap ℚ_[2] _), ← hrank,
    ← LinearMap.det_smul]
  congr 1

end Polarization

section Rank

variable {k : Type u} [Field k]

theorem spec_subsingleton : Subsingleton (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))

theorem spec_nonempty : Nonempty (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))

theorem spec_isLocallyNoetherian :
    IsLocallyNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))

/-- An isogeny of abelian schemes over a field has constant rank on its target. -/
theorem finrank_eq_of_isIsogeny
    {B C : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    (φ : B ⟶ C) (hφ : IsIsogeny φ) (z z' : C.X.left) :
    (hom φ).finrank z = (hom φ).finrank z' := by
  obtain ⟨hfin, hflat, -⟩ := (isIsogeny_iff φ).mp hφ
  have := spec_subsingleton (k := k)
  have := spec_nonempty (k := k)
  have := spec_isLocallyNoetherian (k := k)
  have : ConnectedSpace C.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C.X.hom)
  have : IsLocallyNoetherian C.X.left := LocallyOfFiniteType.isLocallyNoetherian C.X.hom
  have : LocallyOfFinitePresentation (hom φ) := inferInstance
  exact (hom φ).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z z'

/-- The rank of a composite of isogenies, the first of constant rank `r`. -/
theorem finrank_comp_of_isIsogeny
    {B C D : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    (φ : B ⟶ C) (χ : C ⟶ D) (hφ : IsIsogeny φ) (hχ : IsIsogeny χ) (r : ℕ)
    (hr : ∀ y, (hom φ).finrank y = r) (z₀ z : D.X.left) :
    (hom (φ ≫ χ)).finrank z = r * (hom χ).finrank z₀ := by
  obtain ⟨hfin, hflat, -⟩ := (isIsogeny_iff φ).mp hφ
  obtain ⟨hfin', hflat', -⟩ := (isIsogeny_iff χ).mp hχ
  have := spec_isLocallyNoetherian (k := k)
  have : IsLocallyNoetherian D.X.left := LocallyOfFiniteType.isLocallyNoetherian D.X.hom
  rw [hom_comp]
  exact Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition _ _ _ (hom φ) (hom χ)
    r _ hr (fun z => finrank_eq_of_isIsogeny χ hχ z z₀) z

end Rank

section Euler

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X : Scheme.{u}} {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- On a smooth proper scheme of relative dimension `g` over a field, the canonical Euler
polynomial of a line bundle `N` twisted by `L` evaluates to the actual Euler sequence,
its top coefficient is that of the pure polynomial of `L`, and the mixed coefficient is
the difference of the subleading coefficients. -/
theorem euler_facts (g : ℕ) (hs : SmoothOfRelativeDimension g f) (L N : LineBundle X) :
    (∀ n : ℕ, (coherentEulerPolynomial f N.obj (hasFiniteAffineSections_lineBundle N) L g).eval
        (n : ℚ) = coherentEulerSequence f N.obj (hasFiniteAffineSections_lineBundle N) L n) ∧
      (coherentEulerPolynomial f N.obj (hasFiniteAffineSections_lineBundle N) L g).coeff g =
        (lineBundleEulerPolynomial f L g).coeff g ∧
      mixedLineBundleEulerCoefficient f L N g =
        (coherentEulerPolynomial f N.obj (hasFiniteAffineSections_lineBundle N) L g).coeff
          (g - 1) - (lineBundleEulerPolynomial f L g).coeff (g - 1) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth g f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let : X.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.IsSeparated) (f := f)).mp
      inferInstance
  have : (structureSheaf X).IsQuasicoherent := (LineBundle.trivial X).property.isQuasicoherent
  have : (tensorObj (structureSheaf X) N.obj).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_tensor_lineBundle _ N.obj N.property
  have hdim : topologicalKrullDim X ≤ g :=
    Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim K X f g hs inferInstance
  refine ⟨fun n => coherentEulerPolynomial_eval f N.obj _ L g
    (HasSupportDimensionLT.of_topologicalKrullDim_le hdim _) n, ?_, ?_⟩
  · have h := topEulerCoefficientTwistInvariant f g (structureSheaf X)
      (hasFiniteAffineSections_structureSheaf X) L N
      (HasSupportDimensionLT.of_topologicalKrullDim_le hdim _)
    unfold TopEulerCoefficientTwistInvariant at h
    rw [coherentEulerPolynomial_iso f _ (hasFiniteAffineSections_lineBundle N) L g
      (tensorLeftUnitor N.obj)] at h
    exact h
  · simp only [mixedLineBundleEulerCoefficient, mixedLineBundleEulerPolynomial,
      Polynomial.coeff_sub]

/-- Pulling the coefficient bundle back along the identity does not change it. -/
theorem mixed_pullback_id (L : LineBundle X) (d : ℕ) :
    mixedLineBundleEulerCoefficient f L ((LineBundle.pullback (𝟙 X)).obj L) d =
      mixedLineBundleEulerCoefficient f L L d := by
  unfold mixedLineBundleEulerCoefficient
  rw [mixedLineBundleEulerPolynomial_iso f L _ L d ((Scheme.Modules.pullbackId X).app L.obj)]

/-- The mixed coefficient of `L` with itself is `g` times the top pure coefficient. -/
theorem mixed_self_eq (g : ℕ) (hg : 0 < g) (hs : SmoothOfRelativeDimension g f)
    (L : LineBundle X) :
    mixedLineBundleEulerCoefficient f L L g = g * (lineBundleEulerPolynomial f L g).coeff g := by
  let : Smooth f := SmoothOfRelativeDimension.smooth g f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let : X.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.IsSeparated) (f := f)).mp
      inferInstance
  have hdim : topologicalKrullDim X ≤ g :=
    Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim K X f g hs inferInstance
  obtain ⟨d, rfl⟩ : ∃ d, g = d + 1 := ⟨g - 1, by omega⟩
  exact mixedLineBundleEulerCoefficient_self f L d (by exact_mod_cast hdim)

end Euler

section Key

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The key identity: twice the subleading coefficient of the Euler polynomial of
`f^* L` equals its top coefficient times the `2`-adic trace of `f† f`. -/
theorem key_identity (hS1 : IsogenyDegreeTateDeterminantStatement.{u})
    (hS2 : MumfordEulerDegreeStatement.{u})
    (P : Prerequisites.{u}) (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [HasRationalInverse P W lam]
    (g : ℕ) (hg : 0 < g) (hA : A.HasRelativeDimension g)
    (L : LineBundle A.X.left)
    (B : LineBundle (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj)
      B.obj ≅ structureSheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize P.preservation A.X.hom (unitSection A)
        (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅
          structureSheaf A.X.left)
    (hL : L.IsAmple)
    (hpres : (groupHom lam).hom.hom =
      mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
        P.square W.hasDual)
    (f : A ⟶ A) :
    2 * algebraMap ℚ ℚ_[2] ((coherentEulerPolynomial A.X.hom
        ((LineBundle.pullback (hom f)).obj L).obj (hasFiniteAffineSections_lineBundle _)
          L g).coeff (g - 1)) =
      algebraMap ℚ ℚ_[2] ((coherentEulerPolynomial A.X.hom
        ((LineBundle.pullback (hom f)).obj L).obj (hasFiniteAffineSections_lineBundle _)
          L g).coeff g) *
        primeEndomorphismTrace A 2 (involution P W hadd lam (homToHom0 f) * endToEnd0 A f) := by
  obtain ⟨hfin, hrank⟩ := rational_two_finrank A g hA
  obtain ⟨N, μ, hNpos, hμ, hμiso⟩ := exists_integral_inverse P W lam
  have hn₀ := hS2 P k A W lam L B evaluationB M evaluation hL hpres f
  obtain ⟨n₀, hn₀⟩ := hn₀
  have hn₀' : ∀ n : ℕ, n₀ ≤ n →
      IsIsogeny (n • lam + (f ≫ lam ≫ dualMap P W f : A ⟶ W.dual P)) ∧
        ∀ y : (W.dual P).X.left,
          ((hom (n • lam + (f ≫ lam ≫ dualMap P W f : A ⟶ W.dual P))).finrank y : ℚ) =
            coherentEulerSequence A.X.hom ((LineBundle.pullback (hom f)).obj L).obj
              (hasFiniteAffineSections_lineBundle _) L n ^ 2 := hn₀
  obtain ⟨heval, -, -⟩ := euler_facts A.X.hom g hA L ((LineBundle.pullback (hom f)).obj L)
  obtain ⟨z₀⟩ := nonempty_left A
  obtain ⟨y₁⟩ := nonempty_left (W.dual P)
  have h2 : ((2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr two_ne_zero
  have hpoly : C (((hom μ).finrank z₀ : ℕ) : ℚ_[2]) *
      ((coherentEulerPolynomial A.X.hom ((LineBundle.pullback (hom f)).obj L).obj
        (hasFiniteAffineSections_lineBundle _) L g).map (algebraMap ℚ ℚ_[2])) ^ 2 =
      C ((N : ℚ_[2]) ^ (2 * g)) * LinearMap.charpoly
        (-Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) 2 A
          (involution P W hadd lam (homToHom0 f) * endToEnd0 A f)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem
      (f := fun m : ℕ => ((n₀ + m : ℕ) : ℚ_[2]))
      (Nat.cast_injective.comp (add_right_injective n₀))
    intro m
    simp only [Set.mem_ofPred_eq]
    obtain ⟨hiso, hrk⟩ := hn₀' (n₀ + m) (Nat.le_add_right _ _)
    have hconst : ∀ y, (hom (((n₀ + m : ℕ)) • lam +
        (f ≫ lam ≫ dualMap P W f : A ⟶ W.dual P))).finrank y =
          (hom (((n₀ + m : ℕ)) • lam +
            (f ≫ lam ≫ dualMap P W f : A ⟶ W.dual P))).finrank y₁ := fun y =>
      Nat.cast_injective (R := ℚ) (by rw [hrk y, hrk y₁])
    have hfr := finrank_comp_of_isIsogeny _ μ hiso hμiso _ hconst z₀ z₀
    have hdet := (hS1 k A 2 h2 _).1 (hiso.comp hμiso) z₀
    rw [det_rationalMap_comp_inverse P W hadd lam g hrank N μ hμ f (n₀ + m), hfr] at hdet
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_map,
      ← map_natCast (algebraMap ℚ ℚ_[2]) (n₀ + m), Polynomial.eval₂_at_apply, heval,
      Polynomial.eval_mul, Polynomial.eval_C, map_natCast, ← hdet, ← map_pow, ← hrk y₁]
    push_cast
    ring
  have hkey := two_mul_coeff_pred_eq hg
    (pow_ne_zero _ (Int.cast_ne_zero.mpr hNpos.ne')) (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree, hrank])
    (Polynomial.natDegree_map_le.trans (coherentEulerPolynomial_natDegree_le _ _ _ _ _)) hpoly
  rw [Polynomial.coeff_map, Polynomial.coeff_map, nextCoeff_charpoly_neg] at hkey
  rw [primeEndomorphismTrace_eq]
  exact hkey

end Key

end Langlands.AbelianScheme.Rosati.MumfordTraceReduction

namespace Langlands.AbelianScheme.Rosati

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
  MumfordTraceReduction

set_option backward.isDefEq.respectTransparency false

/-- The degree statement `IsogenyDegreeTateDeterminantStatement` and the Euler-degree
statement `MumfordEulerDegreeStatement` together imply the Mumford Rosati mixed Euler
trace formula `MumfordMixedEulerTraceStatement`, at the same universe. -/
def MumfordMixedEulerTraceReductionStatement : Prop :=
  IsogenyDegreeTateDeterminantStatement.{u} → MumfordEulerDegreeStatement.{u} →
    MumfordMixedEulerTraceStatement.{u}

/-- Proof of the reduction by comparing the coefficients of `n ^ (2g)` and
`n ^ (2g - 1)` of the degree polynomial of `(n • lam + f ≫ lam ≫ f^∨) ≫ μ`. -/
theorem mumfordMixedEulerTraceReduction : MumfordMixedEulerTraceReductionStatement.{u} := by
  intro hS1 hS2 P k _ _ _ A W hadd lam _ g hg hA L B evaluationB M evaluation hL hpres f
  obtain ⟨hfin, hrank⟩ := rational_two_finrank A g hA
  have hkf := key_identity hS1 hS2 P k A W hadd lam g hg hA L B evaluationB M evaluation hL
    hpres f
  have hk1 := key_identity hS1 hS2 P k A W hadd lam g hg hA L B evaluationB M evaluation hL
    hpres (𝟙 A)
  obtain ⟨-, htopf, hmixf⟩ := euler_facts A.X.hom g hA L ((LineBundle.pullback (hom f)).obj L)
  obtain ⟨-, htop1, hmix1⟩ :=
    euler_facts A.X.hom g hA L ((LineBundle.pullback (hom (𝟙 A))).obj L)
  have hβ1 : involution P W hadd lam (homToHom0 (𝟙 A)) * endToEnd0 A (𝟙 A) = 1 := by
    rw [show endToEnd0 A (𝟙 A) = 1 from map_one (endToEnd0 A), mul_one, homToHom0_id,
      involution_apply]
    have hd : W.dual0 P hadd (id0 A) = id0 (W.dual P) :=
      dualHom0_id _ _ _ _ _ _ _ _ _ _ _ hadd
    rw [hd, comp0_id0, polarization_comp_inverse]
    rfl
  have htr1 : primeEndomorphismTrace A 2 1 = 2 * g := by
    rw [primeEndomorphismTrace_eq, map_one, LinearMap.trace_one, hrank]
    push_cast
    ring
  rw [hβ1, htr1, htop1] at hk1
  have hq1 : (coherentEulerPolynomial A.X.hom ((LineBundle.pullback (hom (𝟙 A))).obj L).obj
      (hasFiniteAffineSections_lineBundle _) L g).coeff (g - 1) =
        g * (lineBundleEulerPolynomial A.X.hom L g).coeff g := by
    apply (algebraMap ℚ ℚ_[2]).injective
    rw [map_mul, map_natCast]
    linear_combination hk1 / 2
  have hmixid : mixedLineBundleEulerCoefficient A.X.hom L
      ((LineBundle.pullback (hom (𝟙 A))).obj L) g =
        g * (lineBundleEulerPolynomial A.X.hom L g).coeff g :=
    (mixed_pullback_id A.X.hom L g).trans (mixed_self_eq A.X.hom g hg hA L)
  have hp : (lineBundleEulerPolynomial A.X.hom L g).coeff (g - 1) = 0 := by
    rw [hmixid, hq1] at hmix1
    linarith
  rw [traceForm_apply, geometricEndomorphismTrace_mul_comm A, hmixf, hp, sub_zero]
  have htr := algebraMap_geometricEndomorphismTrace A hS1 g hA
    (involution P W hadd lam (homToHom0 f) * endToEnd0 A f)
  have key : algebraMap ℚ ℚ_[2] (geometricEndomorphismTrace A
      (involution P W hadd lam (homToHom0 f) * endToEnd0 A f) *
        (lineBundleEulerPolynomial A.X.hom L g).coeff g) =
      algebraMap ℚ ℚ_[2] (2 * (coherentEulerPolynomial A.X.hom
        ((LineBundle.pullback (hom f)).obj L).obj (hasFiniteAffineSections_lineBundle _)
          L g).coeff (g - 1)) := by
    rw [map_mul (algebraMap ℚ ℚ_[2]), htr, map_mul (algebraMap ℚ ℚ_[2]), map_ofNat, hkf,
      htopf]
    ring
  exact (algebraMap ℚ ℚ_[2]).injective key

end Langlands.AbelianScheme.Rosati
