import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroStatement
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceReduction

/-! # Reduction of the Mumford Rosati trace formula to the characteristic-zero degree statement

`MumfordMixedEulerTraceCharZeroReductionStatement` says that the characteristic-zero degree
statement `IsogenyDegreeTateDeterminantCharZeroStatement` and the Euler-degree statement
`MumfordEulerDegreeStatement` imply `MumfordMixedEulerTraceStatement`.
The proof is the proof of `mumfordMixedEulerTraceReduction`, with the four steps that used
the general degree statement redone with its characteristic-zero case.
-/

noncomputable section

universe u

open Polynomial CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Rosati.MumfordTraceCharZeroReduction

open MumfordTraceReduction

section Tate

variable {k : Type u} [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))

/-- Under the characteristic-zero degree statement, the actual `2`-adic trace of every integral
endomorphism is rational. -/
theorem trace_rationalMap_mem_range
    (hS1 : IsogenyDegreeTateDeterminantCharZeroStatement.{u})
    [IsAlgClosed k] [CharZero k] (g : ℕ) (hA : A.HasRelativeDimension g) (α : A ⟶ A) :
    LinearMap.trace ℚ_[2] _ (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) 2 α) ∈
      Set.range (algebraMap ℚ ℚ_[2]) := by
  obtain ⟨hfin, -⟩ := rational_two_finrank A g hA
  obtain ⟨y⟩ := nonempty_left A
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
    · rw [← ((hS1 k A 2 (n • 𝟙 A + α)).1 hiso y)]
      exact ⟨_, map_natCast _ _⟩
    · rw [(hS1 k A 2 (n • 𝟙 A + α)).2 hiso]
      exact ⟨0, map_zero _⟩
  rw [← nextCoeff_charpoly_neg, Polynomial.nextCoeff]
  split_ifs
  · exact ⟨0, map_zero _⟩
  · exact coeff_mem_range_of_eval_natCast _ hdet _

/-- Under the characteristic-zero degree statement, the actual `2`-adic trace of every rational
endomorphism is rational. -/
theorem primeEndomorphismTrace_mem_range
    (hS1 : IsogenyDegreeTateDeterminantCharZeroStatement.{u})
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

/-- Under the characteristic-zero degree statement, the chosen geometric trace is the rational lift of
the actual `2`-adic trace. -/
theorem algebraMap_geometricEndomorphismTrace
    (hS1 : IsogenyDegreeTateDeterminantCharZeroStatement.{u})
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

section Key

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The key identity: twice the subleading coefficient of the Euler polynomial of
`f^* L` equals its top coefficient times the `2`-adic trace of `f† f`. -/
theorem key_identity (hS1 : IsogenyDegreeTateDeterminantCharZeroStatement.{u})
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
    have hdet := (hS1 k A 2 _).1 (hiso.comp hμiso) z₀
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

end Langlands.AbelianScheme.Rosati.MumfordTraceCharZeroReduction

namespace Langlands.AbelianScheme.Rosati

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
  MumfordTraceReduction MumfordTraceCharZeroReduction

set_option backward.isDefEq.respectTransparency false

/-- The characteristic-zero degree statement `IsogenyDegreeTateDeterminantCharZeroStatement`
and the Euler-degree statement `MumfordEulerDegreeStatement` together imply the Mumford
Rosati mixed Euler trace formula `MumfordMixedEulerTraceStatement`, at the same universe. -/
def MumfordMixedEulerTraceCharZeroReductionStatement : Prop :=
  IsogenyDegreeTateDeterminantCharZeroStatement.{u} → MumfordEulerDegreeStatement.{u} →
    MumfordMixedEulerTraceStatement.{u}

/-- Proof of the reduction by comparing the coefficients of `n ^ (2g)` and
`n ^ (2g - 1)` of the degree polynomial of `(n • lam + f ≫ lam ≫ f^∨) ≫ μ`. -/
theorem mumfordMixedEulerTraceCharZeroReduction :
    MumfordMixedEulerTraceCharZeroReductionStatement.{u} := by
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
