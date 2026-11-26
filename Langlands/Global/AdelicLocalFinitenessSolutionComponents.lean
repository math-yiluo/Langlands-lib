import Langlands.Global.AdelicLocalFinitenessComponentEquations
import Langlands.Global.AdelicLocalFinitenessProductBridge
import Langlands.Global.AdelicLocalFinitenessChamberSlabs
import Langlands.Global.AdelicPositiveTorusSplitComponentStatement

/-! # Residual equations of the Harish-Chandra components of solutions of `Ξ_main`

For each component `P`, orthant `ε` and direction `k` (a simple root outside the Levi of `P` or a
central index) the system `Ξ_main(s)` determines a monic difference polynomial: `D_β(s)` for the
translation `a_β`, `D̃_j(s)` for `z_j` on positive orthants and its normalized reversal for
`z_j⁻¹` on negative ones. The Harish-Chandra components of every solution have zero residual for
these polynomials.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  StandardConstantTerm

namespace LocalFinitenessData

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  {Δ : Type u} {r n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
  (X : LocalFinitenessData F G Δ r n W)

/-- The degree of the residual polynomial in the direction `k`: `deg D_β` for a root `β`,
`deg D̃_j` for a central index `j`. -/
def dirDegree (J : Δ → Prop) : ({β : Δ // ¬ J β} ⊕ Fin r) → ℕ :=
  Sum.elim (fun β => X.degree β.1) X.centralDegree

/-- The lower coefficients of the residual polynomial in the direction `k` on the orthant `ε`:
those of `D_β(s)` for a root `β`, of `D̃_j(s)` if `ε_j` is positive and of the normalized reversal
`D̃_j(s)(0)⁻¹ x^m D̃_j(s)(x⁻¹)` if `ε_j` is negative. -/
def dirCoeff (J : Δ → Prop) (s : W) (ε : Fin r → Bool) :
    (k : {β : Δ // ¬ J β} ⊕ Fin r) → Fin (X.dirDegree J k) → ℂ
  | .inl β => fun q => (X.D β.1 s).coeff q
  | .inr j => fun q => if ε j then (X.centralD j s).coeff q else
      (X.centralD j s).coeff (X.centralDegree j - q) / (X.centralD j s).coeff 0

end LocalFinitenessData

namespace StandardConstantTerm

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- `residualFun_eq_zero_of_monic` for a polynomial of a prescribed degree `m`. -/
theorem residualFun_eq_zero_of_monic_of_natDegree {b : AdelicGroupPoints F G} {D : Polynomial ℂ}
    {m : ℕ} (hD : D.Monic) (hm : D.natDegree = m) {φ : AdelicGroupPoints F G → ℂ}
    (h : IsTranslationPolynomialSolution b D φ) :
    residualFun F G b (fun q : Fin m => D.coeff q) φ = 0 := by
  subst hm
  exact residualFun_eq_zero_of_monic hD h

/-- `residualFun_inv_eq_zero` for a polynomial of a prescribed degree `m`. -/
theorem residualFun_inv_eq_zero_of_natDegree {b : AdelicGroupPoints F G} {D : Polynomial ℂ}
    {m : ℕ} (hm : D.natDegree = m) (h0 : D.coeff 0 ≠ 0) {φ : AdelicGroupPoints F G → ℂ}
    (h : IsTranslationPolynomialSolution b D φ) :
    residualFun F G b⁻¹ (fun q : Fin m => D.coeff (m - q) / D.coeff 0) φ = 0 := by
  subst hm
  exact residualFun_inv_eq_zero h0 h

end StandardConstantTerm

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

/-- **Residual equations of the components of solutions.** Assume
`PositiveTorusSplitComponentStatement`. Let `v` be a solution of `Ξ_main(s)` in `𝔉^R_L` for group
data of `𝓕` and admissible data `X`. For every finset `P`, orthant `ε` and direction `k`, the
Harish-Chandra component `𝓕.hcComponent P v` has zero residual for the orthant shift of `k` and the
coefficients `X.dirCoeff`. -/
theorem residualFun_hcComponent_eq_zero (hsplit : PositiveTorusSplitComponentStatement.{u})
    {Ua : simpleRelativeRoots 𝓕.i 𝓕.ν → GroupScheme (Spec (CommRingCat.of F))}
    [∀ α, IsAffine (Ua α).X.left] {u : ∀ α, Ua α ⟶ G}
    [∀ α, IsClosedImmersion (u α).hom.hom.left]
    {t : simpleRelativeRoots 𝓕.i 𝓕.ν → AdelicGroupPoints F 𝓕.T.toGrp} {r : ℕ}
    {z : Fin r → AdelicGroupPoints F 𝓕.T.toGrp}
    (hdata : IsLocalFinitenessGroupData 𝓕.i 𝓕.ν u t z)
    {n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
    (X : LocalFinitenessData F G (simpleRelativeRoots 𝓕.i 𝓕.ν) r n W) (hX : X.IsAdmissible)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (R : ℝ)
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (s : W)
    {v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L}
    (hv : v ∈ X.solutions u (fun α => map F 𝓕.T.toGrp G 𝓕.i (t α))
      (fun j => map F 𝓕.T.toGrp G 𝓕.i (z j)) rho hN hrho hsmooth hcalc R L s)
    (P : Finset (characterLattice 𝓕.T)) (ε : Fin r → Bool)
    (k : {β : simpleRelativeRoots 𝓕.i 𝓕.ν // ¬ β.val ∈ (𝓕.finsetIndex P).1} ⊕ Fin r) :
    residualFun F G (orthantShift (fun β => map F 𝓕.T.toGrp G 𝓕.i (t β))
        (fun j => map F 𝓕.T.toGrp G 𝓕.i (z j))
        (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε k)
      (X.dirCoeff (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) s ε k)
      (𝓕.hcComponent P (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v)) =
      0 := by
  set f₀ := (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val with hf₀
  have hφ : UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v =
      evaluate F G f₀ := rfl
  rw [hφ]
  rcases k with β | j
  · let Pβ : StandardIndex F G 𝓕.i 𝓕.ν :=
      ⟨simpleRelativeRoots 𝓕.i 𝓕.ν \ {β.1.val}, Set.sdiff_subset⟩
    obtain ⟨a, ha, hmap⟩ := hsplit F G 𝓕 Pβ (t β.1) (hdata.2.1 β.1) fun c0 hc0 =>
      hdata.2.2.1 β.1 ⟨c0, hc0.1⟩ fun h => hc0.2 (by rw [← h]; rfl)
    have hCT : IsTranslationPolynomialSolution (map F (𝓕.P Pβ) G (𝓕.p Pβ) a) (X.D β.1 s)
        (𝓕.constantTerm Pβ (evaluate F G f₀)) := by
      rw [hmap, ← 𝓕.subgroupConstantTerm_eq_constantTerm (u β.1) Pβ (hdata.1 β.1)]
      exact hv.2.1 β.1
    have hle : 𝓕.finsetIndex P ≤ Pβ := fun x hx =>
      ⟨hx.2, fun h => β.2 (by rw [Set.mem_singleton_iff] at h; subst h; exact hx)⟩
    have h := 𝓕.isTranslationPolynomialSolution_hcComponent ⟨a, ha⟩ (X.D β.1 s) f₀ hCT P hle
    rw [hmap] at h
    exact residualFun_eq_zero_of_monic_of_natDegree (hX.2.2.2.2.1 β.1 s).1
      (hX.2.2.2.2.1 β.1 s).2 h
  · obtain ⟨a, ha, hmap⟩ := hsplit F G 𝓕 𝓕.top (z j) (hdata.2.2.2.2.2.1 j) fun c0 hc0 =>
      hdata.2.2.2.2.2.2.1 j ⟨c0, hc0⟩
    have hCT : IsTranslationPolynomialSolution (map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) a)
        (X.centralD j s) (𝓕.constantTerm 𝓕.top (evaluate F G f₀)) := by
      rw [hmap, 𝓕.constantTerm_top]
      exact hv.2.2 j
    have h := 𝓕.isTranslationPolynomialSolution_hcComponent ⟨a, ha⟩ (X.centralD j s) f₀ hCT P
      (𝓕.le_top _)
    rw [hmap] at h
    obtain ⟨hmon, hdeg, h0⟩ := hX.2.2.2.2.2.2.1 j s
    by_cases hε : ε j
    · have hshift : orthantShift (fun β => map F 𝓕.T.toGrp G 𝓕.i (t β))
          (fun j => map F 𝓕.T.toGrp G 𝓕.i (z j))
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε (Sum.inr j) =
          map F 𝓕.T.toGrp G 𝓕.i (z j) := by
        simp [orthantShift, hε]
      have hcoef : X.dirCoeff (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1)
          s ε (Sum.inr j) = fun q : Fin (X.centralDegree j) => (X.centralD j s).coeff q := by
        funext q
        simp [LocalFinitenessData.dirCoeff, hε]
      rw [hshift, hcoef]
      exact residualFun_eq_zero_of_monic_of_natDegree hmon hdeg h
    · have hshift : orthantShift (fun β => map F 𝓕.T.toGrp G 𝓕.i (t β))
          (fun j => map F 𝓕.T.toGrp G 𝓕.i (z j))
          (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1) ε (Sum.inr j) =
          (map F 𝓕.T.toGrp G 𝓕.i (z j))⁻¹ := by
        simp [orthantShift, hε]
      have hcoef : X.dirCoeff (fun β : simpleRelativeRoots 𝓕.i 𝓕.ν => β.val ∈ (𝓕.finsetIndex P).1)
          s ε (Sum.inr j) = fun q : Fin (X.centralDegree j) =>
            (X.centralD j s).coeff (X.centralDegree j - q) / (X.centralD j s).coeff 0 := by
        funext q
        simp [LocalFinitenessData.dirCoeff, hε]
      rw [hshift, hcoef]
      exact residualFun_inv_eq_zero_of_natDegree hdeg h0 h

end StandardParabolicFamily

end Langlands.Global
