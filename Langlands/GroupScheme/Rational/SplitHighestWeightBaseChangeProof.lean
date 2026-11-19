import Langlands.GroupScheme.Rational.SplitHighestWeightBaseChangeStatement
import Langlands.GroupScheme.Rational.HighestWeightScalarEndomorphisms
import Langlands.GroupScheme.Rational.HighestWeightBaseChange
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationProof
import Langlands.GroupScheme.MatrixRepresentation.AbsoluteIrreducibilityFieldExtension
import Langlands.GroupScheme.MatrixRepresentation.SemisimpleCoordinates

/-! # Highest-weight base change and descent of semisimple representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace MatrixRepresentation

section BlockMaps

variable {k : Type u} [Field k]
  {I : Type} [Fintype I] [DecidableEq I] {n m : I → Type}
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

private theorem blockDiagonal_bijective (C : ∀ i, Matrix (m i) (n i) k)
    (hC : ∀ i, Function.Bijective (C i).mulVecLin) :
    Function.Bijective (Matrix.blockDiagonal' C).mulVecLin := by
  classical
  choose D hDC hCD using fun i => exists_mul_eq_one_of_bijective (hC i)
  have hleft : Matrix.blockDiagonal' D * Matrix.blockDiagonal' C = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    simp_rw [hDC]
    exact Matrix.blockDiagonal'_one
  have hright : Matrix.blockDiagonal' C * Matrix.blockDiagonal' D = 1 := by
    rw [← Matrix.blockDiagonal'_mul]
    simp_rw [hCD]
    exact Matrix.blockDiagonal'_one
  constructor
  · intro v w hvw
    have h := congrArg (Matrix.blockDiagonal' D).mulVec hvw
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hleft, Matrix.one_mulVec] using h
  · intro v
    refine ⟨Matrix.blockDiagonal' D *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hright, Matrix.one_mulVec]

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {ρ : ∀ i, MatrixRepresentation G (n i)}
  {σ : ∀ i, MatrixRepresentation G (m i)}

private theorem intertwines_blockDiagonal (C : ∀ i, Matrix (m i) (n i) k)
    (hC : ∀ i, (ρ i).Intertwines (σ i) (C i)) :
    (directSum ρ).Intertwines (directSum σ) (Matrix.blockDiagonal' C) := by
  intro A x
  rw [Matrix.blockDiagonal'_map _ _ (map_zero _),
    directSum_affineMatrix_val, directSum_affineMatrix_val,
    ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  exact hC i A x

end BlockMaps

end MatrixRepresentation

namespace SplitPinning

open MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : SplitPinning G}

/-- The highest-weight line and scalar commutant imply simplicity after any field extension. -/
theorem IsHighestWeight.baseChange_isIrreducible
    {K : Type u} [Field K] [Algebra k K]
    {n : ℕ} {ρ : MatrixRepresentation G (Fin n)} {lam : characterLattice p.torus}
    (hρ : p.IsHighestWeight ρ lam) :
    (ρ.baseChange (algebraBaseMap k K)).IsIrreducible :=
  hρ.1.baseChange_of_scalar_intertwiners
    (fun C hC => IsHighestWeight.intertwiner_eq_scalar p hρ C hC)

/-- Every simple representation over an extension descends, with a bijective actual intertwiner. -/
theorem exists_irreducible_baseChange_intertwiner
    {K : Type u} [Field K] [Algebra k K]
    (p : SplitPinning G) {m : ℕ}
    (σ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin m))
    (hσ : σ.IsIrreducible) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsIrreducible ∧
      ∃ C : Matrix (Fin m) (Fin n) K,
        (ρ.baseChange (algebraBaseMap k K)).Intertwines σ C ∧
          Function.Bijective C.mulVecLin := by
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
  let pK := p.baseChangeField (K := K)
  have hcK := splitHighestWeightClassification K
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) pK
  obtain ⟨mu, ⟨hmu, hσmu⟩, _⟩ := hcK.2.2 m σ hσ
  obtain ⟨lam, rfl⟩ :=
    (p.isSplitTorus.characterLattice_baseChange_bijective
      (algebraBaseMap k K) p.torus).surjective mu
  have hlam : p.IsDominantWeight lam :=
    (p.isDominantWeight_baseChangeField_iff (K := K) lam).mp hmu
  obtain ⟨n, ρ, hρ⟩ := (splitHighestWeightClassification k G p).1 lam hlam
  have hρK := hρ.baseChangeField_of_isIrreducible
    (hρ.baseChange_isIrreducible (K := K))
  obtain ⟨C, hC, hbij⟩ :=
    (hcK.2.1 n m (ρ.baseChange (algebraBaseMap k K)) σ _ _ hρK hσmu).mpr rfl
  exact ⟨n, ρ, hρ.1, C, hC, hbij⟩

/-- Every semisimple representation over an extension descends with the same coordinate dimension. -/
theorem exists_semisimple_baseChange_intertwiner
    {K : Type u} [Field K] [Algebra k K]
    (p : SplitPinning G) {m : ℕ}
    (σ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin m))
    (hσ : σ.IsSemisimple) :
    ∃ ρ : MatrixRepresentation G (Fin m), ρ.IsSemisimple ∧
      ∃ C : Matrix (Fin m) (Fin m) K,
        (ρ.baseChange (algebraBaseMap k K)).Intertwines σ C ∧
          Function.Bijective C.mulVecLin := by
  classical
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
  obtain ⟨r, d', τ', D, hτ', hD, hDbij⟩ := hσ.exists_directSum_coordinates
  choose d τ hτ C hC hCbij using
    fun i => p.exists_irreducible_baseChange_intertwiner (τ' i) (hτ' i)
  let B := Matrix.blockDiagonal' C
  have hB : (directSum fun i => (τ i).baseChange (algebraBaseMap k K)).Intertwines
      (directSum τ') B := intertwines_blockDiagonal C hC
  have hBbij : Function.Bijective B.mulVecLin := blockDiagonal_bijective C hCbij
  have hB' : ((directSum τ).baseChange (algebraBaseMap k K)).Intertwines
      (directSum τ') B := by
    intro A x
    have h := hB A x
    rw [directSum_affineMatrix_val] at h
    rw [directSum_baseChange_affineMatrix_val]
    exact h
  let E := D * B
  have hE : ((directSum τ).baseChange (algebraBaseMap k K)).Intertwines σ E :=
    hB'.comp hD
  have hEbij : Function.Bijective E.mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.coe_comp]
    exact hDbij.comp hBbij
  have hcard : Fintype.card (Σ i, Fin (d i)) = m := by
    have hdim := (LinearEquiv.ofBijective E.mulVecLin hEbij).finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
  let e : ((Σ i, Fin (d i)) → k) ≃ₗ[k] (Fin m → k) :=
    LinearEquiv.ofFinrankEq _ _ (by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hcard)
  let ρ := (directSum τ).transportCoordinates e
  have hforward := intertwines_transportCoordinates (directSum τ) e
  have hρ : ρ.IsSemisimple :=
    (isSemisimple_directSum τ hτ).of_bijective_intertwiner hforward.1 hforward.2
  have hinv := intertwines_transportCoordinates_symm (directSum τ) e
  have hinvbij : Function.Bijective
      (LinearMap.toMatrix' e.symm.toLinearMap).mulVecLin := by
    change Function.Bijective
      (Matrix.toLin' (LinearMap.toMatrix' e.symm.toLinearMap))
    rw [Matrix.toLin'_toMatrix']
    exact e.symm.bijective
  have hinvK := hinv.baseChange_bijective (K := K) hinvbij
  refine ⟨ρ, hρ, E * (LinearMap.toMatrix' e.symm.toLinearMap).map (algebraMap k K),
    hinvK.1.comp hE, ?_⟩
  rw [Matrix.mulVecLin_mul, LinearMap.coe_comp]
  exact hEbij.comp hinvK.2

end SplitPinning

/-- Highest-weight scalarity, absolute simplicity, highest-weight transport and
semisimple descent for every split pinning over every field. -/
theorem splitHighestWeightBaseChange : SplitHighestWeightBaseChangeStatement.{u} := by
  intro k _ G _ p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n ρ lam hρ C hC
    exact SplitPinning.IsHighestWeight.intertwiner_eq_scalar p hρ C hC
  · intro K _ _ n ρ lam hρ
    exact hρ.baseChange_isIrreducible
  · intro K _ _ _ n ρ lam hρ
    exact hρ.baseChange_of_isIrreducible hρ.baseChange_isIrreducible
  · intro K _ _ m σ hσ
    exact p.exists_semisimple_baseChange_intertwiner σ hσ

end Langlands.GroupScheme
