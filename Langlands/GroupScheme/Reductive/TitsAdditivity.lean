import Langlands.GroupScheme.Reductive.TitsSubquotient
import Langlands.GroupScheme.Reductive.HighestWeightTwistedStability
import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebraTensor
import Langlands.Algebra.GaloisTwistedCorner

/-! # Additivity of the Tits class on dominant star-fixed weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct Kronecker

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m n' m' : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']

/-- The universal matrix of a tensor product is the Kronecker product of the universal
matrices. -/
theorem universalMatrix_tensor_eq_kronecker
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m) :
    universalMatrix (ρ.tensor τ) = universalMatrix ρ ⊗ₖ universalMatrix τ := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  rw [universalMatrix_tensor, Matrix.kronecker_apply]

/-- Kronecker products of intertwiners intertwine the tensor products. -/
theorem Intertwines.kronecker
    {ρ₁ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ₁ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n'}
    {ρ₂ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    {τ₂ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m'}
    {C₁ : Matrix n' n K} {C₂ : Matrix m' m K}
    (h₁ : ρ₁.Intertwines τ₁ C₁) (h₂ : ρ₂.Intertwines τ₂ C₂) :
    (ρ₁.tensor ρ₂).Intertwines (τ₁.tensor τ₂) (C₁ ⊗ₖ C₂) := by
  rw [intertwines_iff_universalMatrix] at h₁ h₂ ⊢
  rw [universalMatrix_tensor_eq_kronecker, universalMatrix_tensor_eq_kronecker]
  have hmap : (C₁ ⊗ₖ C₂).map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) =
      C₁.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) ⊗ₖ
        C₂.map (algebraMap K (K ⊗[k] CharacterUnits.Coord G)) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [Matrix.map_apply, Matrix.kronecker_apply, map_mul]
  rw [hmap, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h₁, h₂]

/-- Intertwining only depends on the universal matrix of the target. -/
theorem Intertwines.of_universalMatrix_eq
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ τ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    (h : universalMatrix τ = universalMatrix τ') {C : Matrix m n K}
    (hC : ρ.Intertwines τ C) : ρ.Intertwines τ' C := by
  rw [intertwines_iff_universalMatrix] at hC ⊢
  rw [← h]
  exact hC

/-- The Galois twist of a tensor product has the universal matrix of the tensor product of the
twists. -/
theorem universalMatrix_galoisTwist_tensor (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m) :
    universalMatrix (galoisTwist σ (ρ.tensor τ)) =
      universalMatrix ((galoisTwist σ ρ).tensor (galoisTwist σ τ)) := by
  rw [universalMatrix_galoisTwist, universalMatrix_tensor_eq_kronecker,
    universalMatrix_tensor_eq_kronecker, universalMatrix_galoisTwist, universalMatrix_galoisTwist]
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [Matrix.map_apply, Matrix.kronecker_apply, map_mul]

/-- Kronecker products of Galois intertwiners are Galois intertwiners of the tensor product. -/
theorem intertwines_galoisTwist_tensor (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m}
    {P : Matrix n n K} {Q : Matrix m m K} (hP : ρ.Intertwines (galoisTwist σ ρ) P)
    (hQ : τ.Intertwines (galoisTwist σ τ) Q) :
    (ρ.tensor τ).Intertwines (galoisTwist σ (ρ.tensor τ)) (P ⊗ₖ Q) :=
  Intertwines.of_universalMatrix_eq (universalMatrix_galoisTwist_tensor σ ρ τ).symm
    (hP.kronecker hQ)

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G)

local instance titsAdditivityAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Star-fixed weights are closed under addition. -/
theorem isStarFixedWeight_add {lam mu : characterLattice d.toSplitPinning.torus}
    (hl : d.IsStarFixedWeight lam) (hm : d.IsStarFixedWeight mu) :
    d.IsStarFixedWeight (lam + mu) := fun σ => by
  rw [map_add, hl σ, hm σ]

variable [IsGalois k K]

/-- Additivity of the Tits algebra (Tits 1971, Proposition 3.4 applied to `V(λ) ⊗ V(μ)`): the
Tits algebra of highest weight `λ + μ` is Brauer equivalent to the tensor product of those of
highest weights `λ` and `μ`. -/
theorem titsCSAOf_add_isBrauerEquivalent 
    {n₁ n₂ r : ℕ}
    {ρ₁ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n₁)}
    {ρ₂ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n₂)}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin r)}
    {lam mu : characterLattice d.toSplitPinning.torus}
    (h₁ : d.toSplitPinning.IsHighestWeight ρ₁ lam) (h₂ : d.toSplitPinning.IsHighestWeight ρ₂ mu)
    (hρ : d.toSplitPinning.IsHighestWeight ρ (lam + mu))
    (hl : d.IsStarFixedWeight lam) (hm : d.IsStarFixedWeight mu) :
    IsBrauerEquivalent (d.titsCSAOf hρ (d.isStarFixedWeight_add hl hm))
      (Langlands.Brauer.tensor (d.titsCSAOf h₁ hl) (d.titsCSAOf h₂ hm)) := by
  classical
  have hν := d.isStarFixedWeight_add hl hm
  have := d.nonempty_of_isHighestWeight h₁
  have := d.nonempty_of_isHighestWeight h₂
  -- Galois intertwiners of the factors and of the tensor product
  set P₁ := fun σ => (d.exists_intertwiner_galoisTwist h₁ hl σ).choose with hP₁
  set P₂ := fun σ => (d.exists_intertwiner_galoisTwist h₂ hm σ).choose with hP₂
  have hP₁i : ∀ σ, ρ₁.Intertwines (galoisTwist σ ρ₁) (P₁ σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist h₁ hl σ).choose_spec.1
  have hP₂i : ∀ σ, ρ₂.Intertwines (galoisTwist σ ρ₂) (P₂ σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist h₂ hm σ).choose_spec.1
  have hP₁u : ∀ σ, IsUnit (P₁ σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist h₁ hl σ).choose_spec.2
  have hP₂u : ∀ σ, IsUnit (P₂ σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist h₂ hm σ).choose_spec.2
  set T := ρ₁.tensor ρ₂ with hT
  set P := fun σ => P₁ σ ⊗ₖ P₂ σ with hP
  have hPi : ∀ σ, T.Intertwines (galoisTwist σ T) (P σ) := fun σ =>
    intertwines_galoisTwist_tensor σ (hP₁i σ) (hP₂i σ)
  have hPu : ∀ σ, IsUnit (P σ) := fun σ => isUnit_kronecker (hP₁u σ) (hP₂u σ)
  -- the Kronecker product of the Tits algebras
  have hA₁ := titsAlgebra_le_twistedFixed P₁ hP₁i
  have hA₂ := titsAlgebra_le_twistedFixed P₂ hP₂i
  have hs₁ := span_titsAlgebra_eq_top ρ₁ h₁.1
    (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning h₁)
  have hs₂ := span_titsAlgebra_eq_top ρ₂ h₂.1
    (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning h₂)
  set B := (kroneckerTensor (titsAlgebra ρ₁) (titsAlgebra ρ₂)).range with hBdef
  have hB : B ≤ twistedFixed P := range_kroneckerTensor_le_twistedFixed hA₁ hA₂
  have hBs : Submodule.span K (B : Set (Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) K)) = ⊤ :=
    span_range_kroneckerTensor hs₁ hs₂
  have hTB : titsAlgebra T ≤ B := titsAlgebra_tensor_le ρ₁ ρ₂
  -- the twisted-stable flag of the weight `λ + μ` and an adapted rational idempotent
  have hX := d.isTwistedStable_highestGenerated hν P hPi
  have hY := d.isTwistedStable_highestRadical hν P hPi hPu
  obtain ⟨f, hfB, hff, hfX, hfY, hfid⟩ := exists_adapted_idempotent P hPu B hB hBs
    (d.toSplitPinning.highestRadical_le T (lam + mu)) hX hY
  -- the subquotient of highest weight `λ + μ`
  obtain ⟨D⟩ := d.toSplitPinning.nonempty_highestSubquotientData T (lam + mu)
  have hD : d.toSplitPinning.IsHighestWeight D.quot (lam + mu) :=
    D.isHighestWeight (d.toSplitPinning.finrank_representationWeightSpace_tensor_add h₁ h₂)
      (d.toSplitPinning.sub_mem_positiveRootMonoid_tensor h₁ h₂)
  have := d.nonempty_of_isHighestWeight hD
  set P' := fun σ => (d.exists_intertwiner_galoisTwist hD hν σ).choose with hP'
  have hP'i : ∀ σ, D.quot.Intertwines (galoisTwist σ D.quot) (P' σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist hD hν σ).choose_spec.1
  have hP'u : ∀ σ, IsUnit (P' σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist hD hν σ).choose_spec.2
  obtain ⟨hFE, hEF, heq⟩ := D.titsAlgebra_quot_eq_compressed hD.1
    (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning hD) P' hP'u hP'i B P hPu
    hB hTB hfB hff hfX hfY hfid
  -- chain of Brauer equivalences
  have e1 : IsBrauerEquivalent (d.titsCSAOf hρ hν) (d.titsCSAOf hD hν) :=
    d.titsCSAOf_isBrauerEquivalent hρ hD hν
  have e2 : IsBrauerEquivalent (d.titsCSAOf hD hν)
      (toCSA _ (isUnit_compressed_twist hB hPu _ _ hFE hEF) _
        (compressed_le_twistedFixed hB _ _ hFE hEF) (span_compressed hBs _ _ hFE hEF)) :=
    ⟨1, 1, one_ne_zero, one_ne_zero, ⟨(Subalgebra.equivOfEq _ _ heq).mapMatrix⟩⟩
  have e3 := isBrauerEquivalent_toCSA_compressed P hPu B hB hBs _ _ hFE hEF
  have e4 := kroneckerCSA_isBrauerEquivalent (titsAlgebra ρ₁) (titsAlgebra ρ₂) P₁ P₂ hP₁u hP₂u
    hA₁ hA₂ hs₁ hs₂
  exact ((e1.trans e2).trans e3).trans e4

end Langlands.GroupScheme.GaloisPinningData

namespace Langlands.GroupScheme

open MatrixRepresentation

/-- Additivity of the Tits algebra on dominant star-fixed weights (Tits 1971, Proposition 3.4
applied to `V(λ) ⊗ V(μ)`), relative to the split highest-weight classification. -/
def TitsAdditivityStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : GaloisPinningData k K G)
    (n₁ n₂ r : ℕ)
    (ρ₁ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n₁))
    (ρ₂ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin n₂))
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin r))
    (lam mu : characterLattice d.toSplitPinning.torus)
    (h₁ : d.toSplitPinning.IsHighestWeight ρ₁ lam) (h₂ : d.toSplitPinning.IsHighestWeight ρ₂ mu)
    (hρ : d.toSplitPinning.IsHighestWeight ρ (lam + mu))
    (hl : d.IsStarFixedWeight lam) (hm : d.IsStarFixedWeight mu),
    IsBrauerEquivalent (d.titsCSAOf hρ (d.isStarFixedWeight_add hl hm))
      (Langlands.Brauer.tensor (d.titsCSAOf h₁ hl) (d.titsCSAOf h₂ hm))

theorem titsAdditivity : TitsAdditivityStatement.{u} := by
  intro k K _ _ _ _ G _ _ d n₁ n₂ r ρ₁ ρ₂ ρ lam mu h₁ h₂ hρ hl hm
  exact d.titsCSAOf_add_isBrauerEquivalent h₁ h₂ hρ hl hm

end Langlands.GroupScheme
