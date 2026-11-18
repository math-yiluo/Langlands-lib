import Langlands.GroupScheme.Rational.SplitWeightModule
import Langlands.GroupScheme.Rational.SplitRepresentationCharacterStatement
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationStatement
import Langlands.GroupScheme.Rational.HighestWeightRootEndpoint
import Langlands.GroupScheme.Rational.DominantWeightTriangularity
import Langlands.LinearAlgebra.InvariantOrbitSeparation

/-! # The character theorem from the highest-weight classification -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open MatrixRepresentation

namespace SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

/-! ### Nonzero weight spaces -/

theorem representationWeightSpace_ne_bot_iff_weightSubmodule {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) (lam : characterLattice p.torus) :
    p.representationWeightSpace ρ lam ≠ ⊥ ↔
      p.weightSubmodule (OperatorModule ρ) lam ≠ ⊥ := by
  rw [p.weightSubmodule_operatorModule]
  apply not_congr
  constructor
  · intro h
    rw [h, Submodule.map_bot]
  · intro h
    apply Submodule.map_injective_of_injective (f := ((toModule ρ :
      (n → k) ≃ₗ[k] OperatorModule ρ) : (n → k) →ₗ[k] OperatorModule ρ))
      (toModule ρ).injective
    rw [h, Submodule.map_bot]

theorem representationWeightSpace_ne_bot_of_finrank_ne_zero {n : Type} [Fintype n]
    [DecidableEq n] (ρ : MatrixRepresentation G n) {lam : characterLattice p.torus}
    (h : Module.finrank k (p.representationWeightSpace ρ lam) ≠ 0) :
    p.representationWeightSpace ρ lam ≠ ⊥ := by
  intro hbot
  apply h
  rw [hbot, finrank_bot]

/-! ### The first part: finite support and reflection invariance -/

/-- The weight multiplicities of a representation have finite support. -/
theorem finite_support_nat_finrank_representationWeightSpace {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n)) :
    (Function.support fun lam : characterLattice p.torus =>
      Module.finrank k (p.representationWeightSpace ρ lam)).Finite := by
  refine (p.finite_weightSubmodule_ne_bot_operatorModule ρ).subset ?_
  intro lam hlam
  exact (p.representationWeightSpace_ne_bot_iff_weightSubmodule ρ lam).mp
    (p.representationWeightSpace_ne_bot_of_finrank_ne_zero ρ hlam)

/-! ### The second part: semisimple modules are determined by their characters -/

/-- A simple summand meeting a maximal weight space of a realized module is the module of
a highest-weight representation of that weight. -/
theorem exists_isHighestWeight_of_isSimpleModule
    (hcl3 : ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsIrreducible →
      ∃! lam : characterLattice p.torus, p.IsDominantWeight lam ∧ p.IsHighestWeight ρ lam)
    {M : Type u} [AddCommGroup M] [Module (OperatorAlgebra G) M] [Module k M]
    [IsScalarTower k (OperatorAlgebra G) M] (hM : IsRealized G M)
    (S : Submodule (OperatorAlgebra G) M) [IsSimpleModule (OperatorAlgebra G) S]
    {lam : characterLattice p.torus} (hS : p.weightSubmodule S lam ≠ ⊥)
    (hmax : ∀ mu, p.weightSubmodule M mu ≠ ⊥ → mu - lam ∈ p.positiveRootMonoid →
      mu = lam) :
    ∃ (r : ℕ) (τ : MatrixRepresentation G (Fin r)),
      Nonempty (OperatorModule τ ≃ₗ[OperatorAlgebra G] S) ∧ p.IsHighestWeight τ lam := by
  obtain ⟨r, τ, ⟨e⟩⟩ := (hM.submodule S).exists_linearEquiv
  have : IsSimpleModule (OperatorAlgebra G) (OperatorModule τ) := IsSimpleModule.congr e
  obtain ⟨lam', ⟨-, hhw⟩, -⟩ := hcl3 r τ (isIrreducible_of_isSimpleModule (ρ := τ))
  have hτlam : p.representationWeightSpace τ lam ≠ ⊥ := by
    rw [p.representationWeightSpace_ne_bot_iff_weightSubmodule]
    exact p.weightSubmodule_ne_bot_of_injective e.symm.toLinearMap e.symm.injective hS
  have hle : lam' - lam ∈ p.positiveRootMonoid := hhw.2.2.2 lam hτlam
  have hMlam' : p.weightSubmodule M lam' ≠ ⊥ := by
    have h1 : p.representationWeightSpace τ lam' ≠ ⊥ :=
      p.representationWeightSpace_ne_bot_of_finrank_ne_zero τ (by rw [hhw.2.2.1]; omega)
    rw [p.representationWeightSpace_ne_bot_iff_weightSubmodule] at h1
    exact p.weightSubmodule_ne_bot_of_injective (S.subtype ∘ₗ e.toLinearMap)
      (by exact Subtype.val_injective.comp e.injective) h1
  have heq := hmax lam' hMlam' hle
  rw [heq] at hhw
  exact ⟨r, τ, ⟨e⟩, hhw⟩

/-- Realized semisimple modules with the same weight multiplicities are isomorphic, given
the highest-weight classification. -/
theorem nonempty_linearEquiv_of_finrank_weightSubmodule_eq
    (hcl2 : ∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n))
      (σ : MatrixRepresentation G (Fin m)) (lam mu : characterLattice p.torus),
      p.IsHighestWeight ρ lam → p.IsHighestWeight σ mu →
        ((∃ C : Matrix (Fin m) (Fin n) k,
            ρ.Intertwines σ C ∧ Function.Bijective C.mulVecLin) ↔ lam = mu))
    (hcl3 : ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsIrreducible →
      ∃! lam : characterLattice p.torus, p.IsDominantWeight lam ∧ p.IsHighestWeight ρ lam)
    (d : ℕ) :
    ∀ (M N : Type u) [AddCommGroup M] [Module (OperatorAlgebra G) M] [Module k M]
      [IsScalarTower k (OperatorAlgebra G) M] [IsSemisimpleModule (OperatorAlgebra G) M]
      [AddCommGroup N] [Module (OperatorAlgebra G) N] [Module k N]
      [IsScalarTower k (OperatorAlgebra G) N] [IsSemisimpleModule (OperatorAlgebra G) N],
      IsRealized G M → IsRealized G N → Module.finrank k M = d →
      (∀ lam, Module.finrank k (p.weightSubmodule M lam) =
        Module.finrank k (p.weightSubmodule N lam)) →
      Nonempty (M ≃ₗ[OperatorAlgebra G] N) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ hM hN hd hchar
  have := hM.finiteDimensional
  have := hN.finiteDimensional
  by_cases hzero : ∀ lam, p.weightSubmodule M lam = ⊥
  · have hM0 : ∀ x : M, x = 0 := p.eq_zero_of_isRealized_of_weightSubmodule_eq_bot hM hzero
    have hN0 : ∀ y : N, y = 0 := by
      apply p.eq_zero_of_isRealized_of_weightSubmodule_eq_bot hN
      intro lam
      rw [← Submodule.finrank_eq_zero, ← hchar, hzero lam, finrank_bot]
    have : Subsingleton M := ⟨fun x y => (hM0 x).trans (hM0 y).symm⟩
    have : Subsingleton N := ⟨fun x y => (hN0 x).trans (hN0 y).symm⟩
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  push Not at hzero
  obtain ⟨lam0, hlam0⟩ := hzero
  have hfin := p.finite_weightSubmodule_ne_bot_of_isRealized hM
  obtain ⟨lam, hlamT, hmaxT⟩ := Langlands.RootDatum.Triangular.exists_maximal_of_finset
    (P := p.rootDatum) (b := p.base) hfin.toFinset ⟨lam0, hfin.mem_toFinset.mpr hlam0⟩
  have hlam : p.weightSubmodule M lam ≠ ⊥ := hfin.mem_toFinset.mp hlamT
  have hmaxM : ∀ mu, p.weightSubmodule M mu ≠ ⊥ → mu - lam ∈ p.positiveRootMonoid →
      mu = lam :=
    fun mu hmu hle => hmaxT mu (hfin.mem_toFinset.mpr hmu) hle
  have hiff : ∀ mu, p.weightSubmodule N mu ≠ ⊥ ↔ p.weightSubmodule M mu ≠ ⊥ := by
    intro mu
    rw [Ne, Ne, ← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, hchar mu]
  have hmaxN : ∀ mu, p.weightSubmodule N mu ≠ ⊥ → mu - lam ∈ p.positiveRootMonoid →
      mu = lam :=
    fun mu hmu hle => hmaxM mu ((hiff mu).mp hmu) hle
  obtain ⟨S, hS, hSlam⟩ :=
    p.exists_isSimpleModule_weightSubmodule_ne_bot_of_isRealized hM hlam
  obtain ⟨S', hS', hS'lam⟩ :=
    p.exists_isSimpleModule_weightSubmodule_ne_bot_of_isRealized hN ((hiff lam).mpr hlam)
  obtain ⟨r, τ, ⟨e⟩, hτ⟩ := p.exists_isHighestWeight_of_isSimpleModule hcl3 hM S hSlam hmaxM
  obtain ⟨r', τ', ⟨e'⟩, hτ'⟩ :=
    p.exists_isHighestWeight_of_isSimpleModule hcl3 hN S' hS'lam hmaxN
  obtain ⟨C, hC, hCb⟩ := (hcl2 r r' τ τ' lam lam hτ hτ').mpr rfl
  let eS : S ≃ₗ[OperatorAlgebra G] S' := e.symm.trans ((hC.toLinearEquiv hCb).trans e')
  obtain ⟨T, hT⟩ := exists_isCompl S
  obtain ⟨T', hT'⟩ := exists_isCompl S'
  have hcharT : ∀ mu, Module.finrank k (p.weightSubmodule T mu) =
      Module.finrank k (p.weightSubmodule T' mu) := by
    intro mu
    have h1 := p.finrank_weightSubmodule_eq_add_of_isCompl hT mu
    have h2 := p.finrank_weightSubmodule_eq_add_of_isCompl hT' mu
    have h3 := p.finrank_weightSubmodule_eq_of_linearEquiv eS mu
    have h4 := hchar mu
    omega
  have : FiniteDimensional k S := (hM.submodule S).finiteDimensional
  have : FiniteDimensional k T := (hM.submodule T).finiteDimensional
  have hdim : Module.finrank k M = Module.finrank k S + Module.finrank k T := by
    rw [← Module.finrank_prod]
    exact ((Submodule.prodEquivOfIsCompl S T hT).restrictScalars k).finrank_eq.symm
  have hSpos : 0 < Module.finrank k S := by
    have := IsSimpleModule.nontrivial (OperatorAlgebra G) S
    exact Module.finrank_pos
  obtain ⟨eT⟩ := ih (Module.finrank k T) (by omega) T T' (hM.submodule T)
    (hN.submodule T') rfl hcharT
  exact ⟨(Submodule.prodEquivOfIsCompl S T hT).symm.trans
    ((eS.prodCongr eT).trans (Submodule.prodEquivOfIsCompl S' T' hT'))⟩

/-- Semisimple representations with the same weight multiplicities are isomorphic, given
the highest-weight classification. -/
theorem exists_intertwines_bijective_of_finrank_eq
    (hcl2 : ∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n))
      (σ : MatrixRepresentation G (Fin m)) (lam mu : characterLattice p.torus),
      p.IsHighestWeight ρ lam → p.IsHighestWeight σ mu →
        ((∃ C : Matrix (Fin m) (Fin n) k,
            ρ.Intertwines σ C ∧ Function.Bijective C.mulVecLin) ↔ lam = mu))
    (hcl3 : ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), ρ.IsIrreducible →
      ∃! lam : characterLattice p.torus, p.IsDominantWeight lam ∧ p.IsHighestWeight ρ lam)
    {n m : ℕ} (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m))
    (hρ : sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧
      W ≠ ⊥ ∧ ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤)
    (hσ : sSup {W : Submodule k (Fin m → k) | σ.IsStableSubspace W ∧
      W ≠ ⊥ ∧ ∀ U : Submodule k (Fin m → k), σ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤)
    (h : ∀ lam : characterLattice p.torus,
      Module.finrank k (p.representationWeightSpace ρ lam) =
        Module.finrank k (p.representationWeightSpace σ lam)) :
    ∃ C : Matrix (Fin m) (Fin n) k, ρ.Intertwines σ C ∧ Function.Bijective C.mulVecLin := by
  have := isSemisimpleModule_of_sSup_eq_top hρ
  have := isSemisimpleModule_of_sSup_eq_top hσ
  obtain ⟨e⟩ := p.nonempty_linearEquiv_of_finrank_weightSubmodule_eq hcl2 hcl3 _
    (OperatorModule ρ) (OperatorModule σ) (isRealized_operatorModule ρ)
    (isRealized_operatorModule σ) rfl fun lam => by
      rw [p.finrank_weightSubmodule_operatorModule, p.finrank_weightSubmodule_operatorModule,
        h lam]
  exact exists_intertwines_bijective_of_linearEquiv e

/-! ### The third part: characters span the invariants -/

/-- Every reflection-invariant finitely supported integer function on the character lattice
is a difference of two characters, given highest-weight representations at every dominant
weight. -/
theorem exists_sub_of_reflection_invariant
    (hcl1 : ∀ lam : characterLattice p.torus, p.IsDominantWeight lam →
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), p.IsHighestWeight ρ lam)
    (f : characterLattice p.torus →₀ ℤ)
    (hf : ∀ (i : p.rootIndex) (lam : characterLattice p.torus),
      f (p.rootDatum.reflection i lam) = f lam) :
    ∃ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m)),
      ∀ lam : characterLattice p.torus,
        f lam = (Module.finrank k (p.representationWeightSpace ρ lam) : ℤ) -
          Module.finrank k (p.representationWeightSpace σ lam) := by
  obtain ⟨z, ζ, hζ⟩ := p.exists_finrank_representationWeightSpace_eq_zero
  let S : AddSubgroup (characterLattice p.torus →₀ ℤ) :=
    { carrier := {g | ∃ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n))
          (σ : MatrixRepresentation G (Fin m)), ∀ lam : characterLattice p.torus,
          g lam = (Module.finrank k (p.representationWeightSpace ρ lam) : ℤ) -
            Module.finrank k (p.representationWeightSpace σ lam)}
      zero_mem' := ⟨z, z, ζ, ζ, fun lam => by simp⟩
      add_mem' := by
        rintro g g' ⟨n₁, m₁, ρ₁, σ₁, hg⟩ ⟨n₂, m₂, ρ₂, σ₂, hg'⟩
        obtain ⟨a, α, hα⟩ := p.exists_finrank_representationWeightSpace_eq_add ρ₁ ρ₂
        obtain ⟨b, β, hβ⟩ := p.exists_finrank_representationWeightSpace_eq_add σ₁ σ₂
        refine ⟨a, b, α, β, fun lam => ?_⟩
        rw [Finsupp.add_apply, hg lam, hg' lam, hα lam, hβ lam]
        push_cast
        ring
      neg_mem' := by
        rintro g ⟨n, m, ρ, σ, hg⟩
        refine ⟨m, n, σ, ρ, fun lam => ?_⟩
        rw [Finsupp.neg_apply, hg lam]
        ring }
  have hc : ∀ lam : characterLattice p.torus,
      Langlands.LinearAlgebra.DominantTriangular.IsDominant p.rootDatum p.base lam →
      ∃ c ∈ AddSubgroup.toIntSubmodule S,
        Langlands.LinearAlgebra.DominantTriangular.IsInvariant
          (Langlands.LinearAlgebra.DominantTriangular.reflectionGroup p.rootDatum) c ∧
        c lam = 1 ∧ ∀ mu, c mu ≠ 0 →
          lam - mu ∈ Langlands.LinearAlgebra.DominantTriangular.positiveCone
            p.rootDatum p.base := by
    intro lam hlam
    obtain ⟨n, ρ, hρ⟩ := hcl1 lam hlam
    have hfin := p.finite_support_nat_finrank_representationWeightSpace ρ
    let c : characterLattice p.torus →₀ ℤ := Finsupp.ofSupportFinite
      (fun mu => (Module.finrank k (p.representationWeightSpace ρ mu) : ℤ)) (by
        refine hfin.subset ?_
        intro mu hmu
        simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at hmu ⊢
        exact hmu)
    have hcapp : ∀ mu, c mu = Module.finrank k (p.representationWeightSpace ρ mu) :=
      fun mu => rfl
    refine ⟨c, ⟨n, z, ρ, ζ, fun mu => by rw [hcapp, hζ, Nat.cast_zero, sub_zero]⟩, ?_, ?_, ?_⟩
    · exact Langlands.LinearAlgebra.DominantTriangular.isInvariant_reflectionGroup_of_reflection
        (P := p.rootDatum) fun i mu => by
          rw [hcapp, hcapp, p.finrank_representationWeightSpace_root_reflection]
    · rw [hcapp, hρ.2.2.1, Nat.cast_one]
    · intro mu hmu
      refine hρ.2.2.2 mu (p.representationWeightSpace_ne_bot_of_finrank_ne_zero ρ ?_)
      intro h0
      apply hmu
      rw [hcapp, h0, Nat.cast_zero]
  exact Langlands.LinearAlgebra.DominantTriangular.isInvariant_mem_of_triangular
    (P := p.rootDatum) (b := p.base) (AddSubgroup.toIntSubmodule S) hc
    (Langlands.LinearAlgebra.DominantTriangular.isInvariant_reflectionGroup_of_reflection
      (P := p.rootDatum) hf)

end SplitPinning

/-- The character theorem follows from the classification of simple representations by
highest weight. -/
theorem splitRepresentationCharacterStatement_of_classification
    (h : SplitHighestWeightClassificationStatement.{u}) :
    SplitRepresentationCharacterStatement.{u} := by
  intro k _ G _ p IsSemisimpleRep
  obtain ⟨hcl1, hcl2, hcl3⟩ := h k G p
  refine ⟨fun n ρ => ⟨p.finite_support_nat_finrank_representationWeightSpace ρ,
    fun i lam => p.finrank_representationWeightSpace_root_reflection ρ lam i⟩, ?_, ?_⟩
  · intro n m ρ σ hρ hσ hw
    exact p.exists_intertwines_bijective_of_finrank_eq hcl2 hcl3 ρ σ hρ hσ hw
  · intro f hf
    exact p.exists_sub_of_reflection_invariant hcl1 f hf

end Langlands.GroupScheme
