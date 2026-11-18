import Langlands.GroupScheme.Reductive.TitsObstruction
import Langlands.GroupScheme.Reductive.HighestWeightMaximalSubquotient
import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebraFixed

/-! # The Tits class of a maximal simple weight -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : Type} [Fintype n] [DecidableEq n]

variable (k) in
/-- Matrices with entries in `k`, as a subalgebra of `M_n(K)`. -/
def groundMatrices : Subalgebra k (Matrix n n K) :=
  ((Algebra.ofId k K).mapMatrix : Matrix n n k →ₐ[k] Matrix n n K).range

theorem mapMatrix_injective :
    Function.Injective ((Algebra.ofId k K).mapMatrix : Matrix n n k →ₐ[k] Matrix n n K) := by
  intro x y h
  ext i j
  have := congrFun (congrFun h i) j
  exact (algebraMap k K).injective this

theorem groundMatrices_le_twistedFixed_one :
    (groundMatrices k : Subalgebra k (Matrix n n K)) ≤ twistedFixed (fun _ => 1) := by
  rintro _ ⟨x, rfl⟩ σ
  rw [Matrix.one_mul, Matrix.mul_one]
  ext i j
  change algebraMap k K (x i j) = σ (algebraMap k K (x i j))
  rw [AlgEquiv.commutes]

theorem span_groundMatrices :
    Submodule.span K ((groundMatrices k : Subalgebra k (Matrix n n K)) : Set (Matrix n n K)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h1 : Matrix.single i j (1 : K) ∈ (groundMatrices k : Subalgebra k (Matrix n n K)) :=
    ⟨Matrix.single i j 1, by
      ext a b
      simp [Matrix.single_apply]⟩
  have : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : K) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

variable [IsGalois k K]

theorem twistedFixed_one_eq_groundMatrices :
    twistedFixed (k := k) (fun _ => (1 : Matrix n n K)) = groundMatrices k := by
  have hle := groundMatrices_le_twistedFixed_one (k := k) (K := K) (n := n)
  have hfin : Module.finrank k (groundMatrices k : Subalgebra k (Matrix n n K)) =
      Fintype.card n * Fintype.card n := by
    have := LinearMap.finrank_range_of_inj (f := ((Algebra.ofId k K).mapMatrix :
      Matrix n n k →ₐ[k] Matrix n n K).toLinearMap) mapMatrix_injective
    rw [Module.finrank_matrix, Module.finrank_self, mul_one] at this
    exact this
  have hfd := finiteDimensional (k := k) (fun _ => (1 : Matrix n n K)) (fun _ => isUnit_one)
    (twistedFixed (fun _ => 1)) le_rfl
  have : FiniteDimensional k
      (Subalgebra.toSubmodule (twistedFixed (k := k) (fun _ => (1 : Matrix n n K)))) := hfd
  symm
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_le hle
  change Module.finrank k (twistedFixed (k := k) (fun _ => (1 : Matrix n n K))) ≤
    Module.finrank k (groundMatrices k : Subalgebra k (Matrix n n K))
  rw [hfin]
  exact finrank_twistedFixed_le _ (fun _ => isUnit_one)

/-- The descended algebra for the trivial twisting is `M_n(k)`. -/
def twistedFixedOneEquiv :
    twistedFixed (k := k) (fun _ => (1 : Matrix n n K)) ≃ₐ[k] Matrix n n k :=
  (Subalgebra.equivOfEq _ _ twistedFixed_one_eq_groundMatrices).trans
    (AlgEquiv.ofInjective _ mapMatrix_injective).symm

theorem span_twistedFixed_one :
    Submodule.span K ((twistedFixed (k := k) (fun _ => (1 : Matrix n n K)) : Subalgebra k _) :
      Set (Matrix n n K)) = ⊤ := by
  rw [twistedFixed_one_eq_groundMatrices]
  exact span_groundMatrices

/-- The descended algebra for the trivial twisting has trivial Brauer class. -/
theorem classOf_toCSA_one [Nonempty n] :
    Langlands.Brauer.classOf (toCSA (k := k) (fun _ => (1 : Matrix n n K)) (fun _ => isUnit_one)
      (twistedFixed (fun _ => 1)) le_rfl span_twistedFixed_one) = 0 := by
  have hm : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  have e : (toCSA (k := k) (fun _ => (1 : Matrix n n K)) (fun _ => isUnit_one)
      (twistedFixed (fun _ => 1)) le_rfl span_twistedFixed_one) ≃ₐ[k]
      Langlands.Brauer.matrix (Langlands.Brauer.groundField k) (Fintype.card n) :=
    twistedFixedOneEquiv.trans (Matrix.reindexAlgEquiv k k (Fintype.equivFin n))
  rw [Langlands.Brauer.classOf_eq_of_algEquiv e, Langlands.Brauer.classOf_matrix,
    Langlands.Brauer.classOf_groundField]

end Langlands.Algebra.GaloisTwistedMatrix

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [IsGalois k K]

local instance titsMaximalAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- Tits 1971, Proposition 3.4: a star-fixed maximal weight of multiplicity one of a
representation with Galois intertwiners `P` and a descended algebra `B` has Tits algebra Brauer
equivalent to `B`. -/
theorem titsCSAOf_isBrauerEquivalent_of_maximal {N : Type} [Fintype N] [DecidableEq N]
    [Nonempty N]
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N}
    (P : (K ≃ₐ[k] K) → Matrix N N K) (hPi : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ))
    (hPu : ∀ σ, IsUnit (P σ)) (B : Subalgebra k (Matrix N N K)) (hB : B ≤ twistedFixed P)
    (hBs : Submodule.span K (B : Set (Matrix N N K)) = ⊤) (hρB : titsAlgebra ρ ≤ B)
    {nu : characterLattice d.toSplitPinning.torus} (hfix : d.IsStarFixedWeight nu)
    (hmult : Module.finrank K (d.toSplitPinning.representationWeightSpace ρ nu) = 1)
    (hmaximal : ∀ mu, d.toSplitPinning.representationWeightSpace ρ mu ≠ ⊥ →
      mu - nu ∈ d.toSplitPinning.positiveRootMonoid → mu = nu)
    {r : ℕ} {ρ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin r)}
    (hρ' : d.toSplitPinning.IsHighestWeight ρ' nu) :
    IsBrauerEquivalent (d.titsCSAOf hρ' hfix) (toCSA P hPu B hB hBs) := by
  classical
  have hX := d.isTwistedStable_highestGenerated hfix P hPi
  have hY := d.isTwistedStable_highestRadical hfix P hPi hPu
  obtain ⟨f, hfB, hff, hfX, hfY, hfid⟩ := exists_adapted_idempotent P hPu B hB hBs
    (d.toSplitPinning.highestRadical_le ρ nu) hX hY
  obtain ⟨D⟩ := d.toSplitPinning.nonempty_highestSubquotientData ρ nu
  have hD : d.toSplitPinning.IsHighestWeight D.quot nu :=
    D.isHighestWeight_of_maximal hmult hmaximal
  have := d.nonempty_of_isHighestWeight hD
  set P' := fun σ => (d.exists_intertwiner_galoisTwist hD hfix σ).choose with hP'
  have hP'i : ∀ σ, D.quot.Intertwines (galoisTwist σ D.quot) (P' σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist hD hfix σ).choose_spec.1
  have hP'u : ∀ σ, IsUnit (P' σ) := fun σ =>
    (d.exists_intertwiner_galoisTwist hD hfix σ).choose_spec.2
  obtain ⟨hFE, hEF, heq⟩ := D.titsAlgebra_quot_eq_compressed hD.1
    (SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning hD) P' hP'u hP'i B P hPu
    hB hρB hfB hff hfX hfY hfid
  have e1 : IsBrauerEquivalent (d.titsCSAOf hρ' hfix) (d.titsCSAOf hD hfix) :=
    d.titsCSAOf_isBrauerEquivalent hρ' hD hfix
  have e2 : IsBrauerEquivalent (d.titsCSAOf hD hfix)
      (toCSA _ (isUnit_compressed_twist hB hPu _ _ hFE hEF) _
        (compressed_le_twistedFixed hB _ _ hFE hEF) (span_compressed hBs _ _ hFE hEF)) :=
    ⟨1, 1, one_ne_zero, one_ne_zero, ⟨(Subalgebra.equivOfEq _ _ heq).mapMatrix⟩⟩
  exact (e1.trans e2).trans (isBrauerEquivalent_toCSA_compressed P hPu B hB hBs _ _ hFE hEF)

variable (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

/-- The Tits obstruction of a star-fixed maximal weight of multiplicity one is the class of the
descended algebra of the ambient representation. -/
theorem titsObstructionValue_of_maximal {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N}
    (P : (K ≃ₐ[k] K) → Matrix N N K) (hPi : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ))
    (hPu : ∀ σ, IsUnit (P σ)) (B : Subalgebra k (Matrix N N K)) (hB : B ≤ twistedFixed P)
    (hBs : Submodule.span K (B : Set (Matrix N N K)) = ⊤) (hρB : titsAlgebra ρ ≤ B)
    {nu : characterLattice d.toSplitPinning.torus} (hfix : d.IsStarFixedWeight nu)
    (hmult : Module.finrank K (d.toSplitPinning.representationWeightSpace ρ nu) = 1)
    (hmaximal : ∀ mu, d.toSplitPinning.representationWeightSpace ρ mu ≠ ⊥ →
      mu - nu ∈ d.toSplitPinning.positiveRootMonoid → mu = nu) :
    d.titsObstructionValue hspan nu hfix = classOf (toCSA P hPu B hB hBs) := by
  obtain ⟨D⟩ := d.toSplitPinning.nonempty_highestSubquotientData ρ nu
  have hdom := D.isDominantWeight_of_maximal hmult hmaximal
  have hD := D.isHighestWeight_of_maximal hmult hmaximal
  rw [d.titsObstructionValue_eq_classOf hspan hfix hdom hD]
  exact (classOf_eq_iff _ _).mpr
    (d.titsCSAOf_isBrauerEquivalent_of_maximal P hPi hPu B hB hBs hρB hfix hmult hmaximal hD)

/-- A representation of `G_K` is Galois-rational if its universal matrix is unchanged by every
Galois twist (for instance, the scalar extension of a representation over `k`). -/
def IsGaloisRational {N : Type} [Fintype N] [DecidableEq N]
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N) : Prop :=
  ∀ σ : K ≃ₐ[k] K, universalMatrix (galoisTwist σ ρ) = universalMatrix ρ

omit [LocallyOfFiniteType G.X.hom] [IsGalois k K] in
theorem IsGaloisRational.intertwines_one {N : Type} [Fintype N] [DecidableEq N]
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N}
    (hρ : IsGaloisRational ρ) (σ : K ≃ₐ[k] K) : ρ.Intertwines (galoisTwist σ ρ) 1 := by
  rw [intertwines_iff_universalMatrix, hρ σ, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mul, Matrix.mul_one]

/-- Tits 1971, Proposition 3.4 for `D = k`: a star-fixed maximal weight of multiplicity one of a
Galois-rational representation has trivial Tits obstruction. -/
theorem titsObstructionValue_eq_zero_of_rational {N : Type} [Fintype N] [DecidableEq N]
    [Nonempty N]
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) N}
    (hρ : IsGaloisRational ρ)
    {nu : characterLattice d.toSplitPinning.torus} (hfix : d.IsStarFixedWeight nu)
    (hmult : Module.finrank K (d.toSplitPinning.representationWeightSpace ρ nu) = 1)
    (hmaximal : ∀ mu, d.toSplitPinning.representationWeightSpace ρ mu ≠ ⊥ →
      mu - nu ∈ d.toSplitPinning.positiveRootMonoid → mu = nu) :
    d.titsObstructionValue hspan nu hfix = 0 := by
  rw [d.titsObstructionValue_of_maximal hspan (fun _ => 1) hρ.intertwines_one
    (fun _ => isUnit_one) (twistedFixed (fun _ => 1)) le_rfl span_twistedFixed_one
    (titsAlgebra_le_twistedFixed _ hρ.intertwines_one) hfix hmult hmaximal]
  exact classOf_toCSA_one

end Langlands.GroupScheme.GaloisPinningData
