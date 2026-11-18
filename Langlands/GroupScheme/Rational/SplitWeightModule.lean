import Langlands.GroupScheme.MatrixRepresentation.OperatorModule
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Noetherian.Basic

/-! # Torus weights on modules over the operator algebra of a split group -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

open MatrixRepresentation

namespace MatrixRepresentation

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- A module over the operator algebra is realized when it embeds into the module of a
representation in finite coordinates `Fin r`. -/
def IsRealized (M : Type v) [AddCommGroup M] [Module (OperatorAlgebra G) M] : Prop :=
  ∃ (r : ℕ) (τ : MatrixRepresentation G (Fin r))
    (f : M →ₗ[OperatorAlgebra G] OperatorModule τ), Function.Injective f

variable {G}

theorem isRealized_operatorModule {r : ℕ} (τ : MatrixRepresentation G (Fin r)) :
    IsRealized G (OperatorModule τ) :=
  ⟨r, τ, LinearMap.id, Function.injective_id⟩

variable {M : Type v} [AddCommGroup M] [Module (OperatorAlgebra G) M]
  {N : Type w} [AddCommGroup N] [Module (OperatorAlgebra G) N]

theorem IsRealized.of_injective (hM : IsRealized G M) (g : N →ₗ[OperatorAlgebra G] M)
    (hg : Function.Injective g) : IsRealized G N := by
  obtain ⟨r, τ, f, hf⟩ := hM
  exact ⟨r, τ, f ∘ₗ g, hf.comp hg⟩

theorem IsRealized.submodule (hM : IsRealized G M)
    (S : Submodule (OperatorAlgebra G) M) : IsRealized G S :=
  hM.of_injective S.subtype Subtype.val_injective

theorem IsRealized.finiteDimensional [Module k M] [IsScalarTower k (OperatorAlgebra G) M]
    (hM : IsRealized G M) : FiniteDimensional k M := by
  obtain ⟨r, τ, f, hf⟩ := hM
  exact FiniteDimensional.of_injective (f.restrictScalars k) hf

/-- A module embedding into the module of a representation in arbitrary finite coordinates
is realized. -/
theorem isRealized_of_injective [IsAffineHom G.X.hom] {n : Type} [Fintype n] [DecidableEq n]
    (τ : MatrixRepresentation G n) (f : M →ₗ[OperatorAlgebra G] OperatorModule τ)
    (hf : Function.Injective f) : IsRealized G M := by
  obtain ⟨r, σ, ⟨e⟩⟩ := exists_linearEquiv_submodule (⊤ : Submodule (OperatorAlgebra G)
    (OperatorModule τ))
  refine ⟨r, σ, e.symm.toLinearMap ∘ₗ (LinearEquiv.ofTop ⊤ rfl).symm.toLinearMap ∘ₗ f, ?_⟩
  exact e.symm.injective.comp ((LinearEquiv.ofTop ⊤ rfl).symm.injective.comp hf)

/-- A realized module is isomorphic to the module of a representation in finite
coordinates. -/
theorem IsRealized.exists_linearEquiv [IsAffineHom G.X.hom] (hM : IsRealized G M) :
    ∃ (r : ℕ) (τ : MatrixRepresentation G (Fin r)),
      Nonempty (OperatorModule τ ≃ₗ[OperatorAlgebra G] M) := by
  obtain ⟨r, τ, f, hf⟩ := hM
  obtain ⟨s, σ, ⟨e⟩⟩ := exists_linearEquiv_submodule (LinearMap.range f)
  exact ⟨s, σ, ⟨e.trans (LinearEquiv.ofInjective f hf).symm⟩⟩

end MatrixRepresentation

namespace SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

local instance splitWeightModuleTorusIsAffineHom : IsAffineHom p.torus.toGrp.X.hom :=
  p.isSplitTorus.isAffineHom

/-- The universal point of the split torus, regarded as a point of `G`. -/
def torusPoint :
    (algSpec (CommRingCat.of k)).obj (op (CharacterUnits.Coord p.torus.toGrp)) ⟶ G.X :=
  CharacterUnits.universalPoint p.torus.toGrp ≫ p.inclusion.hom.hom

/-- The coefficient operator of a functional on the torus coordinate algebra at the
universal torus point. -/
def torusOperator (ℓ : CharacterUnits.Coord p.torus.toGrp →ₗ[k] k) : OperatorIndex G :=
  ⟨CharacterUnits.Coord p.torus.toGrp, p.torusPoint, ℓ⟩

/-- The unit of the torus coordinate algebra attached to a weight. -/
def weightUnit (lam : characterLattice p.torus) : CharacterUnits.Coord p.torus.toGrp :=
  (CharacterUnits.unit ((rationalCharacters.equivCharacterLattice p.torus).symm lam) :
    CharacterUnits.Coord p.torus.toGrp)

section Weights

variable (M : Type v) [AddCommGroup M] [Module (OperatorAlgebra G) M] [Module k M]
  [IsScalarTower k (OperatorAlgebra G) M]
  {N : Type w} [AddCommGroup N] [Module (OperatorAlgebra G) N] [Module k N]
  [IsScalarTower k (OperatorAlgebra G) N]

/-- The weight space of `lam` in a module over the operator algebra: the vectors on which
every torus coefficient operator `ℓ` acts by the scalar `ℓ(lam)`. -/
def weightSubmodule (lam : characterLattice p.torus) : Submodule k M where
  carrier := {v | ∀ ℓ : CharacterUnits.Coord p.torus.toGrp →ₗ[k] k,
    FreeAlgebra.ι k (p.torusOperator ℓ) • v = ℓ (p.weightUnit lam) • v}
  zero_mem' := by
    intro ℓ
    simp only [smul_zero]
  add_mem' {v w} hv hw ℓ := by
    rw [smul_add, smul_add, hv ℓ, hw ℓ]
  smul_mem' c v hv ℓ := by
    change FreeAlgebra.ι k (p.torusOperator ℓ) • c • v = ℓ (p.weightUnit lam) • c • v
    rw [smul_comm, hv ℓ, smul_comm]

variable {M}

theorem mem_weightSubmodule {lam : characterLattice p.torus} {v : M} :
    v ∈ p.weightSubmodule M lam ↔ ∀ ℓ : CharacterUnits.Coord p.torus.toGrp →ₗ[k] k,
      FreeAlgebra.ι k (p.torusOperator ℓ) • v = ℓ (p.weightUnit lam) • v :=
  Iff.rfl

theorem map_mem_weightSubmodule (f : M →ₗ[OperatorAlgebra G] N)
    {lam : characterLattice p.torus} {v : M} (hv : v ∈ p.weightSubmodule M lam) :
    f v ∈ p.weightSubmodule N lam := by
  intro ℓ
  rw [← f.map_smul, hv ℓ, LinearMap.map_smul_of_tower]

theorem mem_weightSubmodule_of_injective (f : M →ₗ[OperatorAlgebra G] N)
    (hf : Function.Injective f) {lam : characterLattice p.torus} {v : M}
    (h : f v ∈ p.weightSubmodule N lam) : v ∈ p.weightSubmodule M lam := by
  intro ℓ
  apply hf
  rw [f.map_smul, h ℓ, LinearMap.map_smul_of_tower]

theorem weightSubmodule_ne_bot_of_injective (f : M →ₗ[OperatorAlgebra G] N)
    (hf : Function.Injective f) {lam : characterLattice p.torus}
    (h : p.weightSubmodule M lam ≠ ⊥) : p.weightSubmodule N lam ≠ ⊥ := by
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Submodule.ne_bot_iff]
  refine ⟨f v, p.map_mem_weightSubmodule f hv, ?_⟩
  rw [Ne, ← f.map_zero]
  exact fun h' => hne (hf h')

theorem weightSubmodule_map_linearEquiv (e : M ≃ₗ[OperatorAlgebra G] N)
    (lam : characterLattice p.torus) :
    (p.weightSubmodule M lam).map ((e.restrictScalars k : M ≃ₗ[k] N) : M →ₗ[k] N) =
      p.weightSubmodule N lam := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact p.map_mem_weightSubmodule e.toLinearMap hv
  · intro hx
    refine ⟨e.symm x, p.map_mem_weightSubmodule e.symm.toLinearMap hx, ?_⟩
    change e (e.symm x) = x
    exact e.apply_symm_apply x

theorem finrank_weightSubmodule_eq_of_linearEquiv (e : M ≃ₗ[OperatorAlgebra G] N)
    (lam : characterLattice p.torus) :
    Module.finrank k (p.weightSubmodule M lam) = Module.finrank k (p.weightSubmodule N lam) := by
  rw [← p.weightSubmodule_map_linearEquiv e lam, LinearEquiv.finrank_map_eq]

theorem mem_weightSubmodule_prod {lam : characterLattice p.torus} (x : M × N) :
    x ∈ p.weightSubmodule (M × N) lam ↔
      x.1 ∈ p.weightSubmodule M lam ∧ x.2 ∈ p.weightSubmodule N lam := by
  constructor
  · intro h
    exact ⟨fun ℓ => congrArg Prod.fst (h ℓ), fun ℓ => congrArg Prod.snd (h ℓ)⟩
  · rintro ⟨h1, h2⟩ ℓ
    exact Prod.ext (h1 ℓ) (h2 ℓ)

/-- The weight space of a product is the product of the weight spaces. -/
def weightSubmoduleProdEquiv (lam : characterLattice p.torus) :
    p.weightSubmodule (M × N) lam ≃ₗ[k]
      p.weightSubmodule M lam × p.weightSubmodule N lam where
  toFun x := (⟨x.1.1, ((p.mem_weightSubmodule_prod x.1).mp x.2).1⟩,
    ⟨x.1.2, ((p.mem_weightSubmodule_prod x.1).mp x.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), (p.mem_weightSubmodule_prod _).mpr ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_weightSubmodule_prod [FiniteDimensional k M] [FiniteDimensional k N]
    (lam : characterLattice p.torus) :
    Module.finrank k (p.weightSubmodule (M × N) lam) =
      Module.finrank k (p.weightSubmodule M lam) + Module.finrank k (p.weightSubmodule N lam) := by
  rw [(p.weightSubmoduleProdEquiv lam).finrank_eq, Module.finrank_prod]

theorem mem_weightSubmodule_pi {ι : Type} {P : ι → Type v} [∀ i, AddCommGroup (P i)]
    [∀ i, Module (OperatorAlgebra G) (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k (OperatorAlgebra G) (P i)]
    {lam : characterLattice p.torus} (x : ∀ i, P i) :
    x ∈ p.weightSubmodule (∀ i, P i) lam ↔ ∀ i, x i ∈ p.weightSubmodule (P i) lam := by
  constructor
  · intro h i ℓ
    exact congrFun (h ℓ) i
  · intro h ℓ
    funext i
    exact h i ℓ

/-- The weight space of a product family is the product of the weight spaces. -/
def weightSubmodulePiEquiv {ι : Type} {P : ι → Type v} [∀ i, AddCommGroup (P i)]
    [∀ i, Module (OperatorAlgebra G) (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k (OperatorAlgebra G) (P i)] (lam : characterLattice p.torus) :
    p.weightSubmodule (∀ i, P i) lam ≃ₗ[k] ∀ i, p.weightSubmodule (P i) lam where
  toFun x i := ⟨x.1 i, (p.mem_weightSubmodule_pi x.1).mp x.2 i⟩
  invFun y := ⟨fun i => (y i).1, (p.mem_weightSubmodule_pi _).mpr fun i => (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_weightSubmodule_pi {ι : Type} [Fintype ι] {P : ι → Type v}
    [∀ i, AddCommGroup (P i)] [∀ i, Module (OperatorAlgebra G) (P i)] [∀ i, Module k (P i)]
    [∀ i, IsScalarTower k (OperatorAlgebra G) (P i)] [∀ i, FiniteDimensional k (P i)]
    (lam : characterLattice p.torus) :
    Module.finrank k (p.weightSubmodule (∀ i, P i) lam) =
      ∑ i, Module.finrank k (p.weightSubmodule (P i) lam) := by
  rw [(p.weightSubmodulePiEquiv (P := P) lam).finrank_eq, Module.finrank_pi_fintype]

/-! ### The weight projectors -/

/-- The operator projecting onto the weight space of `lam`. -/
def weightProjector (lam : characterLattice p.torus) : OperatorAlgebra G :=
  FreeAlgebra.ι k (p.torusOperator
    (characterCoefficient ((rationalCharacters.equivCharacterLattice p.torus).symm lam)))

open scoped Classical in
theorem weightProjector_smul_of_mem {lam mu : characterLattice p.torus} {v : M}
    (hv : v ∈ p.weightSubmodule M mu) :
    p.weightProjector lam • v = if mu = lam then v else 0 := by
  rw [weightProjector, hv, weightUnit, characterCoefficient_unit]
  by_cases h : mu = lam
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, one_smul]
  · rw [ite_eq_right h, ite_eq_right, zero_smul]
    intro h'
    exact h ((rationalCharacters.equivCharacterLattice p.torus).symm.injective h')

theorem weightProjector_smul_self {lam : characterLattice p.torus} {v : M}
    (hv : v ∈ p.weightSubmodule M lam) : p.weightProjector lam • v = v := by
  rw [p.weightProjector_smul_of_mem hv, ite_eq_left rfl]

/-! ### Comparison with the weight spaces of a representation -/

variable {n : Type} [Fintype n] [DecidableEq n]

theorem toModule_mem_weightSubmodule_iff (ρ : MatrixRepresentation G n) (v : n → k)
    (lam : characterLattice p.torus) :
    toModule ρ v ∈ p.weightSubmodule (OperatorModule ρ) lam ↔
      v ∈ p.representationWeightSpace ρ lam := by
  have hR : v ∈ p.representationWeightSpace ρ lam ↔
      (ρ.affineMatrix _ p.torusPoint : Matrix n n (CharacterUnits.Coord p.torus.toGrp)) *ᵥ
          (fun r => algebraMap k _ (v r)) =
        p.weightUnit lam • (fun r => algebraMap k _ (v r)) := by
    change v ∈ (ρ.restrict p.inclusion).characterSpace
      ((rationalCharacters.equivCharacterLattice p.torus).symm lam) ↔ _
    rw [MatrixRepresentation.mem_characterSpace_iff,
      MatrixRepresentation.universalCharacterMatrix, affineMatrix_restrict]
    rfl
  rw [hR]
  have hu : ∀ ℓ : CharacterUnits.Coord p.torus.toGrp →ₗ[k] k,
      (fun i => ℓ ((p.weightUnit lam • fun r => algebraMap k _ (v r)) i)) =
        ℓ (p.weightUnit lam) • v := by
    intro ℓ
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  constructor
  · intro h
    apply vector_ext_of_functionals
    intro ℓ
    have h' := h ℓ
    rw [ι_smul_toModule, ← map_smul] at h'
    rw [hu ℓ]
    exact (toModule ρ).injective h'
  · intro h ℓ
    rw [ι_smul_toModule, ← map_smul]
    congr 1
    rw [← hu ℓ]
    exact congrArg (fun a => fun i => ℓ (a i)) h

theorem weightSubmodule_operatorModule (ρ : MatrixRepresentation G n)
    (lam : characterLattice p.torus) :
    p.weightSubmodule (OperatorModule ρ) lam =
      (p.representationWeightSpace ρ lam).map
        ((toModule ρ : (n → k) ≃ₗ[k] OperatorModule ρ) : (n → k) →ₗ[k] OperatorModule ρ) := by
  ext x
  obtain ⟨v, rfl⟩ := (toModule ρ).surjective x
  rw [p.toModule_mem_weightSubmodule_iff, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

theorem finrank_weightSubmodule_operatorModule (ρ : MatrixRepresentation G n)
    (lam : characterLattice p.torus) :
    Module.finrank k (p.weightSubmodule (OperatorModule ρ) lam) =
      Module.finrank k (p.representationWeightSpace ρ lam) := by
  rw [p.weightSubmodule_operatorModule, LinearEquiv.finrank_map_eq]

theorem iSup_weightSubmodule_operatorModule (ρ : MatrixRepresentation G n) :
    (⨆ lam, p.weightSubmodule (OperatorModule ρ) lam) = ⊤ := by
  simp_rw [p.weightSubmodule_operatorModule]
  rw [← Submodule.map_iSup, p.iSup_representationWeightSpace_eq_top, Submodule.map_top,
    LinearEquiv.range]

/-- Every vector of a representation is the sum of its weight projections over a finite
set of weights. -/
theorem exists_finset_eq_sum_weightProjector (ρ : MatrixRepresentation G n)
    (x : OperatorModule ρ) :
    ∃ s : Finset (characterLattice p.torus), x = ∑ mu ∈ s, p.weightProjector mu • x := by
  classical
  have hx : x ∈ ⨆ mu, p.weightSubmodule (OperatorModule ρ) mu := by
    rw [p.iSup_weightSubmodule_operatorModule]
    exact Submodule.mem_top
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  refine ⟨f.support, ?_⟩
  have h : ∀ nu ∈ f.support, p.weightProjector nu • (f.sum fun _ y => y) = f nu := by
    intro nu hnu
    rw [Finsupp.sum, Finset.smul_sum, Finset.sum_eq_single nu]
    · rw [p.weightProjector_smul_of_mem (hf nu), ite_eq_left rfl]
    · intro mu _ hmu
      rw [p.weightProjector_smul_of_mem (hf mu), ite_eq_right hmu]
    · intro hnu'
      exact absurd hnu hnu'
  rw [Finset.sum_congr rfl h]
  rfl

theorem weightProjector_smul_mem_operatorModule (ρ : MatrixRepresentation G n)
    (lam : characterLattice p.torus) (x : OperatorModule ρ) :
    p.weightProjector lam • x ∈ p.weightSubmodule (OperatorModule ρ) lam := by
  have hx : x ∈ ⨆ mu, p.weightSubmodule (OperatorModule ρ) mu := by
    rw [p.iSup_weightSubmodule_operatorModule]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun y =>
    p.weightProjector lam • y ∈ p.weightSubmodule (OperatorModule ρ) lam) hx ?_ ?_ ?_
  · intro mu y hy
    rw [p.weightProjector_smul_of_mem hy]
    split_ifs with h
    · rw [← h]
      exact hy
    · exact Submodule.zero_mem _
  · rw [smul_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [smul_add]
    exact Submodule.add_mem _ hy hz

theorem finite_weightSubmodule_ne_bot_operatorModule (ρ : MatrixRepresentation G n) :
    {lam | p.weightSubmodule (OperatorModule ρ) lam ≠ ⊥}.Finite := by
  have hind : iSupIndep fun lam => p.representationWeightSpace ρ lam :=
    (ρ.restrict p.inclusion).characterSpace_iSupIndep.comp
      (rationalCharacters.equivCharacterLattice p.torus).symm.injective
  have hfin := Submodule.finite_ne_bot_of_iSupIndep hind
  refine hfin.subset ?_
  intro lam hlam hbot
  apply hlam
  rw [p.weightSubmodule_operatorModule, hbot, Submodule.map_bot]

/-! ### Realized modules -/

theorem weightProjector_smul_mem_of_isRealized (hM : IsRealized G M)
    (lam : characterLattice p.torus) (x : M) :
    p.weightProjector lam • x ∈ p.weightSubmodule M lam := by
  obtain ⟨r, τ, f, hf⟩ := hM
  apply p.mem_weightSubmodule_of_injective f hf
  rw [f.map_smul]
  exact p.weightProjector_smul_mem_operatorModule τ lam (f x)

theorem eq_zero_of_isRealized_of_weightSubmodule_eq_bot (hM : IsRealized G M)
    (h : ∀ lam, p.weightSubmodule M lam = ⊥) (x : M) : x = 0 := by
  obtain ⟨r, τ, f, hf⟩ := hM
  apply hf
  rw [f.map_zero]
  obtain ⟨s, hs⟩ := p.exists_finset_eq_sum_weightProjector τ (f x)
  rw [hs]
  apply Finset.sum_eq_zero
  intro mu _
  rw [← f.map_smul]
  have hmem := p.weightProjector_smul_mem_of_isRealized ⟨r, τ, f, hf⟩ mu x
  rw [h mu, Submodule.mem_bot] at hmem
  rw [hmem, f.map_zero]

theorem finite_weightSubmodule_ne_bot_of_isRealized (hM : IsRealized G M) :
    {lam | p.weightSubmodule M lam ≠ ⊥}.Finite := by
  obtain ⟨r, τ, f, hf⟩ := hM
  refine (p.finite_weightSubmodule_ne_bot_operatorModule τ).subset ?_
  intro lam hlam
  exact p.weightSubmodule_ne_bot_of_injective f hf hlam

/-- In a realized semisimple module, a nonzero weight space meets some simple
submodule. -/
theorem exists_isSimpleModule_weightSubmodule_ne_bot_of_isRealized (hM : IsRealized G M)
    [IsSemisimpleModule (OperatorAlgebra G) M] {lam : characterLattice p.torus}
    (h : p.weightSubmodule M lam ≠ ⊥) :
    ∃ S : Submodule (OperatorAlgebra G) M, IsSimpleModule (OperatorAlgebra G) S ∧
      p.weightSubmodule S lam ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have hkill : ∀ x : M, p.weightProjector lam • x = 0 := by
    intro x
    have htop := IsSemisimpleModule.sSup_simples_eq_top (R := OperatorAlgebra G) (M := M)
    rw [sSup_eq_iSup'] at htop
    have hx : x ∈ ⨆ S : ↥{S : Submodule (OperatorAlgebra G) M |
        IsSimpleModule (OperatorAlgebra G) S}, (S : Submodule (OperatorAlgebra G) M) := by
      rw [htop]
      exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun y => p.weightProjector lam • y = 0) hx
      ?_ ?_ ?_
    · rintro ⟨S, hS⟩ y hy
      have hmem : (⟨p.weightProjector lam • y, S.smul_mem _ hy⟩ : S) ∈
          p.weightSubmodule S lam :=
        p.mem_weightSubmodule_of_injective S.subtype Subtype.val_injective
          (p.weightProjector_smul_mem_of_isRealized hM lam y)
      rw [hcon S hS, Submodule.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exact smul_zero _
    · intro y z hy hz
      rw [smul_add, hy, hz, add_zero]
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  apply hne
  rw [← p.weightProjector_smul_self hv]
  exact hkill v

/-- Characters are additive along a complemented pair of submodules. -/
theorem finrank_weightSubmodule_eq_add_of_isCompl [FiniteDimensional k M]
    {S T : Submodule (OperatorAlgebra G) M} (hST : IsCompl S T)
    (lam : characterLattice p.torus) :
    Module.finrank k (p.weightSubmodule M lam) =
      Module.finrank k (p.weightSubmodule S lam) +
        Module.finrank k (p.weightSubmodule T lam) := by
  have : FiniteDimensional k S :=
    FiniteDimensional.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  have : FiniteDimensional k T :=
    FiniteDimensional.of_injective (T.subtype.restrictScalars k) Subtype.val_injective
  rw [← p.finrank_weightSubmodule_eq_of_linearEquiv (Submodule.prodEquivOfIsCompl S T hST),
    p.finrank_weightSubmodule_prod]

/-! ### Characters of direct sums -/

/-- The weight multiplicities of a finite direct sum are the sums of the weight
multiplicities of the summands; the direct sum is realized in coordinates `Fin r`. -/
theorem exists_finrank_representationWeightSpace_eq_sum {I : Type} [Fintype I]
    [DecidableEq I] {ν : I → Type} [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
    (τ : ∀ i, MatrixRepresentation G (ν i)) :
    ∃ (r : ℕ) (σ : MatrixRepresentation G (Fin r)), ∀ lam : characterLattice p.torus,
      Module.finrank k (p.representationWeightSpace σ lam) =
        ∑ i, Module.finrank k (p.representationWeightSpace (τ i) lam) := by
  obtain ⟨r, σ, ⟨e⟩⟩ := (isRealized_of_injective (directSum τ) LinearMap.id
    Function.injective_id).exists_linearEquiv
  refine ⟨r, σ, fun lam => ?_⟩
  rw [← p.finrank_weightSubmodule_operatorModule,
    p.finrank_weightSubmodule_eq_of_linearEquiv (e.trans (directSumModuleEquiv τ)),
    p.finrank_weightSubmodule_pi]
  exact Finset.sum_congr rfl fun i _ => p.finrank_weightSubmodule_operatorModule (τ i) lam

/-- The weight multiplicities of two representations add up to those of a third. -/
theorem exists_finrank_representationWeightSpace_eq_add {a b : ℕ}
    (ρ₁ : MatrixRepresentation G (Fin a)) (ρ₂ : MatrixRepresentation G (Fin b)) :
    ∃ (r : ℕ) (σ : MatrixRepresentation G (Fin r)), ∀ lam : characterLattice p.torus,
      Module.finrank k (p.representationWeightSpace σ lam) =
        Module.finrank k (p.representationWeightSpace ρ₁ lam) +
          Module.finrank k (p.representationWeightSpace ρ₂ lam) := by
  let τ : ∀ t : Bool, MatrixRepresentation G (Fin (bif t then a else b)) := fun t =>
    match t with
    | true => ρ₁
    | false => ρ₂
  obtain ⟨r, σ, hσ⟩ := p.exists_finrank_representationWeightSpace_eq_sum τ
  refine ⟨r, σ, fun lam => ?_⟩
  rw [hσ, Fintype.sum_bool]
  rfl

/-- Some representation has every weight multiplicity zero. -/
theorem exists_finrank_representationWeightSpace_eq_zero :
    ∃ (r : ℕ) (σ : MatrixRepresentation G (Fin r)), ∀ lam : characterLattice p.torus,
      Module.finrank k (p.representationWeightSpace σ lam) = 0 := by
  obtain ⟨r, σ, hσ⟩ := p.exists_finrank_representationWeightSpace_eq_sum
    (I := Empty) (ν := fun _ => Fin 0) (fun i => i.elim)
  refine ⟨r, σ, fun lam => ?_⟩
  rw [hσ, Finset.univ_eq_empty, Finset.sum_empty]

end Weights

end SplitPinning

end Langlands.GroupScheme
