import Langlands.Weil.Representation.Operations
import Langlands.Representation.Twist.SubquotientDefinitions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Closure of finite-dimensional complex representation properties -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Weil

universe uG uV uU

namespace OperationClosure

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {U : Type uU} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]

/-- Annihilators of invariant subspaces are invariant for the contragredient. -/
def annihilator {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Subrepresentation ρ.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g φ hφ := by
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    intro v hv
    exact hφ _ (S.apply_mem_toSubmodule g⁻¹ hv)

/-- The coannihilator of an invariant dual subspace is invariant. -/
def coannihilator {ρ : Representation ℂ G V} (S : Subrepresentation ρ.dual) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro φ hφ
    have h := hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)
    simpa only [Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, inv_inv] using h

/-- Finite-dimensional annihilator duality reverses the invariant-subspace lattice. -/
def annihilatorOrderIso (ρ : Representation ℂ G V) :
    Subrepresentation ρ ≃o (Subrepresentation ρ.dual)ᵒᵈ where
  toFun := annihilator
  invFun := coannihilator
  left_inv _S := Subrepresentation.toSubmodule_injective
    Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv _S := Subrepresentation.toSubmodule_injective
    Subspace.dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := Subspace.dualAnnihilator_le_dualAnnihilator_iff

theorem irreducible_dual_iff (ρ : Representation ℂ G V) :
    Representation.IsIrreducible ρ.dual ↔ Representation.IsIrreducible ρ :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans
    (annihilatorOrderIso ρ).isSimpleOrder_iff.symm

theorem semisimple_dual_iff (ρ : Representation ℂ G V) :
    Representation.IsSemisimpleRepresentation ρ.dual ↔
      Representation.IsSemisimpleRepresentation ρ := by
  constructor
  · intro h
    let := h
    exact (annihilatorOrderIso ρ).complementedLattice_iff.mpr inferInstance
  · intro h
    let := h
    have := (annihilatorOrderIso ρ).complementedLattice_iff.mp h
    exact (inferInstance : ComplementedLattice ((Subrepresentation ρ.dual)ᵒᵈ)ᵒᵈ)

omit [FiniteDimensional ℂ V] in
theorem irreducible_twist_iff (χ : G →* ℂˣ) (ρ : Representation ℂ G V) :
    Representation.IsIrreducible (Langlands.twist χ ρ) ↔
      Representation.IsIrreducible ρ :=
  (Langlands.twistSubrepresentationOrderIso χ ρ).isSimpleOrder_iff.symm

omit [FiniteDimensional ℂ V] in
theorem semisimple_twist_iff (χ : G →* ℂˣ) (ρ : Representation ℂ G V) :
    Representation.IsSemisimpleRepresentation (Langlands.twist χ ρ) ↔
      Representation.IsSemisimpleRepresentation ρ :=
  (Langlands.twistSubrepresentationOrderIso χ ρ).complementedLattice_iff.symm

/-- Recover an endomorphism from its transpose using bidual evaluation. -/
def recoverTranspose : Module.End ℂ (Module.Dual ℂ V) →ₗ[ℂ] Module.End ℂ V :=
  (Module.evalEquiv ℂ V).symm.conj.toLinearMap.comp Module.Dual.transpose

theorem recoverTranspose_transpose (f : Module.End ℂ V) :
    recoverTranspose (Module.Dual.transpose f) = f := by
  ext v
  apply (Module.evalEquiv ℂ V).injective
  ext φ
  simp [recoverTranspose, LinearEquiv.conj_apply, Module.Dual.transpose_apply]

theorem transpose_injective :
    Function.Injective (Module.Dual.transpose :
      Module.End ℂ V → Module.End ℂ (Module.Dual ℂ V)) := by
  intro f g h
  simpa only [recoverTranspose_transpose] using congrArg recoverTranspose h

omit [FiniteDimensional ℂ V] in
theorem transpose_one :
    Module.Dual.transpose (1 : Module.End ℂ V) = 1 := by
  rfl

theorem recoverTranspose_dual (ρ : Representation ℂ G V) (g : G) :
    recoverTranspose (ρ.dual g) = ρ g⁻¹ :=
  recoverTranspose_transpose _

theorem dual_eq_one_iff (ρ : Representation ℂ G V) (g : G) :
    ρ.dual g = 1 ↔ ρ g = 1 := by
  rw [Representation.dual_apply, ← transpose_one,
    transpose_injective.eq_iff]
  exact ρ.ker.inv_mem_iff

theorem finite_range₂ {A B C D : Type*} (f : A → B) (g : A → C)
    (op : B → C → D) (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) :
    (Set.range fun a => op (f a) (g a)).Finite :=
  (Set.Finite.image2 op hf hg).subset (by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, ⟨a, rfl⟩, g a, ⟨a, rfl⟩, rfl⟩)

theorem finite_range_dual_iff (ρ : Representation ℂ G V) :
    (Set.range ρ.dual).Finite ↔ (Set.range ρ).Finite := by
  constructor
  · intro h
    apply (h.image recoverTranspose).subset
    rintro _ ⟨g, rfl⟩
    exact ⟨ρ.dual g⁻¹, ⟨g⁻¹, rfl⟩, by
      rw [recoverTranspose_dual, inv_inv]⟩
  · intro h
    apply (h.image Module.Dual.transpose).subset
    rintro _ ⟨g, rfl⟩
    exact ⟨ρ g⁻¹, ⟨g⁻¹, rfl⟩, rfl⟩

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
theorem prod_eq_one (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (g : G) (hρ : ρ g = 1) (hσ : σ g = 1) : (ρ.prod σ) g = 1 := by
  change LinearMap.prodMap (ρ g) (σ g) = 1
  rw [hρ, hσ]
  rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
theorem tensor_eq_one (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (g : G) (hρ : ρ g = 1) (hσ : σ g = 1) : (ρ.tprod σ) g = 1 := by
  rw [Representation.tprod_apply, hρ, hσ]
  exact TensorProduct.map_one

omit [FiniteDimensional ℂ V] in
theorem twist_eq_one (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (g : G) (hρ : ρ g = 1) (hχ : χ g = 1) : Langlands.twist χ ρ g = 1 := by
  change (χ g : ℂ) • ρ g = 1
  rw [hρ, hχ]
  exact one_smul ℂ _

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
theorem finite_range_prod_tensor (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (hρ : (Set.range ρ).Finite) (hσ : (Set.range σ).Finite) :
    (Set.range (ρ.prod σ)).Finite ∧ (Set.range (ρ.tprod σ)).Finite :=
  ⟨finite_range₂ ρ σ LinearMap.prodMap hρ hσ,
    finite_range₂ ρ σ TensorProduct.map hρ hσ⟩

omit [FiniteDimensional ℂ V] in
theorem finite_range_twist (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : (Set.range ρ).Finite) (hχ : (Set.range χ).Finite) :
    (Set.range (Langlands.twist χ ρ)).Finite :=
  finite_range₂ χ ρ (fun c f => (c : ℂ) • f) hχ hρ

theorem isOpen_ker_of_common_kernel [TopologicalSpace G] [IsTopologicalGroup G]
    {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : G →* M) (g : G →* N) (h : G →* P)
    (hfg : ∀ x, f x = 1 → g x = 1 → h x = 1)
    (hf : IsOpen (f.ker : Set G)) (hg : IsOpen (g.ker : Set G)) :
    IsOpen (h.ker : Set G) :=
  Subgroup.isOpen_mono
    (show f.ker ⊓ g.ker ≤ h.ker from fun x hx => hfg x hx.1 hx.2)
    (hf.inter hg)

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

local instance endTopology (W : Type*) [AddCommGroup W] [Module ℂ W] :
    TopologicalSpace (Module.End ℂ W) := moduleTopology ℂ (Module.End ℂ W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] [IsTopologicalGroup G] in
theorem continuous_prod (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (hρ : Continuous ρ) (hσ : Continuous σ) : Continuous (ρ.prod σ) := by
  have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ (V × U))
  exact (IsModuleTopology.continuous_of_linearMap
    (LinearMap.prodMapAlgHom ℂ V U).toLinearMap).comp (hρ.prodMk hσ)

omit [FiniteDimensional ℂ U] [IsTopologicalGroup G] in
theorem continuous_tensor (ρ : Representation ℂ G V) (σ : Representation ℂ G U)
    (hρ : Continuous ρ) (hσ : Continuous σ) : Continuous (ρ.tprod σ) := by
  change Continuous (fun g => TensorProduct.map (ρ g) (σ g))
  have hc : Continuous (fun p : Module.End ℂ V × Module.End ℂ U =>
      TensorProduct.map p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left
      (TensorProduct.mapBilinear (RingHom.id ℂ) V U V U)
  exact hc.comp (f := fun g : G => (ρ g, σ g)) (hρ.prodMk hσ)

theorem continuous_dual_iff (ρ : Representation ℂ G V) :
    Continuous ρ.dual ↔ Continuous ρ := by
  constructor
  · intro h
    have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ V)
    have hc := (IsModuleTopology.continuous_of_linearMap
      (recoverTranspose (V := V))).comp (h.comp continuous_inv)
    simpa only [Function.comp_def, recoverTranspose_dual, inv_inv] using hc
  · intro h
    have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ (Module.Dual ℂ V))
    exact (IsModuleTopology.continuous_of_linearMap
      (Module.Dual.transpose : Module.End ℂ V →ₗ[ℂ] _)).comp (h.comp continuous_inv)

omit [FiniteDimensional ℂ V] [IsTopologicalGroup G] in
theorem continuous_twist (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hχ : Continuous χ) (hρ : Continuous ρ) : Continuous (Langlands.twist χ ρ) :=
  (Units.continuous_val.comp hχ).smul hρ

end Topology

end OperationClosure

open OperationClosure in
/-- All clauses of the published finite-dimensional complex operation-closure target. -/
theorem representationOperationClosure :
    RepresentationOperationClosure.{uG, uV, uU} := by
  intro G _ _ _ I V _ _ _ U _ _ _ ρ σ
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  let : TopologicalSpace (Module.End ℂ U) := moduleTopology ℂ (Module.End ℂ U)
  let : TopologicalSpace (Module.End ℂ (V × U)) :=
    moduleTopology ℂ (Module.End ℂ (V × U))
  let : TopologicalSpace (Module.End ℂ (V ⊗[ℂ] U)) :=
    moduleTopology ℂ (Module.End ℂ (V ⊗[ℂ] U))
  let : TopologicalSpace (Module.End ℂ (Module.Dual ℂ V)) :=
    moduleTopology ℂ (Module.End ℂ (Module.Dual ℂ V))
  refine ⟨fun hρ hσ => ⟨continuous_prod ρ σ hρ hσ, continuous_tensor ρ σ hρ hσ⟩,
    continuous_dual_iff ρ, ?_, ?_, finite_range_prod_tensor ρ σ,
    finite_range_dual_iff ρ, ?_, ?_, ?_, ?_,
    irreducible_dual_iff ρ, semisimple_dual_iff ρ, ?_⟩
  · intro hρ hσ
    exact ⟨isOpen_ker_of_common_kernel (ρ.comp I.subtype) (σ.comp I.subtype)
        ((ρ.prod σ).comp I.subtype)
        (fun i hi hj => prod_eq_one ρ σ i hi hj) hρ hσ,
      isOpen_ker_of_common_kernel (ρ.comp I.subtype) (σ.comp I.subtype)
        ((ρ.tprod σ).comp I.subtype)
        (fun i hi hj => tensor_eq_one ρ σ i hi hj) hρ hσ⟩
  · have hk : (ρ.dual.comp I.subtype).ker = (ρ.comp I.subtype).ker := by
      ext i
      exact dual_eq_one_iff ρ i
    rw [hk]
  · exact finite_range_prod_tensor (ρ.comp I.subtype) (σ.comp I.subtype)
  · exact finite_range_dual_iff (ρ.comp I.subtype)
  · intro hρ hσ
    exact ⟨fun i => prod_eq_one ρ σ i (hρ i) (hσ i),
      fun i => tensor_eq_one ρ σ i (hρ i) (hσ i)⟩
  · exact forall_congr' (fun i => dual_eq_one_iff ρ i)
  · intro χ
    refine ⟨continuous_twist χ ρ, ?_, fun hχ hρ => finite_range_twist χ ρ hρ hχ,
      fun hχ hρ => finite_range_twist (χ.comp I.subtype) (ρ.comp I.subtype) hρ hχ, ?_,
      irreducible_twist_iff χ ρ, semisimple_twist_iff χ ρ⟩
    · intro hχ hρ
      exact isOpen_ker_of_common_kernel (ρ.comp I.subtype) (χ.comp I.subtype)
        ((Langlands.twist χ ρ).comp I.subtype)
        (fun i hi hj => twist_eq_one χ ρ i hi hj) hρ hχ
    · intro hχ
      apply forall_congr'
      intro i
      change (χ (i : G) : ℂ) • ρ (i : G) = 1 ↔ ρ (i : G) = 1
      rw [hχ i]
      simp only [Units.val_one, one_smul]

end Langlands.Weil
