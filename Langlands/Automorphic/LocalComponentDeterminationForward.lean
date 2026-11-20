import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement

/-!
# Equivalent automorphic representations have the same local components

The forward implication of `LocalComponentDeterminationStatement`, from
`LocalComponentExistenceStatement`: an equivalence of operator subquotients commutes with
every operator, hence carries isotypy at a place from one subquotient to the other.

* `OperatorSubquotient.Equivalence.apply_representation`: an equivalence commutes with
  every operator of the concrete algebra.
* `OperatorSubquotient.isFinitePlaceIsotypic_of_equivalence`,
  `isRealPlaceIsotypic_of_equivalence`, `isComplexPlaceIsotypic_of_equivalence`:
  transport of isotypy along an equivalence.
* `localComponentDetermination_forward`: the forward implication.
-/

noncomputable section

universe u uW uV

set_option autoImplicit false

open scoped TensorProduct

namespace Langlands.Automorphic

open Langlands.Global
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)

attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup localComponentGeneralLinearTopology

attribute [local instance 100] LieRing.ofAssociativeRing

section Transport

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {N : Type*} [AddCommGroup N] [Module ℂ N]
  {N' : Type*} [AddCommGroup N'] [Module ℂ N']

/-- If composition with a linear equivalence `e` sends the maps of a family into a second
family and the ranges of the first family span `N`, the ranges of the second span `N'`. -/
theorem iSup_range_eq_top_of_comp {ι : Type*} {ι' : Type*} (f : ι → M →ₗ[ℂ] N)
    (f' : ι' → M →ₗ[ℂ] N') (e : N ≃ₗ[ℂ] N') (hf : ∀ i, ∃ j, f' j = e.toLinearMap ∘ₗ f i)
    (h : ⨆ i, LinearMap.range (f i) = ⊤) : ⨆ j, LinearMap.range (f' j) = ⊤ := by
  have key : Submodule.map e.toLinearMap (⨆ i, LinearMap.range (f i)) ≤
      ⨆ j, LinearMap.range (f' j) := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i => ?_
    obtain ⟨j, hj⟩ := hf i
    rw [← LinearMap.range_comp, ← hj]
    exact le_iSup (fun j => LinearMap.range (f' j)) j
  rw [h, Submodule.map_top, LinearEquiv.range] at key
  exact eq_top_iff.mpr key

/-- The same for families indexed by the members of two submodules of linear maps. -/
theorem iSup_mem_range_eq_top_of_comp (S : Submodule ℂ (M →ₗ[ℂ] N))
    (S' : Submodule ℂ (M →ₗ[ℂ] N')) (e : N ≃ₗ[ℂ] N')
    (hS : ∀ f ∈ S, e.toLinearMap ∘ₗ f ∈ S') (h : ⨆ f ∈ S, LinearMap.range f = ⊤) :
    ⨆ f ∈ S', LinearMap.range f = ⊤ := by
  have h₁ : ⨆ f : S, LinearMap.range (f : M →ₗ[ℂ] N) = ⊤ :=
    (iSup_subtype' (p := fun f => f ∈ S) (f := fun f _ => LinearMap.range f)).symm.trans h
  have h₂ := iSup_range_eq_top_of_comp (fun f : S => (f : M →ₗ[ℂ] N))
    (fun f : S' => (f : M →ₗ[ℂ] N')) e (fun f => ⟨⟨_, hS f f.2⟩, rfl⟩) h₁
  exact (iSup_subtype' (p := fun f => f ∈ S') (f := fun f _ => LinearMap.range f)).trans h₂

end Transport

namespace OperatorSubquotient

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {Q Q' : OperatorSubquotient F n}

/-- An equivalence commutes with every operator of the concrete algebra. -/
theorem Equivalence.apply_representation (e : Q.Equivalence Q')
    (a : automorphicOperatorAlgebra F n) (x : Q.Space) :
    e.toLinearEquiv (Q.representation a x) = Q'.representation a (e.toLinearEquiv x) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' a) x

/-- An equivalence as an intertwining map of the restrictions to `GL_n(F_v)`. -/
def Equivalence.localIntertwining (e : Q.Equivalence Q') (v : FinitePlace F) :
    (Q.localRepresentation v).IntertwiningMap (Q'.localRepresentation v) where
  toLinearMap := e.toLinearEquiv.toLinearMap
  isIntertwining' g := e.toIntertwiningMap.isIntertwining'
    (finiteOperator F n (FiniteAdelicGL.localInclusion F n v g))

theorem isFinitePlaceIsotypic_of_equivalence (e : Q.Equivalence Q') (v : FinitePlace F)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (FiniteLocalGL F n v) W)
    (h : Q.IsFinitePlaceIsotypic v ρ) : Q'.IsFinitePlaceIsotypic v ρ :=
  iSup_range_eq_top_of_comp (fun f : ρ.IntertwiningMap (Q.localRepresentation v) => f.toLinearMap)
    (fun f : ρ.IntertwiningMap (Q'.localRepresentation v) => f.toLinearMap) e.toLinearEquiv
    (fun f => ⟨(e.localIntertwining v).comp f, rfl⟩) h

theorem isRealPlaceIsotypic_of_equivalence (e : Q.Equivalence Q')
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (h : Q.IsRealPlaceIsotypic v ρ π) : Q'.IsRealPlaceIsotypic v ρ π := by
  refine iSup_mem_range_eq_top_of_comp _ _ e.toLinearEquiv (fun f hf => ⟨fun k x => ?_,
    fun X x => ?_⟩) h
  · exact (congrArg e.toLinearEquiv (hf.1 k x)).trans (e.apply_representation _ (f x))
  · exact (congrArg e.toLinearEquiv (hf.2 X x)).trans (e.apply_representation _ (f x))

theorem isComplexPlaceIsotypic_of_equivalence (e : Q.Equivalence Q')
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (h : Q.IsComplexPlaceIsotypic v ρ π) : Q'.IsComplexPlaceIsotypic v ρ π := by
  refine iSup_mem_range_eq_top_of_comp _ _ e.toLinearEquiv (fun f hf => ⟨fun k x => ?_,
    fun X x => ?_⟩) h
  · exact (congrArg e.toLinearEquiv (hf.1 k x)).trans (e.apply_representation _ (f x))
  · exact (congrArg e.toLinearEquiv (hf.2 X x)).trans (e.apply_representation _ (f x))

end OperatorSubquotient

/-- **Equivalent subquotients have common local components** (the forward implication of
`LocalComponentDeterminationStatement`), from `LocalComponentExistenceStatement`: the local
components of `Q` are local components of every `Q'` equivalent to `Q`. -/
theorem localComponentDetermination_forward (hex : LocalComponentExistenceStatement.{u})
    (F : Type u) [Field F] [NumberField F] (r : ℕ) (Q Q' : IrreducibleOperatorSubquotient F r)
    (hQ : Q.subquotient.IsJointlyAdmissible) (he : Nonempty (Q.Equivalence Q')) :
    (∀ v : FinitePlace F, ∃ (W : ModuleCat.{u} ℂ)
        (ρ : Representation ℂ (FiniteLocalGL F (r + 1) v) W), ρ.IsIrreducible ∧
      Q.subquotient.IsFinitePlaceIsotypic v ρ ∧ Q'.subquotient.IsFinitePlaceIsotypic v ρ) ∧
    (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℝ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
        Archimedean.IsIrreducibleGKModule ρ π ∧
          Q.subquotient.IsRealPlaceIsotypic v ρ π ∧ Q'.subquotient.IsRealPlaceIsotypic v ρ π) ∧
    ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      ∃ (V : ModuleCat.{u} ℂ) (ρ : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) ℂ) V)
        (π : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
        Archimedean.IsIrreducibleGKModule ρ π ∧
          Q.subquotient.IsComplexPlaceIsotypic v ρ π ∧
            Q'.subquotient.IsComplexPlaceIsotypic v ρ π := by
  obtain ⟨e⟩ := he
  have hQex := hex F r Q hQ
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · have hv := hQex.1 v
    obtain ⟨A, hA⟩ := hv
    exact ⟨ModuleCat.of ℂ A.obj, A.obj.representation, A.property.1, hA,
      OperatorSubquotient.isFinitePlaceIsotypic_of_equivalence e v _ hA⟩
  · have hv := hQex.2.1 v
    obtain ⟨V, ρ, π, -, hirr, -, hiso⟩ := hv
    exact ⟨V, ρ, π, hirr, hiso,
      OperatorSubquotient.isRealPlaceIsotypic_of_equivalence e v ρ π hiso⟩
  · have hv := hQex.2.2 v
    obtain ⟨V, ρ, π, -, hirr, -, hiso⟩ := hv
    exact ⟨V, ρ, π, hirr, hiso,
      OperatorSubquotient.isComplexPlaceIsotypic_of_equivalence e v ρ π hiso⟩

end Langlands.Automorphic
