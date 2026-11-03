import Langlands.Algebra.FiniteTypeModuleFlatnessDescentStatement
import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

universe uR₀ uR uB₀ uM₀

open scoped TensorProduct

namespace Langlands.Algebra

/-- Binary products of flat modules are flat. -/
lemma flat_prod {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have hcomm (z : Q ⊗[R] (M × N)) :
      TensorProduct.prodRight R R P M N (Q.subtype.rTensor (M × N) z) =
        (Q.subtype.rTensor M (TensorProduct.prodRight R R Q M N z).1,
          Q.subtype.rTensor N (TensorProduct.prodRight R R Q M N z).2) := by
    induction z with
    | tmul q mn => rfl
    | add z w hz hw => simp only [map_add, Prod.fst_add, Prod.snd_add, hz, hw]; rfl
  intro x y h
  apply (TensorProduct.prodRight R R Q M N).injective
  apply Prod.ext
  · apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) Q.subtype Q.injective_subtype
    have hh := congrArg (TensorProduct.prodRight R R P M N) h
    rw [hcomm, hcomm] at hh
    exact congrArg Prod.fst hh
  · apply Module.Flat.rTensor_preserves_injective_linearMap (M := N) Q.subtype Q.injective_subtype
    have hh := congrArg (TensorProduct.prodRight R R P M N) h
    rw [hcomm, hcomm] at hh
    exact congrArg Prod.snd hh

/-- Flatness of a finite module after scalar extension descends to a finite subalgebra. -/
lemma exists_fg_subalgebra_flat_module
    {R₀ R B₀ M₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    [AddCommGroup M₀] [Module R₀ M₀] [Module B₀ M₀] [IsScalarTower R₀ B₀ M₀]
    [Module.Finite B₀ M₀] [Module.Flat R (R ⊗[R₀] M₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧
      Module.Flat R₁ (R₁ ⊗[R₀] M₀) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R₀ B₀)
  let P := MvPolynomial (Fin n) R₀
  let : Algebra P B₀ := f.toRingHom.toAlgebra
  let : Module P M₀ := Module.compHom M₀ f.toRingHom
  have : IsScalarTower P B₀ M₀ := .of_algebraMap_smul (fun _ _ => rfl)
  have : IsScalarTower R₀ P B₀ := .of_algebraMap_eq' (by ext r; exact (f.commutes r).symm)
  have : IsScalarTower R₀ P M₀ := .of_algebraMap_smul (fun r m => by
    change f (algebraMap R₀ P r) • m = r • m
    rw [f.commutes, algebraMap_smul])
  have : Module.Finite P B₀ := RingHom.Finite.of_surjective f.toRingHom hf
  have : Module.Finite P M₀ := Module.Finite.trans B₀ M₀
  let : Module Pᵐᵒᵖ M₀ := Module.compHom M₀ (RingEquiv.toOpposite P).symm.toRingHom
  have : IsCentralScalar P M₀ := ⟨fun _ _ => rfl⟩
  have : IsScalarTower R₀ Pᵐᵒᵖ M₀ := .of_algebraMap_smul (fun r m => by
    change (algebraMap R₀ P r) • m = r • m
    exact IsScalarTower.algebraMap_smul P r m)
  let E := TrivSqZeroExt P M₀
  have : Module.Finite P E := inferInstanceAs (Module.Finite P (P × M₀))
  have : Algebra.FiniteType R₀ E := Algebra.FiniteType.trans (R := R₀) (S := P) (A := E) inferInstance inferInstance
  have : Algebra.FinitePresentation R₀ E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat R (R ⊗[R₀] P) := inferInstance
  have : Module.Flat R ((R ⊗[R₀] P) × (R ⊗[R₀] M₀)) := flat_prod
  have : Module.Flat R (R ⊗[R₀] E) :=
    Module.Flat.of_linearEquiv (TensorProduct.prodRight R₀ R R P M₀)
  obtain ⟨R₁, hfg, hs, hflat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_tensorProduct (R₀ := R₀) (B₀ := E) s
  refine ⟨R₁, hfg, hs, ?_⟩
  have := hflat
  let i : M₀ →ₗ[R₀] E := (TrivSqZeroExt.inrHom P M₀).restrictScalars R₀
  let r : E →ₗ[R₀] M₀ := (TrivSqZeroExt.sndHom P M₀).restrictScalars R₀
  exact Module.Flat.of_retract
    (TensorProduct.AlgebraTensorModule.lTensor R₁ R₁ i)
    (TensorProduct.AlgebraTensorModule.lTensor R₁ R₁ r) (by
      ext
      rfl)

/-- Once a scalar extension of a module is flat, every larger subalgebra also works. -/
lemma flat_module_baseChange_of_le {R₀ R M₀ : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [AddCommGroup M₀] [Module R₀ M₀]
    {S T : Subalgebra R₀ R} (h : S ≤ T) [Module.Flat S (S ⊗[R₀] M₀)] :
    Module.Flat T (T ⊗[R₀] M₀) := by
  let : Algebra S T := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower R₀ S T := .of_algebraMap_eq' rfl
  have : Module.Flat T (T ⊗[S] (S ⊗[R₀] M₀)) := inferInstance
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ S T T M₀).symm

/-- A finite family of finite modules can be made flat at one common finite subalgebra. -/
lemma exists_fg_subalgebra_forall_flat_module
    {R₀ R ι : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    [IsNoetherianRing R₀] [Finite ι]
    (B₀ : ι → Type*) (M₀ : ι → Type*)
    [∀ i, CommRing (B₀ i)] [∀ i, Algebra R₀ (B₀ i)] [∀ i, Algebra.FiniteType R₀ (B₀ i)]
    [∀ i, AddCommGroup (M₀ i)] [∀ i, Module R₀ (M₀ i)] [∀ i, Module (B₀ i) (M₀ i)]
    [∀ i, IsScalarTower R₀ (B₀ i) (M₀ i)] [∀ i, Module.Finite (B₀ i) (M₀ i)]
    [∀ i, Module.Flat R (R ⊗[R₀] M₀ i)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧
      ∀ i, Module.Flat R₁ (R₁ ⊗[R₀] M₀ i) := by
  classical
  let := Fintype.ofFinite ι
  have hcommon (t : Finset ι) :
      ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧
        ∀ i ∈ t, Module.Flat R₁ (R₁ ⊗[R₀] M₀ i) := by
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨Algebra.adjoin R₀ (s : Set R), Subalgebra.fg_adjoin_finset s,
        Algebra.subset_adjoin, fun _ hi => (Finset.notMem_empty _ hi).elim⟩
    | @insert i t hi ih =>
      obtain ⟨T, hTfg, hsT, hT⟩ := ih
      obtain ⟨S, hSfg, -, hS⟩ := exists_fg_subalgebra_flat_module (R₀ := R₀) (B₀ := B₀ i) (M₀ := M₀ i) s
      refine ⟨S ⊔ T, hSfg.sup hTfg, fun r hr => (le_sup_right : T ≤ S ⊔ T) (hsT hr), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have := hS
        exact flat_module_baseChange_of_le (M₀ := M₀ j) le_sup_left
      · have := hT j hj
        exact flat_module_baseChange_of_le (M₀ := M₀ j) le_sup_right
  obtain ⟨T, hfg, hs, h⟩ := hcommon Finset.univ
  exact ⟨T, hfg, hs, fun i => h i (Finset.mem_univ _)⟩

/-- Finite module flatness descends from an arbitrary scalar extension. -/
theorem finiteTypeModuleFlatnessDescent :
    FiniteTypeModuleFlatnessDescentStatement.{uR₀, uR, uB₀, uM₀} := by
  intro R₀ R B₀ M₀
  intros
  apply exists_fg_subalgebra_flat_module (B₀ := B₀)

end Langlands.Algebra
