import Langlands.Global.Arithmetic.ClassFieldStatement
import Langlands.ClassFieldTheory.Global.Artin.FiniteArtinNormalization
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness
import Langlands.ClassFieldTheory.Global.Artin.OpenSubgroupFiniteIndex
import Langlands.ClassFieldTheory.Global.Artin.ClassField
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Proof of the finite abelian class field statement

This file proves `Langlands.Global.FiniteAbelianClassFieldStatement` and each of its five
clauses, from the bridge modules of `Langlands/ClassFieldTheory/Global/Artin/` onto the NYLL
library.

* Artin reciprocity: the arithmetic Artin map `arithmeticFiniteArtin K L` is a continuous
  surjection with the arithmetic normalization, and any continuous normalized map equals it.
* Open subgroups of `IdeleClasses K` have finite index.
* Existence: `classField K H` with its arithmetic Artin map.
* Rigidity: normalized maps are the arithmetic Artin maps, and equal kernels give equal
  subfields of `AlgebraicClosure K`.
* Hecke characters of finite order: the kernel is open; the character factors through the Artin
  map of the class field of its kernel.
-/

noncomputable section

universe u v

namespace Langlands.Global

open Langlands.ClassFieldTheory.Global.Artin

/-- Finite abelian Artin reciprocity for number fields, with uniqueness. -/
theorem finiteAbelianArtinReciprocity : FiniteAbelianArtinReciprocityStatement.{u, v} := by
  intro K _ _ L _ _ _ _ hcomm
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have : IsAbelianGalois K L := { toIsMulCommutative := IsMulCommutative.of_comm hcomm }
  refine ⟨arithmeticFiniteArtinBot K L,
    ⟨arithmeticFiniteArtin_surjective K L, arithmeticFiniteArtin_hasArithmeticArtinNormalization⟩,
    fun ρ hρ => ?_⟩
  exact eq_of_hasArithmeticArtinNormalization ρ (arithmeticFiniteArtinBot K L) hρ.2
    arithmeticFiniteArtin_hasArithmeticArtinNormalization

/-- Open subgroups of the idèle class group of a number field have finite index. -/
theorem openIdeleClassSubgroupFiniteIndex : OpenIdeleClassSubgroupFiniteIndexStatement.{u} :=
  fun K _ _ H => openSubgroup_finiteIndex K H

/-- Every open subgroup of finite index is the kernel of the normalized Artin map of a finite
abelian subextension of the algebraic closure: its class field. -/
theorem finiteAbelianClassFieldExistence : FiniteAbelianClassFieldExistenceStatement.{u} := by
  intro K _ _ H _
  let := NumberField.of_module_finite K (classField K H)
  refine ⟨classField K H, inferInstance, inferInstance, fun σ τ => mul_comm' σ τ,
    arithmeticFiniteArtinBot K (classField K H), arithmeticFiniteArtin_surjective K _,
    arithmeticFiniteArtin_hasArithmeticArtinNormalization, ?_⟩
  exact arithmeticFiniteArtin_classField_ker K H

/-- Finite abelian subextensions of the algebraic closure whose normalized Artin maps have the
same kernel are equal. -/
theorem finiteAbelianClassFieldKernelRigidity :
    FiniteAbelianClassFieldKernelRigidityStatement.{u} := by
  intro K _ _ L E _ _ _ _ hL hE ρ τ _ _ hρ hτ hker
  let := NumberField.of_module_finite K L
  let := NumberField.of_module_finite K E
  have : IsAbelianGalois K L := { toIsMulCommutative := IsMulCommutative.of_comm hL }
  have : IsAbelianGalois K E := { toIsMulCommutative := IsMulCommutative.of_comm hE }
  have hρeq : ρ = arithmeticFiniteArtinBot K L :=
    eq_of_hasArithmeticArtinNormalization ρ _ hρ
      arithmeticFiniteArtin_hasArithmeticArtinNormalization
  have hτeq : τ = arithmeticFiniteArtinBot K E :=
    eq_of_hasArithmeticArtinNormalization τ _ hτ
      arithmeticFiniteArtin_hasArithmeticArtinNormalization
  have hker' : (arithmeticFiniteArtin K L).ker = (arithmeticFiniteArtin K E).ker := by
    rw [hρeq, hτeq] at hker
    exact hker
  exact eq_of_arithmeticFiniteArtin_ker_eq L E hker'

/-- The kernel of a Hecke character of finite order is open. -/
theorem isOpen_ker_of_hasFiniteOrder {K : Type u} [Field K] [NumberField K]
    (χ : HeckeCharacter K) (hχ : χ.HasFiniteOrder) :
    IsOpen (χ.toMonoidHom.ker : Set (IdeleClasses K)) := by
  obtain ⟨n, hn, hχn⟩ := hχ
  have : NeZero n := ⟨hn.ne'⟩
  have hpow : ∀ x, χ x ^ n = 1 := fun x => by
    have h := DFunLike.congr_fun hχn x
    simpa using h
  let S : Set ℂˣ := (rootsOfUnity n ℂ : Set ℂˣ) \ {1}
  have hfin : (rootsOfUnity n ℂ : Set ℂˣ).Finite :=
    @Set.toFinite _ _ (inferInstanceAs (Finite (rootsOfUnity n ℂ)))
  have hS : IsOpen Sᶜ := (hfin.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hker : (χ.toMonoidHom.ker : Set (IdeleClasses K)) = χ ⁻¹' Sᶜ := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, S,
      Set.mem_sdiff, SetLike.mem_coe, mem_rootsOfUnity, hpow x, Set.mem_singleton_iff, true_and,
      not_not]
    rfl
  rw [hker]
  exact hS.preimage χ.continuous

/-- A Hecke character whose kernel is an open subgroup `H` is a faithful character of the Galois
group of the class field of `H`, composed with the arithmetic Artin map. -/
theorem exists_injective_comp_arithmeticFiniteArtin {K : Type u} [Field K] [NumberField K]
    (χ : HeckeCharacter K) (H : OpenSubgroup (IdeleClasses K))
    (hH : H.toSubgroup = χ.toMonoidHom.ker) :
    letI := NumberField.of_module_finite K (classField K H)
    letI : TopologicalSpace (classField K H ≃ₐ[K] classField K H) := ⊥
    ∃ θ : (classField K H ≃ₐ[K] classField K H) →ₜ* ℂˣ,
      Function.Injective θ ∧ ∀ x, θ (arithmeticFiniteArtinBot K (classField K H) x) = χ x := by
  let := NumberField.of_module_finite K (classField K H)
  let : TopologicalSpace (classField K H ≃ₐ[K] classField K H) := ⊥
  have : DiscreteTopology (classField K H ≃ₐ[K] classField K H) := ⟨rfl⟩
  have hρs : Function.Surjective (arithmeticFiniteArtin K (classField K H)) :=
    arithmeticFiniteArtin_surjective K _
  have hker : (arithmeticFiniteArtin K (classField K H)).ker = χ.toMonoidHom.ker :=
    (arithmeticFiniteArtin_classField_ker K H).trans hH
  let θ₀ : (classField K H ≃ₐ[K] classField K H) →* ℂˣ :=
    (arithmeticFiniteArtin K (classField K H)).liftOfRightInverse (Function.surjInv hρs)
      (Function.rightInverse_surjInv hρs) ⟨χ.toMonoidHom, hker.le⟩
  have hθ₀ : ∀ x, θ₀ (arithmeticFiniteArtin K (classField K H) x) = χ x := fun x =>
    (arithmeticFiniteArtin K (classField K H)).liftOfRightInverse_comp_apply _ _
      ⟨χ.toMonoidHom, hker.le⟩ x
  refine ⟨{ toMonoidHom := θ₀, continuous_toFun := continuous_of_discreteTopology }, ?_, hθ₀⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨x, rfl⟩ := hρs y
  have hx : x ∈ χ.toMonoidHom.ker := (hθ₀ x).symm.trans hy
  rw [← hker] at hx
  exact hx

/-- A Hecke character of finite order is a faithful character of a finite abelian Galois group,
pulled back by the normalized Artin map. -/
theorem finiteOrderHeckeArtinRealization : FiniteOrderHeckeArtinRealizationStatement.{u} := by
  intro K _ _ χ hχ
  let H : OpenSubgroup (IdeleClasses K) := ⟨χ.toMonoidHom.ker, isOpen_ker_of_hasFiniteOrder χ hχ⟩
  obtain ⟨θ, hθ, hθρ⟩ := exists_injective_comp_arithmeticFiniteArtin χ H rfl
  let := NumberField.of_module_finite K (classField K H)
  exact ⟨classField K H, inferInstance, inferInstance, fun σ τ => mul_comm' σ τ,
    arithmeticFiniteArtinBot K (classField K H), θ, arithmeticFiniteArtin_surjective K _, hθ,
    arithmeticFiniteArtin_hasArithmeticArtinNormalization, hθρ⟩

/-- Proof of `FiniteAbelianClassFieldStatement`: finite abelian Artin reciprocity, finiteness
of the index of open idèle-class subgroups, existence and rigidity of class fields, and the
realization of Hecke characters of finite order. -/
theorem finiteAbelianClassField : FiniteAbelianClassFieldStatement.{u, v} :=
  ⟨finiteAbelianArtinReciprocity, openIdeleClassSubgroupFiniteIndex,
    finiteAbelianClassFieldExistence, finiteAbelianClassFieldKernelRigidity,
    finiteOrderHeckeArtinRealization⟩

end Langlands.Global
