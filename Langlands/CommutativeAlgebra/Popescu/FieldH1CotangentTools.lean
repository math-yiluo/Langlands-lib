import Langlands.MathlibBase

/-! # `H₁` of field extensions: vanishing over perfect fields and naturality of `δ` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace FieldH1

open MvPolynomial

open scoped TensorProduct

/-- The default hom between the canonical presentations `K[L] → K[M]` is renaming along
`L → M`. -/
theorem defaultHom_self_toAlgHom {K L M : Type*} [CommRing K] [CommRing L] [CommRing M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] (g : MvPolynomial L K) :
    (Algebra.Generators.defaultHom (Algebra.Generators.self K L)
      (Algebra.Generators.self K M)).toAlgHom g = rename (algebraMap L M) g := by
  have : (Algebra.Generators.defaultHom (Algebra.Generators.self K L)
      (Algebra.Generators.self K M)).toAlgHom = rename (algebraMap L M) := by
    apply MvPolynomial.algHom_ext
    intro l
    rw [Algebra.Generators.Hom.toAlgHom_X, rename_X]
    rfl
  rw [this]

/-- **`H₁(L_{L/F}) = 0` for every field `L` over a perfect field `F`.** Every element of `H₁`
involves finitely many variables, hence comes from `H₁(L_{L'/F})` for a finitely generated
subextension `L'`, which vanishes because `L'/F` is formally smooth (Mathlib). -/
theorem subsingleton_h1Cotangent_of_perfectField (F L : Type*) [Field F] [Field L]
    [Algebra F L] [PerfectField F] : Subsingleton (Algebra.H1Cotangent F L) := by
  classical
  suffices h : ∀ x : Algebra.H1Cotangent F L, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨xv, hx⟩ := x
  obtain ⟨⟨f, hf⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective xv
  let L' : IntermediateField F L := IntermediateField.adjoin F ((f : MvPolynomial L F).vars : Set L)
  have : Algebra.EssFiniteType F L' :=
    IntermediateField.essFiniteType_iff.mpr ⟨(f : MvPolynomial L F).vars, rfl⟩
  have hsub : Subsingleton (Algebra.H1Cotangent F L') := inferInstance
  have hvars : ((f : MvPolynomial L F).vars : Set L) ⊆ Set.range (algebraMap L' L) :=
    fun l hl => ⟨⟨l, IntermediateField.subset_adjoin F _ hl⟩, rfl⟩
  obtain ⟨f', hf'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (f : MvPolynomial L F) (algebraMap L' L) (algebraMap L' L).injective hvars
  have hfker : aeval (fun l : L => l) (f : MvPolynomial L F) = 0 := hf
  have h0 : aeval (fun l : L' => l) f' = 0 := by
    apply (algebraMap L' L).injective
    rw [map_zero, ← hfker, ← hf', MvPolynomial.aeval_rename,
      ← MvPolynomial.aeval_algebraMap_apply]
    rfl
  have hf'ker : f' ∈ (Algebra.Generators.self F L').toExtension.ker := h0
  have hx' : (Algebra.Extension.Cotangent.mk ⟨f', hf'ker⟩ :
      (Algebra.Generators.self F L').toExtension.Cotangent) ∈
      LinearMap.ker (Algebra.Generators.self F L').toExtension.cotangentComplex := by
    rw [LinearMap.mem_ker, Algebra.Extension.cotangentComplex_mk]
    apply (Algebra.Generators.self F L').cotangentSpaceBasis.repr.injective
    ext j : 1
    rw [Algebra.Generators.cotangentSpaceBasis_repr_one_tmul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    have h1 := congrArg (fun z => (Algebra.Generators.self F L).cotangentSpaceBasis.repr z
      (algebraMap L' L j)) (LinearMap.mem_ker.mp hx)
    simp only [Algebra.Extension.cotangentComplex_mk,
      Algebra.Generators.cotangentSpaceBasis_repr_one_tmul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [← hf', MvPolynomial.pderiv_rename (algebraMap L' L).injective,
      MvPolynomial.aeval_rename] at h1
    apply (algebraMap L' L).injective
    rw [map_zero, ← h1, ← MvPolynomial.aeval_algebraMap_apply]
    rfl
  let x' : Algebra.H1Cotangent F L' :=
    (⟨_, hx'⟩ : LinearMap.ker (Algebra.Generators.self F L').toExtension.cotangentComplex)
  have hmap : Algebra.H1Cotangent.map F F L' L x' =
      (⟨Algebra.Extension.Cotangent.mk ⟨f, hf⟩, hx⟩ :
        LinearMap.ker (Algebra.Generators.self F L).toExtension.cotangentComplex) := by
    apply Algebra.Extension.h1Cotangentι_ext
    change Algebra.Extension.Cotangent.map _ (Algebra.Extension.Cotangent.mk
      (P := (Algebra.Generators.self F L').toExtension) ⟨f', hf'ker⟩) = _
    rw [Algebra.Extension.Cotangent.map_mk]
    congr 2
    rw [Algebra.Generators.Hom.toExtensionHom_toAlgHom_apply, defaultHom_self_toAlgHom]
    exact hf'
  change _ = (0 : Algebra.H1Cotangent F L)
  rw [← hmap, Subsingleton.elim x' 0, map_zero]

/-- Naturality of Mathlib's auxiliary map `δAux` in the top ring. -/
theorem δAux_rename {R S T T' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing T']
    [Algebra R S] [Algebra S T] [Algebra S T'] [Algebra T T'] [IsScalarTower S T T']
    [Algebra R T] [Algebra R T'] [IsScalarTower R S T] [IsScalarTower R S T']
    (g : MvPolynomial T S) :
    Algebra.Generators.H1Cotangent.δAux R (Algebra.Generators.self S T')
        (rename (algebraMap T T') g) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange S T T' T' Ω[S⁄R]
        ((1 : T') ⊗ₜ[T] Algebra.Generators.H1Cotangent.δAux R (Algebra.Generators.self S T) g) := by
  induction g using MvPolynomial.induction_on with
  | C s =>
    rw [rename_C, Algebra.Generators.H1Cotangent.δAux_C, Algebra.Generators.H1Cotangent.δAux_C,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, TensorProduct.tmul_add, map_add]
  | mul_X p n hp =>
    rw [map_mul, rename_X, Algebra.Generators.H1Cotangent.δAux_mul,
      Algebra.Generators.H1Cotangent.δAux_X, smul_zero, zero_add, hp,
      Algebra.Generators.H1Cotangent.δAux_mul, Algebra.Generators.H1Cotangent.δAux_X, smul_zero,
      zero_add]
    simp only [← @IsScalarTower.algebraMap_smul (Algebra.Generators.self S T).Ring T,
      ← @IsScalarTower.algebraMap_smul (Algebra.Generators.self S T').Ring T',
      Algebra.Generators.algebraMap_apply, aeval_X, Algebra.Generators.self_val, id_eq]
    rw [TensorProduct.tmul_smul, ← algebraMap_smul T' n, map_smul]

end FieldH1

end Langlands.CommutativeAlgebra.Popescu
