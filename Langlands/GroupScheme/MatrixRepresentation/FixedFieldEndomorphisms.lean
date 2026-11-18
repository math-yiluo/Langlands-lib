import Langlands.GroupScheme.MatrixRepresentation.IrreducibleCharacterLines
import Langlands.GroupScheme.MatrixRepresentation.CharacterIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.GaloisWeightScalars
import Langlands.GroupScheme.MatrixRepresentation.IrreducibleOrbitRealization
import Langlands.LinearAlgebra.GaloisOrbitScalars

/-! # Fixed-field algebra from normalized geometric character lines -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation.FixedFieldEndomorphisms

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Linear maps are determined by a spanning family of conjugate lines. -/
theorem linearMap_ext_of_orbitLines (v : n → K)
    (htop : orbitLineSubspace (k := k) v = ⊤)
    {F G : (n → K) →ₗ[K] (n → K)}
    (h : ∀ σ : K ≃ₐ[k] K, F (fun i => σ (v i)) = G (fun i => σ (v i))) : F = G := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← htop]
  apply iSup_le
  intro σ
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact sub_eq_zero.mpr (h σ)

/-- Matrices over the original field are determined by their conjugate-line actions. -/
theorem matrix_ext_of_orbitLines (v : n → K)
    (htop : orbitLineSubspace (k := k) v = ⊤)
    {C D : Matrix n n k}
    (h : ∀ σ : K ≃ₐ[k] K, C.map (algebraMap k K) *ᵥ (fun i => σ (v i)) =
      D.map (algebraMap k K) *ᵥ (fun i => σ (v i))) : C = D := by
  apply Matrix.map_injective (algebraMap k K).injective
  apply Matrix.toLin'.injective
  exact linearMap_ext_of_orbitLines v htop h

omit [DecidableEq n] in
/-- Original-field matrices commute with coefficientwise automorphisms. -/
theorem mulVec_conjugate (C : Matrix n n k) (σ : K ≃ₐ[k] K) (w : n → K) :
    C.map (algebraMap k K) *ᵥ (fun i => σ (w i)) =
      fun i => σ ((C.map (algebraMap k K) *ᵥ w) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, σ.commutes]

variable (H : Subgroup (K ≃ₐ[k] K)) (v : n → K)
  (htop : orbitLineSubspace (k := k) v = ⊤)
  (F : IntermediateField.fixedField H → Matrix n n k)
  (hF : ∀ (a : IntermediateField.fixedField H) (σ : K ≃ₐ[k] K),
    (F a).map (algebraMap k K) *ᵥ (fun i => σ (v i)) =
      σ (a : K) • (fun i => σ (v i)))

/-- Specified conjugate-line scalar actions force a field-to-matrix algebra map. -/
def orbitActionAlgHom : IntermediateField.fixedField H →ₐ[k] Matrix n n k where
  toFun := F
  map_zero' := by
    apply matrix_ext_of_orbitLines v htop
    intro σ
    rw [hF]
    simp only [ZeroMemClass.coe_zero, map_zero, zero_smul,
      Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
  map_one' := by
    apply matrix_ext_of_orbitLines v htop
    intro σ
    rw [hF]
    simp only [OneMemClass.coe_one, map_one, one_smul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  map_add' a b := by
    apply matrix_ext_of_orbitLines v htop
    intro σ
    rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec, hF, hF, hF]
    change σ ((a : K) + (b : K)) • (fun i => σ (v i)) = _
    rw [map_add, add_smul]
  map_mul' a b := by
    apply matrix_ext_of_orbitLines v htop
    intro σ
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hF (a * b) σ, hF b σ,
      Matrix.mulVec_smul, hF a σ]
    change σ ((a : K) * (b : K)) • (fun i => σ (v i)) = _
    rw [map_mul, smul_smul, mul_comm (σ (a : K)) (σ (b : K))]
  commutes' c := by
    apply matrix_ext_of_orbitLines v htop
    intro σ
    rw [hF]
    change σ (algebraMap k K c) • (fun i => σ (v i)) =
      (algebraMap k (Matrix n n k) c).map (algebraMap k K) *ᵥ (fun i => σ (v i))
    rw [σ.commutes, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero _)]
    funext i
    simp [Matrix.mulVec_diagonal]

variable {H v htop F hF}

/-- The field map is injective when a coordinate index exists. -/
theorem orbitActionAlgHom_injective (j : n) :
    Function.Injective (orbitActionAlgHom H v htop F hF) := by
  let : Nonempty n := ⟨j⟩
  exact (orbitActionAlgHom H v htop F hF).injective

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

local notation "G₁" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- A scalar-action construction exhausts the actual endomorphisms when a
normalized stabilizer-fixed character line and its conjugates span. -/
theorem orbitActionAlgHom_range (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G₁) (j : n)
    (hvj : v j = 1)
    (hfixed : ∀ σ ∈ H, (fun i => σ (v i)) = v)
    (hline : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ =
      Submodule.span K ({v} : Set (n → K)))
    (hendo : ∀ a, ρ.Intertwines ρ (F a)) :
    Set.range (orbitActionAlgHom H v htop F hF) = {C | ρ.Intertwines ρ C} := by
  ext C
  constructor
  · rintro ⟨a, rfl⟩
    exact hendo a
  · intro hC
    have hvχ : v ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ := by
      rw [hline]
      exact Submodule.mem_span_singleton_self v
    have hCv := (hC.baseChange (K := K)).mem_characterSpace hvχ
    rw [hline] at hCv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hCv
    have hact (σ : K ≃ₐ[k] K) : C.map (algebraMap k K) *ᵥ (fun i => σ (v i)) =
        σ a • (fun i => σ (v i)) := by
      rw [mulVec_conjugate, ← ha]
      funext i
      exact map_mul σ a (v i)
    have haH : a ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have he := hact σ
      rw [hfixed σ hσ, ← ha] at he
      have hj := congrFun he j
      simpa only [Pi.smul_apply, smul_eq_mul, hvj, mul_one] using hj.symm
    let aH : IntermediateField.fixedField H := ⟨a, haH⟩
    refine ⟨aH, ?_⟩
    apply matrix_ext_of_orbitLines v htop
    intro σ
    exact (hF aH σ).trans (hact σ).symm

end Langlands.GroupScheme.MatrixRepresentation.FixedFieldEndomorphisms

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.LinearAlgebra.GaloisOrbitScalars FixedFieldEndomorphisms

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

local notation "G₁" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

/-- Spanning character spaces in one Galois orbit identify the actual
endomorphism algebra of an original irreducible representation with the stabilizer fixed field. -/
theorem exists_fixedField_endomorphismAlgHom_of_weightOrbit [IsGalois k K]
    (ρ : MatrixRepresentation G n) (hρ : ρ.IsIrreducible)
    (hspan : (⨆ ψ : rationalCharacters G₁,
      (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ) = ⊤)
    (χ : rationalCharacters G₁)
    (hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥)
    (horbit : {ψ | (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ ≠ ⊥} =
      Set.range (fun σ : K ≃ₐ[k] K => rationalCharacters.galoisRepresentation k K G σ χ))
    (H : Subgroup (K ≃ₐ[k] K))
    (hH : ∀ σ : K ≃ₐ[k] K,
      σ ∈ H ↔ rationalCharacters.galoisRepresentation k K G σ χ = χ) :
    ∃ f : IntermediateField.fixedField H →ₐ[k] Matrix n n k,
      Function.Injective f ∧ Set.range f = {C | ρ.Intertwines ρ C} := by
  classical
  obtain ⟨v, j, hvj, hfixed, hline, htop⟩ :=
    exists_normalized_galois_characterLine ρ hρ χ hχ H hH
  have hvχ : v ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ := by
    rw [hline]
    exact Submodule.mem_span_singleton_self v
  let r := rationalCharacters.galoisRepresentation k K G
  have hex (a : IntermediateField.fixedField H) :
      ∃ D : Matrix n n k, ρ.Intertwines ρ D ∧
        ∀ σ : K ≃ₐ[k] K, D.map (algebraMap k K) *ᵥ (fun i => σ (v i)) =
          σ (a : K) • (fun i => σ (v i)) := by
    let f := orbitValue r χ (a : K)
    have hf (σ : K ≃ₐ[k] K) (ψ : rationalCharacters G₁)
        (hψ : (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ ≠ ⊥) :
        f (rationalCharacters.galoisRepresentation k K G σ ψ) = σ (f ψ) := by
      apply orbitValue_equivariant r χ H hH a σ ψ
      rw [← horbit]
      exact hψ
    obtain ⟨D, hD, hact⟩ := exists_intertwiner_with_weight_scalars ρ hspan f hf
    refine ⟨D, hD, ?_⟩
    intro σ
    have hh := hact (r σ χ) (fun i => σ (v i))
      (conjugate_mem_characterSpace_baseChange ρ σ χ hvχ)
    change D.map (algebraMap k K) *ᵥ (fun i => σ (v i)) =
      orbitValue r χ (a : K) (r σ χ) • (fun i => σ (v i)) at hh
    rwa [orbitValue_apply r χ H hH a σ] at hh
  choose F hFendo hFact using hex
  refine ⟨orbitActionAlgHom H v htop F hFact, orbitActionAlgHom_injective j, ?_⟩
  exact orbitActionAlgHom_range ρ χ j hvj hfixed hline hFendo

/-- The exact fixed-field endomorphism conclusion for every irreducible actual
representation of a multiplicative-type group over any separable closure. -/
theorem exists_fixedField_endomorphismAlgHom_of_isMultiplicativeType
    [IsSepClosure k K] (ρ : MatrixRepresentation G n) (hG : IsMultiplicativeType G)
    (hρ : ρ.IsIrreducible) (χ : rationalCharacters G₁)
    (hχ : (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥)
    (H : Subgroup (K ≃ₐ[k] K))
    (hH : ∀ σ : K ≃ₐ[k] K,
      σ ∈ H ↔ rationalCharacters.galoisRepresentation k K G σ χ = χ) :
    ∃ f : IntermediateField.fixedField H →ₐ[k] Matrix n n k,
      Function.Injective f ∧ Set.range f = {C | ρ.Intertwines ρ C} := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  have hGK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
    k K G hG
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hGK
  let := hΛ
  let := hfg
  have hspan := iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e
    (ρ.baseChange (algebraBaseMap k K))
  obtain ⟨ψ, hweights⟩ :=
    exists_weights_eq_galoisOrbit_of_isMultiplicativeType (K := K) ρ hG hρ
  have hmem : χ ∈ Set.range (fun σ : K ≃ₐ[k] K =>
      rationalCharacters.galoisRepresentation k K G σ ψ) := by
    rw [← hweights]
    exact hχ
  have horbit := hweights.trans (galoisOrbit_range_eq_of_mem χ ψ hmem).symm
  exact exists_fixedField_endomorphismAlgHom_of_weightOrbit ρ hρ hspan χ hχ horbit H hH

end Langlands.GroupScheme.MatrixRepresentation
