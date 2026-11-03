import Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGlue
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.Algebra.GradedHopf.Basic

/-! # Integer graded coordinate algebras from actual torus actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusGradedHopf

open TorusUnipotence CoordinateWeights

section CharacterCoordinates

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual coordinate character grading can be coarsened so that its degree-zero
augmentation part has zero image in the cotangent space. -/
theorem exists_coordinate_grading [LocallyOfFiniteType H.X.hom]
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp H)
    (hb : RelativeRoot.actionWeightSpace b 0 = ⊥) :
    ∃ (𝒜 : ℤ → Submodule k (CharacterUnits.Coord H)) (_ : GradedAlgebra 𝒜),
      (∀ n, ∀ a ∈ 𝒜 n, coordComul H a ∈
        ⨆ i, Submodule.map₂ (TensorProduct.mk k _ _) (𝒜 i) (𝒜 (n - i))) ∧
      (∀ n ≠ 0, ∀ a ∈ 𝒜 n, coordCounit H a = 0) ∧
      ∀ a ∈ 𝒜 0, coordCounit H a = 0 →
        a ∈ RingHom.ker (coordCounit H) ^ 2 := by
  classical
  have hsupp : (0 : characterLattice S) ∉ cotangentSupport b := by
    rw [cotangentLieSupport k H inferInstance inferInstance S hS b]
    rintro ⟨X, hX, hXw, -⟩
    rw [hb] at hXw
    exact hX ((Submodule.mem_bot k).1 hXw)
  let W := CoordinateWeights.weightSpace b
  have hW : DirectSum.IsInternal W :=
    (coordinateWeightDecomposition k H inferInstance S hS b).1
  have h1 : (1 : CharacterUnits.Coord H) ∈ W 0 := one_mem_weightSpace_zero b
  have hmul : ∀ χ ψ, W χ * W ψ ≤ W (χ + ψ) :=
    fun χ ψ => Submodule.mul_le.2 fun f hf g hg => mul_mem_weightSpace b hf hg
  have hε : ∀ χ, χ ≠ 0 → ∀ f ∈ W χ, coordCounit H f = 0 :=
    fun χ hχ f hf => coordCounit_eq_zero b hS hχ hf
  obtain ⟨ν, hν⟩ := hS.exists_pairings_ne_zero (cotangentSupport b)
    (finite_cotangentSupport hS b) fun χ hχ h => hsupp (h ▸ hχ)
  let w : characterLattice S →+ ℤ := ((latticePairing S).flip ν).toAddMonoidHom
  have hsq : ∀ χ, w χ = 0 → ∀ f ∈ W χ, coordCounit H f = 0 →
      f ∈ RingHom.ker (coordCounit H) ^ 2 :=
    fun χ hχ f hf hfε =>
      mem_sq_of_not_mem_cotangentSupport hS b (fun h => hν χ h hχ) hf hfε
  refine ⟨regrade W w,
    gradedAlgebraRegrade hW.submodule_iSupIndep hW.submodule_iSup_eq_top h1 hmul,
    ?_, ?_, ?_⟩
  · exact fun n a ha => regrade_comul (Δ := (coordComul H).toLinearMap)
      (fun _ _ hf => coordComul_mem_iSup b hS hf) n ha
  · exact fun n hn a ha => regrade_augmentation hε n hn ha
  · exact fun a ha haε => regrade_zero_mem_sq h1 hε hsq ha haε

end CharacterCoordinates

section Transport

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [Bialgebra k A]
  [Algebra k B]

/-- Pull a family of subspaces back along an algebra equivalence. -/
def pullGrading (e : A ≃ₐ[k] B) (ℬ : ℤ → Submodule k B) (n : ℤ) : Submodule k A :=
  (ℬ n).map e.symm.toLinearMap

theorem mem_pullGrading (e : A ≃ₐ[k] B) (ℬ : ℤ → Submodule k B) {n : ℤ} {a : A} :
    a ∈ pullGrading e ℬ n ↔ e a ∈ ℬ n := by
  exact Submodule.mem_map_equiv (ℬ n) (e := e.symm.toLinearEquiv)

/-- Algebra equivalences transport graded algebra structures. -/
@[instance_reducible]
def gradedAlgebraPull (e : A ≃ₐ[k] B) (ℬ : ℤ → Submodule k B) [GradedAlgebra ℬ] :
    GradedAlgebra (pullGrading e ℬ) := by
  have hℬ := DirectSum.Decomposition.isInternal ℬ
  have hi : DirectSum.IsInternal (pullGrading e ℬ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (e.symm.toLinearMap.iSupIndep_map e.symm.injective hℬ.submodule_iSupIndep)
      (by
        change (⨆ n, (ℬ n).map e.symm.toLinearMap) = ⊤
        rw [← Submodule.map_iSup, hℬ.submodule_iSup_eq_top, Submodule.map_top]
        exact LinearMap.range_eq_top.2 e.symm.surjective)
  exact
    { toDecomposition := hi.chooseDecomposition
      toGradedMonoid :=
        { one_mem := (mem_pullGrading e ℬ).2 (by
            rw [map_one]
            exact SetLike.GradedOne.one_mem)
          mul_mem := fun i j a b ha hb => (mem_pullGrading e ℬ).2 (by
            rw [map_mul]
            exact SetLike.mul_mem_graded
              ((mem_pullGrading e ℬ).1 ha) ((mem_pullGrading e ℬ).1 hb)) } }

/-- The additive tensor grading used by the coordinate-weight API lies in the
total-degree tensor grading used by `GradedHopf`. -/
theorem iSup_map₂_le_tensorGrade (ℬ : ℤ → Submodule k B) (n : ℤ) :
    (⨆ i, Submodule.map₂ (TensorProduct.mk k B B) (ℬ i) (ℬ (n - i))) ≤
      Langlands.Algebra.GradedHopf.tensorGrade ℬ ℬ n := by
  refine iSup_le fun i => Submodule.map₂_le.2 fun a ha b hb => ?_
  change a ⊗ₜ[k] b ∈ _
  simpa only [add_sub_cancel] using
    Langlands.Algebra.GradedHopf.tmul_mem_tensorGrade ℬ ℬ ha hb

/-- Transport the comultiplication, counit and degree-zero square condition along
an algebra equivalence preserving the two coordinate structure maps. -/
theorem exists_grading_of_coordinate_equiv
    (e : A ≃ₐ[k] B) (Δ : B →ₐ[k] B ⊗[k] B) (ε : B →ₐ[k] k)
    (hΔ : ∀ a, Algebra.TensorProduct.map e.toAlgHom e.toAlgHom
      (Bialgebra.comulAlgHom k A a) = Δ (e a))
    (hε : ∀ a, ε (e a) = Bialgebra.counitAlgHom k A a)
    (hB : ∃ (ℬ : ℤ → Submodule k B) (_ : GradedAlgebra ℬ),
      (∀ n, ∀ b ∈ ℬ n, Δ b ∈
        ⨆ i, Submodule.map₂ (TensorProduct.mk k B B) (ℬ i) (ℬ (n - i))) ∧
      (∀ n ≠ 0, ∀ b ∈ ℬ n, ε b = 0) ∧
      ∀ b ∈ ℬ 0, ε b = 0 → b ∈ RingHom.ker ε ^ 2) :
    ∃ (𝒜 : ℤ → Submodule k A) (_ : GradedAlgebra 𝒜),
      Langlands.Algebra.GradedHopf.IsGradedBialgebra 𝒜 ∧
      ∀ a ∈ 𝒜 0, Bialgebra.counitAlgHom k A a = 0 →
        a ∈ RingHom.ker (Bialgebra.counitAlgHom k A) ^ 2 := by
  classical
  obtain ⟨ℬ, hℬ, hcomul, hcounit, hsq⟩ := hB
  let _ := hℬ
  let 𝒜 := pullGrading e ℬ
  let _ : GradedAlgebra 𝒜 := gradedAlgebraPull e ℬ
  have hmap : ∀ n, ∀ b ∈ ℬ n, e.symm b ∈ 𝒜 n := by
    intro n b hb
    exact (mem_pullGrading e ℬ).2 (by simpa using hb)
  have hinv : ∀ a, Algebra.TensorProduct.map e.symm.toAlgHom e.symm.toAlgHom
      (Δ (e a)) = Bialgebra.comulAlgHom k A a := by
    intro a
    rw [← hΔ]
    exact (Algebra.TensorProduct.congr e e).symm_apply_apply _
  refine ⟨𝒜, inferInstance, ⟨?_, ?_⟩, ?_⟩
  · intro n a ha
    have hb := iSup_map₂_le_tensorGrade ℬ n
      (hcomul n (e a) ((mem_pullGrading e ℬ).1 ha))
    have hh := Langlands.Algebra.GradedHopf.IsGradedMap.map_tensorGrade
      (f := e.symm.toLinearMap) (g := e.symm.toLinearMap) hmap hmap hb
    change Algebra.TensorProduct.map e.symm.toAlgHom e.symm.toAlgHom (Δ (e a)) ∈
      Langlands.Algebra.GradedHopf.tensorGrade 𝒜 𝒜 n at hh
    rwa [hinv] at hh
  · intro n hn a ha
    change Bialgebra.counitAlgHom k A a = 0
    rw [← hε]
    exact hcounit n hn (e a) ((mem_pullGrading e ℬ).1 ha)
  · intro a ha haε
    have he : e a ∈ RingHom.ker ε ^ 2 :=
      hsq (e a) ((mem_pullGrading e ℬ).1 ha) (by rw [hε, haε])
    have himage : (RingHom.ker ε).map e.symm.toRingHom =
        RingHom.ker (Bialgebra.counitAlgHom k A) := by
      ext x
      change x ∈ (RingHom.ker ε).map e.toRingEquiv.symm ↔ _
      rw [Ideal.map_symm e.toRingEquiv, Ideal.mem_comap]
      exact show ε (e x) = 0 ↔ Bialgebra.counitAlgHom k A x = 0 by rw [hε]
    have hm := Ideal.mem_map_of_mem e.symm.toRingHom he
    rw [Ideal.map_pow, himage] at hm
    change e.symm (e a) ∈ _ at hm
    simpa only [e.symm_apply_apply] using hm

end Transport

end Langlands.GroupScheme.TorusGradedHopf
