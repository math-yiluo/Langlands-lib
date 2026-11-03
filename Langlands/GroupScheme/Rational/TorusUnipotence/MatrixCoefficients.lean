import Langlands.GroupScheme.Rational.CharacterUnits
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Rational.TorusUnipotence.TopWeight

/-! # The coordinate coalgebra and matrix coefficients of an affine group scheme -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.TorusUnipotence

open Algebra.TensorProduct (includeLeft includeRight)

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom]

section Points

variable {B C : Type u} [CommRing B] [Algebra (CommRingCat.of k) B] [CommRing C]
  [Algebra (CommRingCat.of k) C]

/-- The point of `G` with prescribed coordinates. -/
def pt (f : CharacterUnits.Coord G →ₐ[CommRingCat.of k] B) : Lie.AffinePoints G B :=
  (Lie.pointCoordinates G).symm f

theorem pt_injective {f g : CharacterUnits.Coord G →ₐ[CommRingCat.of k] B}
    (h : pt G f = pt G g) : f = g :=
  (Lie.pointCoordinates G).symm.injective h

theorem pt_comp (f : CharacterUnits.Coord G →ₐ[CommRingCat.of k] B)
    (g : B →ₐ[CommRingCat.of k] C) : pt G (g.comp f) = Lie.affineMap G g (pt G f) := by
  apply (Lie.pointCoordinates G).injective
  rw [pt, Equiv.apply_symm_apply, Lie.pointCoordinates_naturality, pt, Equiv.apply_symm_apply]

theorem pt_comul :
    pt G (CharacterUnits.comul G) =
      pt G (CharacterUnits.inclLeft G) * pt G (CharacterUnits.inclRight G) := by
  rw [pt, CharacterUnits.comul, Equiv.symm_apply_apply,
    CharacterUnits.affinePointMap_universalPoint_eq,
    CharacterUnits.affinePointMap_universalPoint_eq]
  rfl

/-- Composing the comultiplication with an algebra map out of `O(G) ⊗ O(G)` multiplies
points. -/
theorem pt_comp_comul
    (l : CharacterUnits.Coord G ⊗[CommRingCat.of k] CharacterUnits.Coord G →ₐ[CommRingCat.of k] C)
    {f g : CharacterUnits.Coord G →ₐ[CommRingCat.of k] C}
    (hf : l.comp (CharacterUnits.inclLeft G) = f) (hg : l.comp (CharacterUnits.inclRight G) = g) :
    pt G (l.comp (CharacterUnits.comul G)) = pt G f * pt G g := by
  rw [pt_comp, pt_comul, map_mul, ← pt_comp, ← pt_comp, hf, hg]

/-- Algebra maps factoring through the counit classify the identity point. -/
theorem pt_comp_coordinateOrigin (g : CommRingCat.of k →ₐ[CommRingCat.of k] C) :
    pt G (g.comp (Lie.coordinateOrigin G)) = 1 := by
  rw [pt_comp, pt, Lie.coordinateOrigin, Equiv.symm_apply_apply, map_one]

end Points

section Coalgebra

local notation "R" => CommRingCat.of k
local notation "A" => CharacterUnits.Coord G

/-- Coassociativity of the coordinate comultiplication, from associativity on points. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
        ((Algebra.TensorProduct.map (CharacterUnits.comul G) (AlgHom.id R A)).comp
          (CharacterUnits.comul G)) =
      (Algebra.TensorProduct.map (AlgHom.id R A) (CharacterUnits.comul G)).comp
        (CharacterUnits.comul G) := by
  apply pt_injective G
  rw [← AlgHom.comp_assoc,
    pt_comp_comul G _
      (f := ((Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp includeLeft).comp
        (CharacterUnits.comul G))
      (g := includeRight.comp includeRight)
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]),
    pt_comp_comul G _ (f := includeLeft) (g := includeRight.comp includeLeft)
      (AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]) (AlgHom.ext fun b => by simp),
    pt_comp_comul G _ (f := includeLeft) (g := includeRight.comp (CharacterUnits.comul G))
      (AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]) (AlgHom.ext fun b => by simp),
    pt_comp_comul G (includeRight : A ⊗[R] A →ₐ[R] A ⊗[R] (A ⊗[R] A)) rfl rfl, mul_assoc]

/-- Left counitality, from the left unit law on points. -/
theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (Lie.coordinateOrigin G) (AlgHom.id R A)).comp
        (CharacterUnits.comul G) = (Algebra.TensorProduct.lid R A).symm := by
  apply pt_injective G
  rw [pt_comp_comul G _ (f := includeLeft.comp (Lie.coordinateOrigin G)) (g := includeRight)
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp),
    pt_comp_coordinateOrigin, one_mul]
  exact congrArg (pt G) (AlgHom.ext fun b => by simp)

/-- Right counitality, from the right unit law on points. -/
theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R A) (Lie.coordinateOrigin G)).comp
        (CharacterUnits.comul G) = (Algebra.TensorProduct.rid R R A).symm := by
  apply pt_injective G
  rw [pt_comp_comul G _ (f := includeLeft) (g := includeRight.comp (Lie.coordinateOrigin G))
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp),
    pt_comp_coordinateOrigin, mul_one]
  exact congrArg (pt G) (AlgHom.ext fun b => by simp)

end Coalgebra

section KAlgebra

local notation "A" => CharacterUnits.Coord G

/-- The comultiplication of the coordinate algebra `O(G)`, as a `k`-algebra map. -/
def coordComul : A →ₐ[k] A ⊗[k] A :=
  CharacterUnits.comul G

/-- The counit of the coordinate algebra `O(G)`: evaluation at the identity point. -/
def coordCounit : A →ₐ[k] k :=
  Lie.coordinateOrigin G

theorem coordComul_coassoc :
    (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp
        ((Algebra.TensorProduct.map (coordComul G) (AlgHom.id k A)).comp (coordComul G)) =
      (Algebra.TensorProduct.map (AlgHom.id k A) (coordComul G)).comp (coordComul G) :=
  comul_coassoc G

theorem coordCounit_rTensor :
    (Algebra.TensorProduct.map (coordCounit G) (AlgHom.id k A)).comp (coordComul G) =
      (Algebra.TensorProduct.lid k A).symm :=
  comul_rTensor_counit G

theorem coordCounit_lTensor :
    (Algebra.TensorProduct.map (AlgHom.id k A) (coordCounit G)).comp (coordComul G) =
      (Algebra.TensorProduct.rid k k A).symm :=
  comul_lTensor_counit G

/-- Left counitality in the form `lid ∘ (ε ⊗ id) ∘ Δ = id`. -/
theorem lid_comp_coordCounit :
    (Algebra.TensorProduct.lid k A).toAlgHom.comp
        ((Algebra.TensorProduct.map (coordCounit G) (AlgHom.id k A)).comp (coordComul G)) =
      AlgHom.id k A := by
  rw [coordCounit_rTensor]
  ext a
  simp

/-- Right counitality in the form `rid ∘ (id ⊗ ε) ∘ Δ = id`. -/
theorem rid_comp_coordCounit :
    (Algebra.TensorProduct.rid k k A).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id k A) (coordCounit G)).comp (coordComul G)) =
      AlgHom.id k A := by
  rw [coordCounit_lTensor]
  ext a
  simp

/-- The bialgebra structure of `O(G)` given by `coordComul` and `coordCounit`. -/
abbrev coordBialgebra : Bialgebra k A :=
  Bialgebra.ofAlgHom (coordComul G) (coordCounit G) (coordComul_coassoc G)
    (coordCounit_rTensor G) (coordCounit_lTensor G)

theorem coordComul_coassoc_linear :
    TensorProduct.assoc k A A A ∘ₗ (coordComul G).toLinearMap.rTensor A ∘ₗ
        (coordComul G).toLinearMap =
      (coordComul G).toLinearMap.lTensor A ∘ₗ (coordComul G).toLinearMap :=
  let _ := coordBialgebra G
  Coalgebra.coassoc

theorem coordCounit_rTensor_linear :
    (coordCounit G).toLinearMap.rTensor A ∘ₗ (coordComul G).toLinearMap =
      TensorProduct.mk k k A 1 :=
  let _ := coordBialgebra G
  Coalgebra.rTensor_counit_comp_comul

theorem coordCounit_lTensor_linear :
    (coordCounit G).toLinearMap.lTensor A ∘ₗ (coordComul G).toLinearMap =
      (TensorProduct.mk k A k).flip 1 :=
  let _ := coordBialgebra G
  Coalgebra.lTensor_counit_comp_comul

end KAlgebra

section Matrix

variable {G} {n : Type} [Fintype n] [DecidableEq n]

/-- The coefficient matrix of `ρ`: its matrix at the universal point of `G`. -/
def coeffMatrix (ρ : MatrixRepresentation G n) : Matrix n n (CharacterUnits.Coord G) :=
  (ρ.affineMatrix (CharacterUnits.Coord G) (CharacterUnits.universalPoint G) : Matrix n n _)

/-- The matrix of `ρ` at the point with coordinates `f` is the coefficient matrix with `f`
applied entrywise. -/
theorem affineMatrix_pt (ρ : MatrixRepresentation G n) {B : Type u} [CommRing B]
    [Algebra (CommRingCat.of k) B] (f : CharacterUnits.Coord G →ₐ[CommRingCat.of k] B) :
    (ρ.affineMatrix (CommAlgCat.of _ B) (pt G f) : Matrix n n B) = (coeffMatrix ρ).map f := by
  rw [pt, ← CharacterUnits.affinePointMap_universalPoint_eq, GroupScheme.affinePointMap_apply,
    MatrixRepresentation.affineMatrix_naturality]
  rfl

theorem comul_coeffMatrix (ρ : MatrixRepresentation G n) (i j : n) :
    CharacterUnits.comul G (coeffMatrix ρ i j) =
      ∑ l, coeffMatrix ρ i l ⊗ₜ[CommRingCat.of k] coeffMatrix ρ l j := by
  have hC := affineMatrix_pt ρ (CharacterUnits.comul G)
  rw [pt_comul, map_mul, Units.val_mul, affineMatrix_pt, affineMatrix_pt] at hC
  have h := congrFun (congrFun hC i) j
  rw [Matrix.map_apply, Matrix.mul_apply] at h
  rw [← h]
  simp only [Matrix.map_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul]

theorem coordComul_coeffMatrix (ρ : MatrixRepresentation G n) (i j : n) :
    coordComul G (coeffMatrix ρ i j) = ∑ l, coeffMatrix ρ i l ⊗ₜ[k] coeffMatrix ρ l j :=
  comul_coeffMatrix ρ i j

theorem coordCounit_coeffMatrix (ρ : MatrixRepresentation G n) (i j : n) :
    coordCounit G (coeffMatrix ρ i j) = (1 : Matrix n n k) i j := by
  have h := congrFun (congrFun (affineMatrix_pt ρ (Lie.coordinateOrigin G)) i) j
  rw [Matrix.map_apply] at h
  have h1 := pt_comp_coordinateOrigin G (AlgHom.id _ _)
  rw [AlgHom.id_comp] at h1
  change Lie.coordinateOrigin G (coeffMatrix ρ i j) = _
  rw [← h, h1, map_one, Units.val_one]

/-- A vector whose coefficient combination is the constant vector is fixed by `ρ`. -/
theorem isFixedVector_of_coeffMatrix (ρ : MatrixRepresentation G n) (v : n → k)
    (hv : ∀ i, ∑ j, v j • coeffMatrix ρ i j = v i • (1 : CharacterUnits.Coord G)) :
    ρ.IsFixedVector v := by
  intro T g
  let a : T ⟶ (algSpec (CommRingCat.of k)).obj (op (CharacterUnits.Coord G)) :=
    g ≫ (Lie.coordinateIso G).inv
  have hg : g = a ≫ CharacterUnits.universalPoint G := by
    rw [CharacterUnits.universalPoint_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let ψ : CharacterUnits.Coord G →+* Γ(T.left, ⊤) := a.left.appTop.hom.comp
    (Corepresented.affineSectionsIso (CharacterUnits.Coord G)).inv.hom.toRingHom
  have hM : (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) = (coeffMatrix ρ).map ψ := by
    rw [hg, MatrixRepresentation.pointMatrix_naturality,
      MatrixRepresentation.pointMatrix_eq_affineMatrix]
    rfl
  have hs : ∀ c : k, scalarMap T c = ψ (algebraMap k (CharacterUnits.Coord G) c) := by
    intro c
    rw [← scalarMap_naturality a c]
    change _ = a.left.appTop.hom
      ((Corepresented.affineSectionsIso (CharacterUnits.Coord G)).inv.hom (algebraMap _ _ c))
    rw [AlgHom.commutes]
    rfl
  rw [hM]
  funext i
  simp only [hs]
  have hmv := RingHom.map_mulVec ψ (coeffMatrix ρ)
    (fun j => algebraMap k (CharacterUnits.Coord G) (v j)) i
  simp only [Function.comp_def] at hmv
  rw [← hmv]
  congr 1
  rw [Matrix.mulVec, dotProduct]
  simp only [← Algebra.commutes, ← Algebra.smul_def]
  rw [hv i, Algebra.smul_def, mul_one]

/-- Unipotence from fixed coefficient combinations of every nonzero representation. -/
theorem isUnipotent_of_coord
    (h : ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n),
      ∃ v : n → k, v ≠ 0 ∧ ∀ i, ∑ j, v j • coeffMatrix ρ i j = v i • (1 : CharacterUnits.Coord G)) :
    IsUnipotent G := by
  intro n _ _ _ ρ
  obtain ⟨v, hv0, hv⟩ := h n ρ
  exact ⟨v, hv0, isFixedVector_of_coeffMatrix ρ v hv⟩

end Matrix

section Graded

local notation "A" => CharacterUnits.Coord G

/-- Unipotence from a grading of `O(G)` by an ordered group, compatible with the
comultiplication, with the top-weight rigidity property in degree zero. -/
theorem isUnipotent_of_graded {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (𝒜 : Γ → Submodule k A) (h𝒜 : DirectSum.IsInternal 𝒜)
    (hΔ : ∀ χ, ∀ a ∈ 𝒜 χ,
      coordComul G a ∈ ⨆ α, Submodule.map₂ (TensorProduct.mk k A A) (𝒜 α) (𝒜 (χ - α)))
    (h1 : (1 : A) ∈ 𝒜 0)
    (hrigid : ∀ a ∈ 𝒜 0, (∀ m : Module.Dual k A, (∀ χ, 0 ≤ χ → ∀ b ∈ 𝒜 χ, m b = 0) →
      TensorProduct.rid k A (m.lTensor A (coordComul G a)) = 0) → ∃ c : k, a = c • 1) :
    IsUnipotent G := by
  refine isUnipotent_of_coord fun n _ _ _ ρ => ?_
  have he : (coordComul G).toLinearMap (1 : A) = (1 : A) ⊗ₜ[k] (1 : A) := by
    rw [AlgHom.toLinearMap_apply, map_one, Algebra.TensorProduct.one_def]
  have hεe : (coordCounit G).toLinearMap (1 : A) = 1 := by
    rw [AlgHom.toLinearMap_apply, map_one]
  exact exists_fixed_vector_of_graded' (coordComul G).toLinearMap (coordCounit G).toLinearMap
    (coordComul_coassoc_linear G) (coordCounit_rTensor_linear G) (coordCounit_lTensor_linear G)
    𝒜 h𝒜 hΔ he hεe h1 hrigid (coeffMatrix ρ) (coordComul_coeffMatrix ρ)
    (coordCounit_coeffMatrix ρ)

end Graded

end Langlands.GroupScheme.TorusUnipotence
