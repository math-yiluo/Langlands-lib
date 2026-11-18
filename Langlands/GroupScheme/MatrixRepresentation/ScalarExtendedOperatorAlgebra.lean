import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficientBaseChange
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange

/-! # The operator algebra after scalar extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.MatrixRepresentation.ScalarExtendedOperatorAlgebra

open AffineCoefficientAlgebra AffineCoefficientBaseChange AffineCoefficients

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation G n)

/-- The scalar-extended operator algebra acts on the extended coordinate space. -/
def scalarExtensionHom :
    (K ⊗[k] operatorAlgebra ρ) →ₐ[K] Module.End K (n → K) :=
  AlgHom.liftEquiv k K (operatorAlgebra ρ) (Module.End K (n → K))
    ((extensionHom (K := K)).comp (operatorAlgebra ρ).val)

/-- The image algebra of extended operators. -/
def extendedAlgebra : Subalgebra K (Module.End K (n → K)) :=
  (scalarExtensionHom (K := K) ρ).range

/-- A coefficient with values in the extended field is a linear combination of
the original ground-field coefficients. -/
theorem coefficient_preserves {W : Submodule K (n → K)}
    (hW : ∀ ℓ : CharacterUnits.Coord G →ₗ[k] k, ∀ v ∈ W,
      (coefficientMap ρ ℓ).map (algebraMap k K) *ᵥ v ∈ W)
    (ψ : CharacterUnits.Coord G →ₗ[k] K) (v : n → K) (hv : v ∈ W) :
    ρ.universalCharacterMatrix.map ψ *ᵥ v ∈ W := by
  classical
  let S := AffineCoefficients.coefficientSpace ρ
  obtain ⟨p, hp⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let b := Module.finBasis k S
  let ℓ := fun i => (b.coord i).comp p
  have hmat : ρ.universalCharacterMatrix.map ψ =
      ∑ i, ψ (b i).val • ((coefficientMap ρ (ℓ i)).map (algebraMap k K)) := by
    ext r s
    let a : S := ⟨ρ.universalCharacterMatrix r s, universalCharacterMatrix_mem ρ r s⟩
    have hpa : p a.val = a := LinearMap.congr_fun hp a
    have ha0 : (∑ i, b.repr a i • (b i).val) = a.val := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg Subtype.val (b.sum_repr a)
    have ha := congrArg ψ ha0
    rw [map_sum] at ha
    simp only [Algebra.smul_def] at ha
    have hsmul (i) :
        ψ (algebraMap k (CharacterUnits.Coord G) (b.repr a i) * (b i).val) =
          algebraMap k K (b.repr a i) * ψ (b i).val := by
      simpa only [Algebra.smul_def] using ψ.map_smul (b.repr a i) (b i).val
    simp_rw [hsmul] at ha
    have he (i) : ℓ i a.val = b.repr a i := by
      change b.coord i (p a.val) = _
      rw [hpa]
      rfl
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    change ψ a.val = ∑ i, ψ (b i).val * algebraMap k K (ℓ i a.val)
    simp_rw [he]
    simpa only [mul_comm] using ha.symm
  rw [hmat, Matrix.sum_mulVec]
  apply W.sum_mem
  intro i _
  rw [Matrix.smul_mulVec]
  exact W.smul_mem _ (hW (ℓ i) v hv)

omit [IsAffineHom G.X.hom] in
/-- Forgetting the new base identifies the two affine matrices over a
compatible test algebra. -/
theorem affineMatrix_restrictScalars
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (x : ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).affinePoints
        (CommAlgCat.of K A)) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).affineMatrix
        (CommAlgCat.of K A) x =
      ρ.affineMatrix (CommAlgCat.of k A)
        ((ringTestRestrictScalarsIso k K A).inv ≫
          baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G _ x) := by
  let j := ringTestRestrictScalarsIso k K A
  have h := affineMatrix_baseChange_map ρ (CommRingCat.ofHom (algebraMap k K))
    (CommAlgCat.of k A) (CommAlgCat.of K A) (𝟙 (CommRingCat.of A))
    j.hom (by simp [j]; rfl)
    x (j.inv ≫ baseChangePointsEquiv
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) G _ x) (by simp; rfl)
  simpa using h

/-- Invariance under the original extended operators is actual all-test
stability for the base-changed representation. -/
theorem isStableSubspace_of_operator_preserves {W : Submodule K (n → K)}
    (hW : ∀ f ∈ operatorAlgebra ρ, ∀ v ∈ W, extensionHom (K := K) f v ∈ W) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W := by
  intro A x v hv q
  let : Algebra k A := ((algebraMap K A).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let y := (ringTestRestrictScalarsIso k K A).inv ≫
    baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G _ x
  rw [affineMatrix_restrictScalars ρ A x]
  let ψ := (q.restrictScalars k).comp (Lie.pointCoordinates G y).toLinearMap
  have hc : ∀ ℓ : CharacterUnits.Coord G →ₗ[k] k, ∀ w ∈ W,
      (coefficientMap ρ ℓ).map (algebraMap k K) *ᵥ w ∈ W := by
    intro ℓ w hw
    have h := hW (coefficientMap ρ ℓ).mulVecLin (Algebra.subset_adjoin ⟨ℓ, rfl⟩) w hw
    rwa [extensionHom_mulVecLin] at h
  have h := coefficient_preserves ρ hc ψ v hv
  have hm : ρ.universalCharacterMatrix.map ψ =
      (ρ.affineMatrix (CommAlgCat.of k A) y : Matrix n n A).map q := by
    rw [← universalCharacterMatrix_map]
    rfl
  rw [hm] at h
  convert h using 1
  funext i
  have hs (a : A) (c : K) : q (a * algebraMap K A c) = q a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simp only [Matrix.mulVec, dotProduct, map_sum, hs, Matrix.map_apply]
  rfl

/-- Actual stability is equivalent to invariance under the image of the
scalar-extended operator algebra. -/
theorem isStableSubspace_iff (W : Submodule K (n → K)) :
    (ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsStableSubspace W ↔
      extendedAlgebra (K := K) ρ ≤ preservingAlgebra W := by
  constructor
  · intro h f hf v hv
    obtain ⟨x, rfl⟩ := hf
    induction x using TensorProduct.inductionOn with
    | tmul c a =>
      change c • extensionHom (K := K) a.val v ∈ W
      exact W.smul_mem c (operator_preserves ρ h a.property v hv)
    | add a b ha hb => simpa using W.add_mem ha hb
  · intro h
    apply isStableSubspace_of_operator_preserves ρ
    intro f hf v hv
    have hm : extensionHom (K := K) f ∈ extendedAlgebra (K := K) ρ :=
      ⟨1 ⊗ₜ[k] (⟨f, hf⟩ : operatorAlgebra ρ), by
        simp [scalarExtensionHom]⟩
    exact h hm v hv

end Langlands.GroupScheme.MatrixRepresentation.ScalarExtendedOperatorAlgebra
