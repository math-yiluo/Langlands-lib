import Langlands.GroupScheme.MatrixRepresentation.FrobeniusOrderedDistributions

/-! # Universal actual Frobenius-origin points and their distribution actions -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusOriginUniversality

open FrobeniusCoordinateModel FrobeniusOrderedDistributions

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

/-- The intrinsic origin condition is exactly vanishing on the defining ideal
of the actual Frobenius-origin quotient. -/
theorem isOriginPoint_iff_quotientIdeal_le_ker
    (A : CommAlgCat.{u} k) (g : G.affinePoints A) :
    IsOriginPoint p r A g ↔
      quotientIdeal G p r ≤ RingHom.ker (Lie.pointCoordinates G g).toRingHom := by
  rw [quotientIdeal, Ideal.map_le_iff_le_comap]
  constructor
  · intro h a ha
    change Lie.pointCoordinates G g
      (characteristicPowerMap k p (CharacterUnits.Coord G) r a) = 0
    rw [characteristicPowerMap_apply, map_pow]
    exact h a ha
  · intro h a ha
    have hz := h ha
    change Lie.pointCoordinates G g
      (characteristicPowerMap k p (CharacterUnits.Coord G) r a) = 0 at hz
    simpa only [characteristicPowerMap_apply, map_pow] using hz

/-- The canonical quotient point is itself an intrinsic origin point. -/
theorem isOriginPoint_quotientPoint :
    IsOriginPoint p r (quotientAlgebra G p r) (quotientPoint G p r) := by
  intro a ha
  have he := AlgHom.congr_fun (pointCoordinates_quotientPoint G p r) a
  change Lie.coordinateOrigin G a = 0 at ha
  have hz : quotientMap G p r a ^ p ^ r = 0 := by
    rw [quotient_pow_origin, ha, map_zero,
      zero_pow (pow_ne_zero _ (expChar_ne_zero k p))]
  exact (congrArg (fun z : quotientAlgebra G p r => z ^ p ^ r) he).trans hz

omit [ExpChar k p] in
/-- Intrinsic origin points are preserved by every test-algebra map. -/
theorem isOriginPoint_affineMap {A B : CommAlgCat.{u} k}
    (f : A →ₐ[k] B) {g : G.affinePoints A} (hg : IsOriginPoint p r A g) :
    IsOriginPoint p r B (Lie.affineMap G f g) := by
  intro a ha
  rw [Lie.pointCoordinates_naturality, AlgHom.comp_apply, ← map_pow, hg a ha, map_zero]

/-- The canonical factor of an intrinsic origin point's actual coordinate map. -/
def pointLift (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) : quotientAlgebra G p r →ₐ[k] A :=
  Ideal.Quotient.liftₐ (quotientIdeal G p r) (Lie.pointCoordinates G g)
    ((isOriginPoint_iff_quotientIdeal_le_ker p r A g).mp hg)

@[simp]
theorem pointLift_quotientMap (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) (a : CharacterUnits.Coord G) :
    pointLift p r A g hg (quotientMap G p r a) = Lie.pointCoordinates G g a := rfl

theorem pointLift_comp_quotientMap (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) :
    (pointLift p r A g hg).comp (quotientMap G p r) = Lie.pointCoordinates G g :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- The factor through the actual quotient is unique. -/
theorem pointLift_unique (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) (f : quotientAlgebra G p r →ₐ[k] A)
    (hf : f.comp (quotientMap G p r) = Lie.pointCoordinates G g) :
    f = pointLift p r A g hg := by
  apply Ideal.Quotient.algHom_ext k
  exact hf.trans (pointLift_comp_quotientMap p r A g hg).symm

/-- The original point is the image of the genuine universal quotient point. -/
theorem affineMap_pointLift (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) :
    Lie.affineMap G (pointLift p r A g hg) (quotientPoint G p r) = g := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality]
  exact (congrArg (fun f : CharacterUnits.Coord G →ₐ[k] quotientAlgebra G p r =>
    (pointLift p r A g hg).comp f) (pointCoordinates_quotientPoint G p r)).trans
      (pointLift_comp_quotientMap p r A g hg)

/-- Base change of an intrinsic point corresponds to composition of its lift. -/
theorem pointLift_naturality {A B : CommAlgCat.{u} k}
    (f : A →ₐ[k] B) (g : G.affinePoints A) (hg : IsOriginPoint p r A g) :
    pointLift p r B (Lie.affineMap G f g) (isOriginPoint_affineMap p r f hg) =
      f.comp (pointLift p r A g hg) := by
  apply (pointLift_unique p r B (Lie.affineMap G f g)
    (isOriginPoint_affineMap p r f hg) _ _).symm
  rw [AlgHom.comp_assoc, pointLift_comp_quotientMap, Lie.pointCoordinates_naturality]

/-- Algebra maps out of the actual quotient classify exactly the original
intrinsic origin points, including points over nonreduced test algebras. -/
def originPointEquiv (A : CommAlgCat.{u} k) :
    (quotientAlgebra G p r →ₐ[k] A) ≃
      {g : G.affinePoints A // IsOriginPoint p r A g} where
  toFun f := ⟨Lie.affineMap G f (quotientPoint G p r),
    isOriginPoint_affineMap p r f (isOriginPoint_quotientPoint p r)⟩
  invFun g := pointLift p r A g.val g.property
  left_inv f := by
    change pointLift p r A (Lie.affineMap G f (quotientPoint G p r)) _ = f
    apply (pointLift_unique p r A (Lie.affineMap G f (quotientPoint G p r)) _ f _).symm
    exact (congrArg (fun h : CharacterUnits.Coord G →ₐ[k] quotientAlgebra G p r =>
      f.comp h) (pointCoordinates_quotientPoint G p r).symm).trans
        (Lie.pointCoordinates_naturality G f (quotientPoint G p r)).symm
  right_inv g := Subtype.ext (affineMap_pointLift p r A g.val g.property)

variable {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- The matrix of the original representation at any intrinsic origin point
is obtained from its actual universal quotient matrix. -/
theorem affineMatrix_pointLift (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) :
    (ρ.affineMatrix A g : Matrix n n A) =
      (ρ.affineMatrix (quotientAlgebra G p r) (quotientPoint G p r) :
        Matrix n n (quotientAlgebra G p r)).map (pointLift p r A g hg) := by
  have h := ρ.affineMatrix_naturality
    (CommAlgCat.ofHom (pointLift p r A g hg) :
      quotientAlgebra G p r ⟶ A) (quotientPoint G p r)
  have hp : (algSpec (.of k)).map
      (CommAlgCat.ofHom (pointLift p r A g hg) :
        quotientAlgebra G p r ⟶ A).op ≫ quotientPoint G p r = g :=
    affineMap_pointLift p r A g hg
  rw [hp] at h
  exact congrArg Units.val h

/-- Evaluation of the original action is natural along the unique quotient lift. -/
theorem affineAction_pointLift (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) (v : n → k) :
    ρ.affineAction A g (fun j => algebraMap k A (v j)) =
      fun i => pointLift p r A g hg
        (ρ.affineAction (quotientAlgebra G p r) (quotientPoint G p r)
          (fun j => algebraMap k (quotientAlgebra G p r) (v j)) i) := by
  have h := ρ.affineAction_naturality
    (CommAlgCat.ofHom (pointLift p r A g hg) :
      quotientAlgebra G p r ⟶ A) (quotientPoint G p r)
    (fun j => algebraMap k (quotientAlgebra G p r) (v j))
  have hp : (algSpec (.of k)).map
      (CommAlgCat.ofHom (pointLift p r A g hg) :
        quotientAlgebra G p r ⟶ A).op ≫ quotientPoint G p r = g :=
    affineMap_pointLift p r A g hg
  have hv : (fun i => (CommAlgCat.ofHom (pointLift p r A g hg) :
      quotientAlgebra G p r ⟶ A).hom
        (algebraMap k (quotientAlgebra G p r) (v i))) =
      (fun i => algebraMap k A (v i)) := by
    funext i
    exact (pointLift p r A g hg).commutes (v i)
  rw [hp, hv] at h
  exact h

/-- Applying a quotient distribution to the action matrix commutes with its
action on a constant vector. -/
theorem distributionAction_apply
    (ℓ : Module.Dual k (quotientAlgebra G p r)) (v : n → k) :
    distributionAction p r ρ ℓ v =
      fun i => ℓ (ρ.affineAction (quotientAlgebra G p r) (quotientPoint G p r)
        (fun j => algebraMap k (quotientAlgebra G p r) (v j)) i) := by
  funext i
  have hs (a : quotientAlgebra G p r) (c : k) :
      ℓ (a * algebraMap k (quotientAlgebra G p r) c) = ℓ a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  change (∑ j, ℓ (ρ.affineMatrix _ _ i j) * v j) =
    ℓ (∑ j, ρ.affineMatrix _ _ i j * algebraMap k (quotientAlgebra G p r) (v j))
  simp only [map_sum, hs]

/-- Every scalar contraction of an intrinsic origin-point action is an
actual quotient-distribution action. -/
theorem contract_affineAction (A : CommAlgCat.{u} k) (g : G.affinePoints A)
    (hg : IsOriginPoint p r A g) (ℓ : A →ₗ[k] k) (v : n → k) :
    (fun i => ℓ (ρ.affineAction A g (fun j => algebraMap k A (v j)) i)) =
      distributionAction p r ρ
        (ℓ.comp (pointLift p r A g hg).toLinearMap) v := by
  rw [distributionAction_apply, affineAction_pointLift p r ρ A g hg]
  rfl

/-- The linear orbit map of the entire actual quotient dual. -/
def distributionOrbitMap (v : n → k) :
    Module.Dual k (quotientAlgebra G p r) →ₗ[k] (n → k) :=
  (distributionAction p r ρ).flip v

/-- Without any polynomial coordinate hypothesis, all intrinsic origin
actions span exactly the image of the actual quotient's distribution orbit map. -/
theorem originOrbitSpan_eq_range (v : n → k) :
    originOrbitSpan p r ρ v = LinearMap.range (distributionOrbitMap p r ρ v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨A, g, hg, ℓ, rfl⟩
    exact ⟨ℓ.comp (pointLift p r A g hg).toLinearMap,
      (contract_affineAction p r ρ A g hg ℓ v).symm⟩
  · rintro w ⟨ℓ, rfl⟩
    apply Submodule.subset_span
    exact ⟨quotientAlgebra G p r, quotientPoint G p r,
      isOriginPoint_quotientPoint p r, ℓ, distributionAction_apply p r ρ ℓ v⟩

/-- Stability under all intrinsic origin-point tests is detected by the
single actual quotient matrix and all its linear distributions. -/
theorem stable_originPoints_iff (W : Submodule k (n → k)) :
    (∀ (A : CommAlgCat.{u} k) (g : G.affinePoints A), IsOriginPoint p r A g →
      ∀ v ∈ W, ∀ ℓ : A →ₗ[k] k,
        (fun i => ℓ (ρ.affineAction A g (fun j => algebraMap k A (v j)) i)) ∈ W) ↔
      ∀ ℓ : Module.Dual k (quotientAlgebra G p r), ∀ v ∈ W,
        distributionAction p r ρ ℓ v ∈ W := by
  constructor
  · intro h ℓ v hv
    rw [distributionAction_apply]
    exact h _ _ (isOriginPoint_quotientPoint p r) v hv ℓ
  · intro h A g hg v hv ℓ
    rw [contract_affineAction p r ρ A g hg ℓ v]
    exact h _ v hv

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusOriginUniversality
