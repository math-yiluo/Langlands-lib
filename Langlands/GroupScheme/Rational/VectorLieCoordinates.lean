import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Lie.FiniteAction

/-! # Lie coordinates induced by natural vector coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- Natural vector coordinates on an affine test, expressed in its coefficient algebra. -/
def vectorAffineCoordinates (A : Type u) [CommRing A] [Algebra k A] :
    Lie.AffinePoints V A ≃* Multiplicative (Fin d → A) where
  toFun v := Multiplicative.ofAdd fun j =>
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((e ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))) v).toAdd j)
  invFun v := (e ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))).symm
    (Multiplicative.ofAdd fun j => (Scheme.ΓSpecIso (CommRingCat.of A)).inv (v.toAdd j))
  left_inv v := by
    apply (e _).injective
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply _
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [map_mul, toAdd_mul, Pi.add_apply, toAdd_ofAdd]
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.map_add _ _

variable {e}

/-- The affine-coordinate identification commutes with every coefficient map. -/
theorem IsNaturalVectorCoordinates.vectorAffineCoordinates_naturality
    (he : IsNaturalVectorCoordinates e)
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (v : Lie.AffinePoints V A) :
    (vectorAffineCoordinates e B (Lie.affineMap V f v)).toAdd =
      fun j => f ((vectorAffineCoordinates e A v).toAdd j) := by
  funext j
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    ((e _ (((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op) ≫ v)).toAdd j) = _
  rw [he _ _ ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op)]
  exact congrArg (fun q => q.hom
    ((e ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))) v).toAdd j))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom))

variable (e)

/-- A point of the identity kernel has zero constant vector coordinates. -/
theorem vectorAffineCoordinates_kernel_fst (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (x : lieKernel V A) (j : Fin d) :
    ((vectorAffineCoordinates e (DualNumber A) x.val).toAdd j).fst = 0 := by
  have h := congrFun
    (he.vectorAffineCoordinates_naturality (TrivSqZeroExt.fstHom k A A) x.val) j
  change (vectorAffineCoordinates e A (Lie.reduction V x.val)).toAdd j = _ at h
  rw [x.property, map_one] at h
  exact h.symm

/-- The actual kernel point with the prescribed epsilon coefficients. -/
def vectorLiePoint (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (x : Fin d → A) : lieKernel V A :=
  ⟨(vectorAffineCoordinates e (DualNumber A)).symm
    (Multiplicative.ofAdd fun j => TrivSqZeroExt.inr (x j)), by
      apply (vectorAffineCoordinates e A).injective
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (vectorAffineCoordinates e A
        (Lie.affineMap V (TrivSqZeroExt.fstHom k A A) _)).toAdd = 0
      rw [he.vectorAffineCoordinates_naturality, MulEquiv.apply_symm_apply]
      rfl⟩

@[simp]
theorem vectorAffineCoordinates_vectorLiePoint (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] (x : Fin d → A) :
    (vectorAffineCoordinates e (DualNumber A) (vectorLiePoint e he x).val).toAdd =
      fun j => TrivSqZeroExt.inr (x j) :=
  congrArg Multiplicative.toAdd ((vectorAffineCoordinates e _).apply_symm_apply _)

variable [IsAffineHom V.X.hom]

/-- Epsilon coefficients give linear coordinates on the actual Lie kernel. -/
def vectorLieCoordinates (he : IsNaturalVectorCoordinates e)
    (A : CommAlgCat.{u} (CommRingCat.of k)) :
    Additive (lieKernel V A) ≃ₗ[A] (Fin d → A) where
  toFun x := fun j =>
    ((vectorAffineCoordinates e (DualNumber A) x.toMul.val).toAdd j).snd
  invFun x := Additive.ofMul (vectorLiePoint e he x)
  left_inv x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply (vectorAffineCoordinates e (DualNumber A)).injective
    apply Multiplicative.toAdd.injective
    funext j
    change (vectorAffineCoordinates e (DualNumber A)
      (vectorLiePoint e he (fun i =>
        ((vectorAffineCoordinates e (DualNumber A) x.toMul.val).toAdd i).snd)).val).toAdd j =
      (vectorAffineCoordinates e (DualNumber A) x.toMul.val).toAdd j
    rw [vectorAffineCoordinates_vectorLiePoint]
    apply TrivSqZeroExt.ext
    · exact (vectorAffineCoordinates_kernel_fst e he x.toMul j).symm
    · rfl
  right_inv x := by
    funext j
    change ((vectorAffineCoordinates e (DualNumber A)
      (vectorLiePoint e he x).val).toAdd j).snd = x j
    rw [vectorAffineCoordinates_vectorLiePoint]
    rfl
  map_add' x y := by
    funext j
    change ((vectorAffineCoordinates e (DualNumber A)
      (x.toMul.val * y.toMul.val)).toAdd j).snd = _
    simp only [map_mul, toAdd_mul, Pi.add_apply, TrivSqZeroExt.snd_add]
  map_smul' c x := by
    funext j
    change ((vectorAffineCoordinates e (DualNumber A)
      (Lie.affineMap V (GeneralLinear.DualNumber.epsilonScaleAlg c) x.toMul.val)).toAdd j).snd = _
    rw [he.vectorAffineCoordinates_naturality]
    exact GeneralLinear.DualNumber.epsilonScale_snd c _

/-- The Lie coordinates are natural on all coefficient algebras. -/
theorem vectorLieCoordinates_naturality (he : IsNaturalVectorCoordinates e)
    {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B)
    (x : Additive (lieKernel V A)) :
    vectorLieCoordinates e he B (lieKernelMapLinear V f.hom x) =
      fun j => f.hom (vectorLieCoordinates e he A x j) := by
  funext j
  change ((vectorAffineCoordinates e (DualNumber B)
    (Lie.affineMap V (GeneralLinear.DualNumber.coefficientAlgMap f.hom)
      x.toMul.val)).toAdd j).snd = _
  rw [he.vectorAffineCoordinates_naturality]
  rfl

/-- Natural vector coordinates supply the Library's actual finite Lie coordinates. -/
def finiteLieCoordinatesOfVector (he : IsNaturalVectorCoordinates e) :
    Lie.FiniteCoordinates V d where
  equiv := vectorLieCoordinates e he
  naturality := vectorLieCoordinates_naturality e he

end Langlands.GroupScheme.RelativeRoot
