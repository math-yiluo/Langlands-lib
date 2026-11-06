import Langlands.GroupScheme.Rational.VectorLinearAction
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Points and actual Lie vectors of a weight vector group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {n : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (he : IsNaturalVectorCoordinates e)

/-- Send a vector-group point to the actual tangent vector with the same
coefficients in natural vector coordinates. -/
def vectorPointLieEquiv (A : CommAlgCat.{u} (CommRingCat.of k)) :
    Additive (Lie.AffinePoints V A) ≃+ Additive (lieKernel V A) where
  toFun v := (vectorLieCoordinates e he A).symm
    (vectorAffineCoordinates e A v.toMul).toAdd
  invFun X := Additive.ofMul ((vectorAffineCoordinates e A).symm
    (Multiplicative.ofAdd (vectorLieCoordinates e he A X)))
  left_inv v := by
    apply Additive.toMul.injective
    simp only [LinearEquiv.apply_symm_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply,
      toMul_ofMul]
  right_inv X := by
    simp only [toMul_ofMul, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      LinearEquiv.symm_apply_apply]
  map_add' v w := by
    change (vectorLieCoordinates e he A).symm
        (vectorAffineCoordinates e A (v.toMul * w.toMul)).toAdd = _
    rw [map_mul, toAdd_mul, map_add]

@[simp]
theorem vectorLieCoordinates_vectorPointLieEquiv
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Additive (Lie.AffinePoints V A)) :
    vectorLieCoordinates e he A (vectorPointLieEquiv e he A v) =
      (vectorAffineCoordinates e A v.toMul).toAdd :=
  (vectorLieCoordinates e he A).apply_symm_apply _

/-- The point-to-tangent identification commutes with every coefficient map. -/
theorem vectorPointLieEquiv_naturality
    {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B)
    (v : Lie.AffinePoints V A) :
    vectorPointLieEquiv e he B (Additive.ofMul (Lie.affineMap V f.hom v)) =
      lieKernelMapLinear V f.hom (vectorPointLieEquiv e he A (Additive.ofMul v)) := by
  apply (vectorLieCoordinates e he B).injective
  rw [vectorLieCoordinates_vectorPointLieEquiv, vectorLieCoordinates_naturality,
    vectorLieCoordinates_vectorPointLieEquiv, toMul_ofMul,
    toMul_ofMul, he.vectorAffineCoordinates_naturality]

/-- A scalar-linear action on points becomes its actual differential under
the point-to-tangent identification. -/
theorem vectorPointLieEquiv_act
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction H V} (hb : IsLinearVectorCoordinates b e)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (h : Lie.AffinePoints H A) (v : Lie.AffinePoints V A) :
    vectorPointLieEquiv e he A (Additive.ofMul (b.act h v)) =
      b.differential h (vectorPointLieEquiv e he A (Additive.ofMul v)) := by
  apply (vectorLieCoordinates e he A).injective
  rw [vectorLieCoordinates_vectorPointLieEquiv]
  exact (hb.vectorLieCoordinates_differential A h v).symm

omit [IsAffineHom V.X.hom] in
/-- Scalar multiplication in coefficient coordinates is the same as scalar
multiplication in the original coordinates on the affine test scheme. -/
theorem vectorAffineCoordinates_symm_smul
    {A : Type u} [CommRing A] [Algebra k A] (c : A) (v : Lie.AffinePoints V A) :
    (vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (c • (vectorAffineCoordinates e A v).toAdd)) =
      coordinateSmul e _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv c) v := by
  let T := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))
  let r : Γ(T.left, ⊤) ≅ CommRingCat.of A := Scheme.ΓSpecIso (CommRingCat.of A)
  apply (vectorAffineCoordinates e A).injective
  apply Multiplicative.toAdd.injective
  rw [MulEquiv.apply_symm_apply]
  funext j
  change c * r.hom ((e T v).toAdd j) =
    r.hom ((e T ((e T).symm
      (Multiplicative.ofAdd ((r.inv c) • (e T v).toAdd)))).toAdd j)
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  change _ = r.hom (r.inv c * (e T v).toAdd j)
  rw [r.hom.hom.map_mul, r.inv_hom_id_apply]

/-- The tangent point is epsilon times the constant point in the natural
vector scalar structure. -/
theorem vectorPointLieEquiv_val
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Lie.AffinePoints V A) :
    (vectorPointLieEquiv e he A (Additive.ofMul v)).toMul.val =
      coordinateSmul e _
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber A))).inv
          (TrivSqZeroExt.inr (1 : A))) (Lie.constant V v) := by
  change (vectorLiePoint e he (vectorAffineCoordinates e A v).toAdd).val = _
  rw [vectorLiePoint_eq_epsilon_smul]
  exact vectorAffineCoordinates_symm_smul e
    (TrivSqZeroExt.inr (1 : A) : DualNumber A) (Lie.constant V v)

variable {e he}

/-- For a nonzero weight of a split torus, the point-to-tangent equivalence
is independent of the weight coordinates, including their dimension. -/
theorem vectorPointLieEquiv_eq_of_weight
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {a : characterLattice S}
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    {m : ℕ} {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (hw : IsWeightVectorCoordinates b a e) (hw' : IsWeightVectorCoordinates b a e')
    (A : CommAlgCat.{u} (CommRingCat.of k)) :
    vectorPointLieEquiv e hw.1 A = vectorPointLieEquiv e' hw'.1 A := by
  apply AddEquiv.ext
  intro v
  change vectorPointLieEquiv e hw.1 A (Additive.ofMul v.toMul) =
    vectorPointLieEquiv e' hw'.1 A (Additive.ofMul v.toMul)
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [vectorPointLieEquiv_val, vectorPointLieEquiv_val,
    coordinateSmul_eq_of_isWeightVectorCoordinates hS ha hw hw']

end Langlands.GroupScheme.RelativeRoot
