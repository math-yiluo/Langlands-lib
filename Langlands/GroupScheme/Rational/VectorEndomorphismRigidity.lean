import Langlands.GroupScheme.Rational.VectorLinearAction
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Lie.FiniteCoordinateScalarExtension
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.ElementaryOrbitLimit

/-! # A scalar-linear vector-group map is determined by its actual differential -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))) (f : V ⟶ V)

/-- Postcomposition by the map is scalar-linear in these vector coordinates on every test. -/
def IsCoordinateLinear : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) (v : T ⟶ V.X),
    (e T (coordinateSmul e T c v ≫ f.hom.hom)).toAdd =
      c • (e T (v ≫ f.hom.hom)).toAdd

variable {e f}

/-- The scalar-linearity equation expressed in affine coefficient coordinates. -/
theorem IsCoordinateLinear.vectorAffineCoordinates_smul
    (hf : IsCoordinateLinear e f)
    {A : Type u} [CommRing A] [Algebra k A] (c : A) (v : Lie.AffinePoints V A) :
    (vectorAffineCoordinates e A
      (((vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd (c • (vectorAffineCoordinates e A v).toAdd))) ≫ f.hom.hom)).toAdd =
      c • (vectorAffineCoordinates e A (v ≫ f.hom.hom)).toAdd := by
  let T := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))
  let r : Γ(T.left, ⊤) ≅ CommRingCat.of A := Scheme.ΓSpecIso (CommRingCat.of A)
  let q : T ⟶ V.X := coordinateSmul e T (r.inv c) v
  have hq : q = (vectorAffineCoordinates e A).symm
      (Multiplicative.ofAdd (c • (vectorAffineCoordinates e A v).toAdd)) := by
    apply (vectorAffineCoordinates e A).injective
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.apply_symm_apply]
    funext j
    change r.hom ((e T q).toAdd j) = c * r.hom ((e T v).toAdd j)
    rw [show (e T q).toAdd = (r.inv c) • (e T v).toAdd from
      coordinateSmul_coord e T (r.inv c) v]
    change r.hom (r.inv c * (e T v).toAdd j) = _
    rw [r.hom.hom.map_mul, r.inv_hom_id_apply]
  rw [← hq]
  have hlin := hf T (r.inv c) v
  funext j
  change r.hom ((e T (q ≫ f.hom.hom)).toAdd j) =
    c * r.hom ((e T (v ≫ f.hom.hom)).toAdd j)
  rw [show (e T (q ≫ f.hom.hom)).toAdd =
      (r.inv c) • (e T (v ≫ f.hom.hom)).toAdd from hlin]
  change r.hom (r.inv c * (e T (v ≫ f.hom.hom)).toAdd j) = _
  rw [r.hom.hom.map_mul, r.inv_hom_id_apply]

variable [IsAffineHom V.X.hom]

/-- The actual differential of a scalar-linear map agrees with that map's vector coefficients. -/
theorem IsCoordinateLinear.vectorLieCoordinates_targetMap
    (hf : IsCoordinateLinear e f) (he : IsNaturalVectorCoordinates e)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (v : Lie.AffinePoints V A) :
    vectorLieCoordinates e he A
      (Lie.targetMapLinear f A
        (Additive.ofMul (vectorLiePoint e he (vectorAffineCoordinates e A v).toAdd))) =
      (vectorAffineCoordinates e A (v ≫ f.hom.hom)).toAdd := by
  funext j
  change ((vectorAffineCoordinates e (DualNumber A)
    ((vectorLiePoint e he (vectorAffineCoordinates e A v).toAdd).val ≫ f.hom.hom)).toAdd j).snd = _
  rw [vectorLiePoint_eq_epsilon_smul he, hf.vectorAffineCoordinates_smul]
  have hn : Lie.constant V v ≫ f.hom.hom = Lie.constant V (v ≫ f.hom.hom) :=
    Category.assoc _ _ _
  rw [hn]
  simp only [Lie.constant]
  rw [he.vectorAffineCoordinates_naturality]
  change ((TrivSqZeroExt.inr (1 : A) : DualNumber A) *
    (TrivSqZeroExt.inlAlgHom k A A)
      ((vectorAffineCoordinates e A (v ≫ f.hom.hom)).toAdd j)).snd = _
  simp

/-- Identity of the differential over the field extends to every coefficient algebra. -/
theorem targetMapLinear_eq_self_coefficients_of_coordinates
    (he : IsNaturalVectorCoordinates e)
    (hf : ∀ x, Lie.targetMapLinear f k x = x)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : Additive (lieKernel V A)) :
    Lie.targetMapLinear f A x = x := by
  let c := finiteLieCoordinatesOfVector e he
  obtain ⟨z, rfl⟩ := (c.scalarExtension A).surjective x
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    rw [c.scalarExtension_tmul, map_smul, lieKernelTargetLinear_map, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A natural scalar-linear vector-group endomorphism with identity actual
Lie differential is the identity group-scheme map. -/
theorem eq_id_of_coordinateLinear_of_targetMapLinear_eq_self
    (he : IsNaturalVectorCoordinates e) (hlin : IsCoordinateLinear e f)
    (hf : ∀ x, Lie.targetMapLinear f k x = x) : f = 𝟙 V := by
  have haffine (A : Type u) [CommRing A] [Algebra k A]
      (v : Lie.AffinePoints V A) : v ≫ f.hom.hom = v := by
    apply (vectorAffineCoordinates e A).injective
    apply Multiplicative.toAdd.injective
    have h := hlin.vectorLieCoordinates_targetMap he (CommAlgCat.of k A) v
    rw [targetMapLinear_eq_self_coefficients_of_coordinates he hf] at h
    have hp : vectorLieCoordinates e he (CommAlgCat.of k A)
        (Additive.ofMul (vectorLiePoint e he (vectorAffineCoordinates e A v).toAdd)) =
        (vectorAffineCoordinates e A v).toAdd := by
      funext j
      change ((vectorAffineCoordinates e (DualNumber A)
        (vectorLiePoint e he (vectorAffineCoordinates e A v).toAdd).val).toAdd j).snd = _
      rw [vectorAffineCoordinates_vectorLiePoint]
      rfl
    exact h.symm.trans hp
  apply hom_ext_points
  intro T v
  apply OrbitLimit.hom_ext_of_algebraSpec
  intro A _ _ c
  simpa only [Grp.id_hom_hom, Category.comp_id, ← Category.assoc] using haffine A (c ≫ v)

end Langlands.GroupScheme.RelativeRoot
