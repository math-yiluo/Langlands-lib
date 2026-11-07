import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.Algebra.ReducedNormEvaluation
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Actual polynomial norm characters and norm-one algebra groups -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits

namespace GaloisNorm

variable {k A L : Type u} [Field k] [Ring A] [Algebra k A]
  [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  {n : ℕ} (b : Module.Basis (Fin n) k A)
  {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
  (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)

/-- The existing actual polynomial norm gives a homomorphism on every relative test. -/
def normPoints (T : Over (base k)) :
    (T ⟶ (groupScheme b).X) →* (T ⟶ (Gm (base k)).X) :=
  (Gm.pointsEquiv (base k) T).symm.toMonoidHom.comp
    ((Langlands.ReducedNorm.normFromGaloisUnits b e
      ((algΓ (CommRingCat.of k)).obj T).unop).comp (pointsEquiv b T).toMonoidHom)

@[simp] theorem pointsEquiv_normPoints (T : Over (base k))
    (x : T ⟶ (groupScheme b).X) :
    Gm.pointsEquiv (base k) T (normPoints b e T x) =
      Langlands.ReducedNorm.normFromGaloisUnits b e
        ((algΓ (CommRingCat.of k)).obj T).unop (pointsEquiv b T x) :=
  (Gm.pointsEquiv (base k) T).apply_symm_apply _

/-- The polynomial norm homomorphisms are natural on all actual relative tests. -/
theorem normPoints_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    normPoints b e T' (a ≫ x) = a ≫ normPoints b e T x := by
  apply (Gm.pointsEquiv (base k) T').injective
  rw [pointsEquiv_normPoints, Gm.pointsEquiv_naturality, pointsEquiv_normPoints,
    pointsEquiv_naturality]
  exact Langlands.ReducedNorm.normFromGaloisUnits_naturality b e
    ((algΓ (CommRingCat.of k)).map a).unop.hom _

/-- The actual group-scheme character given by the descended determinant polynomial. -/
def norm : groupScheme b ⟶ (Gm (base k)).toGrp :=
  homOfPoints (normPoints b e) (normPoints_naturality b e)

/-- On every test, the actual character is the existing polynomial norm on tensor units. -/
theorem norm_points (T : Over (base k)) (x : T ⟶ (groupScheme b).X) :
    Gm.pointsEquiv (base k) T (x ≫ (norm b e).hom.hom) =
      Langlands.ReducedNorm.normFromGaloisUnits b e
        ((algΓ (CommRingCat.of k)).obj T).unop (pointsEquiv b T x) := by
  rw [norm, comp_homOfPoints, pointsEquiv_normPoints]

/-- The same actual character recovers the polynomial norm on every affine coefficient algebra. -/
theorem norm_affine_points (R : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (groupScheme b).X) :
    Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op R)).hom
        (x ≫ (norm b e).hom.hom) =
      Langlands.ReducedNorm.normFromGaloisUnits b e R (affinePointsEquiv b R x) := by
  have h := norm_points b e ((algSpec (CommRingCat.of k)).obj (op R)) x
  have hm := congrArg
    (Units.map (Corepresented.affineSectionsIso R).hom.hom.toMonoidHom) h
  rw [← Langlands.ReducedNorm.normFromGaloisUnits_naturality] at hm
  have hx := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor k A) (corepresentableBy b) R x
  change Units.map
      (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).hom.hom
        (AlgHom.id k A)).toMonoidHom
      (pointsEquiv b ((algSpec (CommRingCat.of k)).obj (op R)) x) =
    affinePointsEquiv b R x at hx
  rw [hx] at hm
  apply Units.ext
  have hv := congrArg Units.val hm
  erw [Gm.affinePointsEquiv_val]
  change (Corepresented.affineSectionsIso R).hom.hom.toRingHom
      ((Gm.pointsEquiv (base k) ((algSpec (CommRingCat.of k)).obj (op R))
        (x ≫ (norm b e).hom.hom) :
          Γ(((algSpec (CommRingCat.of k)).obj (op R)).left, ⊤))) = _ at hv
  rw [Corepresented.affineSectionsIso_hom_ringHom] at hv
  exact hv

/-- The actual norm-one algebra group, as a group-scheme kernel. -/
def normOne : GroupScheme (base k) := kernel (norm b e)

/-- The actual inclusion of the polynomial norm-one kernel in the unit group. -/
def normOneι : normOne b e ⟶ groupScheme b := kernelι (norm b e)

/-- The actual norm-one inclusion is a closed immersion. -/
theorem normOne_isClosedSubgroup : IsClosedSubgroup (normOneι b e) :=
  inferInstanceAs (IsClosedImmersion (kernelι (norm b e)).hom.hom.left)

instance normOne_isAffine : IsAffine (normOne b e).X.left := by
  let : IsClosedImmersion (normOneι b e).hom.hom.left := normOne_isClosedSubgroup b e
  exact isAffine_of_isAffineHom (normOneι b e).hom.hom.left

instance normOne_locallyOfFiniteType : LocallyOfFiniteType (normOne b e).X.hom := by
  let : IsClosedImmersion (normOneι b e).hom.hom.left := normOne_isClosedSubgroup b e
  rw [← (normOneι b e).hom.hom.w]
  infer_instance

private def kernelModelEquiv {M N M' N' : Type*}
    [Group M] [Group N] [Group M'] [Group N']
    (f : M →* N) (f' : M' →* N') (eM : M ≃* M') (eN : N ≃* N')
    (h : ∀ x, eN (f x) = f' (eM x)) : f.ker ≃* f'.ker where
  toFun x := ⟨eM x, by
    change f' (eM x.val) = 1
    rw [← h, x.property, map_one]⟩
  invFun x := ⟨eM.symm x, by
    apply eN.injective
    rw [h, eM.apply_symm_apply, x.property, map_one]⟩
  left_inv x := Subtype.ext (eM.symm_apply_apply x)
  right_inv x := Subtype.ext (eM.apply_symm_apply x)
  map_mul' x y := Subtype.ext (eM.map_mul x y)

/-- The actual kernel points are exactly the existing polynomial norm-one tensor units. -/
def normOnePointsEquiv (T : Over (base k)) :
    (T ⟶ (normOne b e).X) ≃*
      Langlands.ReducedNorm.normFromGaloisOne b e
        ((algΓ (CommRingCat.of k)).obj T).unop :=
  (kernelPointsEquiv (norm b e) T).trans
    (kernelModelEquiv _ _ (pointsEquiv b T) (Gm.pointsEquiv (base k) T)
      (norm_points b e T))

/-- Affine points of the actual kernel recover the original polynomial norm-one group. -/
def normOneAffinePointsEquiv (R : CommAlgCat.{u} (CommRingCat.of k)) :
    ((algSpec (CommRingCat.of k)).obj (op R) ⟶ (normOne b e).X) ≃*
      Langlands.ReducedNorm.normFromGaloisOne b e R :=
  (kernelPointsEquiv (norm b e) ((algSpec (CommRingCat.of k)).obj (op R))).trans
    (kernelModelEquiv _ _ (affinePointsEquiv b R)
      (Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op R)).hom)
      (norm_affine_points b e R))

/-- Rational points of the actual kernel recover the base coefficient norm-one group. -/
def normOneRationalPointsEquiv :
    rationalPoints (normOne b e) ≃*
      Langlands.ReducedNorm.normFromGaloisOne b e k :=
  (GaloisPointComparison.rationalCoeffEquiv k (normOne b e)).trans
    (normOneAffinePointsEquiv b e (CommAlgCat.of (CommRingCat.of k) k))

@[simp] theorem normOneAffinePointsEquiv_val (R : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op R) ⟶ (normOne b e).X) :
    (normOneAffinePointsEquiv b e R x).val =
      affinePointsEquiv b R (x ≫ (normOneι b e).hom.hom) := rfl

/-- The rational comparison respects the actual inclusion into the algebra-unit group. -/
theorem normOneRationalPointsEquiv_val (x : rationalPoints (normOne b e)) :
    (normOneRationalPointsEquiv b e x).val =
      affinePointsEquiv b (CommAlgCat.of (CommRingCat.of k) k)
        (GaloisPointComparison.rationalCoeffEquiv k (groupScheme b)
          (rationalPoints.map (normOneι b e) x)) := by
  rw [GaloisPointComparison.rationalCoeffEquiv_map]
  rfl

@[simp] theorem normOnePointsEquiv_val (T : Over (base k))
    (x : T ⟶ (normOne b e).X) :
    (normOnePointsEquiv b e T x).val =
      pointsEquiv b T (x ≫ (normOneι b e).hom.hom) := rfl

/-- Actual test pullback on the existing tensor norm-one groups. -/
def normOneUnitsRestrict {T T' : Over (base k)} (a : T' ⟶ T) :
    Langlands.ReducedNorm.normFromGaloisOne b e
        ((algΓ (CommRingCat.of k)).obj T).unop →*
      Langlands.ReducedNorm.normFromGaloisOne b e
        ((algΓ (CommRingCat.of k)).obj T').unop where
  toFun x := ⟨Units.map (Algebra.TensorProduct.map
      ((algΓ (CommRingCat.of k)).map a).unop.hom (AlgHom.id k A)).toMonoidHom x, by
    change Langlands.ReducedNorm.normFromGaloisUnits b e _ (Units.map _ x.val) = 1
    rw [Langlands.ReducedNorm.normFromGaloisUnits_naturality, x.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

/-- The actual norm-one point comparison is natural on every relative test scheme. -/
theorem normOnePointsEquiv_naturality {T T' : Over (base k)} (a : T' ⟶ T)
    (x : T ⟶ (normOne b e).X) :
    normOnePointsEquiv b e T' (a ≫ x) =
      normOneUnitsRestrict b e a (normOnePointsEquiv b e T x) := by
  apply Subtype.ext
  change pointsEquiv b T' ((a ≫ x) ≫ (normOneι b e).hom.hom) = _
  rw [Category.assoc, pointsEquiv_naturality]
  rfl

end GaloisNorm

end Langlands.GroupScheme.FiniteAlgebraUnits
