import Langlands.GroupScheme.Rational.PolynomialFiniteFieldDescent
import Langlands.GroupScheme.Rational.PolynomialNormTangent

/-! # Finite descent of additive polynomial points and nonzero tangents -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.PolynomialPoint

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    {L : Type u} [Field L] [Algebra k L]

/-- Universal additivity with an extension coefficient field and the original target. -/
def IsAdditiveOver (x : Lie.AffinePoints G (MvPolynomial (Fin n) L)) : Prop :=
  Lie.affineMap G (substituteAlg k L
      (fun i => X (Sum.inl i) + X (Sum.inr i))) x =
    Lie.affineMap G (substituteAlg k L (fun i => X (Sum.inl i))) x *
      Lie.affineMap G (substituteAlg k L (fun i => X (Sum.inr i))) x

/-- Coefficient extension commutes with substitution of base-field polynomials. -/
theorem mapCoefficients_substitute {M : Type u} [Field M] [Algebra k M]
    (f : L →ₐ[k] M) {I J : Type} (v : I → MvPolynomial J k)
    (x : Lie.AffinePoints G (MvPolynomial I L)) :
    Lie.affineMap G (substituteAlg k M v) (mapCoefficients (G := G) f x) =
      mapCoefficients (G := G) f (Lie.affineMap G (substituteAlg k L v) x) := by
  change Lie.affineMap G (substituteAlg k M v)
      (Lie.affineMap G (MvPolynomial.mapAlgHom f) x) =
    Lie.affineMap G (MvPolynomial.mapAlgHom f)
      (Lie.affineMap G (substituteAlg k L v) x)
  rw [← Lie.affineMap_comp, ← Lie.affineMap_comp, substituteAlg_map]

/-- Injective coefficient extension reflects and preserves universal additivity. -/
theorem isAdditiveOver_mapCoefficients_iff [IsAffine G.X.left]
    {M : Type u} [Field M] [Algebra k M] (f : L →ₐ[k] M)
    (x : Lie.AffinePoints G (MvPolynomial (Fin n) L)) :
    IsAdditiveOver (mapCoefficients (G := G) f x) ↔ IsAdditiveOver x := by
  unfold IsAdditiveOver
  rw [mapCoefficients_substitute, mapCoefficients_substitute,
    mapCoefficients_substitute, ← map_mul]
  exact (CocharacterDatum.affineMap_injective (MvPolynomial.mapAlgHom f)
    (MvPolynomial.map_injective _ f.injective)).eq_iff

variable (k L G)
local notation "G_L" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

/-- The affine base-change comparison identifies the two universal additive identities. -/
theorem isAdditiveOver_affineBaseChangeEquiv_iff
    (x : Lie.AffinePoints G_L (MvPolynomial (Fin n) L)) :
    IsAdditiveOver (Lie.affineBaseChangeEquiv k L G _ x) ↔ IsAdditive x := by
  unfold IsAdditiveOver
  rw [affineBaseChangeEquiv_substitute, affineBaseChangeEquiv_substitute,
    affineBaseChangeEquiv_substitute, ← map_mul]
  rw [(Lie.affineBaseChangeEquiv k L G _).injective.eq_iff]
  unfold IsAdditive evaluate
  simp only [MvPolynomial.mapAlgHom_apply, map_add, map_X]

/-- Recover an actual extension-field vector homomorphism from the additive identity. -/
def homOfAdditiveOver (x : Lie.AffinePoints G (MvPolynomial (Fin n) L))
    (hx : IsAdditiveOver x) : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L :=
  homOfAdditive ((Lie.affineBaseChangeEquiv k L G _).symm x)
    ((isAdditiveOver_affineBaseChangeEquiv_iff (k := k) (L := L) (G := G) _).mp (by simpa using hx))

/-- The recovered homomorphism has exactly the original polynomial point. -/
theorem homOfAdditiveOver_extension
    (x : Lie.AffinePoints G (MvPolynomial (Fin n) L)) (hx : IsAdditiveOver x) :
    Lie.affineBaseChangeEquiv k L G _ (homOfAdditiveOver (k := k) (L := L) (G := G) x hx).hom.hom = x := by
  rw [homOfAdditiveOver, homOfAdditive_hom, MulEquiv.apply_symm_apply]

/-- A homomorphism over the extension gives the additive identity in the original group. -/
theorem isAdditiveOver_hom
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) :
    IsAdditiveOver (Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L) f.hom.hom) :=
  (isAdditiveOver_affineBaseChangeEquiv_iff (k := k) (L := L) (G := G) _).mpr (isAdditive_hom f)

/-- Evaluation at a base-field epsilon tuple is the actual input tangent. -/
theorem epsilonEvaluation_inputTangent
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) (v : Fin n → k) :
    Lie.affineMap G (epsilonEvaluation k L v)
        (Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L) f.hom.hom) =
      (inputTangent k L G f v).toMul.val := by
  rw [epsilonEvaluation, ← Lie.affineBaseChangeEquiv_naturality]
  apply congrArg (Lie.affineBaseChangeEquiv k L G (DualNumber L))
  exact (vectorTangent_comp f (fun i => algebraMap k L (v i))).symm

variable {k L G}

/-- A coefficient embedding commutes with evaluating a base-field epsilon direction. -/
theorem epsilonEvaluation_mapCoefficients {M : Type u} [Field M] [Algebra k M]
    (f : L →ₐ[k] M) (v : Fin n → k) :
    (epsilonEvaluation k M v).comp (MvPolynomial.mapAlgHom f) =
      (GeneralLinear.DualNumber.coefficientAlgMap (R := CommRingCat.of k) f).comp
        (epsilonEvaluation k L v) := by
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    apply TrivSqZeroExt.ext <;>
      simp [epsilonEvaluation, MvPolynomial.mapAlgHom_apply,
        GeneralLinear.DualNumber.coefficientAlgMap,
        GeneralLinear.DualNumber.coefficientMap, TrivSqZeroExt.algebraMap_eq_inl]
  · intro i
    apply TrivSqZeroExt.ext <;>
      simp [epsilonEvaluation, MvPolynomial.mapAlgHom_apply,
        GeneralLinear.DualNumber.coefficientAlgMap,
        GeneralLinear.DualNumber.coefficientMap]

/-- A nonidentity evaluated tangent remains nonidentity in any coefficient model. -/
theorem epsilonEvaluation_ne_one_of_mapCoefficients {M : Type u}
    [Field M] [Algebra k M] (f : L →ₐ[k] M) (v : Fin n → k)
    (x : Lie.AffinePoints G (MvPolynomial (Fin n) L))
    (hx : Lie.affineMap G (epsilonEvaluation k M v) (mapCoefficients (G := G) f x) ≠ 1) :
    Lie.affineMap G (epsilonEvaluation k L v) x ≠ 1 := by
  intro h
  apply hx
  change Lie.affineMap G (epsilonEvaluation k M v)
    (Lie.affineMap G (MvPolynomial.mapAlgHom f) x) = 1
  rw [← Lie.affineMap_comp, epsilonEvaluation_mapCoefficients,
    Lie.affineMap_comp, h, map_one]

variable (k L G)

/-- The polynomial point of an extension-field homomorphism, in the original
target group. -/
def polynomialOfHom
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) :
    Lie.AffinePoints G (MvPolynomial (Fin n) L) :=
  Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L) f.hom.hom

theorem epsilonEvaluation_polynomialOfHom
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) (v : Fin n → k) :
    Lie.affineMap G (epsilonEvaluation k L v)
      (polynomialOfHom (k := k) (L := L) (G := G) f) =
      (inputTangent k L G f v).toMul.val :=
  epsilonEvaluation_inputTangent (k := k) (L := L) (G := G) f v

/-- A finite Galois model retains an actual vector-group homomorphism and its
exact coefficient-extension equation. -/
structure FiniteGaloisHomModel
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) where
  field : FiniteGaloisIntermediateField k L
  hom : VectorGroup.groupScheme (CommRingCat.of field) n ⟶
    Functor.obj (GroupScheme.baseChange (algebraBaseMap k field)) G
  extension_eq : mapCoefficients (G := G) (I := Fin n) field.toIntermediateField.val
      (polynomialOfHom (k := k) (L := field) (G := G) hom) =
    polynomialOfHom (k := k) (L := L) (G := G) f

variable {k L G}

/-- Construct a finite Galois model by descending the polynomial point and
reflecting its universal additive identity. -/
def finiteGaloisHomModel [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsGalois k L]
    (f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L) :
    FiniteGaloisHomModel (k := k) (L := L) (G := G) f := by
  let D := finiteGaloisModel (Lie.affineBaseChangeEquiv k L G (MvPolynomial (Fin n) L) f.hom.hom)
  have hD : IsAdditiveOver D.point :=
    (isAdditiveOver_mapCoefficients_iff D.field.toIntermediateField.val D.point).mp
      (by rw [D.extension_eq]; exact isAdditiveOver_hom (k := k) (L := L) (G := G) f)
  refine ⟨D.field, homOfAdditiveOver (k := k) (L := D.field) (G := G) D.point hD, ?_⟩
  exact (congrArg (mapCoefficients (G := G) D.field.toIntermediateField.val)
    (homOfAdditiveOver_extension (k := k) (L := D.field) (G := G) D.point hD)).trans
      D.extension_eq

/-- A finite Galois homomorphism model preserves a nonzero tangent in the
same base-field coordinate direction. -/
theorem FiniteGaloisHomModel.inputTangent_ne_zero
    {f : VectorGroup.groupScheme (CommRingCat.of L) n ⟶ G_L}
    (D : FiniteGaloisHomModel (k := k) (L := L) (G := G) f) (v : Fin n → k)
    (hv : inputTangent k L G f v ≠ 0) :
    inputTangent k D.field G D.hom v ≠ 0 := by
  intro h
  have hmodel : Lie.affineMap G (epsilonEvaluation k D.field v)
      (polynomialOfHom (k := k) (L := D.field) (G := G) D.hom) = 1 := by
    rw [epsilonEvaluation_polynomialOfHom, h]
    rfl
  have horiginal : Lie.affineMap G (epsilonEvaluation k L v)
      (polynomialOfHom (k := k) (L := L) (G := G) f) = 1 := by
    rw [← D.extension_eq]
    change Lie.affineMap G (epsilonEvaluation k L v)
      (Lie.affineMap G (MvPolynomial.mapAlgHom D.field.toIntermediateField.val) _) = 1
    rw [← Lie.affineMap_comp, epsilonEvaluation_mapCoefficients,
      Lie.affineMap_comp, hmodel, map_one]
  apply hv
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (epsilonEvaluation_polynomialOfHom (k := k) (L := L) (G := G) f v).symm.trans horiginal

end Langlands.GroupScheme.PolynomialPoint
