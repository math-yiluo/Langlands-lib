import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.MultiplicativeLaurent
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Weights

/-! # Actual Lie kernels in a whole-torus centralizer -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- Evaluation of the infinitesimal parameter at a specified square-zero element. -/
def dualNumberEvaluation (c : A) (hc : c * c = 0) : DualNumber A →ₐ[R] A :=
  DualNumber.lift ⟨(AlgHom.id R A, c), hc, fun _ => Commute.all _ _⟩

@[simp] theorem dualNumberEvaluation_inl (c : A) (hc : c * c = 0) (a : A) :
    dualNumberEvaluation (R := R) c hc (TrivSqZeroExt.inl a) = a := by
  simp [dualNumberEvaluation]

@[simp] theorem dualNumberEvaluation_eps (c : A) (hc : c * c = 0) :
    dualNumberEvaluation (R := R) c hc DualNumber.eps = c := by
  simp [dualNumberEvaluation]

/-- Any map from base dual numbers factors through coefficient extension and evaluation. -/
theorem dualNumberEvaluation_factor (f : DualNumber R →ₐ[R] A) :
    (dualNumberEvaluation (f DualNumber.eps) (by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero])).comp
        (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) = f := by
  apply DualNumber.algHom_ext
  simp [AlgHom.comp_apply, GeneralLinear.DualNumber.coefficientAlgMap,
    GeneralLinear.DualNumber.coefficientMap_eps]

variable (G : GroupScheme (Spec R))

@[simp] theorem affineMap_dualNumberEvaluation_constant (c : A) (hc : c * c = 0)
    (g : AffinePoints G A) :
    affineMap G (dualNumberEvaluation c hc) (constant G g) = g := by
  rw [constant, ← affineMap_comp]
  have he : (dualNumberEvaluation (R := R) c hc).comp
      (TrivSqZeroExt.inlAlgHom R A A) = AlgHom.id R A := by
    ext a
    exact dualNumberEvaluation_inl c hc a
  rw [he, affineMap_id]

/-- Factor a map to an affine group scheme through the relative affinization unit. -/
def affinizationFactor [IsAffineHom G.X.hom] {V : Over (Spec R)} (x : V ⟶ G.X) :
    (algSpec R).obj ((algΓ R).obj V) ⟶ G.X :=
  (algSpec R).map
    (((algΓAlgSpecAdjunction R).homEquiv V (op (coordinateAlgebra G))).symm
      (x ≫ (coordinateIso G).inv)) ≫ (coordinateIso G).hom

@[simp] theorem unit_affinizationFactor [IsAffineHom G.X.hom]
    {V : Over (Spec R)} (x : V ⟶ G.X) :
    (algΓAlgSpecAdjunction R).unit.app V ≫ affinizationFactor G x = x := by
  rw [affinizationFactor, ← Category.assoc]
  change ((algΓAlgSpecAdjunction R).homEquiv V (op (coordinateAlgebra G))
    (((algΓAlgSpecAdjunction R).homEquiv V (op (coordinateAlgebra G))).symm
      (x ≫ (coordinateIso G).inv))) ≫ (coordinateIso G).hom = x
  rw [Equiv.apply_symm_apply]
  simp

@[simp] theorem characterValue_zero {T : CommGroupScheme (Spec R)}
    (t : AffinePoints T.toGrp A) : characterValue (0 : characterLattice T) t = 1 := by
  unfold characterValue
  rw [comp_groupHom_zero]
  exact map_one _

variable {G} {T : CommGroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- Centralizing on all test schemes implies zero adjoint weight. -/
theorem mem_weightSpace_zero_of_mem_torusCentralizer (i : T.toGrp ⟶ G)
    (X : lieKernel G R)
    (hX : X.val ∈ (torusCentralizer i).carrier
      ((algSpec R).obj (op (CommAlgCat.of R (DualNumber R))))) :
    Additive.ofMul X ∈ weightSpace i 0 := by
  intro A _ _ t
  rw [characterValue_zero, Units.val_one, one_smul]
  apply Additive.toMul.injective
  apply Subtype.ext
  change constant G (t ≫ i.hom.hom) *
      affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) X.val *
        (constant G (t ≫ i.hom.hom))⁻¹ =
      affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) X.val
  have h := hX _ ((algSpec R).map
    (CommAlgCat.ofHom (GeneralLinear.DualNumber.coefficientAlgMap
      (Algebra.ofId R A))).op) (constant T.toGrp t)
  change Commute (affineMap G
      (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) X.val)
      (constant T.toGrp t ≫ i.hom.hom) at h
  have he : constant T.toGrp t ≫ i.hom.hom = constant G (t ≫ i.hom.hom) :=
    Category.assoc _ _ _
  rw [he] at h
  rw [h.symm.eq, mul_inv_cancel_right]

/-- A weight-zero vector commutes after any algebra map out of base dual numbers. -/
theorem commute_of_mem_weightSpace_zero (i : T.toGrp ⟶ G)
    (X : lieKernel G R) (hX : Additive.ofMul X ∈ weightSpace i 0)
    (f : DualNumber R →ₐ[R] A) (t : AffinePoints T.toGrp A) :
    Commute (affineMap G f X.val) (t ≫ i.hom.hom) := by
  have h := hX A t
  rw [characterValue_zero, Units.val_one, one_smul] at h
  have hp := congrArg (fun z : Additive (lieKernel G A) => z.toMul.val) h
  change constant G (t ≫ i.hom.hom) *
      affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) X.val *
        (constant G (t ≫ i.hom.hom))⁻¹ =
      affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) X.val at hp
  have hc : Commute
      (affineMap G (GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)) X.val)
      (constant G (t ≫ i.hom.hom)) :=
    ((mul_inv_eq_iff_eq_mul).mp hp).symm
  have he := hc.map (affineMap G (dualNumberEvaluation (f DualNumber.eps) (by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero])))
  simpa only [← affineMap_comp, dualNumberEvaluation_factor,
    affineMap_dualNumberEvaluation_constant] using he

/-- Zero adjoint weight implies commutation on every test scheme when the acting group
is affine. -/
theorem mem_torusCentralizer_of_mem_weightSpace_zero [IsAffineHom T.toGrp.X.hom]
    (i : T.toGrp ⟶ G) (X : lieKernel G R)
    (hX : Additive.ofMul X ∈ weightSpace i 0) :
    X.val ∈ (torusCentralizer i).carrier
      ((algSpec R).obj (op (CommAlgCat.of R (DualNumber R)))) := by
  intro V a t
  let B : CommAlgCat R := unop ((algΓ R).obj V)
  let f : DualNumber R →ₐ[R] B :=
    (((algΓAlgSpecAdjunction R).homEquiv V
      (op (CommAlgCat.of R (DualNumber R)))).symm a).unop.hom
  have ha : (algΓAlgSpecAdjunction R).unit.app V ≫
      (algSpec R).map (CommAlgCat.ofHom f).op = a :=
    ((algΓAlgSpecAdjunction R).homEquiv V
      (op (CommAlgCat.of R (DualNumber R)))).apply_symm_apply a
  have hc := commute_of_mem_weightSpace_zero i X hX f (affinizationFactor T.toGrp t)
  have hp := congrArg (fun q => (algΓAlgSpecAdjunction R).unit.app V ≫ q) hc.eq
  change (a ≫ X.val) * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * (a ≫ X.val)
  simpa only [MonObj.comp_mul, affineMap_apply, ← Category.assoc, ha,
    unit_affinizationFactor] using hp

/-- The actual Lie kernel in the whole-group centralizer is its zero adjoint weight space. -/
theorem mem_torusCentralizer_iff_mem_weightSpace_zero [IsAffineHom T.toGrp.X.hom]
    (i : T.toGrp ⟶ G) (X : lieKernel G R) :
    X.val ∈ (torusCentralizer i).carrier
      ((algSpec R).obj (op (CommAlgCat.of R (DualNumber R)))) ↔
    Additive.ofMul X ∈ weightSpace i 0 :=
  ⟨mem_weightSpace_zero_of_mem_torusCentralizer i X,
    mem_torusCentralizer_of_mem_weightSpace_zero i X⟩

/-- The submodule of actual Lie vectors lying in the whole-group centralizer on all tests. -/
def torusCentralizerLie [IsAffineHom T.toGrp.X.hom] (i : T.toGrp ⟶ G) :
    Submodule R (Additive (lieKernel G R)) :=
  (weightSpace i 0).copy
    {X | X.toMul.val ∈ (torusCentralizer i).carrier
      ((algSpec R).obj (op (CommAlgCat.of R (DualNumber R))))}
    (by
      ext X
      exact mem_torusCentralizer_iff_mem_weightSpace_zero i X.toMul)

theorem mem_torusCentralizerLie [IsAffineHom T.toGrp.X.hom]
    (i : T.toGrp ⟶ G) (X : Additive (lieKernel G R)) :
    X ∈ torusCentralizerLie i ↔
      X.toMul.val ∈ (torusCentralizer i).carrier
        ((algSpec R).obj (op (CommAlgCat.of R (DualNumber R)))) :=
  Iff.rfl

@[simp] theorem torusCentralizerLie_eq_weightSpace_zero [IsAffineHom T.toGrp.X.hom]
    (i : T.toGrp ⟶ G) :
    torusCentralizerLie i = weightSpace i 0 := by
  apply Submodule.ext
  intro X
  exact mem_torusCentralizer_iff_mem_weightSpace_zero i X.toMul

/-- The centralizer clause of the dynamic Lie comparison holds over any commutative base. -/
theorem mem_dynamicCentralizer_iff_mem_weightSpace_zero
    (χ : (Gm (Spec R)).toGrp ⟶ G) (X : lieKernel G R) :
    X.val ∈ (Dynamic.centralizer χ).carrier
      ((algSpec R).obj (op (CommAlgCat.of R (DualNumber R)))) ↔
    Additive.ofMul X ∈ weightSpace χ (Gm.powerHom (Spec R) 0) := by
  have : IsAffine (Gm.relativeLaurent R).left := by
    dsimp [Gm.relativeLaurent]
    infer_instance
  have : IsAffine (Gm (Spec R)).X.left :=
    IsAffine.of_isIso (Gm.relativeLaurentIso R).hom.left
  rw [map_zero, ← torusCentralizer_gm_eq_dynamicCentralizer]
  exact mem_torusCentralizer_iff_mem_weightSpace_zero χ X

end Langlands.GroupScheme.Lie
