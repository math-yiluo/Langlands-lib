import Langlands.GroupScheme.Rational.ClassFunctionsBaseChangeStatement
import Langlands.GroupScheme.Lie.BaseChange
import Mathlib.RingTheory.Flat.Equalizer

/-! # Field base change for the actual class-function algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.ClassFunctions

namespace BaseChange

variable (K F : Type u) [Field K] [Field F] [Algebra K F]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap K F
local notation "GF" => Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

/-- The tensor coordinate presentation as an isomorphism over the new field. -/
def presentation :
    (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (F ⊗[K] Coord G))) ≅ (GF).X :=
  Over.isoMk (Descent.TensorCoordinates.baseChangeIso K F (Coord G) G.X
    (Lie.coordinateIso G)) (by
      exact Descent.TensorCoordinates.baseChangeIso_hom_snd K F (Coord G) G.X
        (Lie.coordinateIso G))

/-- The canonical comparison with the fixed coordinates of the actual pullback. -/
def coordinates : (F ⊗[K] Coord G) ≃ₐ[F] Coord GF :=
  CommAlgCat.algEquivOfIso
    (algSpec.fullyFaithful.preimageIso
      (Lie.coordinateIso GF ≪≫ (presentation K F G).symm)).unop

theorem coordinates_spec :
    (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (coordinates K F G).toAlgHom).op ≫
      (presentation K F G).hom = (Lie.coordinateIso GF).hom := by
  change (algSpec (CommRingCat.of F)).map
      (algSpec.fullyFaithful.preimage
        ((Lie.coordinateIso GF).hom ≫ (presentation K F G).inv)) ≫
      (presentation K F G).hom = _
  rw [algSpec.fullyFaithful.map_preimage]
  simp

theorem coordinates_spec_left :
    Spec.map (CommRingCat.ofHom (coordinates K F G).toRingHom) ≫
      (Descent.TensorCoordinates.baseChangeIso K F (Coord G) G.X
        (Lie.coordinateIso G)).hom = (Lie.coordinateIso GF).hom.left :=
  congrArg (fun f => f.left) (coordinates_spec K F G)

local instance : Algebra K (Coord GF) := Algebra.compHom _ (algebraMap K F)
local instance : IsScalarTower K F (Coord GF) := .of_algebraMap_eq' rfl

/-- Restriction of original coordinates to the actual base change. -/
def restriction : Coord G →ₐ[K] Coord GF :=
  ((coordinates K F G).toAlgHom.restrictScalars K).comp
    Algebra.TensorProduct.includeRight

theorem restriction_spec :
    Spec.map (CommRingCat.ofHom (restriction K F G).toRingHom) ≫
      (Lie.coordinateIso G).hom.left =
      (Lie.coordinateIso GF).hom.left ≫ pullback.fst G.X.hom b := by
  have h := congrArg (fun f => f ≫ pullback.fst G.X.hom b)
    (coordinates_spec_left K F G)
  rw [Category.assoc, Descent.TensorCoordinates.baseChangeIso_hom_fst] at h
  change Spec.map (CommRingCat.ofHom
      ((coordinates K F G).toRingHom.comp
        (Algebra.TensorProduct.includeRight : Coord G →ₐ[K] F ⊗[K] Coord G).toRingHom)) ≫
      (Lie.coordinateIso G).hom.left = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact h

variable (A : Type u) [CommRing A] [Algebra K A] [Algebra F A]
  [IsScalarTower K F A]

/-- Coordinate restriction is the actual pullback equivalence on every affine test. -/
theorem point_restriction (x : Lie.AffinePoints GF A) :
    Lie.pointCoordinates G (Lie.affineBaseChangeEquiv K F G A x) =
      ((Lie.pointCoordinates GF x).restrictScalars K).comp (restriction K F G) := by
  apply (Lie.pointCoordinates G).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left]
  change x.left ≫ pullback.fst G.X.hom b =
    Spec.map (CommRingCat.ofHom
      ((Lie.pointCoordinates GF x).toRingHom.comp
        (restriction K F G).toRingHom)) ≫ (Lie.coordinateIso G).hom.left
  erw [CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, restriction_spec K F G]
  rw [← Category.assoc]
  have hx := congrArg (fun f => f.left) ((Lie.pointCoordinates GF).symm_apply_apply x)
  exact congrArg (fun f => f ≫ pullback.fst G.X.hom b) hx.symm

local instance : Algebra K (Coord GF ⊗[F] Coord GF) :=
  Algebra.compHom _ (algebraMap K F)
local instance : IsScalarTower K F (Coord GF ⊗[F] Coord GF) :=
  .of_algebraMap_eq' rfl

/-- The tensor square of the ambient coordinate comparison. -/
def squareCoordinates :
    (F ⊗[K] (Coord G ⊗[K] Coord G)) ≃ₐ[F] (Coord GF ⊗[F] Coord GF) :=
  ((Algebra.TensorProduct.cancelBaseChange K F F (F ⊗[K] Coord G) (Coord G)).trans
    (Algebra.TensorProduct.assoc K K F F (Coord G) (Coord G))).symm.trans
      (Algebra.TensorProduct.congr (coordinates K F G) (coordinates K F G))

theorem squareCoordinates_tmul (c : F) (a d : Coord G) :
    squareCoordinates K F G (c ⊗ₜ[K] (a ⊗ₜ[K] d)) =
      coordinates K F G (c ⊗ₜ[K] a) ⊗ₜ[F]
        coordinates K F G (1 ⊗ₜ[K] d) := by
  simp [squareCoordinates]

/-- The tensor-square comparison evaluates at the two actual restricted universal points. -/
theorem square_restriction :
    ((squareCoordinates K F G).toAlgHom.restrictScalars K).comp
        Algebra.TensorProduct.includeRight =
      tensorEvaluation G
        (Lie.affineBaseChangeEquiv K F G _ (leftPoint GF))
        (Lie.affineBaseChangeEquiv K F G _ (rightPoint GF)) := by
  apply Algebra.TensorProduct.ext <;> apply AlgHom.ext <;> intro a <;>
    simp [AlgHom.comp_apply, squareCoordinates_tmul, tensorEvaluation,
      point_restriction K F G, leftPoint, rightPoint, restriction, includeLeft,
      includeRight, ← Algebra.TensorProduct.one_def]

/-- Conjugation pullback commutes with the ambient tensor comparison. -/
theorem conjugation_coordinates :
    (squareCoordinates K F G).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id F F) (conjugationPullback G)) =
      (conjugationPullback GF).comp (coordinates K F G).toAlgHom := by
  have h :
      (((squareCoordinates K F G).toAlgHom.restrictScalars K).comp
        Algebra.TensorProduct.includeRight).comp (conjugationPullback G) =
      ((conjugationPullback GF).restrictScalars K).comp (restriction K F G) := by
    rw [square_restriction, evaluate_conjugationPullback]
    rw [← map_inv, ← map_mul, ← map_mul, point_restriction K F G]
    rfl
  ext a
  exact DFunLike.congr_fun h a

/-- Projection to the conjugated factor commutes with the same comparison. -/
theorem right_coordinates :
    (squareCoordinates K F G).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id F F) (includeRight G)) =
      (includeRight GF).comp (coordinates K F G).toAlgHom := by
  ext a
  simp [includeRight, squareCoordinates_tmul, ← Algebra.TensorProduct.one_def]

/-- The equalizer of the two scalar-extended coordinate maps. -/
def tensorAlgebra : Subalgebra F (F ⊗[K] Coord G) :=
  AlgHom.equalizer
    (Algebra.TensorProduct.map (AlgHom.id F F) (conjugationPullback G))
    (Algebra.TensorProduct.map (AlgHom.id F F) (includeRight G))

theorem mem_tensorAlgebra (x : F ⊗[K] Coord G) :
    x ∈ tensorAlgebra K F G ↔ coordinates K F G x ∈ algebra GF := by
  change _ = _ ↔ _ = _
  rw [← (squareCoordinates K F G).injective.eq_iff]
  change ((squareCoordinates K F G).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id F F) (conjugationPullback G))) x =
    ((squareCoordinates K F G).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id F F) (includeRight G))) x ↔ _
  rw [conjugation_coordinates, right_coordinates]
  rfl

/-- Transport of the scalar-extended equalizer to the actual invariant subalgebra. -/
def equalizerCoordinates : tensorAlgebra K F G ≃ₐ[F] algebra GF where
  toFun x := ⟨coordinates K F G x, (mem_tensorAlgebra K F G x).mp x.property⟩
  invFun y := ⟨(coordinates K F G).symm y,
    (mem_tensorAlgebra K F G _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext ((coordinates K F G).symm_apply_apply x)
  right_inv y := Subtype.ext ((coordinates K F G).apply_symm_apply y)
  map_mul' x y := Subtype.ext ((coordinates K F G).map_mul x y)
  map_add' x y := Subtype.ext ((coordinates K F G).map_add x y)
  commutes' c := Subtype.ext ((coordinates K F G).commutes c)

/-- Flatness of the field extension identifies the actual class-function algebras. -/
def invariants : (F ⊗[K] algebra G) ≃ₐ[F] algebra GF :=
  (AlgHom.tensorEqualizerEquiv F F (conjugationPullback G) (includeRight G)).trans
    (equalizerCoordinates K F G)

theorem invariants_inclusion :
    (coordinates K F G).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id F F) (inclusion G)) =
      (inclusion GF).comp (invariants K F G).toAlgHom := by
  apply AlgHom.ext
  intro x
  change coordinates K F G
    (Algebra.TensorProduct.map (AlgHom.id F F) (inclusion G) x) =
      coordinates K F G
        (AlgHom.tensorEqualizerEquiv F F (conjugationPullback G) (includeRight G) x)
  rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]
  rfl

/-- The standard tensor-spectrum comparison, retaining its structure over `Spec F`. -/
def scalarSpec (D : Type u) [CommRing D] [Algebra K D] :
    (Over.pullback b).obj
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K D))) ≅
      (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (F ⊗[K] D))) :=
  Over.isoMk (HopfMorphismBaseChange.tensorSpecIso K F D) (by
    change (HopfMorphismBaseChange.tensorSpecIso K F D).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap F (F ⊗[K] D))) = _
    simp [HopfMorphismBaseChange.tensorSpecIso])

@[reassoc]
theorem scalarSpec_naturality {D E : Type u} [CommRing D] [CommRing E]
    [Algebra K D] [Algebra K E] (f : D →ₐ[K] E) :
    (Over.pullback b).map ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op) ≫
        (scalarSpec K F D).hom =
      (scalarSpec K F E).hom ≫ (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id F F) f)).op := by
  apply Over.OverMorphism.ext
  change Over.Hom.left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K F)))).map
        ((algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom f).op)) ≫
      (HopfMorphismBaseChange.tensorSpecIso K F D).hom =
    (HopfMorphismBaseChange.tensorSpecIso K F E).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id F F) f).toRingHom)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun g => g ≫ (HopfMorphismBaseChange.tensorSpecIso K F D).hom)
      (HopfMorphismBaseChange.tensorSpecIso_naturality (R := K) (S := F) f)

theorem presentation_eq :
    (presentation K F G).hom =
      (scalarSpec K F (Coord G)).inv ≫
        (Over.pullback b).map (Lie.coordinateIso G).hom := by
  apply Over.OverMorphism.ext
  rfl

/-- The comparison of the actual canonical affine class-function quotients. -/
def quotientComparison :
    (Over.pullback b).obj (quotient G) ≅ quotient GF :=
  scalarSpec K F (algebra G) ≪≫
    (algSpec (CommRingCat.of F)).mapIso
      (CommAlgCat.isoMk (invariants K F G).symm).op

theorem quotientComparison_left :
    (quotientComparison K F G).hom.left =
      (HopfMorphismBaseChange.tensorSpecIso K F (algebra G)).hom ≫
        Spec.map (CommRingCat.ofHom (invariants K F G).symm.toRingHom) := rfl

theorem quotientComparison_rho :
    (Over.pullback b).map (rho G) ≫ (quotientComparison K F G).hom = rho GF := by
  apply (cancel_epi (Lie.coordinateIso GF).hom).mp
  rw [coordinateIso_hom_rho]
  rw [← coordinates_spec K F G, Category.assoc, presentation_eq]
  simp only [rho, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id]
  simp only [(Over.pullback b).map_id, Category.id_comp]
  change (algSpec (CommRingCat.of F)).map
      (CommAlgCat.ofHom (coordinates K F G).toAlgHom).op ≫
    (scalarSpec K F (Coord G)).inv ≫
      (Over.pullback b).map ((algSpec (CommRingCat.of K)).map
        (CommAlgCat.ofHom (inclusion G)).op) ≫
      (scalarSpec K F (algebra G)).hom ≫
      (algSpec (CommRingCat.of F)).map
        (CommAlgCat.ofHom (invariants K F G).symm.toAlgHom).op = _
  rw [scalarSpec_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    ← CommAlgCat.ofHom_comp, ← CommAlgCat.ofHom_comp]
  congr 3
  rw [← AlgHom.comp_assoc, invariants_inclusion, AlgHom.comp_assoc]
  simp

end BaseChange

/-- Field extension preserves the actual canonical class-function algebra and quotient. -/
theorem fieldBaseChange : FieldBaseChangeStatement.{u} := by
  intro K F _ _ _ G _
  exact ⟨BaseChange.coordinates K F G, BaseChange.invariants K F G,
    BaseChange.quotientComparison K F G, BaseChange.coordinates_spec_left K F G,
    BaseChange.invariants_inclusion K F G, BaseChange.quotientComparison_left K F G,
    BaseChange.quotientComparison_rho K F G⟩

end Langlands.GroupScheme.ClassFunctions
