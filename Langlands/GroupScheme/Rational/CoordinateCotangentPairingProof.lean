import Langlands.GroupScheme.Rational.CoordinateCotangentDualityProof
import Langlands.GroupScheme.Lie.ActionDifferential

/-! # The actual base-cotangent and Lie-kernel action pairing -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (A : Type u) [CommRing A] [Algebra k A]

/-- The actual identity augmentation makes the test algebra a coordinate module. -/
abbrev baseOriginAlgebra : Algebra (A ⊗[k] CharacterUnits.Coord G) A :=
  (baseAugmentation G A).toAlgebra

attribute [local instance] baseOriginAlgebra Lie.coordinateOriginAlgebra

instance baseOriginScalarTower : IsScalarTower A (A ⊗[k] CharacterUnits.Coord G) A :=
  IsScalarTower.of_algHom (baseAugmentation G A)

/-- Extend the actual dual-number point's coordinate map over A. -/
def baseKernelLift (X : Additive (lieKernel G A)) :
    A ⊗[k] CharacterUnits.Coord G →ₐ[A] DualNumber A :=
  AlgHom.liftEquiv k A (CharacterUnits.Coord G) (DualNumber A)
    (Lie.pointCoordinates G X.toMul.val)

@[simp] theorem baseKernelLift_tmul (X : Additive (lieKernel G A))
    (a : A) (c : CharacterUnits.Coord G) :
    baseKernelLift G A X (a ⊗ₜ[k] c) = a • Lie.pointCoordinates G X.toMul.val c := rfl

/-- Its constant part is precisely the tensor augmentation. -/
theorem baseKernelLift_fst (X : Additive (lieKernel G A)) :
    (TrivSqZeroExt.fstHom A A A).comp (baseKernelLift G A X) = baseAugmentation G A := by
  apply Algebra.TensorProduct.ext'
  intro a c
  change a * (Lie.pointCoordinates G X.toMul.val c).fst =
    a * Lie.pointCoordinates G (1 : Lie.AffinePoints G A) c
  congr 1
  have h := DFunLike.congr_fun (Lie.pointCoordinates_kernel G X.toMul) c
  rw [Lie.pointCoordinates_one]
  exact h

/-- The infinitesimal coefficient of the extended actual coordinate map. -/
def baseKernelDerivation (X : Additive (lieKernel G A)) :
    Derivation A (A ⊗[k] CharacterUnits.Coord G) A :=
  Lie.liftDerivation (baseKernelLift G A X) (baseKernelLift_fst G A X)

@[simp] theorem baseKernelDerivation_tmul (X : Additive (lieKernel G A))
    (a : A) (c : CharacterUnits.Coord G) :
    baseKernelDerivation G A X (a ⊗ₜ[k] c) =
      a * Lie.kernelDerivationEquiv G X.toMul c := rfl

/-- This construction is linear for the existing actual kernel module. -/
def baseKernelDerivationLinear : Additive (lieKernel G A) →ₗ[A]
    Derivation A (A ⊗[k] CharacterUnits.Coord G) A where
  toFun := baseKernelDerivation G A
  map_add' X Y := by
    apply Derivation.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a c =>
      simp only [baseKernelDerivation_tmul, Derivation.add_apply, toMul_add,
        Lie.kernelDerivationEquiv_mul, mul_add]
    | add x y hx hy => simp only [map_add, hx, hy, Derivation.add_apply]
  map_smul' a X := by
    apply Derivation.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b c =>
      simp only [baseKernelDerivation_tmul, Derivation.smul_apply, lieKernel_smul_toMul,
        Lie.kernelDerivationEquiv_scale, smul_eq_mul, RingHom.id_apply]
      ring
    | add x y hx hy => simp only [map_add, hx, hy, Derivation.smul_apply]

/-- Every A-linear first-order lift comes from an actual kernel point. -/
theorem baseKernelDerivationLinear_bijective :
    Function.Bijective (baseKernelDerivationLinear G A) := by
  constructor
  · intro X Y h
    apply (Lie.kernelDerivationLinearEquiv G).injective
    apply Derivation.ext
    intro c
    change Lie.kernelDerivationEquiv G X.toMul c = Lie.kernelDerivationEquiv G Y.toMul c
    have hh := DFunLike.congr_fun h (1 ⊗ₜ[k] c)
    simpa only [baseKernelDerivationLinear, LinearMap.coe_mk, AddHom.coe_mk,
      baseKernelDerivation_tmul, one_mul] using hh
  · intro d
    let f := (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (DualNumber A)).symm
      (Lie.derivationLift d)
    have hf : (TrivSqZeroExt.fstHom k A A).comp f =
        (Algebra.ofId k A).comp (Lie.coordinateOrigin G) := by
      ext c
      change baseAugmentation G A (1 ⊗ₜ[k] c) = _
      rw [baseAugmentation, evaluate_tmul, one_mul, Lie.pointCoordinates_one]
    let X : Additive (lieKernel G A) :=
      Additive.ofMul ((Lie.kernelCoordinates G).symm ⟨f, hf⟩)
    refine ⟨X, ?_⟩
    have hl : baseKernelLift G A X = Lie.derivationLift d := by
      change (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (DualNumber A))
        (Lie.pointCoordinates G ((Lie.kernelCoordinates G).symm ⟨f, hf⟩).val) = _
      have hc := congrArg Subtype.val ((Lie.kernelCoordinates G).apply_symm_apply ⟨f, hf⟩)
      change Lie.pointCoordinates G ((Lie.kernelCoordinates G).symm ⟨f, hf⟩).val = f at hc
      rw [hc]
      exact (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (DualNumber A)).apply_symm_apply _
    ext z
    change (baseKernelLift G A X z).snd = d z
    rw [hl]
    rfl

/-- The actual Lie kernel is the module of derivations of the actual tensor coordinates. -/
def kernelBaseDerivationEquiv : Additive (lieKernel G A) ≃ₗ[A]
    Derivation A (A ⊗[k] CharacterUnits.Coord G) A :=
  LinearEquiv.ofBijective (baseKernelDerivationLinear G A)
    (baseKernelDerivationLinear_bijective G A)

/-- The actual Lie kernel is dual to the actual base-changed augmentation cotangent. -/
def kernelBaseCotangentEquiv : Additive (lieKernel G A) ≃ₗ[A]
    Module.Dual A (BaseCotangent G A) :=
  (kernelBaseDerivationEquiv G A).trans
    (AugmentedAlgebra.duality (baseAugmentation G A) (fun _ => rfl))

@[simp] theorem kernelBaseCotangentEquiv_mk (X : Additive (lieKernel G A))
    (f : baseAugmentationIdeal G A) :
    kernelBaseCotangentEquiv G A X ((baseAugmentationIdeal G A).toCotangent f) =
      (baseKernelLift G A X f.val).snd := rfl

@[simp] theorem kernelBaseCotangentEquiv_baseChange (X : Additive (lieKernel G A))
    (f : augmentation G) :
    kernelBaseCotangentEquiv G A X (cotangentBaseChange (cotangentMk G f)) =
      Lie.kernelDerivationEquiv G X.toMul f.val := by
  change 1 * Lie.kernelDerivationEquiv G X.toMul f.val = _
  exact one_mul _


variable {G A}

/-- The extended actual point sends coefficient elements to constant dual numbers. -/
theorem baseKernelLift_coefficients (X : Additive (lieKernel G A)) :
    ((baseKernelLift G A X).restrictScalars k).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] CharacterUnits.Coord G) =
      TrivSqZeroExt.inlAlgHom k A A := by
  apply AlgHom.ext
  intro a
  exact (baseKernelLift G A X).commutes a

/-- Evaluation of coordinate pullback at an actual dual-number kernel point. -/
theorem baseKernelLift_actionCoordinates
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (s : Lie.AffinePoints S.toGrp A)
    (X : Additive (lieKernel G A)) :
    ((baseKernelLift G A X).restrictScalars k).comp (actionCoordinates b s) =
      Lie.pointCoordinates G (b.act (Lie.constant S.toGrp s) X.toMul.val) := by
  unfold actionCoordinates
  rw [← Lie.pointCoordinates_naturality G ((baseKernelLift G A X).restrictScalars k),
    RelativeRoot.act_affineMap]
  have hs : Lie.affineMap S.toGrp ((baseKernelLift G A X).restrictScalars k)
      (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s) =
      Lie.constant S.toGrp s := by
    rw [← Lie.affineMap_comp, baseKernelLift_coefficients]
    rfl
  have hg : Lie.affineMap G ((baseKernelLift G A X).restrictScalars k)
      ((Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight) = X.toMul.val := by
    apply (Lie.pointCoordinates G).injective
    rw [Lie.pointCoordinates_naturality, Equiv.apply_symm_apply]
    exact (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (DualNumber A)).symm_apply_apply _
  rw [hs, hg]

/-- Actual kernel action is transpose to the direct coordinate pullback. -/
theorem baseKernelLift_action
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (s : Lie.AffinePoints S.toGrp A)
    (X : Additive (lieKernel G A)) :
    baseKernelLift G A (b.differential s X) =
      (baseKernelLift G A X).comp (actionPullback b s) := by
  apply Algebra.TensorProduct.ext_ring
  rw [show ((baseKernelLift G A (b.differential s X)).restrictScalars k).comp
      Algebra.TensorProduct.includeRight =
      Lie.pointCoordinates G (b.differential s X).toMul.val from
    (AlgHom.liftEquiv k A (CharacterUnits.Coord G) (DualNumber A)).symm_apply_apply _]
  change Lie.pointCoordinates G (b.differential s X).toMul.val =
    ((baseKernelLift G A X).restrictScalars k).comp
      (((actionPullback b s).restrictScalars k).comp Algebra.TensorProduct.includeRight)
  rw [actionPullback_coordinates, baseKernelLift_actionCoordinates]
  rfl

/-- The transpose formula holds on every class of the actual base cotangent. -/
theorem kernelBaseCotangentEquiv_action
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (s : Lie.AffinePoints S.toGrp A)
    (X : Additive (lieKernel G A)) (q : BaseCotangent G A) :
    kernelBaseCotangentEquiv G A (b.differential s X) q =
      kernelBaseCotangentEquiv G A X (cotangentAction b s q) := by
  obtain ⟨f, rfl⟩ := (baseAugmentationIdeal G A).toCotangent_surjective q
  change (baseKernelLift G A (b.differential s X) f.val).snd =
    (baseKernelLift G A X (actionPullback b s f.val)).snd
  rw [baseKernelLift_action, AlgHom.comp_apply]

/-- The second exact comparison, including its prescribed actual acted point. -/
theorem cotangentActionPairing : CotangentActionPairingStatement.{u} := by
  intro k _ G hAff
  let := hAff
  intro A _ _
  refine ⟨kernelBaseCotangentEquiv G A, kernelBaseCotangentEquiv_baseChange G A, ?_⟩
  intro S b s X
  exact ⟨b.differential s X, rfl, kernelBaseCotangentEquiv_action b s X⟩

end Langlands.GroupScheme.CoordinateWeights
