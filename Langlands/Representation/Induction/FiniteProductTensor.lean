import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Tensor.Finite

/-! The pointwise external tensor map for finite products in smooth induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uI uG uV

variable {R : Type uR} [CommRing R] {ι : Type uI}
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable (P : ∀ i, Subgroup (G i)) (σ : ∀ i, Representation R (P i) (V i))

/-- Coordinate projection from the actual product subgroup to a factor subgroup. -/
def productSubgroupCoordinate (i : ι) : Subgroup.pi Set.univ P →* P i where
  toFun p := ⟨p.1 i, p.2 i (Set.mem_univ i)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The external tensor representation pulled back to the actual product subgroup. -/
def productInducing : Representation R (Subgroup.pi Set.univ P) (PiTensorProduct R V) :=
  (FiniteTensor.external σ).comp (MonoidHom.pi (productSubgroupCoordinate P))

@[simp]
theorem productInducing_tprod (p : Subgroup.pi Set.univ P) (v : ∀ i, V i) :
    productInducing P σ p (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i => σ i (productSubgroupCoordinate P i p) (v i)) :=
  FiniteTensor.external_tprod σ _ v

variable [∀ i, TopologicalSpace (G i)]

private def factorEval (i : ι) (g : G i) : SmoothFunctions (P i) (σ i) →ₗ[R] V i where
  toFun f := eval (P i) (σ i) f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pointwise pure tensor as a multilinear map into all functions on the product. -/
def pointwiseTensorFunctions :
    MultilinearMap R (fun i => SmoothFunctions (P i) (σ i))
      ((∀ i, G i) → PiTensorProduct R V) :=
  MultilinearMap.pi (fun g => (PiTensorProduct.tprod R).compLinearMap
    (fun i => factorEval P σ i (g i)))

@[simp]
theorem pointwiseTensorFunctions_apply
    (f : ∀ i, SmoothFunctions (P i) (σ i)) (g : ∀ i, G i) :
    pointwiseTensorFunctions P σ f g =
      PiTensorProduct.tprod R (fun i => eval (P i) (σ i) (f i) (g i)) := rfl

/-- Covariance of the pointwise pure product for the actual product subgroup. -/
theorem pointwiseTensorFunctions_covariant
    (f : ∀ i, SmoothFunctions (P i) (σ i))
    (p : Subgroup.pi Set.univ P) (g : ∀ i, G i) :
    pointwiseTensorFunctions P σ f ((p : ∀ i, G i) * g) =
      productInducing P σ p (pointwiseTensorFunctions P σ f g) := by
  rw [pointwiseTensorFunctions_apply, pointwiseTensorFunctions_apply, productInducing_tprod]
  congr 1
  funext i
  exact (f i).1.property (productSubgroupCoordinate P i p) (g i)

/-- One open subgroup fixes the whole pointwise pure product by right translation. -/
theorem pointwiseTensorFunctions_uniform [Finite ι]
    (f : ∀ i, SmoothFunctions (P i) (σ i)) :
    ∃ K : OpenSubgroup (∀ i, G i), ∀ (k : K) (g : ∀ i, G i),
      pointwiseTensorFunctions P σ f (g * (k : ∀ i, G i)) =
        pointwiseTensorFunctions P σ f g := by
  classical
  choose K hK using fun i => (f i).property
  let L : OpenSubgroup (∀ i, G i) :=
    ⟨Subgroup.pi Set.univ (fun i => (K i).toSubgroup),
      isOpen_set_pi Set.finite_univ (fun i _ => (K i).isOpen)⟩
  refine ⟨L, ?_⟩
  intro k g
  rw [pointwiseTensorFunctions_apply, pointwiseTensorFunctions_apply]
  congr 1
  funext i
  exact congrArg (fun F : EquivariantFunctions (P i) (σ i) => F.1 (g i))
    (hK i ⟨k.1 i, k.2 i (Set.mem_univ i)⟩)

private def pointwiseTensorCovariant :
    MultilinearMap R (fun i => SmoothFunctions (P i) (σ i))
      (EquivariantFunctions (Subgroup.pi Set.univ P) (productInducing P σ)) :=
  (pointwiseTensorFunctions P σ).codRestrict _
    (fun f => pointwiseTensorFunctions_covariant P σ f)

/-- The actual multilinear pointwise product with its intrinsic uniform smoothness. -/
def pointwiseTensorMultilinear [Finite ι] :
    MultilinearMap R (fun i => SmoothFunctions (P i) (σ i))
      (SmoothFunctions (Subgroup.pi Set.univ P) (productInducing P σ)) :=
  (pointwiseTensorCovariant P σ).codRestrict _ (by
    intro f
    obtain ⟨K, hK⟩ := pointwiseTensorFunctions_uniform P σ f
    refine ⟨K, ?_⟩
    intro k
    apply Subtype.ext
    exact funext (hK k))

@[simp]
theorem pointwiseTensorMultilinear_eval [Finite ι]
    (f : ∀ i, SmoothFunctions (P i) (σ i)) (g : ∀ i, G i) :
    eval (Subgroup.pi Set.univ P) (productInducing P σ)
      (pointwiseTensorMultilinear P σ f) g =
        PiTensorProduct.tprod R (fun i => eval (P i) (σ i) (f i) (g i)) := rfl

variable [∀ i, IsTopologicalGroup (G i)]

/-- The canonical pointwise finite external-tensor map in actual smooth induction. -/
def finiteProductTensorMap [Finite ι] :
    (FiniteTensor.external (fun i => smoothInduced (P i) (σ i))).IntertwiningMap
      (smoothInduced (Subgroup.pi Set.univ P) (productInducing P σ)) where
  toLinearMap := PiTensorProduct.lift (pointwiseTensorMultilinear P σ)
  isIntertwining' g := by
    ext f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      FiniteTensor.external_tprod, PiTensorProduct.lift.tprod]
    rfl

/-- Pure-tensor evaluation characterizes the canonical map pointwise. -/
@[simp]
theorem finiteProductTensorMap_tprod_eval [Finite ι]
    (f : ∀ i, SmoothFunctions (P i) (σ i)) (g : ∀ i, G i) :
    eval (Subgroup.pi Set.univ P) (productInducing P σ)
      (finiteProductTensorMap P σ (PiTensorProduct.tprod R f)) g =
        PiTensorProduct.tprod R (fun i => eval (P i) (σ i) (f i) (g i)) := by
  change eval _ _ (PiTensorProduct.lift (pointwiseTensorMultilinear P σ)
    (PiTensorProduct.tprod R f)) g = _
  rw [PiTensorProduct.lift.tprod]
  rfl

end Langlands.Induction
