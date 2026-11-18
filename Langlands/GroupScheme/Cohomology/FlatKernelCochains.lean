import Langlands.GroupScheme.Cohomology.FlatKernelActions
import Langlands.GroupScheme.Cohomology.SurjectiveBaseChange

/-! # Actual regular deformation cochains from flat kernel comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology

open Lie.NonaffineKernel Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) [IsAffineHom H.X.hom]

instance pairCoordinateAlgebra_flat [Flat H.X.hom] :
    Module.Flat R (pairCoordinateAlgebra H) := by
  change Module.Flat R (Lie.coordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)
  infer_instance

/-- The flat coordinate algebra of three independent source points. -/
abbrev tripleCoordinateAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (pairCoordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)

instance tripleCoordinateAlgebra_flat [Flat H.X.hom] :
    Module.Flat R (tripleCoordinateAlgebra H) := by
  change Module.Flat R (pairCoordinateAlgebra H ⊗[R] Lie.coordinateAlgebra H)
  infer_instance

def genericTripleFirst : H.affinePoints (tripleCoordinateAlgebra H) :=
  Lie.affineMap H Algebra.TensorProduct.includeLeft (genericFirst H)

def genericTripleSecond : H.affinePoints (tripleCoordinateAlgebra H) :=
  Lie.affineMap H Algebra.TensorProduct.includeLeft (genericSecond H)

def genericTripleThird : H.affinePoints (tripleCoordinateAlgebra H) :=
  Lie.affineMap H Algebra.TensorProduct.includeRight (genericPoint H)

def tripleSpecialization {A : CommAlgCat.{u} R} (h k l : H.affinePoints A) :
    tripleCoordinateAlgebra H ⟶ A :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift
    (pairSpecialization H h k).hom (pointSpecialization H l).hom (fun _ _ => Commute.all _ _))

@[simp]
theorem genericTripleFirst_specialize {A : CommAlgCat.{u} R} (h k l : H.affinePoints A) :
    H.affinePointMap (tripleSpecialization H h k l) (genericTripleFirst H) = h := by
  change Lie.affineMap H _ (Lie.affineMap H _ (genericFirst H)) = h
  rw [← Lie.affineMap_comp]
  change Lie.affineMap H
    ((Algebra.TensorProduct.lift (pairSpecialization H h k).hom (pointSpecialization H l).hom
      (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeLeft) (genericFirst H) = h
  rw [Algebra.TensorProduct.lift_comp_includeLeft]
  exact genericFirst_specialize H h k

@[simp]
theorem genericTripleSecond_specialize {A : CommAlgCat.{u} R} (h k l : H.affinePoints A) :
    H.affinePointMap (tripleSpecialization H h k l) (genericTripleSecond H) = k := by
  change Lie.affineMap H _ (Lie.affineMap H _ (genericSecond H)) = k
  rw [← Lie.affineMap_comp]
  change Lie.affineMap H
    ((Algebra.TensorProduct.lift (pairSpecialization H h k).hom (pointSpecialization H l).hom
      (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeLeft) (genericSecond H) = k
  rw [Algebra.TensorProduct.lift_comp_includeLeft]
  exact genericSecond_specialize H h k

@[simp]
theorem genericTripleThird_specialize {A : CommAlgCat.{u} R} (h k l : H.affinePoints A) :
    H.affinePointMap (tripleSpecialization H h k l) (genericTripleThird H) = l := by
  change Lie.affineMap H _ (Lie.affineMap H _ (genericPoint H)) = l
  rw [← Lie.affineMap_comp]
  change Lie.affineMap H
    ((Algebra.TensorProduct.lift (pairSpecialization H h k).hom (pointSpecialization H l).hom
      (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeRight) (genericPoint H) = l
  rw [Algebra.TensorProduct.lift_comp_includeRight']
  exact genericPoint_specialize H l

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Naturality extends a two-cocycle identity from flat tests to all tests of
a flat affine source, by specializing the flat independent generic triple. -/
theorem twoCocycle_of_flat [Flat H.X.hom] (ρ : ModuleRepresentation M H)
    (c : TwoCochain M H)
    (hc : ∀ (A : CommAlgCat.{u} R) [Module.Flat R A] (h k l : H.affinePoints A),
      c.value A h k + c.value A (h * k) l =
        ρ.action A h (c.value A k l) + c.value A h (k * l)) :
    c.IsCocycle ρ := by
  have ht := hc (tripleCoordinateAlgebra H) (genericTripleFirst H)
    (genericTripleSecond H) (genericTripleThird H)
  intro A h k l
  have he := congrArg (modulePointMap M (tripleSpecialization H h k l)) ht
  simpa only [map_add, c.naturality, ρ.naturality, map_mul,
    genericTripleFirst_specialize, genericTripleSecond_specialize,
    genericTripleThird_specialize] using he

/-- The same reduction for a regular one-cocycle uses the flat generic pair. -/
theorem oneCocycle_of_flat [Flat H.X.hom] (ρ : ModuleRepresentation M H)
    (c : OneCochain M H)
    (hc : ∀ (A : CommAlgCat.{u} R) [Module.Flat R A] (h k : H.affinePoints A),
      c.value A (h * k) = c.value A h + ρ.action A h (c.value A k)) :
    c.IsCocycle ρ :=
  (oneCocycle_iff_generic H M ρ c).mpr (hc _ _ _)

variable (G : GroupScheme (Spec R)) (I : Ideal R) [Fact (SqZero I)] [Smooth G.X.hom]
variable [Flat H.X.hom]
variable (s : H.X ⟶ G.X)
variable (s₀ : ∀ A : CommAlgCat.{u} R,
  H.affinePoints A →* Lie.AffinePoints G (A ⧸ I.map (algebraMap R A)))
variable (hs : ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
  reduction G (I.map (algebraMap R A)) (h ≫ s) = s₀ A h)

/-- The actual kernel-valued pointwise defect of the supplied regular lift. -/
abbrev liftDefectPoint (A : CommAlgCat.{u} R) (h k : H.affinePoints A) :
    Additive (Lie.NonaffineKernel.kernel G (I.map (algebraMap R A))) :=
  kernelDefect G (I.map (algebraMap R A)) (fun h => h ≫ s) (s₀ A) (hs A) h k

omit [IsAffineHom H.X.hom] [Flat H.X.hom] [Smooth G.X.hom] [Fact (SqZero I)] in
/-- Defect points commute with actual coefficient maps. -/
theorem liftDefectPoint_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (h k : H.affinePoints A) :
    kernelMapAdd G (I.map (algebraMap R A)) f.hom (map_le_map_extended I f.hom)
        (liftDefectPoint H G I s s₀ hs A h k) =
      liftDefectPoint H G I s s₀ hs B (H.affinePointMap f h) (H.affinePointMap f k) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [kernelMapAdd_val, liftDefectPoint, kernelDefect_val, map_mul, map_inv,
    Lie.affineMap_apply, affinePointMap_apply, Category.assoc,
    CommAlgCat.ofHom_hom]
  rw [← Category.assoc ((algSpec R).map f.op) (h * k) s, MonObj.comp_mul]

/-- The universal actual defect, transported to the pair-coordinate tensor,
defines a regular two-cochain on every affine test algebra. -/
def regularDefectCochain : TwoCochain (Additive (Lie.NonaffineKernel.kernel G I)) H :=
  twoCochainOfCoordinates H (Additive (Lie.NonaffineKernel.kernel G I))
    (flatKernelEquiv G I (pairCoordinateAlgebra H)
      (liftDefectPoint H G I s s₀ hs (pairCoordinateAlgebra H) (genericFirst H) (genericSecond H)))

/-- On every flat test the regular cochain is the actual multiplicativity
defect under the canonical kernel scalar-extension comparison. -/
theorem regularDefectCochain_flat (A : CommAlgCat.{u} R) [Module.Flat R A]
    (h k : H.affinePoints A) :
    (regularDefectCochain H G I s s₀ hs).value A h k =
      flatKernelEquiv G I A (liftDefectPoint H G I s s₀ hs A h k) := by
  change modulePointMap (Additive (Lie.NonaffineKernel.kernel G I)) (pairSpecialization H h k)
    (flatKernelEquiv G I (pairCoordinateAlgebra H)
      (liftDefectPoint H G I s s₀ hs _ (genericFirst H) (genericSecond H))) = _
  rw [flatComparison_naturality, liftDefectPoint_naturality,
    genericFirst_specialize, genericSecond_specialize]

/-- The actual regular defect is a two-cocycle for the regular coefficient
representation, including its values on nonflat test algebras. -/
theorem regularDefectCochain_isCocycle :
    (regularDefectCochain H G I s s₀ hs).IsCocycle
      (regularKernelRepresentation H G I s s₀ hs) := by
  apply twoCocycle_of_flat H (Additive (Lie.NonaffineKernel.kernel G I))
  intro A hA h k l
  simp only [regularDefectCochain_flat, regularKernelRepresentation_action]
  have he := congrArg (flatKernelEquiv G I A)
    (kernelDefect_cocycle G (I.map (algebraMap R A))
      (fun h => h ≫ s) (s₀ A) (hs A) h k l)
  simpa only [map_add, liftDefectPoint, flatConjugationAction, reductionLiftAction,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using he

/-- Vanishing on the quotient-base source supplies an actual regular
one-cochain primitive for the original defect. -/
theorem regularDefectCochain_isCoboundary
    (hH : HasVanishingLowDegreeCohomology
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H)) :
    (regularDefectCochain H G I s s₀ hs).IsCoboundary
      (regularKernelRepresentation H G I s s₀ hs) := by
  exact (SurjectiveBaseChange.lowDegreeCoboundaries_of_baseChange
    (CommAlgCat.of R (R ⧸ I)) Ideal.Quotient.mk_surjective hH
      (regularKernelRepresentation H G I s s₀ hs)).2 _
    (regularDefectCochain_isCocycle H G I s s₀ hs)

section Difference

variable (f f' : H ⟶ G)
variable (hf : ∀ (A : CommAlgCat.{u} R) (h : H.affinePoints A),
  reduction G (I.map (algebraMap R A)) (h ≫ f.hom.hom) =
    reduction G (I.map (algebraMap R A)) (h ≫ f'.hom.hom))

/-- The regular coefficient representation through an actual homomorphism. -/
def homKernelRepresentation : ModuleRepresentation (Additive (Lie.NonaffineKernel.kernel G I)) H :=
  regularKernelRepresentation H G I f.hom.hom
    (fun A => (reduction G (I.map (algebraMap R A))).comp (H.affinePointsTarget f A))
    (fun _ _ => rfl)

theorem homKernelRepresentation_action (A : CommAlgCat.{u} R) [Module.Flat R A]
    (h : H.affinePoints A) (x : ModulePoints (Additive (Lie.NonaffineKernel.kernel G I)) A) :
    (homKernelRepresentation H G I f).action A h x =
      flatConjugationAction G I A (h ≫ f.hom.hom) x :=
  regularKernelRepresentation_action H G I f.hom.hom _ _ A h x

/-- The pointwise actual reduction-kernel difference. -/
abbrev homDifferencePoint (A : CommAlgCat.{u} R) (h : H.affinePoints A) :
    Additive (Lie.NonaffineKernel.kernel G (I.map (algebraMap R A))) :=
  kernelDifference G (I.map (algebraMap R A))
    (H.affinePointsTarget f A) (H.affinePointsTarget f' A) (hf A) h

omit [IsAffineHom H.X.hom] [Flat H.X.hom] [Smooth G.X.hom] [Fact (SqZero I)] in
/-- Actual difference points commute with every coefficient map. -/
theorem homDifferencePoint_naturality {A B : CommAlgCat.{u} R} (q : A ⟶ B)
    (h : H.affinePoints A) :
    kernelMapAdd G (I.map (algebraMap R A)) q.hom (map_le_map_extended I q.hom)
        (homDifferencePoint H G I f f' hf A h) =
      homDifferencePoint H G I f f' hf B (H.affinePointMap q h) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [kernelMapAdd_val, homDifferencePoint, kernelDifference_val, map_mul, map_inv,
    Lie.affineMap_apply, affinePointMap_apply, affinePointsTarget_apply,
    Category.assoc, CommAlgCat.ofHom_hom]
  erw [H.affinePointsTarget_apply f' A h, H.affinePointsTarget_apply f A h]

/-- The actual universal difference determines a regular one-cochain. -/
def regularDifferenceCochain : OneCochain (Additive (Lie.NonaffineKernel.kernel G I)) H :=
  oneCochainOfCoordinates H (Additive (Lie.NonaffineKernel.kernel G I))
    (flatKernelEquiv G I (Lie.coordinateAlgebra H)
      (homDifferencePoint H G I f f' hf (Lie.coordinateAlgebra H) (genericPoint H)))

theorem regularDifferenceCochain_flat (A : CommAlgCat.{u} R) [Module.Flat R A]
    (h : H.affinePoints A) :
    (regularDifferenceCochain H G I f f' hf).value A h =
      flatKernelEquiv G I A (homDifferencePoint H G I f f' hf A h) := by
  change modulePointMap (Additive (Lie.NonaffineKernel.kernel G I)) (pointSpecialization H h)
    (flatKernelEquiv G I (Lie.coordinateAlgebra H)
      (homDifferencePoint H G I f f' hf _ (genericPoint H))) = _
  rw [flatComparison_naturality, homDifferencePoint_naturality, genericPoint_specialize]

/-- The actual regular difference is a one-cocycle on every affine test. -/
theorem regularDifferenceCochain_isCocycle :
    (regularDifferenceCochain H G I f f' hf).IsCocycle (homKernelRepresentation H G I f) := by
  apply oneCocycle_of_flat H (Additive (Lie.NonaffineKernel.kernel G I))
  intro A hA h k
  simp only [regularDifferenceCochain_flat, homKernelRepresentation_action]
  have he := congrArg (flatKernelEquiv G I A)
    (kernelDifference_cocycle G (I.map (algebraMap R A))
      (H.affinePointsTarget f A) (H.affinePointsTarget f' A) (hf A) h k)
  erw [H.affinePointsTarget_apply f A h] at he
  simpa only [map_add, homDifferencePoint, flatConjugationAction,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using he

/-- Quotient-base vanishing supplies an actual element of the original base
kernel as a regular one-coboundary primitive. -/
theorem regularDifferenceCochain_isCoboundary
    (hH : HasVanishingLowDegreeCohomology
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj H)) :
    (regularDifferenceCochain H G I f f' hf).IsCoboundary (homKernelRepresentation H G I f) := by
  exact (SurjectiveBaseChange.lowDegreeCoboundaries_of_baseChange
    (CommAlgCat.of R (R ⧸ I)) Ideal.Quotient.mk_surjective hH
      (homKernelRepresentation H G I f)).1 _
    (regularDifferenceCochain_isCocycle H G I f f' hf)

end Difference

end Langlands.GroupScheme.Cohomology
