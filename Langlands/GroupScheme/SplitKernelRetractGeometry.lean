import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.AbelianScheme.Kernel

/-! # Geometry of the kernel of a split homomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineRetractGeometry

variable {R : CommRingCat.{u}}

/-- A retract of a smooth affine algebra over a noetherian ring is smooth. -/
theorem smooth_algSpec_retract [IsNoetherianRing R] {A B : CommAlgCat.{u} R}
    [Smooth ((algSpec R).obj (op A)).hom]
    (i : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A))
    (r : (algSpec R).obj (op A) ⟶ (algSpec R).obj (op B)) (h : i ≫ r = 𝟙 _) :
    Smooth ((algSpec R).obj (op B)).hom := by
  have : Algebra.Smooth R A := (DynamicSmooth.smooth_algSpec_iff A).1 inferInstance
  have hformal : Algebra.FormallySmooth R B :=
    DynamicSmooth.formallySmooth_of_algSpec_retract i r h
  have hcoord : (algSpec.fullyFaithful.preimage r).unop ≫
      (algSpec.fullyFaithful.preimage i).unop = 𝟙 B := by
    have h' := congrArg algSpec.fullyFaithful.preimage h
    rw [Functor.FullyFaithful.preimage_comp, Functor.FullyFaithful.preimage_id] at h'
    simpa using congrArg Quiver.Hom.unop h'
  have hsurj : Function.Surjective (algSpec.fullyFaithful.preimage i).unop.hom := by
    intro b
    refine ⟨(algSpec.fullyFaithful.preimage r).unop.hom b, ?_⟩
    exact congrArg (fun f => f.hom b) hcoord
  have hfinite : Algebra.FiniteType R B :=
    Algebra.FiniteType.of_surjective (algSpec.fullyFaithful.preimage i).unop.hom hsurj
  exact (DynamicSmooth.smooth_algSpec_iff B).2
    ⟨hformal, Algebra.FinitePresentation.of_finiteType.mp hfinite⟩

/-- An affine scheme retract of a smooth affine scheme over a noetherian ring is smooth. -/
theorem smooth_of_retract [IsNoetherianRing R] {X Y : Over (Spec R)}
    [IsAffine X.left] [IsAffine Y.left] [Smooth X.hom]
    (i : Y ⟶ X) (r : X ⟶ Y) (h : i ≫ r = 𝟙 Y) : Smooth Y.hom := by
  let hX : (algSpec R).essImage X := essImage_algSpec.mpr inferInstance
  let hY : (algSpec R).essImage Y := essImage_algSpec.mpr inferInstance
  let A : CommAlgCat R := hX.witness.unop
  let B : CommAlgCat R := hY.witness.unop
  let eX : (algSpec R).obj (op A) ≅ X := hX.getIso
  let eY : (algSpec R).obj (op B) ≅ Y := hY.getIso
  have : Smooth ((algSpec R).obj (op A)).hom :=
    smooth_of_over_iso eX inferInstance
  have h' : (eY.hom ≫ i ≫ eX.inv) ≫ (eX.hom ≫ r ≫ eY.inv) = 𝟙 _ := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc i r, h, Category.id_comp, eY.hom_inv_id]
  exact smooth_of_over_iso eY.symm
    (smooth_algSpec_retract (eY.hom ≫ i ≫ eX.inv) (eX.hom ≫ r ≫ eY.inv) h')

/-- A scheme retract of a connected scheme is connected. -/
theorem connectedSpace_of_retract {S : Scheme.{u}} {X Y : Over S}
    [ConnectedSpace X.left] (i : Y ⟶ X) (r : X ⟶ Y) (h : i ≫ r = 𝟙 Y) :
    ConnectedSpace Y.left := by
  have h' : i.left ≫ r.left = 𝟙 Y.left := congrArg (fun f => f.left) h
  have hsurj : Function.Surjective r.left := by
    intro y
    refine ⟨i.left y, ?_⟩
    change (i.left ≫ r.left) y = y
    rw [h']
    rfl
  exact hsurj.connectedSpace r.left.continuous

end AffineRetractGeometry

namespace SplitKernelRetract

variable {S : Scheme.{u}} {H D L : GroupScheme S}

/-- Removing the chosen section part of a point. -/
def adjustment (q : H ⟶ D) (s : D ⟶ H) : H.X ⟶ H.X :=
  𝟙 H.X * (q.hom.hom ≫ s.hom.hom)⁻¹

/-- The adjustment is killed by the quotient homomorphism. -/
theorem adjustment_comp (q : H ⟶ D) (s : D ⟶ H) (hs : s ≫ q = 𝟙 D) :
    adjustment q s ≫ q.hom.hom = 1 := by
  have hs' : s.hom.hom ≫ q.hom.hom = 𝟙 D.X := congrArg (fun f => f.hom.hom) hs
  rw [adjustment, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp,
    Category.assoc, hs', Category.comp_id, mul_inv_cancel]

/-- The inclusion of the actual kernel of a factored map is also killed by its quotient. -/
theorem kernelι_comp_quotient (f : H ⟶ L) (d : D ⟶ L) [Mono d.hom.hom]
    (q : H ⟶ D) (hf : q ≫ d = f) :
    (kernelι f).hom.hom ≫ q.hom.hom = 1 := by
  apply (cancel_mono d.hom.hom).mp
  rw [Category.assoc, show q.hom.hom ≫ d.hom.hom = f.hom.hom from
    congrArg (fun g => g.hom.hom) hf]
  rw [(kernel_isPullback f).w, MonObj.one_comp]
  rfl

/-- A section of the quotient gives a retraction onto the full scheme-theoretic kernel. -/
def retraction (f : H ⟶ L) (d : D ⟶ L) (q : H ⟶ D) (s : D ⟶ H)
    (hf : q ≫ d = f) (hs : s ≫ q = 𝟙 D) : H.X ⟶ (kernel f).X :=
  (kernel_isPullback f).lift (adjustment q s) (toUnit _) (by
    change adjustment q s ≫ f.hom.hom = 1
    rw [← hf]
    change adjustment q s ≫ (q.hom.hom ≫ d.hom.hom) = 1
    rw [← Category.assoc, adjustment_comp q s hs, MonObj.one_comp])

@[reassoc (attr := simp)]
theorem retraction_ι (f : H ⟶ L) (d : D ⟶ L) (q : H ⟶ D) (s : D ⟶ H)
    (hf : q ≫ d = f) (hs : s ≫ q = 𝟙 D) :
    retraction f d q s hf hs ≫ (kernelι f).hom.hom = adjustment q s :=
  (kernel_isPullback f).lift_fst _ _ _

/-- The retraction is the identity on the actual kernel. -/
theorem ι_retraction (f : H ⟶ L) (d : D ⟶ L) [Mono d.hom.hom]
    (q : H ⟶ D) (s : D ⟶ H) (hf : q ≫ d = f) (hs : s ≫ q = 𝟙 D) :
    (kernelι f).hom.hom ≫ retraction f d q s hf hs = 𝟙 (kernel f).X := by
  apply (cancel_mono (kernelι f).hom.hom).mp
  rw [Category.assoc, retraction_ι, adjustment, MonObj.comp_mul, GrpObj.comp_inv,
    Category.comp_id, ← Category.assoc, kernelι_comp_quotient f d q hf,
    MonObj.one_comp, inv_one, mul_one, Category.id_comp]

/-- A split factorization through a monomorphism has smooth connected kernel whenever its
source is smooth, connected and affine over a noetherian base and its target is separated. -/
theorem smooth_connected_kernel {R : CommRingCat.{u}} [IsNoetherianRing R]
    {H D L : GroupScheme (Spec R)} [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left] [IsSeparated L.X.hom]
    (f : H ⟶ L) (d : D ⟶ L) [Mono d.hom.hom] (q : H ⟶ D) (s : D ⟶ H)
    (hf : q ≫ d = f) (hs : s ≫ q = 𝟙 D) :
    Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffineHom (kernel f).X.hom := by
    rw [← (kernelι f).hom.hom.w]
    infer_instance
  have : IsAffine (kernel f).X.left := isAffine_of_isAffineHom (kernel f).X.hom
  exact ⟨AffineRetractGeometry.smooth_of_retract (kernelι f).hom.hom
      (retraction f d q s hf hs) (ι_retraction f d q s hf hs),
    AffineRetractGeometry.connectedSpace_of_retract (kernelι f).hom.hom
      (retraction f d q s hf hs) (ι_retraction f d q s hf hs)⟩

end SplitKernelRetract

end Langlands.GroupScheme
