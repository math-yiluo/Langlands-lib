import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.TorusPointsTensor

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} (T : CommGroupScheme S) (U : Over S)

/-- Evaluation of actual cocharacters is bilinear over the lifted integers. -/
def evaluation : Additive (U ⟶ (Gm S).X) →ₗ[(ULift.{u} ℤ)]
    cocharacterLattice T →ₗ[(ULift.{u} ℤ)] Additive (U ⟶ T.X) where
  toFun x := (evalPoint x.toMul).toIntLinearMap.restrictScalars (ULift.{u} ℤ)
  map_add' x y := by
    apply LinearMap.ext
    intro ν
    exact congrArg Additive.ofMul (MonObj.mul_comp x.toMul y.toMul _)
  map_smul' r x := by
    apply LinearMap.ext
    intro ν
    let f : (U ⟶ (Gm S).X) →* (U ⟶ T.X) :=
      { toFun := fun y => y ≫ (CommGroupScheme.groupHom ν).hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun y z => MonObj.mul_comp y z _ }
    exact map_smul (f.toAdditive.toIntLinearMap.restrictScalars (ULift.{u} ℤ)) r x

/-- The tensor map induced by actual cocharacter evaluation. -/
def tensorEvaluation : Additive (U ⟶ (Gm S).X) ⊗[(ULift.{u} ℤ)] cocharacterLattice T →ₗ[(ULift.{u} ℤ)]
    Additive (U ⟶ T.X) := TensorProduct.lift (evaluation T U)

@[simp] theorem tensorEvaluation_tmul (x : Additive (U ⟶ (Gm S).X))
    (ν : cocharacterLattice T) :
    tensorEvaluation T U (x ⊗ₜ[(ULift.{u} ℤ)] ν) =
      Additive.ofMul (x.toMul ≫ (CommGroupScheme.groupHom ν).hom.hom) := rfl

/-- A group-scheme isomorphism identifies additive point modules. -/
def pointsCongr {T T' : CommGroupScheme S} (e : T.toGrp ≅ T'.toGrp) :
    Additive (U ⟶ T.X) ≃ₗ[ULift.{u} ℤ] Additive (U ⟶ T'.X) :=
  (isoPointsEquiv e U).toAdditive.toIntLinearEquiv.restrictScalars (ULift.{u} ℤ)

/-- The lattice identification induced by a group-scheme isomorphism. -/
def latticeCongr {T T' : CommGroupScheme S} (e : T.toGrp ≅ T'.toGrp) :
    cocharacterLattice T ≃ₗ[ULift.{u} ℤ] cocharacterLattice T' :=
  (cocharacterLattice.congr (CommGroupScheme.isoOfGroupIso e)).toIntLinearEquiv.restrictScalars
    (ULift.{u} ℤ)

/-- The tensor map commutes with actual group-scheme isomorphisms. -/
theorem tensorEvaluation_congr {T T' : CommGroupScheme S} (e : T.toGrp ≅ T'.toGrp) :
    (pointsCongr U e).toLinearMap ∘ₗ tensorEvaluation T U =
      tensorEvaluation T' U ∘ₗ
        (TensorProduct.congr (LinearEquiv.refl (ULift.{u} ℤ) _) (latticeCongr e)).toLinearMap := by
  apply TensorProduct.ext'
  intro x ν
  apply Additive.toMul.injective
  change (x.toMul ≫ (CommGroupScheme.groupHom ν).hom.hom) ≫ e.hom.hom.hom =
    x.toMul ≫ ((CommGroupScheme.groupHom ν).hom.hom ≫ e.hom.hom.hom)
  exact Category.assoc _ _ _

section Field

variable (L : Type u) [Field L]

/-- Cocharacter coordinates of a coordinate split torus, with lifted integral values. -/
def latticeCoordinates (I : Type u) [Finite I] :
    cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) ≃ₗ[(ULift.{u} ℤ)]
      (I → (ULift.{u} ℤ)) :=
  ((splitTorus.cocharacterLatticeEquiv L I).trans
    (AddEquiv.piCongrRight fun _ => (AddEquiv.ulift : (ULift.{u} ℤ) ≃+ ℤ).symm)).toIntLinearEquiv.restrictScalars (ULift.{u} ℤ)

/-- Coordinate points, written additively and identified with Gm points. -/
def splitPointCoordinates (I : Type u) [Finite I] (U : Over (Spec (CommRingCat.of L))) :
    Additive (U ⟶ (splitTorus (Spec (CommRingCat.of L)) I).X) ≃ₗ[(ULift.{u} ℤ)]
      (I → Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X)) :=
  ({ toFun x i := Additive.ofMul ((Gm.pointsEquiv _ U).symm (splitTorus.pointsEquiv I U x.toMul i))
     invFun y := Additive.ofMul ((splitTorus.pointsEquiv I U).symm
       (fun i => Gm.pointsEquiv _ U (y i).toMul))
     left_inv x := by simp
     right_inv y := by simp
     map_add' x y := by ext i; simp [map_mul]
   } : Additive (U ⟶ (splitTorus (Spec (CommRingCat.of L)) I).X) ≃+
      (I → Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X))).toIntLinearEquiv.restrictScalars (ULift.{u} ℤ)

/-- Cocharacter evaluation in each split coordinate is scalar multiplication. -/
theorem splitPointCoordinates_evaluation (I : Type u) [Finite I]
    (U : Over (Spec (CommRingCat.of L)))
    (x : Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X))
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I))
    (i : I) :
    splitPointCoordinates L I U (evaluation _ U x ν) i =
      latticeCoordinates L I ν i • x := by
  apply Additive.toMul.injective
  change (Gm.pointsEquiv _ U).symm
      (splitTorus.pointsEquiv I U (x.toMul ≫ (CommGroupScheme.groupHom ν).hom.hom) i) =
    x.toMul ^ (splitTorus.cocharacterLatticeEquiv L I ν i)
  apply (Gm.pointsEquiv _ U).injective
  rw [MulEquiv.apply_symm_apply, map_zpow]
  have h := splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm L I
    (splitTorus.cocharacterLatticeEquiv L I ν) x.toMul
  rw [AddEquiv.symm_apply_apply] at h
  exact congrFun h i

/-- The elementary tensor-coordinate equivalence for a coordinate split torus. -/
def coordinateTensorEquiv (I : Type u) [Finite I]
    (U : Over (Spec (CommRingCat.of L))) :
    Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X) ⊗[(ULift.{u} ℤ)]
      cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) ≃ₗ[(ULift.{u} ℤ)]
      (I → Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X)) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  exact (TensorProduct.congr (LinearEquiv.refl (ULift.{u} ℤ) _) (latticeCoordinates L I)).trans
    (TensorProduct.piScalarRight (ULift.{u} ℤ) (ULift.{u} ℤ) _ I)

/-- In split coordinates the actual evaluation map is the elementary tensor equivalence. -/
theorem split_tensorEvaluation_eq (I : Type u) [Finite I]
    (U : Over (Spec (CommRingCat.of L))) :
    (splitPointCoordinates L I U).toLinearMap ∘ₗ
        tensorEvaluation (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U =
      (coordinateTensorEquiv L I U).toLinearMap := by
  apply TensorProduct.ext'
  intro x ν
  funext i
  simpa [coordinateTensorEquiv, tensorEvaluation] using
    splitPointCoordinates_evaluation L I U x ν i

/-- Actual cocharacter evaluation identifies the tensor product with points of a split torus. -/
theorem split_tensorEvaluation_bijective (I : Type u) [Finite I]
    (U : Over (Spec (CommRingCat.of L))) :
    Function.Bijective
      (tensorEvaluation (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U) := by
  have h := congrArg (fun f => f.toFun) (split_tensorEvaluation_eq L I U)
  have hb : Function.Bijective
      ((splitPointCoordinates L I U) ∘
        tensorEvaluation (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U) := by
    rw [show (splitPointCoordinates L I U) ∘
        tensorEvaluation (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U =
        coordinateTensorEquiv L I U from h]
    exact (coordinateTensorEquiv L I U).bijective
  exact ⟨fun x y hxy => hb.injective (congrArg (splitPointCoordinates L I U) hxy),
    fun y => by
      obtain ⟨x, hx⟩ := hb.surjective (splitPointCoordinates L I U y)
      exact ⟨x, (splitPointCoordinates L I U).injective hx⟩⟩

/-- Evaluation is bijective for any actual split torus over a field. -/
theorem tensorEvaluation_bijective
    (T : CommGroupScheme (Spec (CommRingCat.of L))) (hT : IsSplitTorus T.toGrp)
    (U : Over (Spec (CommRingCat.of L))) :
    Function.Bijective (tensorEvaluation T U) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let a := TensorProduct.congr (LinearEquiv.refl (ULift.{u} ℤ)
    (Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X)))
    (latticeCongr (T := T) (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) e)
  let b := pointsCongr (T := T) (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U e
  have h (t) : b (tensorEvaluation T U t) =
      tensorEvaluation (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U (a t) :=
    LinearMap.congr_fun (tensorEvaluation_congr
      (T := T) (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) U e) t
  have hb := split_tensorEvaluation_bijective L I U
  refine ⟨?_, ?_⟩
  · intro t t' htt'
    apply a.injective
    apply hb.injective
    rw [← h, ← h, htt']
  · intro y
    obtain ⟨z, hz⟩ := hb.surjective (b y)
    refine ⟨a.symm z, b.injective ?_⟩
    rw [h, LinearEquiv.apply_symm_apply]
    exact hz

/-- The actual tensor-point equivalence of a split torus, canonical as a map. -/
def tensorPointEquiv
    (T : CommGroupScheme (Spec (CommRingCat.of L))) (hT : IsSplitTorus T.toGrp)
    (U : Over (Spec (CommRingCat.of L))) :
    Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X) ⊗[ULift.{u} ℤ] cocharacterLattice T ≃ₗ[ULift.{u} ℤ]
      Additive (U ⟶ T.X) :=
  LinearEquiv.ofBijective (tensorEvaluation T U) (tensorEvaluation_bijective L T hT U)

@[simp] theorem tensorPointEquiv_tmul
    (T : CommGroupScheme (Spec (CommRingCat.of L))) (hT : IsSplitTorus T.toGrp)
    (U : Over (Spec (CommRingCat.of L)))
    (x : Additive (U ⟶ (Gm (Spec (CommRingCat.of L))).X)) (ν : cocharacterLattice T) :
    tensorPointEquiv L T hT U (x ⊗ₜ[ULift.{u} ℤ] ν) =
      Additive.ofMul (x.toMul ≫ (CommGroupScheme.groupHom ν).hom.hom) := rfl

end Field

end Langlands.GroupScheme.TorusPointsTensor
