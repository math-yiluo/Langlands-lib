import Langlands.AbelianScheme.RationalAlgebraAction
import Langlands.AbelianScheme.RelativeHomNeronExtension
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Extending a rational algebra action on a good model over a DVR -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AbelianScheme

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]

local notation "j" => Spec.map (CommRingCat.ofHom (algebraMap V K))
local notation "S" => Spec (CommRingCat.of V)

/-- Restriction on actual homomorphisms between two good abelian models is bijective. -/
theorem dvrGenericHom_bijective (B C : AbelianScheme S) :
    Function.Bijective ((baseChange j).map : (B ⟶ C) → _) := by
  constructor
  · intro f g h
    have he : (Over.pullback j).map (groupHom f).hom.hom =
        (Over.pullback j).map (groupHom g).hom.hom :=
      congrArg (fun k => (groupHom k).hom.hom) h
    have he' := genericFibre_map_injective K he
    change Additive.ofMul (groupHom f) = Additive.ofMul (groupHom g)
    exact congrArg Additive.ofMul (Grp.hom_ext _ _ he')
  · intro f
    have hC : GoodReductionJacobian.AbelianSchemePropertyBundle V C.X.hom :=
      ⟨inferInstance, inferInstance,
        fun s => C.X.hom.isConnected_preimage_singleton s,
        ⟨@GoodReductionJacobian.relativeGroupLawOfGrpObj V _ _ _
          (inferInstanceAs (GrpObj C.X))⟩⟩
    obtain ⟨g, hg⟩ := baseChange_map_surjective K B.toGrp C.toGrp hC (groupHom f)
    exact ⟨Additive.ofMul g, congrArg Additive.ofMul hg⟩

/-- The same bijectivity holds on the rationalized Hom groups. -/
theorem dvrGenericRationalHom_bijective (B C : AbelianScheme S) :
    Function.Bijective (rationalBaseChangeHom (A := B) (B := C) j) := by
  let e := LinearEquiv.ofBijective ((baseChange j).mapAddHom (X := B) (Y := C)).toIntLinearMap
    (dvrGenericHom_bijective K B C)
  let eQ := e.baseChange ℤ ℚ (B ⟶ C) ((baseChange j).obj B ⟶ (baseChange j).obj C)
  have he : eQ.toLinearMap = rationalBaseChangeHom j := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q f
    rw [rationalBaseChangeHom_tmul]
    rfl
  rw [← he]
  exact eQ.bijective

/-- Rational endomorphisms of a good abelian model over a DVR identify with the
actual rational endomorphisms of its generic fibre. -/
def dvrRationalEndEquiv (B : AbelianScheme S) :
    End0 B ≃ₐ[ℚ] End0 ((baseChange j).obj B) :=
  AlgEquiv.ofBijective (rationalBaseChangeEnd j B) (dvrGenericRationalHom_bijective K B B)

@[simp]
theorem dvrRationalEndEquiv_apply (B : AbelianScheme S) (f : End0 B) :
    dvrRationalEndEquiv K B f = rationalBaseChangeEnd j B f := rfl

/-- The unique rational algebra action whose restriction is the supplied action
on the generic fibre of the model. -/
def extendDvrRationalAction {A : Type} [Ring A] [Algebra ℚ A] (B : AbelianScheme S)
    (i : A →ₐ[ℚ] End0 ((baseChange j).obj B)) : A →ₐ[ℚ] End0 B :=
  (dvrRationalEndEquiv K B).symm.toAlgHom.comp i

@[simp]
theorem rationalBaseChangeEnd_extendDvrRationalAction {A : Type} [Ring A] [Algebra ℚ A]
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 ((baseChange j).obj B)) :
    (rationalBaseChangeEnd j B).comp (extendDvrRationalAction K B i) = i := by
  ext a
  exact (dvrRationalEndEquiv K B).apply_symm_apply (i a)

theorem extendDvrRationalAction_unique {A : Type} [Ring A] [Algebra ℚ A] (B : AbelianScheme S)
    (i : A →ₐ[ℚ] End0 ((baseChange j).obj B)) (i' : A →ₐ[ℚ] End0 B)
    (hi' : (rationalBaseChangeEnd j B).comp i' = i) :
    i' = extendDvrRationalAction K B i := by
  apply AlgHom.ext
  intro a
  apply (dvrRationalEndEquiv K B).injective
  exact (DFunLike.congr_fun hi' a).trans ((dvrRationalEndEquiv K B).apply_symm_apply (i a)).symm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
