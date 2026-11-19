import Langlands.Geometry.FormalGroup.AtlasRationalEndAlgebra
import Langlands.Geometry.FormalGroup.DivisionOrderRationalAction
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeMorphism

/-! # The whole rational division-algebra action on a formal atlas -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel TensorProduct ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {σ : Type} [Finite σ] {X : BasicAtlas 𝒪[K] R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

local instance : Algebra 𝒪[K] (BasicAtlas.RationalHom K X X rfl) :=
  Algebra.compHom _ (algebraMap 𝒪[K] K)

local instance : IsScalarTower 𝒪[K] K (BasicAtlas.RationalHom K X X rfl) :=
  .of_algebraMap_eq (fun _ => rfl)

private def atlasOrderEndomorphism (E : BasicAtlas.OrderAction (IntegerRing K D) X) :
    IntegerRing K D →+* BasicAtlas.Hom X X rfl where
  toFun := E.endomorphism
  map_zero' := by
    apply BasicAtlas.Hom.ext
    intro A b hb
    exact map_zero ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)).action
  map_add' a c := by
    apply BasicAtlas.Hom.ext
    intro A b hb
    exact map_add ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)).action a c
  map_one' := by
    apply BasicAtlas.Hom.ext
    intro A b hb
    exact map_one ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)).action
  map_mul' a c := by
    apply BasicAtlas.Hom.ext
    intro A b hb
    exact map_mul ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)).action a c

private def atlasIntegralAction (E : BasicAtlas.OrderAction (IntegerRing K D) X) :
    IntegerRing K D →ₐ[𝒪[K]] BasicAtlas.RationalHom K X X rfl where
  toRingHom := BasicAtlas.RationalHom.ofHomEnd.comp (atlasOrderEndomorphism K D E)
  commutes' a := by
    have h : E.endomorphism (algebraMap 𝒪[K] (IntegerRing K D) a) = a • BasicAtlas.Hom.id X := by
      apply BasicAtlas.Hom.ext
      intro A b hb
      apply ModuleLaw.Hom.ext
      change (((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)).action
        (algebraMap 𝒪[K] (IntegerRing K D) a)).toHom = (a • ModuleLaw.Hom.id _).toHom
      rw [ModuleLaw.OrderAction.extends_scalars, ModuleLaw.Hom.smul_toHom,
        ModuleLaw.Hom.id_toHom, CommLaw.Hom.comp_id]
    change BasicAtlas.RationalHom.ofHom (F := K)
        (E.endomorphism (algebraMap 𝒪[K] (IntegerRing K D) a)) =
      (algebraMap 𝒪[K] K a) • BasicAtlas.RationalHom.id (F := K) X
    rw [h]
    change (1 : K) ⊗ₜ[𝒪[K]] (a • BasicAtlas.Hom.id X) =
      (algebraMap 𝒪[K] K a) • ((1 : K) ⊗ₜ[𝒪[K]] BasicAtlas.Hom.id X)
    rw [← TensorProduct.smul_tmul, ← IsScalarTower.algebraMap_smul K a (1 : K),
      TensorProduct.smul_tmul']

/-- The actual atlas order action extends to the whole rational endomorphism tensor. -/
def atlasRationalAction (E : BasicAtlas.OrderAction (IntegerRing K D) X) :
    D →ₐ[K] BasicAtlas.RationalHom K X X rfl :=
  (AlgHom.liftEquiv 𝒪[K] K (IntegerRing K D) (BasicAtlas.RationalHom K X X rfl)
    (atlasIntegralAction K D E)).comp (integerTensorEquiv K D).symm.toAlgHom

@[simp]
theorem atlasRationalAction_coe (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (a : IntegerRing K D) :
    atlasRationalAction K D E (a : D) = BasicAtlas.RationalHom.ofHom (E.endomorphism a) := by
  simp only [atlasRationalAction, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    integerTensorEquiv_symm_coe, AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- Restriction to a test chart is the rational action of its actual base-extended order. -/
theorem atlasRationalAction_onChart (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (A : CommAlgCat.{v} R) (b : X.opens) (hb : IsUnit (algebraMap R A b.val)) :
    (BasicAtlas.RationalHom.onChartEnd (F := K) A b hb).comp (atlasRationalAction K D E) =
      rationalAction K D ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)) := by
  apply algHom_ext_onIntegers K D
  intro a
  change BasicAtlas.RationalHom.onChart (F := K) (X := X) (h := rfl) A b hb
      (atlasRationalAction K D E (a : D)) = _
  rw [atlasRationalAction_coe, BasicAtlas.RationalHom.onChart_ofHom, rationalAction_coe]
  rfl

@[simp]
theorem atlasRationalAction_onChart_apply (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (A : CommAlgCat.{v} R) (b : X.opens) (hb : IsUnit (algebraMap R A b.val)) (d : D) :
    BasicAtlas.RationalHom.onChart (F := K) (X := X) (h := rfl) A b hb
        (atlasRationalAction K D E d) =
      rationalAction K D ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)) d :=
  DFunLike.congr_fun (atlasRationalAction_onChart K D E A b hb) d

private theorem atlasEndomorphism_baseChange (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (S : CommAlgCat.{v} R) (a : IntegerRing K D) :
    (E.endomorphism a).baseChange S = (E.baseChange S).endomorphism a := by
  apply BasicAtlas.Hom.ext
  intro A b hb
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp (CoordinateMap.comp
      ((E.endomorphism a).hom (BasicAtlas.restrictTest S A) (X.baseSource S b)
        (X.baseSource_unit S A b hb)).toHom.toCoordinateMap CoordinateMap.id) =
    (((E.baseOrderChart S b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)).action
      a).toHom.toCoordinateMap
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id]
  exact (E.baseOrderChart_coordinates S A b hb a).symm

/-- Coefficient extension preserves the whole rational order action of the atlas. -/
theorem atlasRationalAction_baseChange (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (S : CommAlgCat.{v} R) :
    (BasicAtlas.RationalHom.baseChangeEnd X S).comp (atlasRationalAction K D E) =
      atlasRationalAction K D (E.baseChange S) := by
  apply algHom_ext_onIntegers K D
  intro a
  change BasicAtlas.RationalHom.baseChange (F := K) (X := X) (h := rfl) S
      (atlasRationalAction K D E (a : D)) = _
  rw [atlasRationalAction_coe, BasicAtlas.RationalHom.baseChange_ofHom,
    atlasEndomorphism_baseChange, atlasRationalAction_coe]

@[simp]
theorem atlasRationalAction_baseChange_apply (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (S : CommAlgCat.{v} R) (d : D) :
    BasicAtlas.RationalHom.baseChange (F := K) (X := X) (h := rfl) S
        (atlasRationalAction K D E d) = atlasRationalAction K D (E.baseChange S) d :=
  DFunLike.congr_fun (atlasRationalAction_baseChange K D E S) d

end Langlands.FormalGroup.LocalDivision
