import Langlands.Geometry.FormalGroup.DivisionOrderAtlasRationalAction
import Langlands.Geometry.FormalGroup.DivisionOrderTwistComposition
import Langlands.Geometry.FormalGroup.SpecialAtlasUnitTwist
import Langlands.Geometry.FormalGroup.AtlasOrderRationalBaseChange

/-! # Division-unit quasi-isogenies of actual formal atlases -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {σ : Type} [Finite σ] {X : BasicAtlas 𝒪[K] R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Conjugate the order action on the original charts and keep their formal transitions. -/
abbrev atlasTwist (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ) :
    BasicAtlas.OrderAction (IntegerRing K D) X :=
  E.twist (conjugation K D g)

/-- The whole atlas rational action of a twist is precomposition by inverse conjugation. -/
theorem atlasRationalAction_twist (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ) :
    atlasRationalAction K D (atlasTwist K D E g) =
      (atlasRationalAction K D E).comp (divisionConjugation K D g).toAlgHom := by
  apply algHom_ext_onIntegers K D
  intro a
  change atlasRationalAction K D (atlasTwist K D E g) (a : D) =
    atlasRationalAction K D E (divisionConjugation K D g (a : D))
  rw [atlasRationalAction_coe, divisionConjugation_coe, atlasRationalAction_coe]
  rfl

/-- The inverse division unit gives the actual whole atlas quasi-isogeny to the conjugated order. -/
def atlasTwistQuasiIsogeny (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ) :
    BasicAtlas.OrderAction.QuasiIsogeny K E (atlasTwist K D E g) rfl :=
  BasicAtlas.OrderAction.QuasiIsogeny.ofAtlasQuasiIsogeny
    { hom := atlasRationalAction K D E ((g⁻¹ : Dˣ) : D)
      inv := atlasRationalAction K D E (g : D)
      inv_hom := by
        change atlasRationalAction K D E (g : D) *
          atlasRationalAction K D E ((g⁻¹ : Dˣ) : D) = 1
        rw [← map_mul, Units.mul_inv, map_one]
      hom_inv := by
        change atlasRationalAction K D E ((g⁻¹ : Dˣ) : D) *
          atlasRationalAction K D E (g : D) = 1
        rw [← map_mul, Units.inv_mul, map_one] }
    (fun A b hb a => by
      let θ := BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb
      let E' := (E.chart b).map θ
      change RationalHom.comp
          (BasicAtlas.RationalHom.onChart (F := K) (X := X) (h := rfl) A b hb
            (atlasRationalAction K D E ((g⁻¹ : Dˣ) : D)))
          (RationalHom.ofHom (E'.action a)) =
        RationalHom.comp (RationalHom.ofHom ((twist K D E' g).action a))
          (BasicAtlas.RationalHom.onChart (F := K) (X := X) (h := rfl) A b hb
            (atlasRationalAction K D E ((g⁻¹ : Dˣ) : D)))
      rw [atlasRationalAction_onChart_apply]
      exact (twistQuasiIsogeny K D E' g).hom.commutes a)

@[simp]
theorem atlasTwistQuasiIsogeny_hom_val (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ) :
    (atlasTwistQuasiIsogeny K D E g).hom.val = atlasRationalAction K D E ((g⁻¹ : Dˣ) : D) := rfl

@[simp]
theorem atlasTwistQuasiIsogeny_inv_val (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ) :
    (atlasTwistQuasiIsogeny K D E g).inv.val = atlasRationalAction K D E (g : D) := rfl

/-- Evaluation gives the complete coordinate quasi-isogeny on every actual test chart. -/
@[simp]
theorem atlasTwistQuasiIsogeny_onChart (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ)
    (A : CommAlgCat.{v} R) (b : X.opens) (hb : IsUnit (algebraMap R A b.val)) :
    (atlasTwistQuasiIsogeny K D E g).onChart A b hb =
      twistQuasiIsogeny K D
        ((E.chart b).map (BasicAtlas.coefficientLift (O := 𝒪[K]) b.val A hb)) g := by
  apply OrderAction.QuasiIsogeny.ext
  apply OrderAction.RationalHom.ext
  exact atlasRationalAction_onChart_apply K D E A b hb ((g⁻¹ : Dˣ) : D)

/-- Coefficient extension commutes with conjugation of the order action on the atlas. -/
theorem atlasTwist_baseChange (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g : Dˣ)
    (S : CommAlgCat.{v} R) :
    (atlasTwist K D E g).baseChange S = atlasTwist K D (E.baseChange S) g := rfl

/-- The complete whole atlas quasi-isogeny commutes with coefficient extension. -/
@[simp]
theorem atlasTwistQuasiIsogeny_baseChange (E : BasicAtlas.OrderAction (IntegerRing K D) X)
    (g : Dˣ) (S : CommAlgCat.{v} R) :
    (atlasTwistQuasiIsogeny K D E g).baseChange S =
      atlasTwistQuasiIsogeny K D (E.baseChange S) g := by
  apply BasicAtlas.OrderAction.QuasiIsogeny.ext_hom
  apply BasicAtlas.OrderAction.RationalHom.ext
  exact atlasRationalAction_baseChange_apply K D E S ((g⁻¹ : Dˣ) : D)

variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

/-- The atlas map for an integral unit is the rationalization of the original special atlas isomorphism. -/
@[simp]
theorem atlasTwistQuasiIsogeny_integerUnit (Y : SpecialAtlas K D ι R) (a : (IntegerRing K D)ˣ) :
    atlasTwistQuasiIsogeny K D Y.order (integerUnit K D a) =
      BasicAtlas.OrderAction.QuasiIsogeny.ofIso (Y.twistIntegerUnitIso a) := by
  apply BasicAtlas.OrderAction.QuasiIsogeny.ext_hom
  apply BasicAtlas.OrderAction.RationalHom.ext
  exact atlasRationalAction_coe K D Y.order (a⁻¹ : (IntegerRing K D)ˣ)

end Langlands.FormalGroup.LocalDivision
