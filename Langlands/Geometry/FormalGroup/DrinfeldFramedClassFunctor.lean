import Langlands.Geometry.FormalGroup.DrinfeldFramedCompositionComparison

/-! # Actual varying-Nilp functor of height-zero framed comparison classes -/

noncomputable section

universe u v w s z

namespace Langlands.FormalGroup.Nilp

open CategoryTheory ModuleLaw

variable (O : Type u) [CommRing O]
variable (R : Type v) [CommRing R] [Algebra O R] (r : R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- View each actual Nilp coefficient algebra over the original acting scalar ring. -/
def coefficientFunctor : Nilp.{v,w} R r ⥤ CommAlgCat.{w} O where
  obj A := CommAlgCat.of O A.obj
  map f := CommAlgCat.ofHom (scalarMap O f)
  map_id _A := rfl
  map_comp _f _g := rfl

variable (κ : Type z) [CommRing κ] [Algebra O κ]

/-- Actual residue algebra maps to the quotient, with the induced quotient scalar maps. -/
def residueMapFunctor : Nilp.{v,w} R r ⥤ Type (max z w) where
  obj A := κ →ₐ[O] ((reductionFunctor R r).obj A).obj
  map f := ↾(fun ψ => (reducedScalarMap O f).comp ψ)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro ψ
    change (reducedScalarMap O (𝟙 A)).comp ψ = ψ
    rw [reducedScalarMap_id, AlgHom.id_comp]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro ψ
    change (reducedScalarMap O (f ≫ g)).comp ψ =
      (reducedScalarMap O g).comp ((reducedScalarMap O f).comp ψ)
    rw [reducedScalarMap_comp, AlgHom.comp_assoc]

end Langlands.FormalGroup.Nilp

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual height-zero framed comparison quotient is a functor under varying Nilp bases. -/
def comparisonClassFunctor :
    Nilp.{v,u} R (algebraMap 𝒪[K] R π) ⥤ Type (u + 1) where
  obj A := ComparisonClass Φ A
  map f := ↾(fun q => q.baseChange f)
  map_id A := by
    ext q
    exact q.baseChange_id
  map_comp f g := by
    ext q
    exact (q.baseChange_comp f g).symm

/-- A representative is mapped by the same actual framed base-extension construction. -/
@[simp]
theorem comparisonClassFunctor_map_comparisonClassOf
    {A B : Nilp.{v,u} R (algebraMap 𝒪[K] R π)} (f : A ⟶ B) (X : DrinfeldFramedAtlas Φ A) :
    (comparisonClassFunctor Φ).map f (comparisonClassOf X) = comparisonClassOf (X.baseChange f) := rfl

/-- Forgetting framing is natural to the actual height-certified target-class functor. -/
def targetClassNatTrans : comparisonClassFunctor Φ ⟶
    Nilp.coefficientFunctor 𝒪[K] R (algebraMap 𝒪[K] R π) ⋙
      SpecialAtlas.HeightSquaredAtlas.classFunctor ι π where
  app A := ↾ComparisonClass.targetClass
  naturality A B f := by
    ext q
    exact q.targetClass_baseChange f

/-- Quotient-reduced targets are natural through the same actual quotient functor. -/
def reducedTargetClassNatTrans : comparisonClassFunctor Φ ⟶
    Nilp.reductionFunctor R (algebraMap 𝒪[K] R π) ⋙
      Nilp.coefficientFunctor 𝒪[K] R (algebraMap 𝒪[K] R π) ⋙
        SpecialAtlas.HeightSquaredAtlas.classFunctor ι π where
  app A := ↾ComparisonClass.reducedTargetClass
  naturality A B f := by
    ext q
    exact q.reducedTargetClass_baseChange f

/-- The actual descended residue map is natural under the induced quotient scalar map. -/
def residueMapNatTrans : comparisonClassFunctor Φ ⟶
    Nilp.residueMapFunctor 𝒪[K] R (algebraMap 𝒪[K] R π) κ ⋙ uliftFunctor.{u + 1, u} where
  app A := ↾(fun q => ULift.up q.residueMap)
  naturality A B f := by
    apply ConcreteCategory.hom_ext
    intro q
    change ULift.up (q.baseChange f).residueMap =
      ULift.up ((Nilp.reducedScalarMap 𝒪[K] f).comp q.residueMap)
    exact congrArg ULift.up (q.residueMap_baseChange f)

/-- The natural target component retains the exact original height-certified target class. -/
@[simp]
theorem targetClassNatTrans_app {A : Nilp.{v,u} R (algebraMap 𝒪[K] R π)} (q : ComparisonClass Φ A) :
    (targetClassNatTrans Φ).app A q = q.targetClass := rfl

/-- The reduced-target component retains the exact quotient-reduced target class. -/
@[simp]
theorem reducedTargetClassNatTrans_app {A : Nilp.{v,u} R (algebraMap 𝒪[K] R π)} (q : ComparisonClass Φ A) :
    (reducedTargetClassNatTrans Φ).app A q = q.reducedTargetClass := rfl

/-- Removing the universe lift recovers exactly the actual descended residue map. -/
@[simp]
theorem residueMapNatTrans_app_down {A : Nilp.{v,u} R (algebraMap 𝒪[K] R π)} (q : ComparisonClass Φ A) :
    ((residueMapNatTrans Φ).app A q).down = q.residueMap := rfl

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
