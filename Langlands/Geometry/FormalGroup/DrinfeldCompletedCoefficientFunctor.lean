import Langlands.Geometry.FormalGroup.CompletedUnramifiedResidueMaps
import Langlands.Geometry.FormalGroup.DrinfeldDeligneResidueComparisonStatement

/-! # Actual Drinfeld and Deligne point functors over completed unramified coefficients -/

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 80000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w z

open CategoryTheory IsLocalRing ValuativeRel
open Langlands.LocalGalois.Separable

namespace Langlands.FormalGroup.Nilp

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (π : 𝒪[K])

local notation "Ĉ" => CompletedUnramifiedIntegers K
local notation "π̂" => (algebraMap 𝒪[K] Ĉ π)

/-- Restrict scalars of an actual completed-coefficient Nilp test. -/
def completedNilpRestriction : Nilp.{u, v} Ĉ π̂ ⥤ Nilp.{u, v} 𝒪[K] π where
  obj B := ⟨(coefficientFunctor 𝒪[K] Ĉ π̂).obj B, B.nilpotent⟩
  map f := ObjectProperty.homMk ((coefficientFunctor 𝒪[K] Ĉ π̂).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

/-- Reduce the actual structural map of the completed test to get its residue coordinate. -/
def completedBaseResidueMap (hπ : maximalIdeal 𝒪[K] = Ideal.span {π})
    (B : Nilp.{u, v} Ĉ π̂) :
    ResidueField (fixedFieldIntegers K) →ₐ[𝒪[K]] Reduction π ((completedNilpRestriction π).obj B).obj :=
  ((completedNilpRestriction π).obj B).completedUnramifiedResidueMapEquiv hπ
    (IsScalarTower.toAlgHom 𝒪[K] Ĉ B.obj)

/-- Every morphism of completed-coefficient tests respects that residue coordinate. -/
theorem completedBaseResidueMap_natural (hπ : maximalIdeal 𝒪[K] = Ideal.span {π})
    {B B' : Nilp.{u, v} Ĉ π̂} (f : B ⟶ B') :
    completedBaseResidueMap π hπ B' =
      (reductionMap ((completedNilpRestriction π).map f).hom.hom).comp (completedBaseResidueMap π hπ B) := by
  have he := (((completedNilpRestriction π).obj B).completedUnramifiedResidueMapEquiv_natural hπ
    ((completedNilpRestriction π).map f) (IsScalarTower.toAlgHom 𝒪[K] Ĉ B.obj))
  have hstruct : ((completedNilpRestriction π).map f).hom.hom.comp
      (IsScalarTower.toAlgHom 𝒪[K] Ĉ B.obj) = IsScalarTower.toAlgHom 𝒪[K] Ĉ B'.obj :=
    AlgHom.ext fun a => f.hom.hom.commutes a
  rw [hstruct] at he
  exact he

end Langlands.FormalGroup.Nilp

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CentralDivision Langlands.DeligneFormalSpace

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] {ι : L →ₐ[K] D} {π : 𝒪[K]}

local notation "κ" => ResidueField (fixedFieldIntegers K)
local notation "Ĉ" => CompletedUnramifiedIntegers K
local notation "π̂" => (algebraMap 𝒪[K] Ĉ π)
local notation "degD" => CentralSimple.reducedDegree K D

local notation "FixedFrame" => SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π

private instance completedFramedDegree : NeZero degD := ⟨(CentralSimple.reducedDegree_pos K D).ne'⟩

private def sectionFibre {J : Type w} [Category J] (P : J ⥤ Type v) (Q : J ⥤ Type z)
    (p : ∀ j, P.obj j → Q.obj j) (s : ∀ j, Q.obj j)
    (hp : ∀ {i j : J} (f : i ⟶ j) x, p j (P.map f x) = Q.map f (p i x))
    (hs : ∀ {i j : J} (f : i ⟶ j), Q.map f (s i) = s j) : J ⥤ Type v where
  obj j := {x : P.obj j // p j x = s j}
  map f := ↾(fun x => ⟨P.map f x.1, (hp f x.1).trans ((congrArg (Q.map f) x.2).trans (hs f))⟩)
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Subtype.ext (ConcreteCategory.congr_hom (P.map_id j) x.1)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Subtype.ext (ConcreteCategory.congr_hom (P.map_comp f g) x.1)

private abbrev residueComparisonSource (Φ : FixedFrame) : Nilp.{u, u} 𝒪[K] π ⥤ Type (u + 1) :=
  comparisonClassFunctor (R := 𝒪[K]) Φ

private abbrev residueComparisonTarget (Φ : FixedFrame) : Nilp.{u, u} 𝒪[K] π ⥤ Type (u + 1) :=
  nilpDeligneResidueFunctor (d := degD) κ (coefficientUniformizer_ne_zero (F := K) Φ.property.1)

/-- Drinfeld's framed classes with the residue map supplied by the actual
completed coefficient algebra of the test. -/
def completedDrinfeldClassFunctor (Φ : FixedFrame) (hπ : maximalIdeal 𝒪[K] = Ideal.span {π}) : Nilp.{u, u} Ĉ π̂ ⥤ Type (u + 1) :=
  sectionFibre (Nilp.completedNilpRestriction (K := K) π ⋙ residueComparisonSource Φ)
    (Nilp.completedNilpRestriction (K := K) π ⋙ Nilp.residueMapFunctor 𝒪[K] 𝒪[K] π κ)
    (fun _ x => x.residueMap) (Nilp.completedBaseResidueMap (K := K) π hπ)
    (fun f x => x.residueMap_baseChange ((Nilp.completedNilpRestriction (K := K) π).map f))
    (fun f => (Nilp.completedBaseResidueMap_natural (K := K) π hπ f).symm)

/-- The actual Deligne points after base change to the completed unramified
integers, on the same affine test category. -/
def completedDeligneClassFunctor (hπ : Irreducible π) : Nilp.{u, u} Ĉ π̂ ⥤ Type (u + 1) :=
  Nilp.completedNilpRestriction (K := K) π ⋙
    nilpSheafClassFunctor degD π K (coefficientUniformizer_ne_zero (F := K) hπ)

/-- A comparison preserving every actual residue map restricts to a comparison
on completed-coefficient tests. -/
def completedComparisonOfResidue (Φ : FixedFrame) (hπ : maximalIdeal 𝒪[K] = Ideal.span {π})
    (e : residueComparisonSource Φ ≅ residueComparisonTarget Φ)
    (he : ∀ (B : Nilp.{u, u} 𝒪[K] π) (x : ComparisonClass Φ B),
      (e.hom.app B x).2 = x.residueMap) :
    completedDrinfeldClassFunctor Φ hπ ≅ completedDeligneClassFunctor (D := D) Φ.property.1 :=
  NatIso.ofComponents (fun B => by
    let A := (Nilp.completedNilpRestriction (K := K) π).obj B
    let ψ := Nilp.completedBaseResidueMap (K := K) π hπ B
    let b := (e.app A).toEquiv
    refine Equiv.toIso {
      toFun := fun x => (b x.1).1
      invFun := fun y => ⟨b.symm (y, ψ), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · calc
        (b.symm (y, ψ)).residueMap = (b (b.symm (y, ψ))).2 := (he A _).symm
        _ = ψ := congrArg Prod.snd (b.apply_symm_apply (y, ψ))
    · intro x
      apply Subtype.ext
      have hx : b x.1 = ((b x.1).1, ψ) := Prod.ext rfl ((he A _).trans x.2)
      exact (congrArg b.symm hx).symm.trans (b.symm_apply_apply x.1)
    · intro y
      exact congrArg Prod.fst (b.apply_symm_apply (y, ψ))) (by
    intro B B' f
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg Prod.fst
      (ConcreteCategory.congr_hom (e.hom.naturality ((Nilp.completedNilpRestriction (K := K) π).map f)) x.1))

/-- The published residue-coordinate theorem target implies the underlying
comparison on the actual completed base. -/
theorem nonempty_completedComparison_of_residue (Φ : FixedFrame)
    (hπ : maximalIdeal 𝒪[K] = Ideal.span {π})
    (h : DrinfeldDeligneResidueComparisonStatement ι Φ)
    (hcyc : HasDrinfeldCyclicRelations ι π) :
    Nonempty (completedDrinfeldClassFunctor Φ hπ ≅ completedDeligneClassFunctor (D := D) Φ.property.1) := by
  obtain ⟨e, he⟩ := h hcyc
  exact ⟨completedComparisonOfResidue Φ hπ e he⟩

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
