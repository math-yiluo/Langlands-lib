import Langlands.GroupScheme.Rational.NumberFieldHassePrincipleStatement
import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction

/-! # Reduction of the number-field Hasse principle to finite Galois covers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

variable {S S' : Scheme.{u}} {G : GroupScheme S} {U V : Over S}

/-- Refining a cover commutes, on cocycle values, with its pullback to a new base. -/
theorem baseChange_pullback_refine_toFun (ξ : Cocycle G U) (s : V ⟶ U) (b : S' ⟶ S)
    {Z : Over S'} (x y : Z ⟶ (Over.pullback b).obj V) :
    ((ξ.refine s).baseChange b _ ((Over.mapPullbackAdj b).counit.app V)).toFun x y =
      ((ξ.baseChange b _ ((Over.mapPullbackAdj b).counit.app U)).refine
        ((Over.pullback b).map s)).toFun x y := by
  apply (baseChangePointsEquiv b G Z).injective
  have hs : (Over.map b).map ((Over.pullback b).map s) ≫
      (Over.mapPullbackAdj b).counit.app U =
      (Over.mapPullbackAdj b).counit.app V ≫ s :=
    (Over.mapPullbackAdj b).counit.naturality s
  simp only [refine_toFun, baseChange_toFun, Functor.map_comp, Category.assoc, hs]

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {U V : Over (Spec (CommRingCat.of F))}

/-- Two cocycles on an arbitrary cover over a number field are locally cohomologous when
their pullbacks are cohomologous over every completion. -/
def LocallyCohomologous (ξ ζ : Cocycle G U) : Prop :=
  ∀ i : Langlands.Global.Place F,
    let b := algebraBaseMap F (Langlands.Global.placeCompletion F i)
    let r := (Over.mapPullbackAdj b).counit.app U
    (ξ.baseChange b _ r).Cohomologous (ζ.baseChange b _ r)

/-- Local cohomology is preserved under arbitrary refinement of the cover. -/
theorem LocallyCohomologous.refine {ξ ζ : Cocycle G U}
    (h : ξ.LocallyCohomologous ζ) (s : V ⟶ U) :
    (ξ.refine s).LocallyCohomologous (ζ.refine s) := by
  intro i
  let b := algebraBaseMap F (Langlands.Global.placeCompletion F i)
  obtain ⟨f, hf⟩ := (h i).refine ((Over.pullback b).map s)
  refine ⟨f, fun x y => ?_⟩
  rw [baseChange_pullback_refine_toFun]
  rw [hf]
  simp only [twist, baseChange_pullback_refine_toFun, b]

end Cocycle

open Langlands.GroupScheme.Quaternionic

/-- The number-field Hasse principle for the same three group classes, restricted to
finite Galois covers. This is an internal reduction target, not an assumed theorem. -/
def NumberFieldGaloisHassePrincipleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    (IsSimplyConnected G ∨ IsAdjoint G ∨
      ∃ (m : ℕ) (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin m)),
        (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q ∧
          Nonempty (G ≅ (FirstKindInvolution.scalar F).isometryGroup q)) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ ζ : Cocycle G (Over.mk (algebraBaseMap F L))),
      ξ.LocallyCohomologous ζ → ξ.Cohomologous ζ

/-- A finite separable cover embeds into a finite Galois cover, where the hypothesis
applies. Fpqc reflection then descends the resulting cochain. -/
theorem numberFieldHassePrinciple_of_galois
    (h : NumberFieldGaloisHassePrincipleStatement.{u}) :
    NumberFieldHassePrincipleStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ ζ hlocal
  obtain ⟨E, hfin, hgal, ⟨φ⟩⟩ := exists_finite_galois_algHom F L
  let : Algebra L E := φ.toRingHom.toAlgebra
  obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc L E
  let : Surjective (ringTestMap F φ).left := h₁
  let : Flat (ringTestMap F φ).left := h₂
  let : QuasiCompact (ringTestMap F φ).left := h₃
  let ξ' : Cocycle G (ringTest F L) := ξ
  let ζ' : Cocycle G (ringTest F L) := ζ
  have hl : ξ'.LocallyCohomologous ζ' := hlocal
  have hE := h F G hG E (ξ'.refine (ringTestMap F φ)) (ζ'.refine (ringTestMap F φ))
    (hl.refine (ringTestMap F φ))
  exact (ξ'.cohomologous_refine_iff ζ' (ringTestMap F φ)).mp hE

/-- The original Hasse principle specializes to finite Galois covers. -/
theorem numberFieldGaloisHassePrinciple_of_separable
    (h : NumberFieldHassePrincipleStatement.{u}) :
    NumberFieldGaloisHassePrincipleStatement.{u} := by
  intro F _ _ G hG L _ _ _ _ ξ ζ hlocal
  exact h F G hG L ξ ζ hlocal

/-- The finite Galois reduction retains all fields, universes, group classes and places. -/
theorem numberFieldGaloisHassePrinciple_iff :
    NumberFieldGaloisHassePrincipleStatement.{u} ↔ NumberFieldHassePrincipleStatement.{u} :=
  ⟨numberFieldHassePrinciple_of_galois, numberFieldGaloisHassePrinciple_of_separable⟩

end Langlands.GroupScheme
