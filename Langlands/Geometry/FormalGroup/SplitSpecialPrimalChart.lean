import Langlands.Geometry.FormalGroup.FormalIdempotentLocalImage
import Langlands.Geometry.FormalGroup.HarrisSplitSpecialAffine
import Langlands.Geometry.FormalGroup.SplitDivisionCentralScalars
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Special formal division-module charts of the split primal image -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.Harris

open ValuativeRel ModuleLaw LocalDivision

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Algebra ℤ_[prime] 𝒪[K]]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

local instance primalDivisionPadicAlgebra : Algebra ℤ_[prime] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[prime] 𝒪[K])

variable {R : Type} [CommRing R] [Algebra ℤ_[prime] R]
variable {σ : Type} [Finite σ] {M : ModuleLaw ℤ_[prime] R σ}
variable (E : OrderAction ((IntegerRing K D)ᵐᵒᵖ × IntegerRing K D) M)

/-- A coordinate presentation of the actual division projector on a principal open. -/
abbrev PrimalImageChart (a : R) :=
  Σ N : ModuleLaw ℤ_[prime] (Localization.Away a) (Fin (CentralSimple.reducedDegree K D)),
    (E.map (IsScalarTower.toAlgHom ℤ_[prime] R (Localization.Away a))).DivisionImage N

/-- The geometric character condition fixes the dimension of the formal projector
image on a principal open containing the given point. -/
theorem exists_primalImageChart
    (hgeo : E.HasGeometricDivisionTangentCharacters.{0, u, 0, u, s}
      (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D))
    (x : PrimeSpectrum R) : ∃ a : R, a ∉ x.asIdeal ∧ Nonempty (PrimalImageChart E a) := by
  obtain ⟨a, ha, n, ⟨image⟩⟩ := Hom.IdempotentImage.exists_basicOpen E.divisionProjector
    E.divisionProjector_comp x
  let φ := IsScalarTower.toAlgHom ℤ_[prime] R (Localization.Away a)
  let κ := AlgebraicClosure (ULift.{u} x.asIdeal.ResidueField)
  let j : x.asIdeal.ResidueField →+* κ :=
    (algebraMap (ULift.{u} x.asIdeal.ResidueField) κ).comp ULift.ringEquiv.symm.toRingHom
  let g := j.comp (algebraMap R x.asIdeal.ResidueField)
  have ha0 : algebraMap R x.asIdeal.ResidueField a ≠ 0 :=
    fun h => ha (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hag : IsUnit (g a) := IsUnit.mk0 _ (by
    change j (algebraMap R x.asIdeal.ResidueField a) ≠ 0
    exact (map_ne_zero j).mpr ha0)
  let g' : Localization.Away a →+* κ := IsLocalization.Away.lift a hag
  obtain ⟨H⟩ := hgeo.map φ κ g'
  have A : (E.map φ).DivisionImage image.1 := image.2
  have hdim := (A.tangentEquiv g').trans H.coordinates
  have hn : n = CentralSimple.reducedDegree K D := by
    simpa only [Module.finrank_fin_fun] using hdim.finrank_eq
  subst n
  exact ⟨a, ha, ⟨image⟩⟩

variable [Algebra 𝒪[K] R]

/-- The actual image law is a special formal division module on its chart. -/
def primalSpecialChart (a : R) (A : PrimalImageChart E a)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (hstr : E.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] R))
    (hgeo : E.HasGeometricDivisionTangentCharacters.{0, u, 0, u, s}
      (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D)) :
    SpecialModule K D ι (Localization.Away a) := by
  let φ := IsScalarTower.toAlgHom ℤ_[prime] R (Localization.Away a)
  have hstr' : (E.map φ).HasStructuralDivisionTangent
      (algebraMap 𝒪[K] (IntegerRing K D)) (algebraMap 𝒪[K] (Localization.Away a)) := by
    rw [IsScalarTower.algebraMap_eq 𝒪[K] R (Localization.Away a)]
    exact hstr.map φ
  exact {
    formalModule := A.2.centralModule hstr'
    order := A.2.centralOrder hstr'
    unramified := hL
    tangent := A.2.centralOrder_hasGeometricTangentCharacters hstr' (hgeo.map φ) }

variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable {ϖ : 𝒪[K]} {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}

/-- Every affine split-special target has principal charts on its actual division image. -/
theorem HasSplitSpecialTangent.exists_primalImageChart (h : HasSplitSpecialTangent ι X)
    (x : PrimeSpectrum T.obj) :
    ∃ a : T.obj, a ∉ x.asIdeal ∧ Nonempty (PrimalImageChart X.target.order a) :=
  Harris.exists_primalImageChart X.target.order h.2.2 x

/-- The actual special formal division module on a chart of an affine split-special target. -/
def HasSplitSpecialTangent.primalSpecialChart (h : HasSplitSpecialTangent ι X)
    {a : T.obj} (A : PrimalImageChart X.target.order a) :
    SpecialModule K D ι (Localization.Away a) :=
  Harris.primalSpecialChart X.target.order a A h.1 h.2.1 h.2.2

end Langlands.FormalGroup.Harris
