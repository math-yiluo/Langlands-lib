import Langlands.Geometry.FormalGroup.DivisionImageOrderAtlas
import Langlands.Geometry.FormalGroup.OrderActionCentralAtlas
import Langlands.Geometry.FormalGroup.SpecialAtlas
import Langlands.Geometry.FormalGroup.SplitSpecialPrimalChart

/-! # Special formal division-module atlas of the split primal image -/

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

attribute [local instance] primalDivisionPadicAlgebra

variable {R : Type} [CommRing R] [Algebra ℤ_[prime] R]
variable {σ : Type} [Finite σ] {M : ModuleLaw ℤ_[prime] R σ}
variable (E : OrderAction ((IntegerRing K D)ᵐᵒᵖ × IntegerRing K D) M)
variable (hg : E.HasGeometricDivisionTangentCharacters.{0, u, 0, u, s}
  (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D))

include hg in
/-- Principal elements carrying actual image coordinates form a cover of the base. -/
def primalImageCover : IdempotentImageCover E.divisionProjector (Fin (CentralSimple.reducedDegree K D)) where
  opens := {a | Nonempty (PrimalImageChart E a)}
  covers := by
    by_contra h
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ h
    let x : PrimeSpectrum R := ⟨I, hI.isPrime⟩
    obtain ⟨a, ha, A⟩ := exists_primalImageChart E hg x
    exact ha (hle (Ideal.subset_span A))
  image a := Classical.choice a.property

variable [Algebra 𝒪[K] R]
variable (hs : E.HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D)) (algebraMap 𝒪[K] R))

include hs in
private theorem primalImageCover_structuralTangent (b : (primalImageCover E hg).opens)
    (a : 𝒪[K]) (x : Fin (CentralSimple.reducedDegree K D) → Localization.Away b.val) :
    (((primalImageCover E hg).divisionOrder E).chart b).fiberTangent (RingHom.id _)
      (algebraMap 𝒪[K] (IntegerRing K D) a) x = algebraMap 𝒪[K] (Localization.Away b.val) a • x := by
  let φ := IsScalarTower.toAlgHom ℤ_[prime] R (Localization.Away b.val)
  have hs' : (E.map φ).HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] (Localization.Away b.val)) := by
    rw [IsScalarTower.algebraMap_eq 𝒪[K] R (Localization.Away b.val)]
    exact hs.map φ
  exact OrderAction.DivisionImage.structuralCentralTangent (E := E.map φ)
    ((primalImageCover E hg).image b).2 hs' a x

/-- The special atlas uses the actual local projector retractions, their canonical
transitions, and the central division-module law on each chart. -/
def primalSpecialAtlas (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    SpecialAtlas K D ι R where
  atlas := ((primalImageCover E hg).divisionOrder E).centralAtlas
    (primalImageCover_structuralTangent E hg hs)
  order := ((primalImageCover E hg).divisionOrder E).centralAtlasOrder
    (primalImageCover_structuralTangent E hg hs)
  unramified := hL
  tangent b := by
    let φ := IsScalarTower.toAlgHom ℤ_[prime] R (Localization.Away b.val)
    have hs' : (E.map φ).HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
        (algebraMap 𝒪[K] (Localization.Away b.val)) := by
      rw [IsScalarTower.algebraMap_eq 𝒪[K] R (Localization.Away b.val)]
      exact hs.map φ
    exact OrderAction.DivisionImage.centralOrder_hasGeometricTangentCharacters (E := E.map φ)
      ((primalImageCover E hg).image b).2 hs' (hg.map φ)

variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable {ϖ : 𝒪[K]} {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}

/-- The formal atlas of the primal target of an affine split-special point. -/
def HasSplitSpecialTangent.primalSpecialAtlas (h : HasSplitSpecialTangent ι X) :
    SpecialAtlas K D ι T.obj := Harris.primalSpecialAtlas X.target.order h.2.2 h.2.1 h.1

end Langlands.FormalGroup.Harris
