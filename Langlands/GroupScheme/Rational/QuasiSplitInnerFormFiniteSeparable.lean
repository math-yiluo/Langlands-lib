import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.LocalGroupIsoRefinement
import Mathlib.FieldTheory.IsSepClosed

/-! # Finite Galois refinement of a finite-separable inner-form presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitInnerForm

variable {K L M : Type u} [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M]

/-- The actual morphism of field covers induced contravariantly by an embedding. -/
def coverRefinement (f : L →ₐ[K] M) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K M))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext f.comp_algebraMap)

/-- The cover refinement induced by a field embedding is fpqc. -/
theorem coverRefinement_fpqc (f : L →ₐ[K] M) :
    Surjective (coverRefinement f).left ∧ Flat (coverRefinement f).left ∧
      QuasiCompact (coverRefinement f).left := by
  let : Algebra L M := f.toRingHom.toAlgebra
  exact fieldExtension_fpqc L M

variable {G : GroupScheme (Spec (CommRingCat.of K))}

/-- Enlarge a supplied finite-separable inner-form presentation to a finite-Galois
one without changing its quasi-split model, adjoint quotient, or actual action. -/
def ofFiniteSeparable [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (model : GroupScheme (Spec (CommRingCat.of K))) (hmodel : IsQuasiSplit model)
    (adjoint : GroupScheme (Spec (CommRingCat.of K))) (quotient : model ⟶ adjoint)
    (hquotient : IsAdjointQuotient quotient) (hadjoint : IsQuasiSplit adjoint)
    (e : LocalGroupIso model G
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (ξ : Cocycle adjoint
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (h : e.HasDiscrepancy hquotient.innerAction ξ) : QuasiSplitInnerForm G := by
  let N := IntermediateField.normalClosure K L (SeparableClosure K)
  let f : L →ₐ[K] N :=
    (normalClosure.algHomEquiv K L (SeparableClosure K)).symm IsSepClosed.lift
  let r := coverRefinement f
  exact {
    model := model
    isQuasiSplit := hmodel
    adjoint := adjoint
    quotient := quotient
    isAdjointQuotient := hquotient
    isQuasiSplit_adjoint := hadjoint
    carrier := N
    field := inferInstance
    algebra := inferInstance
    finiteDimensional := inferInstance
    isGalois := inferInstance
    localIso := e.refine r
    cocycle := ξ.refine r
    hasDiscrepancy := h.refine r }

end Langlands.GroupScheme.QuasiSplitInnerForm
