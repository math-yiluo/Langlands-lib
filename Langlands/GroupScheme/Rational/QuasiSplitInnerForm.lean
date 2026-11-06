import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.LocalGroupIso
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.FieldTheory.Galois.Basic

/-! # Actual finite-Galois inner twisting from a quasi-split group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K]

/-- An actual quasi-split inner-form presentation, retaining the adjoint quotient
and the discrepancy of the local isomorphisms on every relative test scheme. -/
structure QuasiSplitInnerForm (G : GroupScheme (Spec (CommRingCat.of K))) where
  model : GroupScheme (Spec (CommRingCat.of K))
  isQuasiSplit : IsQuasiSplit model
  adjoint : GroupScheme (Spec (CommRingCat.of K))
  quotient : model ⟶ adjoint
  isAdjointQuotient : IsAdjointQuotient quotient
  isQuasiSplit_adjoint : IsQuasiSplit adjoint
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  [isGalois : IsGalois K carrier]
  localIso : LocalGroupIso model G
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K carrier))))
  cocycle : Cocycle adjoint
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K carrier))))
  hasDiscrepancy : localIso.HasDiscrepancy isAdjointQuotient.innerAction cocycle

attribute [instance] QuasiSplitInnerForm.field QuasiSplitInnerForm.algebra
  QuasiSplitInnerForm.finiteDimensional QuasiSplitInnerForm.isGalois

namespace QuasiSplitInnerForm

variable {G : GroupScheme (Spec (CommRingCat.of K))} (d : QuasiSplitInnerForm G)

/-- Triviality of the actual adjoint discrepancy produces a ground-field isomorphism. -/
def isoOfTrivial (h : d.cocycle.IsTrivial) : d.model ≅ G := by
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K d.carrier
  letI : Surjective
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))).hom := hsurj
  letI : Flat
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))).hom := hflat
  letI : QuasiCompact
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))).hom := hqc
  exact d.localIso.descendOfTrivial d.isAdjointQuotient.innerAction
    d.cocycle d.hasDiscrepancy h

/-- A trivial adjoint discrepancy transports the actual geometric Borel to the given group. -/
theorem isQuasiSplit_of_isTrivial (h : d.cocycle.IsTrivial) : IsQuasiSplit G :=
  d.isQuasiSplit.of_iso (d.isoOfTrivial h).symm

end QuasiSplitInnerForm

end Langlands.GroupScheme
