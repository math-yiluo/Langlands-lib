import Langlands.Algebra.NilpotentFlatPresentation
import Langlands.AlgebraicGeometry.Modules.AffineSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent

/-! # Finite presentations of affine sheaves across nilpotent base reduction -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

variable (A : Type v) (B : CommRingCat.{u}) [CommRing A] [Algebra A B]
variable (M : (Spec B).Modules) [M.IsQuasicoherent]
variable [Module A (moduleSpecΓFunctor.obj M)]
variable [IsScalarTower A B (moduleSpecΓFunctor.obj M)]
variable [Module.Flat A (moduleSpecΓFunctor.obj M)]

/-- A finite global presentation of the actual reduced pullback makes affine sections
finitely presented before nilpotent base reduction, when these sections are base-flat. -/
lemma finitePresentation_moduleSpecΓFunctor_of_base_nilpotent
    (I : Ideal A) (hI : IsNilpotent I)
    (P : ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))))).obj
        M).Presentation) [P.IsFinite] :
    Module.FinitePresentation B (moduleSpecΓFunctor.obj M) := by
  let J := I.map (algebraMap A B)
  let φ : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have : Module.FinitePresentation (B ⧸ J)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) :=
    finitePresentation_moduleSpecΓFunctor_of_presentation P
  have : Module.FinitePresentation (B ⧸ J)
      ((B ⧸ J) ⊗[B] (moduleSpecΓFunctor.obj M)) :=
    Module.FinitePresentation.of_equiv
      (Langlands.Scheme.Modules.affineScalarSectionsIso φ M).symm.toLinearEquiv
  exact Langlands.Algebra.finitePresentation_of_base_nilpotent A B I hI

/-- A finite presentation of the actual reduced pullback lifts to a finite global
presentation of the existing quasi-coherent sheaf. -/
lemma exists_presentation_of_base_nilpotent (I : Ideal A) (hI : IsNilpotent I)
    (P : ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))))).obj
        M).Presentation) [P.IsFinite] :
    ∃ Q : M.Presentation, Q.IsFinite := by
  have := finitePresentation_moduleSpecΓFunctor_of_base_nilpotent A B M I hI P
  obtain ⟨Q, hQ⟩ := exists_presentation_tilde (moduleSpecΓFunctor.obj M)
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨Q.ofIsIso M.fromTildeΓ, inferInstance⟩

/-- Choose a finite global presentation of the existing sheaf from a finite global
presentation of its actual nilpotent reduction. -/
def finitePresentationOfBaseNilpotent (I : Ideal A) (hI : IsNilpotent I)
    (P : ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))))).obj
        M).Presentation) [P.IsFinite] :
    {Q : M.Presentation // Q.IsFinite} :=
  ⟨Classical.choose (exists_presentation_of_base_nilpotent A B M I hI P),
    Classical.choose_spec (exists_presentation_of_base_nilpotent A B M I hI P)⟩

/-- Local finite presentation of an affine quasi-coherent sheaf follows from a finite
global presentation of its actual nilpotent reduction and base-flat affine sections. -/
lemma isFinitePresentation_of_base_nilpotent (I : Ideal A) (hI : IsNilpotent I)
    (P : ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap A B)))))).obj
        M).Presentation) [P.IsFinite] :
    M.IsFinitePresentation := by
  obtain ⟨Q, hQ⟩ := exists_presentation_of_base_nilpotent A B M I hI P
  exact isFinitePresentation_of_presentation Q

end Langlands.AlgebraicGeometry.Modules
