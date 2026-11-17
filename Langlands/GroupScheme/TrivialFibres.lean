import Langlands.AbelianScheme.GroupScheme
import Langlands.AlgebraicGeometry.DiscreteValuationFibreIsomorphism

/-! # Group schemes with trivial residue-field fibres -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A locally finite-type group scheme all of whose residue-field fibres are trivial
is the trivial group scheme. No flatness or separatedness hypothesis is needed. -/
theorem isIso_hom_of_residueField_fibres {S : Scheme.{u}} (K : GroupScheme S)
    [LocallyOfFiniteType K.X.hom]
    (hK : ∀ s : S, IsIso ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj K).X.hom) :
    IsIso K.X.hom := by
  let e : Over.mk (𝟙 S) ⟶ K.X := η[K.X]
  have : Flat (Over.mk (𝟙 S)).hom := inferInstanceAs (Flat (𝟙 S))
  have : LocallyOfFinitePresentation (Over.mk (𝟙 S)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 S))
  have he : IsIso e := by
    apply Langlands.AlgebraicGeometry.isIso_of_residueField_fibres e
    intro s
    have : IsIso ((Over.pullback (S.fromSpecResidueField s)).obj K.X).hom := hK s
    let es := (Over.pullback (S.fromSpecResidueField s)).map e
    have : IsIso ((Over.pullback (S.fromSpecResidueField s)).obj
        (Over.mk (𝟙 S))).hom := by
      change IsIso (Limits.pullback.snd (𝟙 S) (S.fromSpecResidueField s))
      infer_instance
    have : IsIso es.left := IsIso.of_isIso_fac_right es.w
    have : IsIso ((Over.forget _).map es) := ‹IsIso es.left›
    exact isIso_of_reflects_iso es (Over.forget _)
  have : IsIso e.left := Functor.map_isIso (Over.forget S) e
  have hsec : e.left ≫ K.X.hom = 𝟙 S := e.w
  rw [IsIso.eq_inv_of_hom_inv_id hsec]
  infer_instance

/-- The canonical isomorphism with the base for a locally finite-type group scheme
whose residue-field fibres are trivial. Its forward map is the structure map. -/
noncomputable def residueFieldTrivialityIso {S : Scheme.{u}} (K : GroupScheme S)
    [LocallyOfFiniteType K.X.hom]
    (hK : ∀ s : S, IsIso ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj K).X.hom) :
    K.X.left ≅ S := by
  have := isIso_hom_of_residueField_fibres K hK
  exact asIso K.X.hom

@[simp]
theorem residueFieldTrivialityIso_hom {S : Scheme.{u}} (K : GroupScheme S)
    [LocallyOfFiniteType K.X.hom]
    (hK : ∀ s : S, IsIso ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj K).X.hom) :
    (residueFieldTrivialityIso K hK).hom = K.X.hom := rfl

end Langlands.GroupScheme
