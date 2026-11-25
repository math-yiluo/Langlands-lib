/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionOrdinaryNormalizedMap
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionOrdinaryNormalizedIso

/-! Ordinary generator normalization for a fixed sectionwise scalar model.

## References

* Stacks 03EK and 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- A fixed sectionwise model admits the ordinary comparison normalized on generators. -/
theorem scalar_section_ordinary_comparison_exists (T : Scheme.{u})
    (model : SectionModel a T) :
    ∃ ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ≅
      (equivalence Λ T).functor ⋙ model.E,
      ∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
        (((ordinary.hom.app M) ≫ eqToHom (model.obj_eq _)).val.app W)
            (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
          (toSheafify (Scheme.ProEt.topology T)
            (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
              ((equivalence Λ T).functor.obj M)).presheaf).app W
                ((1 : (ring Λ' T).obj.obj W)
                  ⊗ₜ[(ring Λ T).obj.obj W,
                    ((sectionQuotient a T).hom.app W).hom] m) := by
  obtain ⟨ordinary, hordinary⟩ := scalar_section_ordinary_normalized_map a T model
  have hIso : ∀ M : Modules Λ T, IsIso (ordinary.app M) :=
    scalar_section_ordinary_normalized_isIso a T model ordinary hordinary
  let comparison : QuotientChange.extension a T ⋙
      (equivalence Λ' T).functor ≅
      (equivalence Λ T).functor ⋙ model.E :=
    NatIso.ofComponents (fun M => by
      letI := hIso M
      exact asIso (ordinary.app M)) (by
      intro M N f
      letI := hIso M
      letI := hIso N
      exact (ordinary.naturality f).trans (by simp))
  refine ⟨comparison, ?_⟩
  intro M W m
  simpa [comparison] using hordinary M W m

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
