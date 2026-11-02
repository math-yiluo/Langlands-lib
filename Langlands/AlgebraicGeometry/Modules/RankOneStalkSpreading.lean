import Langlands.AlgebraicGeometry.Modules.AffineRankOneSpreading
import Langlands.AlgebraicGeometry.Modules.RestrictionStalkLinearEquiv

/-! # Rank-one stalk spreading on arbitrary schemes -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- The actual stalk of the sheaf associated to a finitely presented module is
finitely presented over the actual local ring. -/
lemma finitePresentation_tilde_stalk {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] (x : Spec R) :
    Module.FinitePresentation ((Spec R).presheaf.stalk x) (stalk (tilde M) x) := by
  let : Algebra R ((Spec R).presheaf.stalk x) :=
    inferInstanceAs (Algebra R ((structurePresheafInCommRingCat R).stalk x))
  let : IsLocalization x.asIdeal.primeCompl ((Spec R).presheaf.stalk x) :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat R).stalk x))
  let : IsScalarTower R ((Spec R).presheaf.stalk x) (stalk (tilde M) x) :=
    inferInstanceAs (IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))
  exact FinitePresentation.of_isBaseChange (tilde.toStalk M x).hom
    (IsLocalizedModule.isBaseChange x.asIdeal.primeCompl
      ((Spec R).presheaf.stalk x) (tilde.toStalk M x).hom)

/-- Finite presentation of actual affine global sections gives finite
presentation of every actual stalk of a quasi-coherent module sheaf. -/
lemma finitePresentation_spec_stalk {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] [Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤)]
    (x : Spec R) :
    Module.FinitePresentation ((Spec R).presheaf.stalk x) (stalk M x) := by
  have : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) :=
    finitePresentation_moduleSpecΓFunctor M
  let t : tilde (moduleSpecΓFunctor.obj M) ≅ M := asIso M.fromTildeΓ
  have : Module.FinitePresentation ((Spec R).presheaf.stalk x)
      (stalk (tilde (moduleSpecΓFunctor.obj M)) x) :=
    finitePresentation_tilde_stalk (moduleSpecΓFunctor.obj M) x
  exact Module.FinitePresentation.of_equiv (stalkIso t x)

/-- Local finite presentation gives a spectrum chart containing a specified
point with a finite presentation of the actual restricted module. -/
lemma exists_Spec_finitePresentation_restrict (M : X.Modules) [M.IsFinitePresentation]
    (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
      f y = x ∧ ∃ (P : (M.restrict f).Presentation), P.IsFinite := by
  obtain ⟨U, hxU, P, hP⟩ := exists_finitePresentation_restrict M x
  let := hP
  obtain ⟨R, f, hf, y, hy⟩ :=
    Scheme.exists_Spec_apply_eq (X := U.toScheme) (⟨x, hxU⟩ : U.toScheme)
  let := hf
  let g := f ≫ U.ι
  let e : M.restrict g ≅ (Scheme.Modules.pullback f).obj (M.restrict U.ι) :=
    (Scheme.Modules.restrictFunctorComp f U.ι).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback f).app (M.restrict U.ι)
  let Q := (presentationPullback f P).ofIsIso e.inv
  refine ⟨R, g, inferInstance, y, ?_, Q, inferInstance⟩
  change U.ι (f y) = x
  rw [hy]
  rfl

/-- Such a chart has finitely presented actual global sections. -/
lemma exists_Spec_finitePresentation_sections (M : X.Modules) [M.IsFinitePresentation]
    (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
      f y = x ∧ Module.FinitePresentation Γ(Spec R, ⊤) Γ(M.restrict f, ⊤) := by
  obtain ⟨R, f, hf, y, hy, P, hP⟩ := exists_Spec_finitePresentation_restrict M x
  let := hf
  let := hP
  exact ⟨R, f, hf, y, hy,
    finitePresentation_sections_of_presentation (M.restrict f) P ⊤ (isAffineOpen_top _)⟩

/-- A rank-one actual stalk of a locally finitely presented module sheaf has an
actual trivializing open neighbourhood, over an arbitrary scheme. -/
lemma mem_rankOneLocus_of_stalkEquiv (M : X.Modules) [M.IsFinitePresentation]
    (x : X) (e : stalk M x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) :
    x ∈ Picard.rankOneLocus M := by
  obtain ⟨R, f, hf, y, hy, hM⟩ := exists_Spec_finitePresentation_sections M x
  let := hf
  let := hM
  subst x
  have h := mem_rankOneLocus_spec_of_stalkEquiv (M.restrict f) y
    (restrictStalkRankOneEquiv f M y e)
  rw [Picard.rankOneLocus_restrict] at h
  exact h

/-- Select an actual trivializing neighbourhood of a rank-one stalk of a
locally finitely presented module sheaf on any scheme. -/
def rankOneTrivializingNeighbourhood (M : X.Modules) [M.IsFinitePresentation]
    (x : X) (e : stalk M x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) :
    {U : X.Opens // x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)} :=
  let h := (Picard.mem_rankOneLocus M x).mp (mem_rankOneLocus_of_stalkEquiv M x e)
  ⟨h.choose, h.choose_spec⟩

end Langlands.AlgebraicGeometry.Modules
