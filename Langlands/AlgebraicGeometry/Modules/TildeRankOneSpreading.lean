import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Langlands.AlgebraicGeometry.Picard.LineBundleLocusRestriction
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.BaseChange

/-! # Spreading a rank-one stalk trivialization of an associated sheaf -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- A rank-one trivialization at an actual stalk of an associated sheaf spreads
to an actual pullback trivialization over some principal localization. -/
lemma exists_tilde_localization_trivialization [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    (e : stalk (tilde M) x ≃ₗ[(Spec R).presheaf.stalk x] (Spec R).presheaf.stalk x) :
    ∃ (r : R), r ∉ x.asIdeal ∧
      Nonempty ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj (tilde M) ≅
        SheafOfModules.unit (Spec (.of (Localization.Away r))).ringCatSheaf) := by
  let : Algebra R ((Spec R).presheaf.stalk x) :=
    inferInstanceAs (Algebra R ((structurePresheafInCommRingCat R).stalk x))
  let : IsLocalization x.asIdeal.primeCompl ((Spec R).presheaf.stalk x) :=
    inferInstanceAs (IsLocalization x.asIdeal.primeCompl
      ((structurePresheafInCommRingCat R).stalk x))
  let : IsScalarTower R ((Spec R).presheaf.stalk x) (stalk (tilde M) x) :=
    inferInstanceAs (IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))
  obtain ⟨r, hr, l, _⟩ :=
    Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule x.asIdeal.primeCompl
      (tilde.toStalk M x).hom (Algebra.linearMap R ((Spec R).presheaf.stalk x))
      (e.restrictScalars R)
  let A : CommRingCat.{u} := .of (Localization.Away r)
  let a : (Localization.Away r) ⊗[R] M ≃ₗ[Localization.Away r] Localization.Away r :=
    (LocalizedModule.equivTensorProduct (.powers r) M).symm ≪≫ₗ l ≪≫ₗ
      LocalizedModule.equivTensorProduct (.powers r) R ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid R (Localization.Away r) (Localization.Away r)
  exact ⟨r, hr, ⟨Langlands.Scheme.Modules.tildePullbackAlgebraIso R A M ≪≫
    (tilde.functor A).mapIso a.toModuleIso ≪≫ tildeSelf⟩⟩

/-- Finite presentation makes a rank-one actual stalk lie in the actual open
rank-one locus of the associated sheaf. -/
lemma mem_rankOneLocus_tilde_of_stalkEquiv [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    (e : stalk (tilde M) x ≃ₗ[(Spec R).presheaf.stalk x] (Spec R).presheaf.stalk x) :
    x ∈ Picard.rankOneLocus (tilde M) := by
  obtain ⟨r, hr, ⟨t⟩⟩ := exists_tilde_localization_trivialization M x e
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  have hx : x ∈ f.opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hr
  change x ∈ Set.range f at hx
  obtain ⟨y, hy⟩ := hx
  let t' : (tilde M).restrict f ≅ SheafOfModules.unit (Spec (.of (Localization.Away r))).ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback f).app (tilde M)) ≪≫ t
  have h : Picard.IsLocallyFreeRankOne ((tilde M).restrict f) :=
    (Picard.LineBundle.trivial _).property.of_iso t'.symm
  have hy' : y ∈ Picard.rankOneLocus ((tilde M).restrict f) :=
    (Picard.mem_rankOneLocus _ y).mpr (h y)
  rw [Picard.rankOneLocus_restrict] at hy'
  change f y ∈ Picard.rankOneLocus (tilde M) at hy'
  simpa only [hy] using hy'

/-- Choose an actual trivializing open neighbourhood from a rank-one stalk
trivialization of an associated sheaf with finitely presented defining module. -/
def tildeRankOneTrivializingNeighbourhood [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    (e : stalk (tilde M) x ≃ₗ[(Spec R).presheaf.stalk x] (Spec R).presheaf.stalk x) :
    {U : (Spec R).Opens // x ∈ U ∧
      Nonempty ((tilde M).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)} :=
  let h := (Picard.mem_rankOneLocus (tilde M) x).mp
    (mem_rankOneLocus_tilde_of_stalkEquiv M x e)
  ⟨h.choose, h.choose_spec⟩

end Langlands.AlgebraicGeometry.Modules
