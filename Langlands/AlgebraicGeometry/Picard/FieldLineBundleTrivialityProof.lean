import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

/-! # Triviality of line bundles on the spectrum of a field -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Every actual line bundle on the spectrum of a field is trivial. -/
theorem fieldLineBundleTriviality : FieldLineBundleTrivialityStatement.{u} := by
  intro K _ L
  let X := Spec (CommRingCat.of K)
  obtain ⟨U, hx, ⟨e⟩⟩ := L.property (default : X)
  have hU : U = ⊤ := by
    apply top_unique
    intro x _
    simpa only [Subsingleton.elim x (default : X)] using hx
  subst U
  let e' : (Scheme.Modules.pullback (⊤ : X.Opens).ι).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (⊤ : X.Opens).toScheme :=
    ((Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app L.obj).symm ≪≫ e
  let back : (Scheme.Modules.pullback X.topIso.inv).obj
      ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj L.obj) ≅ L.obj :=
    (Scheme.Modules.pullbackComp X.topIso.inv (⊤ : X.Opens).ι).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr X.toIso_inv_ι).app L.obj ≪≫
        (Scheme.Modules.pullbackId X).app L.obj
  exact ⟨back.symm ≪≫ (Scheme.Modules.pullback X.topIso.inv).mapIso e' ≪≫
    Langlands.Scheme.Modules.pullbackUnitIso X.topIso.inv⟩

end Langlands.AlgebraicGeometry.Picard
