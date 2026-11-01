import Langlands.AlgebraicGeometry.Modules.FiniteFlatPushforwardStructureStatement
import Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Closure
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne

/-! # Affine sections and rank of the actual structure-module pushforward -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules

open QuasicoherentLocal

private def affinePresentation {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : M.Presentation := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact SheafOfModules.Presentation.ofIsIso.{u, u, u} M.fromTildeΓ
    (presentationTilde (moduleSpecΓFunctor.obj M) Set.univ (by simp) _ (Submodule.span_eq _))

private theorem isQuasicoherent_of_affineLocal {X : Scheme.{u}} (M : X.Modules)
    (hM : IsAffineLocallyQuasicoherent M) : M.IsQuasicoherent := by
  classical
  let U : X.affineOpens → X.Opens := Subtype.val
  have hU (x : X.affineOpens) : IsAffineOpen (U x) := x.2
  have hcov : (_root_.Opens.grothendieckTopology X).CoversTop U := by
    exact (_root_.Opens.coversTop_iff X U).mpr (iSup_affineOpens_eq_top X)
  let pres (x : X.affineOpens) : (M.restrict (U x).ι).Presentation := by
    have := hM (U x) (hU x)
    let p := affinePresentation (M.restrict (hU x).fromSpec)
    let q := Scheme.Modules.presentationRestrict (hU x).isoSpec.hom p
    let e := ((Scheme.Modules.restrictFunctorComp
      (hU x).isoSpec.hom (hU x).fromSpec).app M).symm ≪≫
        ((Scheme.Modules.restrictFunctorCongr (hU x).isoSpec_hom_fromSpec).app M)
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u} e.hom q
  let q : M.QuasicoherentData := {
    I := X.affineOpens
    X := U
    coversTop := hcov
    presentation := fun x => by
      let E := Scheme.Modules.overEquiv (U x)
      have : PreservesColimitsOfSize.{u, u} E.inverse :=
        inferInstanceAs (PreservesColimitsOfSize.{u, u}
          (Scheme.Modules.overEquiv (U x)).inverse)
      let p := (pres x).map E.inverse
        ((U x).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
      exact SheafOfModules.Presentation.ofIsIso.{u, u, u}
        ((E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv (U x)).app M)).symm ≪≫
          (E.unitIso.app (M.over (U x))).symm).hom p }
  exact q.isQuasicoherent

/-- Finite flat affine sections compute the actual native rank. -/
theorem finiteFlatPushforwardStructure : FiniteFlatPushforwardStructureStatement.{u} := by
  intro X Y f hf hflat
  let : IsFinite f := hf
  let : Flat f := hflat
  have : (Langlands.Scheme.Modules.structureSheaf X).IsQuasicoherent :=
    CechDegreeOne.isQuasicoherent_unit X
  let P := (Scheme.Modules.pushforward f).obj (Langlands.Scheme.Modules.structureSheaf X)
  refine ⟨?_, ?_, ?_⟩
  · exact isQuasicoherent_of_affineLocal P
      (IsAffineLocallyQuasicoherent.pushforward f
        (IsAffineLocallyQuasicoherent.of_isQuasicoherent _))
  · intro U
    let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    constructor
    · exact f.finite_app U.1 U.2
    · have h : (f.app U.1).hom.Flat := by
        simpa only [Scheme.Hom.app_eq_appLE] using
          f.flat_appLE U.2 (U.2.preimage f) le_rfl
      exact h
  · intro hY U x hx
    let : IsIntegral Y := hY
    let : Nonempty U.1 := ⟨⟨x, hx⟩⟩
    let : IsDomain Γ(Y, U.1) := IsIntegral.component_integral _
    let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    have hfin := f.finite_app U.1 U.2
    have hV : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
    have hflat' : (f.app U.1).hom.Flat := by
      simpa only [Scheme.Hom.app_eq_appLE] using f.flat_appLE U.2 hV le_rfl
    let : Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := hfin
    let : Module.Flat Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := hflat'
    let : IsFinite (Spec.map (f.app U.1)) := (IsFinite.SpecMap_iff _).mpr hfin
    let : Flat (Spec.map (f.app U.1)) := Flat.SpecMap_iff.mpr hflat'
    have hpb := IsOpenImmersion.isPullback (Spec.map (f.app U.1))
      hV.fromSpec U.2.fromSpec f
      (by simpa only [Scheme.Hom.app_eq_appLE] using
        (U.2.SpecMap_appLE_fromSpec f hV le_rfl).symm)
      (by rw [U.2.opensRange_fromSpec, hV.opensRange_fromSpec])
    have hr := Scheme.Hom.finrank_of_isPullback hV.fromSpec
      (Spec.map (f.app U.1)) f U.2.fromSpec hpb.flip (U.2.primeIdealOf ⟨x, hx⟩)
    rw [U.2.fromSpec_primeIdealOf] at hr
    rw [Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat'] at hr
    change Module.rankAtStalk Γ(X, f ⁻¹ᵁ U.1) _ = f.finrank x at hr
    rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at hr
    exact hr

end Langlands.AlgebraicGeometry.Modules
