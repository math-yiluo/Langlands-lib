import Langlands.GroupScheme.Reductive.PicardRootWeightLines
import Langlands.Geometry.FormalGroup.DeligneLineSheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Finite projective rank-one modules give affine line sheaves -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open _root_.CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
private def basicOpenLineSections (f : R)
    (e : LocalizedModule.Away f M ≃ₗ[Localization.Away f] Localization.Away f) :
    Γ(tilde M, PrimeSpectrum.basicOpen f) ≃ₗ[Γ(Spec R, PrimeSpectrum.basicOpen f)]
      Γ(Spec R, PrimeSpectrum.basicOpen f) := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let A := Γ(Spec R, U)
  let e₁ : LocalizedModule.Away f M ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (PrimeSpectrum.basicOpen f)) :=
    IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap _ M) (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
  let e₁' : LocalizedModule.Away f M ≃ₗ[R] Γ(tilde M, U) := e₁
  let e₂ : Localization.Away f ≃ₐ[R] A := IsLocalization.algEquiv (Submonoid.powers f) _ _
  exact LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers f) A
    (e₁'.symm.trans ((e.restrictScalars R).trans e₂.toLinearEquiv))

set_option backward.isDefEq.respectTransparency false in
/-- A line basis over a principal localization yields an actual sheaf trivialization. -/
def affineLineTrivialization (f : R)
    (e : LocalizedModule.Away f M ≃ₗ[Localization.Away f] Localization.Away f) :
    let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
    (tilde M).restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let hU : IsAffineOpen U := IsAffineOpen.Spec_basicOpen f
  let A := Γ(Spec R, U)
  let j := hU.fromSpec
  let N : (Spec A).Modules := (tilde M).restrict j
  let V : (Spec A).Opens := ⊤
  let U' := j ''ᵁ V
  have himage : U' = U := j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let eU : Γ(tilde M, U') ≃ₗ[Γ(Spec R, U')] Γ(Spec R, U') := by
    rw [himage]
    exact basicOpenLineSections M f e
  let res := (tilde M).restrictAppIso j V
  let α := j.appIso V ≪≫ Scheme.ΓSpecIso A
  let g : (moduleSpecΓFunctor.obj N) →+ A :=
    α.hom.hom.toAddMonoidHom.comp (eU.toLinearMap.toAddMonoidHom.comp res.hom.hom)
  let gL : (moduleSpecΓFunctor.obj N) →ₗ[A] A :=
    { __ := g
      map_smul' a x := by
        change α.hom (eU (res.hom (a • x))) = a • α.hom (eU (res.hom x))
        rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_restrictAppIso_hom_apply,
          map_smul, smul_eq_mul, map_mul, smul_eq_mul]
        have hV : (⊤ : (Spec A).Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
        simp [α, res, hV]
        exact congrArg (fun c : A => c * _) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso A) a) }
  let eN : (moduleSpecΓFunctor.obj N) ≃ₗ[A] A :=
    LinearEquiv.ofBijective gL ((ConcreteCategory.bijective_of_isIso α.hom).comp
      (eU.bijective.comp (ConcreteCategory.bijective_of_isIso res.hom)))
  let nIso : N ≅ SheafOfModules.unit (Spec A).ringCatSheaf :=
    (asIso N.fromTildeΓ).symm ≪≫ (tilde.functor A).mapIso eN.toModuleIso ≪≫ tildeSelf
  let k := hU.isoSpec.hom
  exact ((Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app (tilde M)).symm ≪≫
    (Scheme.Modules.restrictFunctorComp k j).app (tilde M) ≪≫
    (Scheme.Modules.restrictFunctor k).mapIso nIso ≪≫ Scheme.Modules.restrictUnitIso k

set_option backward.isDefEq.respectTransparency false in
/-- A finite projective module of rank one at every prime has an associated line sheaf. -/
theorem isLineSheaf_tilde_of_rankAtStalk [Module.Finite R M] [Module.Projective R M]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1) :
    IsLineSheaf (Spec R) (tilde M) :=
  Langlands.Algebra.isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one M hrank

end Langlands.DeligneFormalSpace
