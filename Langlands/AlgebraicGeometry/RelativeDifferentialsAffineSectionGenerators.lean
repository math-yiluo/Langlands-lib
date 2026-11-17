import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineSections

/-! # Differential generators of the actual affine section comparison -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- A map out of a pullback acts on restricted pulled-back sections by the
restriction of its actual adjoint. -/
theorem app_sectionPullbackLE_eq_adjoint (g : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (α : (AlgebraicGeometry.Scheme.Modules.pullback g).obj M ⟶ N)
    {W : Y.Opens} {T : X.Opens} (h : T ≤ g ⁻¹ᵁ W) (m : Γ(M, W)) :
    α.app T (sectionPullbackLE g M h m) =
      N.presheaf.map (homOfLE h).op
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
          M N α).app W m) := by
  have heq :
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
        M N α).app W m = α.app (g ⁻¹ᵁ W) (sectionPullback g M W m) := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [heq]
  exact PresheafOfModules.naturality_apply α.val (homOfLE h).op
    (sectionPullback g M W m)

end Langlands.Scheme.Modules

namespace Langlands.Scheme

open Langlands.Scheme.Modules

theorem moduleIso_inv_D_of_algebra_eq {R A M : Type u} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] (α β : Algebra R A) (hαβ : α = β)
    (e : letI := α
      ModuleCat.of A M ≅ ModuleCat.of A (KaehlerDifferential R A))
    (a : A) (m : M)
    (he : letI := α
      e.inv (KaehlerDifferential.D R A a) = m) :
    letI := β
    (hαβ ▸ e).toLinearEquiv.symm (KaehlerDifferential.D R A a) = m := by
  cases hαβ
  exact he

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    {U : S.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ f ⁻¹ᵁ U)

theorem affineChartSquareMap_fromSpec_D (a : Γ(X, V)) :
    letI := (f.appLE U V h).hom.toAlgebra
    (moduleSpecΓFunctor (R := Γ(X, V))).map
        (relativeDifferentialsAffineChartSquareMap f hU hV h)
        (fromSpecSectionsLinear (relativeDifferentials f) hV
          ((relativeDifferentialsDerivation f).app V a)) =
      (moduleSpecΓFunctor (R := Γ(X, V))).map
        (relativeDifferentialsSpecMap Γ(S, U) Γ(X, V))
        ((tilde.isoTop (ModuleCat.of Γ(X, V)
          (KaehlerDifferential Γ(S, U) Γ(X, V)))).hom
            (KaehlerDifferential.D Γ(S, U) Γ(X, V) a)) := by
  let := (f.appLE U V h).hom.toAlgebra
  let N := relativeDifferentials (Spec.map (f.appLE U V h))
  let dN := relativeDifferentialsDerivation (Spec.map (f.appLE U V h))
  let ht := hV.fromSpec_preimage_self.ge
  have hleft0 := app_sectionPullbackLE_eq_adjoint hV.fromSpec
    (relativeDifferentials f) N (relativeDifferentialsAffineChartSquareMap f hU hV h)
    ht ((relativeDifferentialsDerivation f).app V a)
  have hleft1 := congrArg (fun m => N.presheaf.map (homOfLE ht).op m)
    (relativeDifferentialsAffineChartSquareMap_adjoint_app f hU hV h V a)
  have hleft2 := dN.app_restrict (homOfLE ht) (hV.fromSpec.app V a)
  have hf : (Spec Γ(X, V)).presheaf.map (homOfLE ht).op (hV.fromSpec.app V a) =
      (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).inv a := by
    change hV.fromSpec.appLE V ⊤ ht a = _
    rw [isAffineOpen_fromSpec_appLE_top]
  have hleft3 := congrArg (fun q => dN.app ⊤ q) hf
  have hleft := hleft0.trans (hleft1.trans (hleft2.symm.trans hleft3))
  have hright := relativeDifferentialsSpecMap_app_toOpen_D Γ(S, U) Γ(X, V) ⊤ a
  have hid : (Spec Γ(X, V)).presheaf.map
      (homOfLE (le_refl (⊤ : (Spec Γ(X, V)).Opens))).op
      ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).inv a) =
      (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).inv a := by
    change (Spec Γ(X, V)).presheaf.map (𝟙 (op ⊤))
      ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).inv a) = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hright' := hright.trans (congrArg (fun q => dN.app ⊤ q) hid)
  exact hleft.trans hright'.symm

/-- The canonical affine section comparison takes each actual differential to
the corresponding algebraic differential. -/
theorem relativeDifferentialsSectionsIso_D (a : Γ(X, V)) :
    letI := (f.appLE U V h).hom.toAlgebra
    (relativeDifferentialsSectionsIso f hU hV h).hom
        ((relativeDifferentialsDerivation f).app V a) =
      KaehlerDifferential.D Γ(S, U) Γ(X, V) a := by
  let := (f.appLE U V h).hom.toAlgebra
  let := relativeDifferentialsSpecMapIsIso Γ(S, U) Γ(X, V)
  let k := (tilde.isoTop (ModuleCat.of Γ(X, V)
      (KaehlerDifferential Γ(S, U) Γ(X, V)))).hom ≫
    (moduleSpecΓFunctor (R := Γ(X, V))).map
      (relativeDifferentialsSpecMap Γ(S, U) Γ(X, V))
  apply (ConcreteCategory.bijective_of_isIso k).1
  exact (congrArg (fun q => q ((relativeDifferentialsDerivation f).app V a))
      (relativeDifferentialsSectionsIso_fac f hU hV h)).trans
    (affineChartSquareMap_fromSpec_D f hU hV h a)

/-- The inverse affine comparison realizes algebraic differential generators as
the actual relative derivation sections. -/
theorem relativeDifferentialsSectionsIso_inv_D (a : Γ(X, V)) :
    letI := (f.appLE U V h).hom.toAlgebra
    (relativeDifferentialsSectionsIso f hU hV h).inv
        (KaehlerDifferential.D Γ(S, U) Γ(X, V) a) =
      (relativeDifferentialsDerivation f).app V a := by
  let := (f.appLE U V h).hom.toAlgebra
  apply (relativeDifferentialsSectionsIso f hU hV h).toLinearEquiv.injective
  change (relativeDifferentialsSectionsIso f hU hV h).hom
      ((relativeDifferentialsSectionsIso f hU hV h).inv
        (KaehlerDifferential.D Γ(S, U) Γ(X, V) a)) = _
  rw [Iso.inv_hom_id_apply]
  exact (relativeDifferentialsSectionsIso_D f hU hV h a).symm

end Langlands.Scheme
