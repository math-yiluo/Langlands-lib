import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof

/-! # Scalar-linear cohomology base-change maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  (M : X.Modules)
  (hM : ∀ q : ℕ, IsZero
    ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))

/-- The `R'`-linear adjunct of the published cohomology base-change map.
The acyclicity of pushforwards of injectives is supplied by its published proof. -/
def scalarBaseChangeMap (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeCohomology f n).obj M) ⟶
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback g).obj M) :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _ |>.symm <|
    baseChangeMap φ f f' g w M hM
      (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n

/-- Under the scalar adjunction, the new map is exactly `baseChangeMap`. -/
@[simp]
lemma scalarBaseChangeMap_homEquiv
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        (scalarBaseChangeMap φ f f' g w M hM n) =
      baseChangeMap φ f f' g w M hM hJ n := by
  simp [scalarBaseChangeMap]

/-- Composing with the scalar unit recovers the published semilinear map. -/
@[reassoc]
lemma scalarBaseChangeMap_unit
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((relativeCohomology f n).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map (scalarBaseChangeMap φ f f' g w M hM n) =
      baseChangeMap φ f f' g w M hM hJ n := by
  simpa only [Adjunction.homEquiv_unit] using
    scalarBaseChangeMap_homEquiv φ f f' g w M hM hJ n

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-linear map sends `1 ⊗ x` to the published base-change image of `x`. -/
lemma scalarBaseChangeMap_one_tmul
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J)))
    (n : ℕ) (x : (relativeCohomology f n).obj M) :
    scalarBaseChangeMap φ f f' g w M hM n ((1 : R') ⊗ₜ[R,φ.hom] x) =
      baseChangeMap φ f f' g w M hM hJ n x := by
  have h := congrArg (fun k => k x)
    (scalarBaseChangeMap_homEquiv φ f f' g w M hM hJ n)
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] using h

/-- The scalar-linear map is natural in the coefficient module. -/
@[reassoc]
lemma scalarBaseChangeMap_naturality {M N : X.Modules} (a : M ⟶ N)
    (hM : ∀ q : ℕ, IsZero
      ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hN : ∀ q : ℕ, IsZero
      ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj N)))
    (n : ℕ) :
    (ModuleCat.extendScalars φ.hom).map ((relativeCohomology f n).map a) ≫
        scalarBaseChangeMap φ f f' g w N hN n =
      scalarBaseChangeMap φ f f' g w M hM n ≫
        (relativeCohomology f' n).map ((Scheme.Modules.pullback g).map a) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [scalarBaseChangeMap, Equiv.apply_symm_apply]
  exact baseChangeMap_naturality φ f f' g w a hM hN
    (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
