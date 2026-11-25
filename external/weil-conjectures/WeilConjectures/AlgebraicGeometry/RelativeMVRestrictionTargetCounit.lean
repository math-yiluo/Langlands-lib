/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.AlgebraicGeometry.RelativeMVCompositeBaseChangeCounit
import WeilConjectures.AlgebraicGeometry.RelativeMVOpenSquareCounit

/-! # A counit normal form for the relative restriction square

Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

private theorem restriction_glue {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B C₀ D₀ D₁ D₂ D₃ Y : D} {B₀ E₀ E H₀ H₁ H : C}
    (a₁ : A ⟶ B) (a₂ : B ⟶ C₀) (a₃ : C₀ ⟶ F.obj B₀)
    (b₁ : B₀ ⟶ E₀) (b₂ : E₀ ⟶ E)
    {x : A ⟶ Y} {d₁ : F.obj E ⟶ D₁} {d₂ : D₁ ⟶ D₀}
    {e₁ : D₀ ⟶ D₂} {e₂ : D₂ ⟶ D₃} {e₃ : D₃ ⟶ Y}
    {c₁ : E ⟶ H₀} {c₂ : H₀ ⟶ H₁} {c₃ : H₁ ⟶ H} {γ : F.obj H ⟶ Y}
    (hcomp : x = a₁ ≫ a₂ ≫ a₃ ≫ F.map (b₁ ≫ b₂) ≫ d₁ ≫ d₂ ≫ e₁ ≫ e₂ ≫ e₃)
    (hopen : d₁ ≫ d₂ ≫ e₁ ≫ e₂ ≫ e₃ = F.map (c₁ ≫ c₂ ≫ c₃) ≫ γ) :
    x =
      a₁ ≫ a₂ ≫ a₃ ≫ F.map (b₁ ≫ b₂ ≫ c₁ ≫ c₂ ≫ c₃) ≫ γ := by
  rw [hcomp]
  rw [hopen]
  simp only [F.map_comp, Category.assoc]

/-- The target path has the explicit restricted-counit normal form.
Source: Stacks Project, Cohomology, Tags 08HY, 08BV and 08HZ.
(blueprint: new-relative-mv-restriction-target-counit).
Proof: Transpose only the target path under L(W'→S') adjoint to R(W'→S').
Expand its relative restriction and remove the right-adjoint composition
comparisons by their defining mate equations. Transpose the U base-change
map using 08HY. Move the counit for U'→X' through the coefficient comparison
by naturality and use both triangle identities to cancel the intermediate
adjunction unit. The remaining factors are pullbacks of the counits for f
and U→X. Apply the associativity coherence of relativeMVComp to the triples
W→U→X→S and W'→U'→X'→S'. The identities for relativeMVOpenLift with each
projection, together with Scheme.homOfLE_ι, identify the resulting composites
of scheme morphisms. Thus the equality transports in the comparisons agree
by proof irrelevance. After canceling inverse comparison pairs, the outside
factors are the W square comparison and the W coefficient comparison, and
the inside factors are exactly the displayed restricted f and U counits.
This is the displayed normal form, independent of computing the source path.
The same equations apply for W=U, empty opens and zero complexes. -/
theorem relativeMV_restriction_target_counit
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (W U : X.Opens) (i : W ≤ U) :
    let A := (schemeDerivedDirectImage (U.ι ≫ f)).obj ((derivedPullback U.ι).obj K)
    let c := relativeMVComp (X.homOfLE i) U.ι ≪≫
      eqToIso (congrArg (fun t : W.toScheme ⟶ X ↦ derivedPullback t)
        (Scheme.homOfLE_ι X i))
    let t := (relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app A ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj A)
        (show pullback.snd g' W.ι ≫ (W.ι ≫ f) =
            (pullback.fst g' W.ι ≫ f') ≫ g by
          rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc]).symm) ≫
      (relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app A ≫
      (derivedPullback (pullback.snd g' W.ι)).map
        ((relativeMVComp W.ι f).inv.app A ≫
          (derivedPullback W.ι).map
            ((derivedPullback f).map
                ((relativeMVImageComp U.ι f).inv.app ((derivedPullback U.ι).obj K)) ≫
              (relativeMVAdj f).counit.app
                ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K))) ≫
          c.inv.app ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)) ≫
          (derivedPullback (X.homOfLE i)).map
            ((relativeMVAdj U.ι).counit.app ((derivedPullback U.ι).obj K)) ≫
          c.hom.app K) ≫
      (relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app K ≫
      eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
        (pullback.condition (f := g') (g := W.ι)).symm) ≫
      (relativeMVComp (pullback.fst g' W.ι) g').inv.app K
    ((relativeMVAdj (pullback.fst g' W.ι ≫ f')).homEquiv _ _).symm
      ((relativeMVLocalArrow f f' g g' hpull K ((derivedPullback g').obj K)
          (𝟙 _) U).hom ≫
        relativeMVRestriction (relativeMVOpenLift g' i) (pullback.fst g' U.ι)
          (pullback.fst g' W.ι) (pullback.lift_fst _ _ _) f'
          ((derivedPullback g').obj K)) = t := by
  dsimp only
  have hcomp := relativeMV_composite_baseChange_counit f f' g g' hpull K W U i
  have hopen := relativeMV_open_square_counit g' K W U i
  dsimp only at hcomp hopen
  exact restriction_glue (derivedPullback (pullback.snd g' W.ι))
    ((relativeMVComp (pullback.fst g' W.ι ≫ f') g).hom.app _)
    (eqToHom _)
    ((relativeMVComp (pullback.snd g' W.ι) (W.ι ≫ f)).inv.app _)
    ((relativeMVComp W.ι f).inv.app _)
    ((derivedPullback W.ι).map
      ((derivedPullback f).map ((relativeMVImageComp U.ι f).inv.app
        ((derivedPullback U.ι).obj K)) ≫
        (relativeMVAdj f).counit.app
          ((schemeDerivedDirectImage U.ι).obj ((derivedPullback U.ι).obj K)))) hcomp
    (by simpa only [Category.assoc] using hopen)

end AlgebraicGeometry
