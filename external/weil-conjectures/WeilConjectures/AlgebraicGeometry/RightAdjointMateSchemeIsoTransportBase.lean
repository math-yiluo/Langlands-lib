/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeSourceIso
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh

/-! # Transport of a right-adjoint mate across a scheme isomorphism

Source: Stacks Project, Duality for Schemes, Tag 0ATR.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem map_id_coefficient
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : C ⥤ B) (X : A) (Y : C)
    (v : F.obj X ⟶ G.obj Y) :
    F.map (𝟙 X) ≫ v = v ≫ G.map (𝟙 Y) ≫ 𝟙 (G.obj Y) := by
  rw [F.map_id, G.map_id]
  simp only [Category.id_comp, Category.comp_id]

/-- Transport both ordinary base change and its right-adjoint mate when the source
scheme of the vertical morphism is replaced by an isomorphic scheme.
Source: Stacks Project, Duality for Schemes, Tag 0ATR, Lemma 48.5.2,
and Tag 0E9S, invariance under the cartesian restriction identification.
(blueprint: lem-sc-right-adjoint-mate-scheme-iso-transport-base)

Proof: The projection equations identify r with the pullback of e.hom, hence r is
an isomorphism. Derived pullback along e.hom and along r are equivalences; their
inverse functors are pullback along the inverse scheme maps, with the composition
and identity comparisons. Derived direct-image composition identifies the two
vertical direct images under these equivalences. Uniqueness of right adjoints,
with its unit and counit identities, identifies a with b and d with b'.
Ordinary base change is natural under this identification: transpose under the
pullback/direct-image adjunction, use the two projection equations and the
associativity of pullback composition, then use injectivity of the Hom equivalence.
Thus the ordinary base-change component for f is a conjugate of the component
for f' at the equivalent object, and is invertible. In the formula for the second
mate, move the units and counits across these adjunction comparisons. ConjugateEquiv
preserves the conjugated ordinary comparison and its inverse. The resulting square
commutes and has invertible vertical sides, giving the asserted arrow isomorphism.
No invertibility of either right-adjoint mate is required. Empty schemes and zero
objects satisfy the same naturality and triangle identities. -/
theorem rightAdjoint_mate_scheme_iso_transport_base
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f') (g : T ⟶ S)
    (hβ : ∀ E : schemeDerivedQCohCategory U,
      IsIso (schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
        (pullback.fst f' g) pullback.condition E.obj))
    (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f' g) :
    (∀ E : schemeDerivedQCohCategory P,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj)) := by
  classical
  let ri : pullback f g ⟶ pullback f' g := pullback.lift
    (pullback.fst f g ≫ e.inv) (pullback.snd f g) (by
      rw [Category.assoc, ← he]
      simp only [← Category.assoc, e.inv_hom_id, Category.id_comp, pullback.condition])
  have hi : r ≫ ri = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [ri, pullback.lift_fst, Category.assoc, Category.id_comp]
      rw [← Category.assoc, hr₁]
      simp
    · simp only [ri, pullback.lift_snd, Category.assoc, Category.id_comp, hr₂]
  have hj : ri ≫ r = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr₁, ← Category.assoc]
      simp [ri]
    · rw [Category.assoc, hr₂]
      simp [ri]
  let er : pullback f' g ≅ pullback f g := ⟨r, ri, hi, hj⟩
  intro E
  let N : schemeDerivedQCohCategory U := ⟨(derivedPullback e.hom).obj E.obj,
    (derivedPullback_tensor_preserve_QCoh e.hom).1 E.obj E.property⟩
  let c : ∀ {A B C : Scheme.{u}} (v : A ⟶ B) (v' : B ⟶ C),
      derivedPullback v' ⋙ derivedPullback v ≅ derivedPullback (v ≫ v') :=
    @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let z : (derivedPullback (pullback.fst f' g)).obj N.obj ≅
      (derivedPullback r).obj ((derivedPullback (pullback.fst f g)).obj E.obj) :=
    (c (pullback.fst f' g) e.hom).app E.obj ≪≫
      eqToIso (congrArg (fun s ↦ (derivedPullback s).obj E.obj) hr₁.symm) ≪≫
      ((c r (pullback.fst f g)).app E.obj).symm
  have ht : pullback.fst f' g ≫ e.hom = er.hom ≫ pullback.fst f g := hr₁.symm
  have h0 : pullback.fst f' g ≫ (e.hom ≫ f) =
      (er.hom ≫ pullback.snd f g) ≫ g := by
    change pullback.fst f' g ≫ (e.hom ≫ f) = (r ≫ pullback.snd f g) ≫ g
    rw [he, hr₂, pullback.condition]
  obtain ⟨a₀, b₀, hh⟩ := exists_derivedBaseChange_source_iso f
    (pullback.snd f g) g (pullback.fst f g) pullback.condition e er
    (pullback.fst f' g) ht h0 E.obj ((derivedPullback (pullback.fst f g)).obj E.obj)
    N.obj ((derivedPullback r).obj ((derivedPullback (pullback.fst f g)).obj E.obj))
    (𝟙 _) z.hom (Iso.refl _) (Iso.refl _) (by
      simpa only [Iso.refl_hom, z, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
        Iso.symm_hom, eqToIso.hom, Category.assoc] using
        map_id_coefficient (derivedPullback (pullback.fst f' g)) (derivedPullback r)
          N.obj ((derivedPullback (pullback.fst f g)).obj E.obj) z.hom)
  have hz : IsIso z.hom := inferInstance
  have hβN := hβ N
  have hb : IsIso (schemeDerivedBaseChangeMap (e.hom ≫ f)
      (r ≫ pullback.snd f g) g (pullback.fst f' g) h0 N.obj) := by
    have h : ∀ (l : U ⟶ S) (q : pullback f' g ⟶ T)
        (hl : l = f') (hq : q = pullback.snd f' g)
        (hc : pullback.fst f' g ≫ l = q ≫ g),
        IsIso (schemeDerivedBaseChangeMap l q g (pullback.fst f' g) hc N.obj) := by
      intro l q hl hq hc
      subst l
      subst q
      exact hβN
    exact h _ _ he hr₂ h0
  have hc : IsIso (a₀.hom ≫ (schemeDerivedBaseChangeMap (e.hom ≫ f)
      (r ≫ pullback.snd f g) g (pullback.fst f' g) h0 N.obj ≫
      (schemeDerivedDirectImage (r ≫ pullback.snd f g)).map z.hom)) := inferInstance
  change IsIso (a₀.hom ≫ (schemeDerivedBaseChangeMap (e.hom ≫ f)
    (er.hom ≫ pullback.snd f g) g (pullback.fst f' g) h0 N.obj ≫
    (schemeDerivedDirectImage (er.hom ≫ pullback.snd f g)).map z.hom)) at hc
  rw [← hh] at hc
  have hm := (isIso_comp_right_iff _ b₀.hom).mp hc
  rw [(schemeDerivedDirectImage (pullback.snd f g)).map_id, Category.comp_id] at hm
  exact hm

end AlgebraicGeometry
