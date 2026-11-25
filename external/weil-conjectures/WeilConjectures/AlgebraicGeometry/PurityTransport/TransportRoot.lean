/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients

/-! # Purity transport statement interfaces

## References

* Stacks 03PK
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The section-normalized identification of the two existing presentations of roots. -/
theorem rootComparison_existsUnique (X : Scheme.{u}) (N : ℕ) :
    ∃! e : rootsOfUnitySheaf X N ≅ proEtaleRootsOfUnitySheaf X N,
      ∀ (U : X.ProEtᵒᵖ) (z : (rootsOfUnityPresheaf X N).obj U),
        proEtaleRootsOfUnitySections X N U
          (e.hom.hom.app U ((toSheafify (ProEt.topology X)
            (rootsOfUnityPresheaf X N)).app U z)) = z.down := by
  let F := proEtaleRootsOfUnitySheaf X N
  let P := rootsOfUnityPresheaf X N
  let J := ProEt.topology X
  have hs (U : X.ProEtᵒᵖ) (x : F.obj.obj U) :
      ULift.up (Additive.ofMul (proEtaleRootsOfUnitySections X N U x).toMul.val) =
        (proEtaleRootsOfUnityInclusion X N).hom.app U x :=
    (existsUnique_proEtaleRootsOfUnitySections X N U).exists.choose_spec x
  let i : F.obj ≅ P := NatIso.ofComponents
    (fun U ↦ ((proEtaleRootsOfUnitySections X N U).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) (by
      intro U V a
      ext x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      have h := congrArg (fun b ↦ b x)
        ((proEtaleRootsOfUnityInclusion X N).hom.naturality a)
      change (proEtaleRootsOfUnityInclusion X N).hom.app V (F.obj.map a x) =
        (proEtaleUnitsSheaf X).obj.map a
          ((proEtaleRootsOfUnityInclusion X N).hom.app U x) at h
      rw [← hs V _, ← hs U x] at h
      exact congrArg (fun y ↦ y.down.toMul) h)
  let e : rootsOfUnitySheaf X N ≅ F :=
    (presheafToSheaf J Ab.{u + 1}).mapIso i.symm ≪≫ (sheafificationIso F).symm
  have he : toSheafify J P ≫ e.hom.hom = i.inv := by
    change toSheafify J P ≫ sheafifyMap J i.inv ≫
      (isoSheafify J F.property).inv = i.inv
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
    simp only [← isoSheafify_hom J F.property, Iso.hom_inv_id, Category.comp_id]
  have he' (U : X.ProEtᵒᵖ) (z : P.obj U) :
      proEtaleRootsOfUnitySections X N U
        (e.hom.hom.app U ((toSheafify J P).app U z)) = z.down := by
    have h := congrArg (fun b ↦ b.app U z) he
    change proEtaleRootsOfUnitySections X N U
      (e.hom.hom.app U ((toSheafify J P).app U z)) = z.down
    rw [show e.hom.hom.app U ((toSheafify J P).app U z) = i.inv.app U z from h]
    exact (proEtaleRootsOfUnitySections X N U).apply_symm_apply z.down
  refine ⟨e, he', ?_⟩
  intro e' he''
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ F.property
  ext U z
  apply (proEtaleRootsOfUnitySections X N U).injective
  exact (he'' U z).trans (he' U z).symm

/-- The unique generator-preserving comparison, not an arbitrary root frame. -/
def rootComparison (X : Scheme.{u}) (N : ℕ) :=
  (rootComparison_existsUnique X N).exists.choose

/-- Pullback on roots through the two existing presentations. -/
def rootPull {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) :=
  (ProEtale.upperStar Ab.{u + 1} f).map (rootComparison Y N).hom ≫
    proEtaleRootsOfUnityInverseImageMap f N ≫ (rootComparison X N).inv

/-- The underlying free-module comparison: coefficient pullback tensor root pullback. -/
def rootTensorPull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :=
  Functor.OplaxMonoidal.δ (ProEtale.upperStar Ab.{u + 1} f)
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) Y)
      (rootsOfUnitySheaf Y (ell ^ n)) ≫
    (condensedPullbackHom (Profinite.continuousMapRingObj ℤ_[ell]) f ⊗ₘ
      rootPull f (ell ^ n))

/-- Normalization of a module pullback comparison by its underlying abelian map. -/
def PullNormalized
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)}
    (e : (CondensedRing.upperStar R f).obj M ≅ N)
    {B : Type (u + 1)} (raw : B) : Prop :=
  HEq ((Mod.forget (condensedRingObj R X)).map
    ((Functor.isoWhiskerLeft
        ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj R Y))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom R f))).inv.app M ≫ e.hom)) raw

end AlgebraicGeometry.ProEtale.PurityTransport
