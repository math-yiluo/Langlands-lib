/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # Flatness under sectionwise reindexing

## References

* Stacks Project, Tags 08FC and 05VD
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance 2000] SheafOfModules.hasSheafify_coefficientUniverse
attribute [local instance 2000] SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

private theorem postcompose_cocontinuous
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleIsoPostcompose g).IsCocontinuous (ProEt.topology X) (ProEt.topology Y) := by
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt := CategoryTheory.Equivalence.mk
    (proEtaleIsoPostcompose g) (proEtaleIsoPostcompose (inv g))
    e.2.1.some.symm e.2.2.1.some
  exact (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.2.2.2.2.some

/-- Sectionwise inverse image with an invertible coefficient identification preserves
flat module sheaves. -/
theorem isoSectionwiseModuleInverseImage_preservesFlat
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj RY ≅ RX)
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤
      SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) [F.Additive]
    (_hF : F = isoSectionwiseModuleInverseImage.{u, u} g
      (RY := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)
      (RX := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom) :
    ∀ M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY),
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := RY) M →
        SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology X) (R := RX) (F.obj M) := by
  subst F
  intro M hM
  simp only [isoSectionwiseModuleInverseImage, IsIso.Iso.inv_hom]
  let G := proEtaleIsoPostcompose g
  have : G.IsCocontinuous (ProEt.topology X) (ProEt.topology Y) :=
    postcompose_cocontinuous g
  have hc (V : X.ProEt) (b : RY.obj.obj (op (G.obj V))) :
      c.inv.hom.app (op V) (c.hom.hom.app (op V) b) = b := by
    have h := congrArg (fun k ↦ k.hom.app (op V) b) c.hom_inv_id
    exact h
  have hd (V : X.ProEt) (a : RX.obj.obj (op V)) :
      c.hom.hom.app (op V) (c.inv.hom.app (op V) a) = a := by
    have h := congrArg (fun k ↦ k.hom.app (op V) a) c.inv_hom_id
    exact h
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion RX
  intro U n a s hs
  change Fin n → M.val.obj (op (G.obj U)) at s
  change (∑ p, c.inv.hom.app (op U) (a p) • s p) = 0 at hs
  obtain ⟨S, hS, hlocal⟩ :=
    (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      RY M).1 hM
      (G.obj U) n (fun p ↦ c.inv.hom.app (op U) (a p)) s hs
  refine ⟨S.functorPullback G, G.cover_lift _ _ hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, hfac, hrel⟩ := hlocal (G.obj V) (G.map f) hf
  refine ⟨l, fun p q ↦ c.hom.hom.app (op V) (b p q), t, ?_, ?_⟩
  · intro p
    change M.val.map (G.map f).op (s p) =
      ∑ q, c.inv.hom.app (op V) (c.hom.hom.app (op V) (b p q)) • t q
    simpa only [hc] using hfac p
  · intro q
    have h := congrArg (c.hom.hom.app (op V)) (hrel q)
    simp only [map_sum, map_mul, map_zero] at h
    have hn (p : Fin n) :
        c.hom.hom.app (op V)
            (RY.obj.map (G.map f).op (c.inv.hom.app (op U) (a p))) =
          RX.obj.map f.op (a p) := by
      have hnat := ConcreteCategory.congr_hom (c.hom.hom.naturality f.op)
        (c.inv.hom.app (op U) (a p))
      change _ = RX.obj.map f.op
        (c.hom.hom.app (op U) (c.inv.hom.app (op U) (a p))) at hnat
      rw [hd] at hnat
      exact hnat
    simpa only [hn] using h

end AlgebraicGeometry.Scheme
