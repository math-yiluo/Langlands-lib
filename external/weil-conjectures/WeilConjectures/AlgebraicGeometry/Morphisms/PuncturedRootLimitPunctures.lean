/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.AdjoinRoot

import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootBaseChange
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Auxiliary limit statements for punctured root charts

## References

* Stacks Project, Tags 0BSK, 05N9 and 01YW
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Punctured root charts commute with cofiltered affine ring colimits over R. -/
theorem punctured_root_colimit_continuity
    (R H : CommRingCat.{u}) (f : R) (n : ℕ) (b : R ⟶ H)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (F : Iᵒᵖ ⥤ CommRingCat.{u}) (c₀ : Cocone F) (hc₀ : IsColimit c₀)
    (a : (Functor.const Iᵒᵖ).obj R ⟶ F) (e₀ : c₀.pt ≅ H)
    (ha : ∀ j, a.app j ≫ c₀.ι.app j ≫ e₀.hom = b) :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (D : I ⥤ Scheme.{u}) (c : Cone D)
      (t : D ⟶ (Functor.const I).obj (Spec R)),
      Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
      ∃ e : V.toScheme ≅ c.pt,
        (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
        ∀ j,
          let S := F.obj (Opposite.op j)
          let g := (a.app (Opposite.op j)).hom f
          let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
          let N := Spec (CommRingCat.of A)
          let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
          let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
          ∃ d : V.toScheme ≅ D.obj j,
            d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map (a.app (Opposite.op j)) := by
  classical
  have : IsConnected I := IsCofiltered.isConnected I
  let A₀ := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)
  let N₀ := Spec (CommRingCat.of A₀)
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap R A₀))
  let V₀ : N₀.Opens := PrimeSpectrum.basicOpen (algebraMap R A₀ f)
  let k := V₀.ι ≫ q₀
  let E := F.rightOp ⋙ Scheme.Spec
  let s : E ⟶ (Functor.const I).obj (Spec R) :=
    { app := fun j => Spec.map (a.app (Opposite.op j))
      naturality := by
        intro i j h
        dsimp [E]
        rw [← Spec.map_comp]
        congr 1
        simpa using (a.naturality h.op).symm }
  let cE := Scheme.Spec.mapCone (coneRightOpOfCocone c₀)
  have hcE : IsLimit cE := isLimitOfPreserves Scheme.Spec
    (isLimitConeRightOpOfCocone F hc₀)
  let cH := cE.extend (Spec.map e₀.hom)
  -- Infer the extended cone from the specified morphism before checking its type.
  have hcH := IsLimit.extendIso (Spec.map e₀.hom) hcE
  have hlegs : ∀ j, cH.π.app j ≫ s.app j = Spec.map b := by
    intro j
    change Spec.map e₀.hom ≫ Spec.map (c₀.ι.app (Opposite.op j)) ≫
      Spec.map (a.app (Opposite.op j)) = Spec.map b
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    simpa only [Category.assoc] using ha (Opposite.op j)
  let L := Over.lift E s
  let cL := Over.liftCone E s cH (Spec.map b) hlegs
  have hcL : IsLimit cL := Over.isLimitLiftCone E s cH (Spec.map b) hlegs hcH
  let P := Over.pullback k
  let D := L ⋙ P ⋙ Over.forget V₀.toScheme
  let c := (P ⋙ Over.forget V₀.toScheme).mapCone cL
  have hc : IsLimit c := isLimitOfPreserves (P ⋙ Over.forget V₀.toScheme) hcL
  let t : D ⟶ (Functor.const I).obj (Spec R) :=
    { app := fun j => pullback.fst (s.app j) k ≫ s.app j
      naturality := by
        intro i j h
        change pullback.lift (pullback.fst (s.app i) k ≫ E.map h)
          (pullback.snd (s.app i) k) _ ≫
          (pullback.fst (s.app j) k ≫ s.app j) =
          (pullback.fst (s.app i) k ≫ s.app i) ≫ 𝟙 _
        simp only [Category.assoc, pullback.lift_fst_assoc, Category.comp_id]
        have hs := s.naturality h
        have hs' : E.map h ≫ s.app j = s.app i := by
          change E.map h ≫ s.app j = s.app i ≫ 𝟙 (Spec R) at hs
          exact hs.trans (Category.comp_id _)
        rw [hs'] }
  have hV₀ : IsAffine V₀.toScheme := IsAffineOpen.Spec_basicOpen _
  obtain ⟨e, he⟩ := punctured_root_base_change R H f n b
  refine ⟨D, c, t, ⟨hc⟩, ?_, e, ?_, ?_⟩
  · intro j
    change IsAffine (pullback (s.app j) k)
    change IsAffine (pullback (Spec.map (a.app (Opposite.op j))) k)
    exact Pullback.isAffine_of_isAffine_isAffine_isAffine _ _
  · intro j
    change e.hom ≫
      pullback.lift (pullback.fst (Spec.map b) k ≫ cH.π.app j)
        (pullback.snd (Spec.map b) k) _ ≫
      (pullback.fst (s.app j) k ≫ s.app j) = _
    simp only [Category.assoc, pullback.lift_fst_assoc]
    rw [hlegs, ← Category.assoc, he]
    simp only [Category.assoc]
  · intro j
    obtain ⟨d, hd⟩ := punctured_root_base_change R (F.obj (Opposite.op j)) f n
      (a.app (Opposite.op j))
    refine ⟨d, ?_⟩
    change d.hom ≫ pullback.fst (s.app j) k ≫ s.app j = _
    rw [← Category.assoc, hd]
    simp only [Category.assoc]
    rfl

end AlgebraicGeometry.Scheme
