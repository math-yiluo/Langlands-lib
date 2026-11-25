/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations

import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.Monoidal.Conjugate

/-!
# Canonical base-change mates for arbitrary pro-etale ring sheaves

## References

* Stacks Tags 03CB and 03CC
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem compMonoidal {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).hom := by
  have h₁ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (f ≫ g))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂ : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  have : NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).symm.hom :=
    isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp Ab.{u + 1} f g).inv
  exact inferInstanceAs (NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).symm.inv)
private theorem congrMonoidal {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (upperStarCongr Ab.{u + 1} h).hom := by
  subst h
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
private theorem squareMonoidal {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :
    NatTrans.IsMonoidal (ringSheafSquareComparison g f).hom := by
  have := compMonoidal (pullback.fst g f) g
  have := compMonoidal (pullback.snd g f) f
  have := congrMonoidal (pullback.condition (f := g) (g := f))
  rw [ringSheafSquareComparison_eq]
  dsimp only [upperStarCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance
private theorem squareLift {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    Exists fun [_h : IsMonHom (ringSheafSquareCoefficient g f B)] ↦
      ∃ delta : ringSheafInverseImage g B ⋙
          ringSheafInverseImage (pullback.fst g f) ((upperStar Ab.{u + 1} g).obj B) ≅
        ringSheafInverseImage f B ⋙ ringSheafSquarePullback g f B,
      ∀ M, (delta.hom.app M).hom = (ringSheafSquareComparison g f).hom.app M.X := by
  have := squareMonoidal g f
  have h := NatTrans.isMonHom_app (ringSheafSquareComparison g f).hom B
  have : IsMonHom (ringSheafSquareCoefficient g f B) :=
    IsMonHom.of_eq
      (h₁ := ((upperStar Ab.{u + 1} g) ⋙ (upperStar Ab.{u + 1} (pullback.fst g f))).monObjObj B)
      (h₂ := ((upperStar Ab.{u + 1} f) ⋙ (upperStar Ab.{u + 1} (pullback.snd g f))).monObjObj B)
      ((ringSheafSquareComparison g f).hom.app B)
      (Functor.monObjObj_comp _ _ B) (Functor.monObjObj_comp _ _ B)
  refine ⟨this, ?_⟩
  refine ⟨?_, ?_⟩
  · refine NatIso.ofComponents (fun M ↦ Mod.isoMk ((ringSheafSquareComparison g f).app M.X)
        ?_) (fun φ ↦ Mod.hom_ext _ _ ((ringSheafSquareComparison g f).hom.naturality φ.hom))
    change (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} (pullback.fst g f))
        ((upperStar Ab.{u + 1} g).obj B) ((upperStar Ab.{u + 1} g).obj M.X) ≫
        (upperStar Ab.{u + 1} (pullback.fst g f)).map
          (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} g) B M.X ≫
            (upperStar Ab.{u + 1} g).map (Mod.act (A := B) M.X))) ≫
        (ringSheafSquareComparison g f).hom.app M.X = _
    have h₁ := (ringSheafSquareComparison g f).hom.naturality (Mod.act (A := B) M.X)
    have h₂ := NatTrans.IsMonoidal.tensor (τ := (ringSheafSquareComparison g f).hom) B M.X
    rw [Functor.LaxMonoidal.comp_μ] at h₂
    simp only [Mod.act_comap_obj, Functor.act_mapMod_obj]
    change _ =
      (upperStar Ab.{u + 1} (pullback.fst g f)).obj ((upperStar Ab.{u + 1} g).obj B) ◁
        (ringSheafSquareComparison g f).hom.app M.X ≫
      (ringSheafSquareComparison g f).hom.app B ▷
        (upperStar Ab.{u + 1} (pullback.snd g f)).obj ((upperStar Ab.{u + 1} f).obj M.X) ≫
      Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} (pullback.snd g f))
        ((upperStar Ab.{u + 1} f).obj B) ((upperStar Ab.{u + 1} f).obj M.X) ≫
      (upperStar Ab.{u + 1} (pullback.snd g f)).map
        (Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} f) B M.X ≫
          (upperStar Ab.{u + 1} f).map (Mod.act (A := B) M.X))
    simp only [Functor.comp_map] at h₁
    simp only [Functor.map_comp, Category.assoc]
    rw [h₁]
    simpa only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, Functor.map_comp, tensorHom_def',
      Category.assoc] using congrArg
        (fun k ↦ k ≫ (upperStar Ab.{u + 1} (pullback.snd g f)).map
          ((upperStar Ab.{u + 1} f).map (Mod.act (A := B) M.X))) h₂
  · intro M
    rfl

private theorem abZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj F))
    (hj : IsZero ((upperStar Ab.{u + 1} j).obj F)) : IsZero F := by
  have := (abelian_closed_support_counit_and_unit i j hU).2 F hj
  exact ((lowerStar Ab.{u + 1} i).map_isZero hi).of_iso
    (asIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F))
private theorem modZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    (hi : IsZero ((ringSheafInverseImage i B).obj M))
    (hj : IsZero ((ringSheafInverseImage j B).obj M)) : IsZero M := by
  have h := abZeroDetect i j hU M.X ((Mod.forget _).map_isZero hi)
    ((Mod.forget _).map_isZero hj)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact h.eq_of_src _ _

private theorem modIsoDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B} (φ : M ⟶ N)
    (hi : IsIso ((ringSheafInverseImage i B).map φ))
    (hj : IsIso ((ringSheafInverseImage j B).map φ)) : IsIso φ := by
  have := hi
  have := hj
  have hker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (kernel φ)) := fun f _ ↦
    (isZero_kernel_of_mono ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (cokernel φ)) := fun f _ ↦
    (isZero_cokernel_of_epi ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (modZeroDetect i j hU B _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (modZeroDetect i j hU B _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

private theorem openUnit {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (N) : IsIso ((ringSheafOpenAdjunction j B).unit.app N) := by
  have h : IsIso ((Mod.forget _).map ((ringSheafOpenAdjunction j B).unit.app N)) := by
    change IsIso (((ringSheafOpenAdjunction j B).unit.app N).hom)
    simp only [ringSheafOpenAdjunction, Adjunction.mapModLeftAdjunction,
      Adjunction.mkOfHomEquiv_unit_app]
    change IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv _ _
      (𝟙 ((openImmersionLowerShriek Ab.{u + 1} j).obj N.X)))
    rw [Adjunction.homEquiv_id]
    have := Adjunction.unit_isIso_of_L_fully_faithful
      (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j)
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

-- The transported module actions involve several nested functor structures.
/-- The canonical open and closed base-change mates are invertible. -/
theorem ringSheaf_baseChange_mates
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (_hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    (∀ {X' : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] (g : X' ⟶ X),
      Exists fun [_hu : IsMonHom (ringSheafSquareCoefficient g j B)] ↦
      Exists fun [_hz : IsMonHom (ringSheafSquareCoefficient g i B)] ↦
      ∃ delta : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage j B ⋙ ringSheafSquarePullback g j B,
      ∃ gamma : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage i B ⋙ ringSheafSquarePullback g i B,
        (∀ M, (delta.hom.app M).hom = (ringSheafSquareComparison g j).hom.app M.X) ∧
        (∀ M, (gamma.hom.app M).hom = (ringSheafSquareComparison g i).hom.app M.X) ∧
        ∃ alpha : ringSheafOpenExtension j B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g j B ⋙
              ringSheafOpenExtension (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B),
        ∃ beta : ringSheafDirectImage i B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g i B ⋙
              ringSheafDirectImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B),
          (∀ N, (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _ (alpha.inv.app N) =
            (ringSheafSquarePullback g j B).map ((ringSheafOpenAdjunction j B).unit.app N) ≫
              delta.inv.app ((ringSheafOpenExtension j B).obj N)) ∧
          (∀ G, ((ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _).symm (beta.hom.app G) =
            gamma.hom.app ((ringSheafDirectImage i B).obj G) ≫
              (ringSheafSquarePullback g i B).map ((ringSheafAdjunction i B).counit.app G))) := by
  intro X' _ _ g
  obtain ⟨hu, delta, hd⟩ := squareLift g j B
  have := hu
  obtain ⟨hz, gamma, hg⟩ := squareLift g i B
  have := hz
  have hU' : Set.range (pullback.fst g j) = (Set.range (pullback.fst g i))ᶜ := by
    rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, _hU]
    rfl
  obtain ⟨_, hc, hv, _⟩ := ringSheaf_closed_localization i j _hU B
  obtain ⟨_, hc', hv', _⟩ := ringSheaf_closed_localization (pullback.fst g i)
    (pullback.fst g j) hU' ((upperStar Ab.{u + 1} g).obj B)
  let a := ringSheafOpenAdjunction j B
  let a' := ringSheafOpenAdjunction (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B)
  let b := ringSheafAdjunction i B
  let b' := ringSheafAdjunction (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B)
  let qU := ringSheafSquarePullback g j B
  let qZ := ringSheafSquarePullback g i B
  have hzi (N) : IsZero ((ringSheafInverseImage i B).obj
      ((ringSheafOpenExtension j B).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b.homEquiv _ _).injective
    apply (a.homEquiv _ _).injective
    exact (hv _).eq_of_tgt _ _
  have hzi' (N) : IsZero ((ringSheafInverseImage (pullback.fst g i)
      ((upperStar Ab.{u + 1} g).obj B)).obj
      ((ringSheafOpenExtension (pullback.fst g j)
        ((upperStar Ab.{u + 1} g).obj B)).obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (b'.homEquiv _ _).injective
    apply (a'.homEquiv _ _).injective
    exact (hv' _).eq_of_tgt _ _
  let t : qU ⋙ ringSheafOpenExtension (pullback.fst g j)
        ((upperStar Ab.{u + 1} g).obj B) ⟶
      ringSheafOpenExtension j B ⋙ ringSheafInverseImage g B :=
    { app N := (a'.homEquiv _ _).symm
        (qU.map (a.unit.app N) ≫ delta.inv.app ((ringSheafOpenExtension j B).obj N))
      naturality N P φ := by
        apply (a'.homEquiv _ _).injective
        change a'.homEquiv _ _
            ((ringSheafOpenExtension (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).map (qU.map φ) ≫ _) =
          a'.homEquiv _ _ (_ ≫ (ringSheafInverseImage g B).map ((ringSheafOpenExtension j B).map φ))
        rw [a'.homEquiv_naturality_left, a'.homEquiv_naturality_right]
        simp only [Functor.comp_obj, Equiv.apply_symm_apply]
        have hn := delta.inv.naturality ((ringSheafOpenExtension j B).map φ)
        change qU.map ((ringSheafInverseImage j B).map
            ((ringSheafOpenExtension j B).map φ)) ≫ delta.inv.app _ =
          delta.inv.app _ ≫ _ at hn
        rw [Category.assoc]
        erw [← hn]
        simp only [← Category.assoc, ← qU.map_comp]
        congr 2
        exact a.unit.naturality φ }
  let v : ringSheafDirectImage i B ⋙ ringSheafInverseImage g B ⟶
      qZ ⋙ ringSheafDirectImage (pullback.fst g i)
        ((upperStar Ab.{u + 1} g).obj B) :=
    { app G := b'.homEquiv _ _
        (gamma.hom.app ((ringSheafDirectImage i B).obj G) ≫ qZ.map (b.counit.app G))
      naturality G H φ := by
        apply (b'.homEquiv _ _).symm.injective
        change (b'.homEquiv _ _).symm
            ((ringSheafInverseImage g B).map ((ringSheafDirectImage i B).map φ) ≫ _) =
          (b'.homEquiv _ _).symm (_ ≫
            (ringSheafDirectImage (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).map (qZ.map φ))
        rw [b'.homEquiv_naturality_left_symm, b'.homEquiv_naturality_right_symm]
        simp only [Functor.comp_obj, Equiv.symm_apply_apply]
        have hn := gamma.hom.naturality ((ringSheafDirectImage i B).map φ)
        change _ ≫ gamma.hom.app _ = gamma.hom.app _ ≫
          qZ.map ((ringSheafInverseImage i B).map ((ringSheafDirectImage i B).map φ)) at hn
        rw [← Category.assoc]
        erw [hn]
        simp only [Category.assoc, ← qZ.map_comp]
        congr 2
        exact b.counit.naturality φ }
  have ht (N) : IsIso (t.app N) := by
    apply modIsoDetect (pullback.fst g i) (pullback.fst g j) hU'
      ((upperStar Ab.{u + 1} g).obj B)
    · have hs := hzi' (qU.obj N)
      have ht := (qZ.map_isZero (hzi N)).of_iso
        (gamma.app ((ringSheafOpenExtension j B).obj N))
      exact isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero
    · have he : a'.unit.app (qU.obj N) ≫
          (ringSheafInverseImage (pullback.fst g j)
            ((upperStar Ab.{u + 1} g).obj B)).map (t.app N) =
          qU.map (a.unit.app N) ≫ delta.inv.app ((ringSheafOpenExtension j B).obj N) := by
        exact (a'.homEquiv _ _).apply_symm_apply _
      have := openUnit j B N
      have := openUnit (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B) (qU.obj N)
      have : IsIso (a'.unit.app (qU.obj N) ≫
          (ringSheafInverseImage (pullback.fst g j)
            ((upperStar Ab.{u + 1} g).obj B)).map (t.app N)) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_left (a'.unit.app (qU.obj N)) _
  have hvIso (G) : IsIso (v.app G) := by
    apply modIsoDetect (pullback.fst g i) (pullback.fst g j) hU'
      ((upperStar Ab.{u + 1} g).obj B)
    · have he : (ringSheafInverseImage (pullback.fst g i)
            ((upperStar Ab.{u + 1} g).obj B)).map (v.app G) ≫
          b'.counit.app (qZ.obj G) =
          gamma.hom.app ((ringSheafDirectImage i B).obj G) ≫ qZ.map (b.counit.app G) := by
        exact (b'.homEquiv _ _).symm_apply_apply _
      have := hc G
      have := hc' (qZ.obj G)
      have : IsIso ((ringSheafInverseImage (pullback.fst g i)
            ((upperStar Ab.{u + 1} g).obj B)).map (v.app G) ≫
          b'.counit.app (qZ.obj G)) := by
        rw [he]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (b'.counit.app (qZ.obj G))
    · have hs := (qU.map_isZero (hv G)).of_iso
        (delta.app ((ringSheafDirectImage i B).obj G))
      have ht := hv' (qZ.obj G)
      exact isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero
  have : IsIso t := (NatTrans.isIso_iff_isIso_app _).2 ht
  have : IsIso v := (NatTrans.isIso_iff_isIso_app _).2 hvIso
  refine ⟨hu, hz, delta, gamma, hd, hg, (asIso t).symm, asIso v, ?_, ?_⟩
  · intro N
    exact (a'.homEquiv _ _).apply_symm_apply _
  · intro G
    exact (b'.homEquiv _ _).symm_apply_apply _

end AlgebraicGeometry.ProEtale
