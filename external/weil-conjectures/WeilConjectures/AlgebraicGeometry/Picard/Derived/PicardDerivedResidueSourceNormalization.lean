/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueNormalizationMap
import WeilConjectures.AlgebraicGeometry.Flat.FlatInvertibleCanonicalDerivedBaseChange

/-! # PicardDerivedResidueSourceNormalization

## References

* Stacks Project, Tags 0096, 06YJ, 0A1D, 08HY, 0D5S and 01F7
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The explicit fibre-normalization map is invertible for a proper flat family
and an invertible coefficient. -/
theorem isIso_picardResidueNormalizationMap
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S)
    {T T' : Scheme.{v}} (g : T ⟶ W) (t : T' ⟶ S) (r : T ≅ T')
    (e : pullback (pullback.snd f k) g ≅ pullback f t)
    (hefst : e.hom ≫ pullback.fst f t =
      pullback.fst (pullback.snd f k) g ≫ pullback.fst f k)
    (hesnd : e.hom ≫ pullback.snd f t ≫ r.inv = pullback.snd (pullback.snd f k) g)
    (τ : (Modules.tensorPullback (pullback.fst f t)).obj L ≅
      SheafOfModules.unit (pullback f t).ringCatSheaf) :
    IsIso (picardResidueNormalizationMap f L W k g t r e hefst hesnd τ) := by
  classical
  let b := e.inv ≫ pullback.fst (pullback.snd f k) g
  let q := pullback.snd f t ≫ r.inv
  have hs : e.inv ≫ pullback.snd (pullback.snd f k) g = q := by
    rw [← hesnd, e.inv_hom_id_assoc]
  have hw : b ≫ pullback.snd f k = q ≫ g := by
    dsimp only [b]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]
  have sq : IsPullback b q (pullback.snd f k) g :=
    IsPullback.of_iso_pullback ⟨hw⟩ e.symm rfl hs
  let M := (Modules.tensorPullback (pullback.fst f k)).obj L
  let : SheafOfModules.IsInvertible M := by
    let c := (Classical.choose (Modules.exists_tensorPullbackAdjunction
      (pullback.fst f k))).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction (pullback.fst f k))
    have := Modules.IsInvertible.sheafOfModules_isInvertible
      ((Modules.pullback (pullback.fst f k)).obj L)
    exact SheafOfModules.IsInvertible.of_iso (c.app L).symm
  have := Modules.isIso_derivedBaseChange_of_flat_invertible
    (pullback.snd f k) g b q sq M
  have : IsIso (Modules.canonicalSinglePullbackMap b M) := by
    apply Modules.isIso_canonicalSinglePullbackMap
  unfold picardResidueNormalizationMap picardResidueNormalizationCoefficient
  dsimp only
  infer_instance

end AlgebraicGeometry.Scheme
