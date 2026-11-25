/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreResidueBridge

/-! # Geometric naturality before choosing affine models

## References

* Stacks Project, Tags 0B91, 0BF2 and 01XK
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- The derived fibre comparison elaborates nested functor and fibre-product terms.
/-- Direct-image residue fibres admit compatible geometric comparisons. -/
theorem picard_derived_fibre_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
 :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))
      ∃ e : derivedFiberCohomology W E 1 w ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1,
      ∀ i : Fin n,
        ∃ ei : derivedFiberCohomology W (Ei i) 1 w ≃+
            Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1,
          ∀ z : derivedFiberCohomology W E 1 w,
            ei ((derivedFiberCohomologyFunctor W w 1).map
              (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) z) =
              structureSheafCohomologyPullback
                (((Over.pullback (S.fromSpecResidueField s)).map
                  (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (e z) := by
  classical
  dsimp only
  obtain ⟨U, hwU, hU, p, hp, hprime, K, C, hK, hC, m, m', φ, e, ei, hfamily⟩ :=
    picard_derived_fibre_residue_bridge f Xi fi ui hui L W k w s hw τ
  exact ⟨e, fun i ↦ ⟨ei i, (hfamily i).2.1⟩⟩

end AlgebraicGeometry.Scheme
