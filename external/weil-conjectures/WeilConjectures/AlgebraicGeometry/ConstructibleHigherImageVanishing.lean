/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Extending constructible higher-image vanishing to arbitrary sheaves

Source: Stacks Project, Tags 03SA and 09Z1; ILO, Exposé XIII, Proposition 2.3.4.
The geometric affine Lefschetz calculation in that proof treats constructible sheaves.
Constructible generation and filtered-colimit continuity extend its uniform bound.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Over a finite coefficient ring, vanishing of a higher direct image on constructible
sheaves implies its vanishing on all sheaves, when the source is quasi-compact and
quasi-separated and the morphism is quasi-compact and quasi-separated.

Source: Stacks Project, Tags 03SA (constructible generation) and 09Z1 (continuity);
ILO, Exposé XIII, Proposition 2.3.4, printed p. 198, reduction to constructible sheaves.

Proof: express an arbitrary sheaf as a filtered colimit of constructible sheaves.
The degree-q higher-direct-image functor preserves this filtered colimit. Each object of
the resulting diagram is zero by the hypothesis. The colimit is zero: its identity and
zero morphism agree
after every cocone leg, whose source is zero. Compare bounded-below homology with the
ordinary right derived functor. The argument preserves the given degree and therefore any
uniform bound; it also works in degree zero and on the empty scheme.

(blueprint: lem-per-qe-open-residue-constructible-vanishing-extension)
-/
theorem isZero_rightDerived_lowerStar_of_constructible
    (B : Type (u + 1)) [CommRing B] [Finite B] {Y S : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (h : ∀ (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)),
      Scheme.IsConstructibleEtaleModuleSheaf M →
        IsZero (((lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M))
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    IsZero (((lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M) := by
  obtain ⟨J, _, _, D, hD, ι, ⟨hc⟩⟩ := Scheme.exists_filtered_colimit_constructible M
  let H := DerivedCategory.Plus.singleFunctor _ 0 ⋙
    rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f ⋙
      DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} H :=
    preservesFilteredColimitsOfSize_higherDirectImage B f q
  have hz : IsZero (H.obj M) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (isColimitOfPreserves H hc).hom_ext
    intro j
    have hj := h (D.obj j) (hD j)
    have hzj : IsZero (H.obj (D.obj j)) := hj.of_iso
      ((lowerStar (ModuleCat.{u + 1} B) f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
        (D.obj j) q)
    exact hzj.eq_of_src _ _
  exact hz.of_iso
    ((lowerStar (ModuleCat.{u + 1} B) f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
      M q).symm

end AlgebraicGeometry.Etale
