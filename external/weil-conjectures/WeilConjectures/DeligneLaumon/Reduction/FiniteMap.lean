/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology

/-!
# Compactly supported cohomology along a finite map

For a finite morphism `g : C ⟶ Y` of separated `k₀`-schemes of finite type, the direct image
`g₀*` is exact and `Rg₀! = Rg₀*`, so that `H_c^i(C, F) ≅ H_c^i(Y, g₀*F)`. Combined with the
extension by zero along a quasi-compact open immersion `j : C ⟶ C'`, this transports the
compactly supported cohomology of a sheaf on `C` to that of `g₀*j₀!F` on `Y`; this is how the
Deligne–Laumon bound on a curve is reduced to the affine line.

## Main statements

- `WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerStar_of_isFinite`:
  blueprint `lemma-finite-generically-etale-map-line--3`.
- `WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerStar_extensionByZero`:
  blueprint `lemma-finite-generically-etale-map-line--3`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Cohomology under a finite map** (blueprint: `lemma-finite-generically-etale-map-line--3`,
there for `Y = 𝔸¹` and `F` lisse). For a finite morphism `g : C ⟶ Y` of separated `k₀`-schemes of
finite type and a Weil sheaf `F` on `C`, `H_c^i(C, F) ≅ H_c^i(Y, g₀*F)` as Frobenius modules: the
direct image `Rg₀*F` is `g₀*F` placed in degree zero, `g₀*` being exact, and
`R(a_C)₀! ≅ R(a_Y)₀! ∘ Rg₀! ≅ R(a_Y)₀! ∘ Rg₀*` since `g` is proper. -/
theorem nonempty_equiv_compactlySupportedCohomology_lowerStar_of_isFinite
    {C Y : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (g : C ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsFinite g] (F : WeilSheaf k₀ l C)
    (i : ℤ) :
    Nonempty ((F.compactlySupportedCohomology i).Equiv
      (((lowerStar g).obj F).compactlySupportedCohomology i)) := by
  -- `Rg₀*F` is `g₀*F` placed in degree zero
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_toComplex_homologySheaf_zero
    ((WeilComplex.derivedLowerStar g).obj (toComplex.obj F)) fun b hb ↦ by
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact isZero_homologySheaf_derivedLowerStar_of_neg g F hb
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
        exact isZero_higherLowerStar_of_isFinite g F n (by exact_mod_cast hb)
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) g
    (Y ↘ Spec (CommRingCat.of k₀))
  let E := (WeilComplex.derivedLowerShriekCongr (comp_over g _).symm).app (toComplex.obj F) ≪≫
    e₅.app _ ≪≫ (WeilComplex.derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).mapIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar g _ ≪≫ e₂ ≪≫
        toComplex.mapIso (homologySheafZeroDerivedLowerStarIso g F))
  exact ⟨globalSectionsEquivOfIso ((WeilComplex.homologySheaf i).mapIso E)⟩

/-- **Cohomology transport under the finite-map reduction** (blueprint:
`lemma-finite-generically-etale-map-line--3`, there for curves and `Y = 𝔸¹`). For a quasi-compact
open immersion `j : C ⟶ C'` and a finite morphism `g : C' ⟶ Y` of separated `k₀`-schemes of finite
type and a Weil sheaf `F` on `C`, `H_c^i(C, F) ≅ H_c^i(Y, g₀*j₀!F)` as Frobenius modules:
`H_c^i(C, F) ≅ H_c^i(C', j₀!F)` since `R(a_C)₀! ≅ R(a_{C'})₀! ∘ Rj₀!` and `Rj₀!F ≅ j₀!F`, and
the finite-map transport
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_lowerStar_of_isFinite`)
applies to `j₀!F`. -/
theorem nonempty_equiv_compactlySupportedCohomology_lowerStar_extensionByZero
    {C C' Y : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
    [C'.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C' ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (j : C ⟶ C') [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (g : C' ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsFinite g] (F : WeilSheaf k₀ l C)
    (i : ℤ) :
    Nonempty ((F.compactlySupportedCohomology i).Equiv
      (((lowerStar g).obj ((extensionByZero j).obj F)).compactlySupportedCohomology i)) := by
  obtain ⟨e₁⟩ := WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion j F
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j
    (C' ↘ Spec (CommRingCat.of k₀))
  let E := (WeilComplex.derivedLowerShriekCongr (comp_over j _).symm).app (toComplex.obj F) ≪≫
    e₅.app _ ≪≫ (WeilComplex.derivedLowerShriek k₀ l (C' ↘ Spec (CommRingCat.of k₀))).mapIso e₁
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_lowerStar_of_isFinite g
    ((extensionByZero j).obj F) i
  exact ⟨(globalSectionsEquivOfIso ((WeilComplex.homologySheaf i).mapIso E)).trans e⟩

end AlgebraicGeometry.WeilSheaf
