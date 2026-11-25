/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Shifting a uniform direct-image bound to the truncation tail

Source: Stacks Project, Tag 08D5, final truncation argument
(blueprint: lem-pc-direct-image-truncation-tail-bound).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A bound on nonpositive quasi-coherent derived objects gives a bound on the
upper truncation tail, without any geometric hypotheses beyond the supplied bound.
Source: Stacks Project, Tag 08D5, final truncation argument
(blueprint: lem-pc-direct-image-truncation-tail-bound).

Proof: Put T = τ_{< -n} E. Its cohomology is quasi-coherent, since it is either
zero or the corresponding cohomology of E. The shift T[-n-1] has no positive
cohomology: H^m(T[-n-1]) = H^{m-n-1}(T), which vanishes when m > 0.
Apply the supplied uniform bound to this shifted quasi-coherent derived object
in degree j+n+1. Derived direct image commutes with shifts and
H^{j+n+1}(Rf_*(T[-n-1])) is naturally isomorphic to H^j(Rf_*T).
Transport its zero-object property along this isomorphism. This works for all
integers n and j; no nonnegativity hypothesis on n is needed. -/
theorem directImage_truncation_tail_bound
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) (N : ℤ)
    (hN : ∀ E : schemeDerivedQCohCategory X,
      (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj)) →
      ∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj))
    (E : schemeDerivedQCohCategory X) (n j : ℤ) (hj : N ≤ j + n + 1) :
    IsZero ((schemeHigherDirectImage f j).obj
      ((DerivedCategory.TStructure.t.truncLT (-n)).obj E.obj)) := by
  let T := (DerivedCategory.TStructure.t.truncLT (-n)).obj E.obj
  let R := moduleRings X.toRingedSpace
  let P := SheafOfModules.isQuasicoherent R
  have hzero : IsZero (SheafOfModules.free (R := R) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : P.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free (R := R) PEmpty.{u + 1}⟩⟩
  have hT : DerivedCategory.homologyProperty P T := by
    have hle := DerivedCategory.homologyProperty_truncLE E.property (-n - 1)
    exact (DerivedCategory.homologyProperty P).prop_of_iso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (-n - 1) (-n) (by omega)).app E.obj)
      hle
  have hshift : schemeDerivedQCohProperty X (T⟦-n - 1⟧) :=
    (DerivedCategory.homologyProperty P).le_shift (-n - 1) T hT
  have : (T⟦-n - 1⟧).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_shift T (-n - 1) (-n - 1) 0 (by omega)
  have hz := hN ⟨T⟦-n - 1⟧, hshift⟩
    (fun m hm ↦ DerivedCategory.isZero_of_isLE _ 0 m hm) (j + n + 1) hj
  let e := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (j + n + 1)).mapIso
      (((schemeDerivedDirectImage f).commShiftIso (-n - 1)).app T) ≪≫
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).shiftIso
      (-n - 1) (j + n + 1) j (by omega)).app ((schemeDerivedDirectImage f).obj T)
  exact hz.of_iso e.symm

end AlgebraicGeometry
