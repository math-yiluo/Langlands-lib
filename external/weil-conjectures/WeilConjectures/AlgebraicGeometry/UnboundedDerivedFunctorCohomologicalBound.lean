/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.AlgebraicGeometry.DerivedFunctorTruncationStabilization
import WeilConjectures.AlgebraicGeometry.QCohTruncationDerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.DerivedLimitEventuallyIso
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# An upper cohomological bound for an unbounded derived functor

Source: Stacks Project, Derived Categories of Schemes, Tag 08D4, part (3), upper-bound
clause (blueprint: lem-pc-unbounded-derived-functor-cohomological-bound).
-/

@[expose] public section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An additive functor commuting with countable products and with `R^p F = 0` on
quasi-coherent modules for `p ≥ N` sends quasi-coherent derived objects supported in
degrees at most `b` to objects supported in degrees at most `b + N - 1`.

Source: Stacks Project, Tag 08D4, part (3), upper-bound clause
(blueprint: lem-pc-unbounded-derived-functor-cohomological-bound).

Proof:
1. Put `E_n = τ_{≥ -n} E`. Use `lem-pc-qcoh-truncation-derived-limit` to
reconstruct after `RF`, and apply `lem-pc-derived-limit-milnor-sequence` in degree `i`.
2. For `i ≥ b + N`, start with `E_{-b-1} = τ_{≥ b+1} E = 0`, by the standard
t-structure and the support assumption. The right derived functor preserves zero
objects. Integer induction using `lem-pc-derived-functor-truncation-stabilization`
then gives `H^i(RF(E_n)) = 0` for every integer `n ≥ -b-1`: the successor index
`n+1` is at least `N-i`.
3. In degree `i-1`, successor transitions of the natural-number tower are
isomorphisms for `n ≥ max(0,N-i)`. Apply
`lem-pc-derived-limit-eventually-iso` to make the left Milnor endpoint zero.
4. The degree-`i` tower is eventually zero by step 2. For each projection to term
`j`, choose a natural `n ≥ j` and `n ≥ -b-1`; compatibility factors that projection
through the zero term `n`. Limit extensionality makes the right Milnor endpoint
zero. Exactness between zero endpoints gives the required vanishing.
-/
theorem isZero_homology_rightDerivedFunctor_of_cohomological_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
    [Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤ AddCommGrpCat.{u})
    [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      M.IsQuasicoherent → ∀ p : ℕ, N ≤ p → IsZero ((F.rightDerived p).obj M))
    (b : ℤ) (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) :
    ∀ i : ℤ, b + (N : ℤ) - 1 < i →
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        (F.rightDerivedFunctor.obj E)) := by
  intro i hi
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let G := F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  have hLE : E.IsLE b := (DerivedCategory.isLE_iff E b).2 hb
  have hbase : IsZero (G.obj ((t.truncGE (-(-b - 1))).obj E)) := by
    have hz : IsZero ((t.truncGE (b + 1)).obj E) :=
      t.isZero_truncGE_obj_of_isLE b (b + 1) rfl E
    have hz' := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map_isZero
      (F.isZero_rightDerivedFunctor_obj hz)
    simpa only [G, Functor.comp_obj, show -(-b - 1) = b + 1 by omega] using hz'
  have hzero : ∀ n : ℤ, -b - 1 ≤ n → IsZero (G.obj ((t.truncGE (-n)).obj E)) := by
    refine Int.leInduction (motive := fun n _ ↦
      IsZero (G.obj ((t.truncGE (-n)).obj E))) hbase ?_
    intro n hn ih
    have hstep := isIso_rightDerivedFunctor_lowerTruncation_step
      X F N hN ⟨E, hE⟩ i (n + 1) (by omega)
    have htarget : IsZero (G.obj ((t.truncGE (-(n + 1) + 1)).obj E)) := by
      simpa only [show -(n + 1) + 1 = -n by omega] using ih
    have : IsIso (G.map ((t.natTransTruncGEOfLE (-(n + 1)) (-(n + 1) + 1)
      (Int.le_add_one (le_refl (-(n + 1))))).app E)) := hstep
    exact htarget.of_iso (asIso (G.map
      ((t.natTransTruncGEOfLE (-(n + 1)) (-(n + 1) + 1)
        (Int.le_add_one (le_refl (-(n + 1))))).app E)))
  let T : ℕ → DerivedCategory AddCommGrpCat.{u} := fun n ↦
    F.rightDerivedFunctor.obj ((t.truncGE (-(n : ℤ))).obj E)
  let f : ∀ n : ℕ, T (n + 1) ⟶ T n := fun n ↦
    F.rightDerivedFunctor.map ((t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)
  let K := Functor.ofOpSequence f
  obtain ⟨δ, hδ⟩ := rightDerivedFunctor_qcoh_truncation_isDerivedLimitTriangle X E hE F
  let p : F.rightDerivedFunctor.obj E ⟶ ∏ᶜ T := Pi.lift (fun n ↦
    F.rightDerivedFunctor.map ((t.truncGEπ (-(n : ℤ))).app E))
  obtain ⟨a, c, hmilnor, _⟩ := milnor_shortExact.{u, w'} i
  have hδ' : IsDerivedLimitTriangle
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
      (F.rightDerivedFunctor.obj E) p δ := by
    simpa only [K, Functor.ofOpSequence_map_homOfLE_succ] using hδ
  obtain ⟨⟨hz, hexact⟩, _⟩ := hmilnor K (F.rightDerivedFunctor.obj E) p δ hδ'
  let A := K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)
  have hA : ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op) := by
    refine ⟨((N : ℤ) - i).toNat, ?_⟩
    intro n hn
    have hstep := isIso_rightDerivedFunctor_lowerTruncation_step
      X F N hN ⟨E, hE⟩ (i - 1) ((n + 1 : ℕ) : ℤ) (by omega)
    rw! [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega] at hstep
    simpa only [A, K, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
      f, t] using hstep
  have hleft := isZero_firstDerivedLimit_of_eventually_isIso A hA
  let B := K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  have hright : IsZero (limit B) := by
    rw [IsZero.iff_id_eq_zero]
    apply limit.hom_ext
    intro j
    let n := max j.unop (-b - 1).toNat
    have hn : -b - 1 ≤ (n : ℤ) := by dsimp [n]; omega
    have hBn : IsZero (B.obj (Opposite.op n)) := hzero n hn
    have hπ : limit.π B (Opposite.op n) = 0 := hBn.eq_of_tgt _ _
    have hw := limit.w B (homOfLE (show j.unop ≤ n by exact le_max_left _ _)).op
    simpa only [hπ, zero_comp, Category.id_comp] using hw.symm
  exact hexact.exact.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

end AlgebraicGeometry
