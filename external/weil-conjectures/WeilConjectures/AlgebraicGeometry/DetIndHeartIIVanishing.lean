/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity

/-! # Uniform vanishing on ind-constructible targets

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-ind-constructible-sheaves/sk-cor-ind-heart-ii/
sk-cor-ind-heart-ii-vanishing.md and its proof (blueprint: corollary-ind-heart-b--1).

The fixed bound on constructible targets is retained. Ext in every integer degree is
written as shifted Hom in the ordinary derived category of internal module objects.
The comparison is the map induced by the given ambient colimit cocone.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Every filtered constructible presentation gives the canonical Ext isomorphism,
and the supplied constructible-target cutoff also bounds every ind-constructible target.
The coefficient equality is between bundled monoid objects, including multiplication.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-ind-constructible-sheaves/sk-cor-ind-heart-ii/
sk-cor-ind-heart-ii-vanishing.md and its proof (blueprint: corollary-ind-heart-b--1).

Proof, following the three DAG steps:
1. Regard each constructible stage as a complex in degree zero. These complexes have
   common lower bound zero; the termwise colimit is the degree-zero complex of the
   ambient module colimit. The cocone is the specified module colimit cocone.
2. Apply clause (1) of lemma-continuity-ext-out-constructible-complex--1 to C in degree zero and
   this diagram, in every integer degree q. The standing scheme is separated and
   finite type over a field of positive characteristic different from ell, so its
   geometric hypotheses hold. The finite constant models and the pulled-back
   condensed E or finite-subextension-valued algebraic closure are the same ones.
   The resulting map is exactly colimit.desc of the mapped cocone below.
3. For q > d every stage Ext group is zero by the supplied bound. Its filtered
   colimit is zero, hence so is Ext into the colimit by step 2. Every object of
   IndCons has such a small filtered constructible presentation by
   proposition-ind-constructible-sheaves; apply the same argument to obtain the last clause with the
   original cutoff d. -/
theorem det_ind_heart_ii_vanishing
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (C : ConstantModelConstructible Λ X) (d : ℕ)
    (_hbound : ∀ N : ConstantModelConstructible Λ X, ∀ r : ℤ, (d : ℤ) < r →
      Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
        (shiftFunctor _ r).obj ((DerivedCategory.singleFunctor _ 0).obj N.obj))) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      (∀ i : I, IsConstantModelConstructible Λ X (D.obj i)) →
      ∀ (c : Cocone D), IsColimit c → ∀ q : ℤ,
        IsIso (colimit.desc _
          ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
            preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone
              c))) ∧
    (∀ B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
      ∀ q : ℤ, (d : ℤ) < q →
        Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C.obj ⟶
          (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj B))) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  rcases _hΛ with ⟨E, hE⟩ | hE
  · cases hE
    let R := Profinite.padicSubfieldCondensedRing ℓ E
    have hcomparison :
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
          (D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj R) X)),
          (∀ i : I, IsConstantModelConstructible (coefficientHeartRingObj R) X
            (D.obj i)) →
          ∀ (c : Cocone D), IsColimit c → ∀ q : ℤ,
            IsIso (colimit.desc _
              ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
                preadditiveCoyoneda.obj
                  (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone c)) := by
      intro I _ _ D hD c hc q
      exact constructible_sheaf_ext_continuity ℓ E R (Or.inl rfl) X C.obj C.property
        D c hc q
    constructor
    · intro I _ _ D hD c hc q
      exact hcomparison I D hD c hc q
    · intro B hB q hq
      rcases hB with ⟨I, _instI, _instF, pres, hpres⟩
      let F := pres.diag ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))
      have hiso : IsIso (colimit.desc _
          ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
            preadditiveCoyoneda.obj
              (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone
                pres.cocone)) := by
        exact hcomparison I pres.diag hpres pres.cocone pres.isColimit q
      let e := colimit.desc _
          ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
            preadditiveCoyoneda.obj
              (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone
                pres.cocone)
      let : IsIso e := hiso
      let Z : Ab.{u + 1} := colimit F
      have hsub : Subsingleton Z := by
        constructor
        intro x y
        obtain ⟨i, xi, hxi⟩ :=
          Concrete.isColimit_exists_rep F (colimit.isColimit F) x
        obtain ⟨j, yj, hyj⟩ :=
          Concrete.isColimit_exists_rep F (colimit.isColimit F) y
        let k := IsFiltered.max i j
        let hik := IsFiltered.leftToMax i j
        let hjk := IsFiltered.rightToMax i j
        let : Subsingleton (F.obj k) := _hbound
          ⟨pres.diag.obj k, hpres k⟩ q hq
        rw [← hxi, ← hyj]
        exact Concrete.isColimit_rep_eq_of_exists F xi yj
          ⟨k, hik, hjk, Subsingleton.elim _ _⟩
      let : Subsingleton Z := hsub
      constructor
      intro f g
      have hfg : (inv e).hom f = (inv e).hom g := Subsingleton.elim _ _
      have hfg' := congrArg (fun z => e.hom z) hfg
      simpa [e] using hfg'
  · cases hE
    let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
    let R := Profinite.padicAlgClCondensedRing ℓ
    have hcomparison :
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
          (D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (coefficientHeartRingObj R) X)),
          (∀ i : I, IsConstantModelConstructible (coefficientHeartRingObj R) X
            (D.obj i)) →
          ∀ (c : Cocone D), IsColimit c → ∀ q : ℤ,
            IsIso (colimit.desc _
              ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
                preadditiveCoyoneda.obj
                  (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone c)) := by
      intro I _ _ D hD c hc q
      exact constructible_sheaf_ext_continuity ℓ E R (Or.inr rfl) X C.obj C.property
        D c hc q
    constructor
    · intro I _ _ D hD c hc q
      exact hcomparison I D hD c hc q
    · intro B hB q hq
      rcases hB with ⟨I, _instI, _instF, pres, hpres⟩
      let F := pres.diag ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))
      have hiso : IsIso (colimit.desc _
          ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
            preadditiveCoyoneda.obj
              (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone
                pres.cocone)) := by
        exact hcomparison I pres.diag hpres pres.cocone pres.isColimit q
      let e := colimit.desc _
          ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
            preadditiveCoyoneda.obj
              (op ((DerivedCategory.singleFunctor _ 0).obj C.obj))).mapCocone
                pres.cocone)
      let : IsIso e := hiso
      let Z : Ab.{u + 1} := colimit F
      have hsub : Subsingleton Z := by
        constructor
        intro x y
        obtain ⟨i, xi, hxi⟩ :=
          Concrete.isColimit_exists_rep F (colimit.isColimit F) x
        obtain ⟨j, yj, hyj⟩ :=
          Concrete.isColimit_exists_rep F (colimit.isColimit F) y
        let k := IsFiltered.max i j
        let hik := IsFiltered.leftToMax i j
        let hjk := IsFiltered.rightToMax i j
        let : Subsingleton (F.obj k) := _hbound
          ⟨pres.diag.obj k, hpres k⟩ q hq
        rw [← hxi, ← hyj]
        exact Concrete.isColimit_rep_eq_of_exists F xi yj
          ⟨k, hik, hjk, Subsingleton.elim _ _⟩
      let : Subsingleton Z := hsub
      constructor
      intro f g
      have hfg : (inv e).hom f = (inv e).hom g := Subsingleton.elim _ _
      have hfg' := congrArg (fun z => e.hom z) hfg
      simpa [e] using hfg'

end AlgebraicGeometry.ProEtale
