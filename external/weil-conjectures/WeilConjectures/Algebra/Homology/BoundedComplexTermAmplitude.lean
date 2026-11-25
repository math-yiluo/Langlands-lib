/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage

/-! # Bounded complexes and the amplitudes of their terms

Source: Stacks Project, Tag 066H.
(blueprint: lem-pc-bounded-complex-term-amplitude).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma bounded_mem_of_single_terms
    {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D] [HasZeroObject D]
    (S : ObjectProperty (HomotopyCategory D (.up ℤ)))
    [S.IsTriangulatedClosed₂] [S.IsClosedUnderIsomorphisms] [S.ContainsZero]
    (K : CochainComplex D ℤ) (r s : ℤ) [K.IsStrictlyGE r] [K.IsStrictlyLE s]
    (hK : ∀ n : ℤ, r ≤ n → n ≤ s → S ((HomotopyCategory.singleFunctor D n).obj (K.X n))) :
    S ((HomotopyCategory.quotient D _).obj K) := by
  by_cases h₀ : r ≤ s
  · obtain ⟨n, hn⟩ := Int.le.dest h₀
    clear h₀
    revert K hn r s
    induction n with
    | zero =>
        intro K r s _ _ hK hrs
        obtain rfl : r = s := by simpa using hrs
        exact S.prop_of_iso
          ((HomotopyCategory.singleFunctorPostcompQuotientIso D r).app _ ≪≫
            ((HomotopyCategory.quotient D _).mapIso (K.isoSingle r)).symm)
          (hK r (by rfl) (by rfl))
    | succ n ih =>
        intro K r s _ _ hK hrs
        apply S.ext_of_isTriangulatedClosed₂ _
          (HomotopyCategory.trianglehOfDegreewiseSplit_distinguished _
            (K.shortComplexStupidTruncSplitting
              (ComplexShape.Embedding.embeddingUpInt_areComplementary (r + n) s (by omega))))
        · dsimp
          refine @ih _ (r + 1) s
            (CochainComplex.isStrictlyGE_of_ge _ _ s (by omega)) inferInstance
            (fun m h₁ h₂ ↦ ?_) (by omega)
          obtain h₃ | rfl := h₂.lt_or_eq
          · apply S.prop_of_isZero
            apply Functor.map_isZero
            exact CochainComplex.isZero_of_isStrictlyGE _ s _ h₃
          · obtain ⟨k, hk⟩ := Int.le.dest h₂
            exact S.prop_of_iso ((HomotopyCategory.singleFunctor D m).mapIso
              ((CategoryTheory.Iso.ofIsIso
                (K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE m) (i := k)
                  (by dsimp; omega))).symm))
              (hK m (by omega) h₂)
        · dsimp
          refine @ih _ r (r + n) inferInstance inferInstance (fun m h₁ h₂ ↦ ?_) rfl
          obtain ⟨k, hk⟩ := Int.le.dest h₂
          exact S.prop_of_iso ((HomotopyCategory.singleFunctor D m).mapIso
            (CategoryTheory.Iso.ofIsIso
              (K.isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE (r + n)) (i := k)
                (by dsimp; omega))))
            (hK m h₁ (by omega))
  · have hzero : IsZero K := by
      rw [IsZero.iff_id_eq_zero]
      ext n
      apply IsZero.eq_of_src
      by_cases hn : r ≤ n
      · exact K.isZero_of_isStrictlyLE s n (by omega)
      · exact K.isZero_of_isStrictlyGE r n (by omega)
    exact S.prop_of_isZero ((HomotopyCategory.quotient D _).map_isZero hzero)

/-- A bounded complex has amplitude `[a,b]` if each of its terms, placed in its actual
cochain degree, has that amplitude.

Source: Stacks Project, Tag 066H.
(blueprint: lem-pc-bounded-complex-term-amplitude).

Proof: induct on the finite number of supported degrees, using the degreewise split
stupid-truncation triangle. Tensoring this distinguished triangle with a module in degree
zero remains distinguished. Both bounds of the canonical t-structure are extension closed,
so the middle object inherits the two bounds from the two outer objects. The one-term
case is the corresponding single complex. If the support interval is empty, every term
is zero and so is the complex. This argument imposes no flatness on the terms. -/
theorem bounded_torAmplitude_of_single_terms
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r s a b : ℤ)
    (hdegrees : ∀ n : ℤ, n < r ∨ s < n → IsZero (K.X n))
    (hterms : ∀ n : ℤ, r ≤ n → n ≤ s →
      DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (K.X n))) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b (DerivedCategory.Q.obj K) := by
  have : K.IsStrictlyGE r := (isStrictlyGE_iff K r).2 fun n hn ↦ hdegrees n (Or.inl hn)
  have : K.IsStrictlyLE s := (isStrictlyLE_iff K s).2 fun n hn ↦ hdegrees n (Or.inr hn)
  intro M
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
  let := DerivedCategory.commShiftTensorRightQhObj P hP
  have := DerivedCategory.isTriangulated_tensorRightQhObj P hP
  let F := DerivedCategory.Qh (C := ModuleCat.{u} R) ⋙
    (MonoidalCategory.curriedTensor (DerivedCategory (ModuleCat.{u} R))).flip.obj
      (DerivedCategory.Qh.obj P)
  let S : ObjectProperty (HomotopyCategory (ModuleCat.{u} R) (.up ℤ)) :=
    (DerivedCategory.homologyConcentratedIn a b).inverseImage F
  have : S.IsClosedUnderIsomorphisms := inferInstance
  let Z := (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj 0
  have hZ : IsZero Z := (HomotopyCategory.quotient _ _).map_isZero (isZero_zero _)
  have : S.ContainsZero := ⟨⟨Z, hZ, by
    change DerivedCategory.homologyConcentratedIn a b (F.obj Z)
    have hz := F.map_isZero hZ
    exact ⟨DerivedCategory.TStructure.t.isGE_of_isZero hz a,
      DerivedCategory.TStructure.t.isLE_of_isZero hz b⟩⟩⟩
  have : S.IsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦ by
    exact ⟨DerivedCategory.TStructure.t.isGE₂ _ (F.map_distinguished T hT) a h₁.1 h₃.1,
      DerivedCategory.TStructure.t.isLE₂ _ (F.map_distinguished T hT) b h₁.2 h₃.2⟩
  have h := bounded_mem_of_single_terms S K r s (fun n hn hn' ↦ by
    exact ((DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (MonoidalCategory.whiskerRightIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) n).app _ ≪≫
          ((DerivedCategory.quotientCompQhIso _).app _).symm) _)
      ((DerivedCategory.homologyConcentratedIn a b).prop_of_iso
        (MonoidalCategory.whiskerLeftIso _ e.symm) (hterms n hn hn' M))))
  exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
    (MonoidalCategory.whiskerRightIso ((DerivedCategory.quotientCompQhIso _).app K) _ ≪≫
      MonoidalCategory.whiskerLeftIso _ e) h

end CochainComplex
