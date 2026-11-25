/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization
import WeilConjectures.AlgebraicGeometry.Native.NativeAdicProperCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration

/-! # Actual locally finite adic compact supports on constructible localizing hulls
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

/-- The full replete localizing hull of bounded complexes with native constructible cohomology.
This specializes the existing localizing closure and bounded constructible predicates. -/
abbrev nativeAdicConstructibleLocalizingHull (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (AdicSheaf l T)) :=
  (DerivedCategory.boundedAdicConstructible l T).localizingClosure

/-- Actual ambient compact support for a specified compactification: apply the native open
extension by zero termwise and then take the ordinary total right derived proper direct image. -/
noncomputable abbrev nativeAdicCompactSupport (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    _root_.DerivedCategory (AdicSheaf l X) ⥤ _root_.DerivedCategory (AdicSheaf l Y) :=
  (adicOpenImmersionLowerShriek l c.i).mapDerivedCategory ⋙
    (adicLowerStar l c.g).rightDerivedFunctor

private theorem nativeCompactSupport_bounded
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime] (hl : ringChar k₀ ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∀ K, DerivedCategory.boundedAdicConstructible l X K →
      DerivedCategory.boundedAdicConstructible l Y ((nativeAdicCompactSupport l c).obj K) := by
  classical
  let : Fintype k₀ := Fintype.ofFinite k₀
  obtain ⟨n, hp, hn⟩ := FiniteField.card k₀ (ringChar k₀)
  let D : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := ringChar k₀, a := n, q := Nat.card k₀, prime := hp
      exponent_pos := n.pos, cardinality_eq := by simpa only [Nat.card_eq_fintype_card] using hn
      k₀ := k₀, card_base := rfl, k := k }
  obtain ⟨P⟩ :=
    WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_construction
      l (ULift.{u} (PadicAlgCl l)) D (Ne.symm hl) f
  obtain ⟨G, ⟨C⟩⟩ :=
    WeilConjectures.LocallyFiniteAdicCompactSupport.locally_finite_adic_compact_support_realization
      l D (Ne.symm hl) P c
  exact C.preserves

private theorem nativeOpen_bounded
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime] (hl : ringChar k₀ ≠ l)
    {X Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    (j : X ⟶ Z) [j.IsOver (Spec (CommRingCat.of k))]
    [IsOpenImmersion j] [QuasiCompact j] :
    ∀ K, DerivedCategory.boundedAdicConstructible l X K →
      DerivedCategory.boundedAdicConstructible l Z
        ((adicOpenImmersionLowerShriek l j).mapDerivedCategory.obj K) := by
  intro K hK
  have h := nativeCompactSupport_bounded k₀ k l hl j (.ofIsOpenImmersion j) K hK
  let e : (adicLowerStar l (𝟙 Z)).rightDerivedFunctor ≅
      𝟭 (_root_.DerivedCategory (AdicSheaf l Z)) :=
    (adicLowerStar l (𝟙 Z)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso (adicLowerStarId l Z) ≪≫
      Functor.mapDerivedCategoryIdIso _
  have : (DerivedCategory.boundedAdicConstructible l Z).IsClosedUnderIsomorphisms := by
    dsimp [DerivedCategory.boundedAdicConstructible]
    infer_instance
  exact (DerivedCategory.boundedAdicConstructible l Z).prop_of_iso
    (e.app ((adicOpenImmersionLowerShriek l j).mapDerivedCategory.obj K)) h

/-- The actual compact-support functor restricts to an exact functor between the constructible
localizing hulls and preserves every small coproduct there. Absolute separatedness of the
schemes is not assumed. The ambient derived categories are ordinary module derived categories;
no coproduct assertion is made for the whole ambient categories.
-/
theorem nativeAdicCompactSupport_localizing_preservesCoproducts
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime] (hl : ringChar k₀ ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ h : ∀ K, nativeAdicConstructibleLocalizingHull l X K →
        nativeAdicConstructibleLocalizingHull l Y ((nativeAdicCompactSupport l c).obj K),
      ((nativeAdicConstructibleLocalizingHull l X).liftFullSubcategory
        (nativeAdicConstructibleLocalizingHull l Y)
        (nativeAdicCompactSupport l c) h).IsTriangulated ∧
      ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
        ((nativeAdicConstructibleLocalizingHull l X).liftFullSubcategory
          (nativeAdicConstructibleLocalizingHull l Y) (nativeAdicCompactSupport l c) h) := by
  let S := Spec (CommRingCat.of k)
  let : c.Z.Over S := ⟨c.g ≫ (Y ↘ S)⟩
  have : c.i.IsOver S := ⟨by
    change c.i ≫ (c.g ≫ (Y ↘ S)) = (X ↘ S)
    rw [← Category.assoc, ← c.comm]
    exact comp_over f S⟩
  have : LocallyOfFiniteType (c.Z ↘ S) := by
    change LocallyOfFiniteType (c.g ≫ (Y ↘ S))
    infer_instance
  have : QuasiCompact (c.Z ↘ S) := by
    change QuasiCompact (c.g ≫ (Y ↘ S))
    infer_instance
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ S)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have : IsNoetherian Y := ⟨⟩
  let J := (adicOpenImmersionLowerShriek l c.i).mapDerivedCategory
  let G := (adicLowerStar l c.g).rightDerivedFunctor
  let PX := DerivedCategory.boundedAdicConstructible l X
  let PZ := DerivedCategory.boundedAdicConstructible l c.Z
  let PY := DerivedCategory.boundedAdicConstructible l Y
  have : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) J := fun _ ↦
    inferInstance
  have hJ : ∀ K, PX.localizingClosure K → PZ.localizingClosure (J.obj K) :=
    ObjectProperty.localizingClosure_le_inverseImage PX PZ fun K hK ↦
      PZ.le_localizingClosure _ (nativeOpen_bounded k₀ k l hl c.i K hK)
  let JL := PX.localizingClosure.liftFullSubcategory PZ.localizingClosure J hJ
  have hJL (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) JL := by
    have : PreservesColimitsOfShape (Discrete I) (JL ⋙ PZ.localizingClosure.ι) :=
      preservesColimitsOfShape_of_natIso
        (PX.localizingClosure.liftFullSubcategoryCompιIso PZ.localizingClosure J hJ).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves JL PZ.localizingClosure.ι
  have hchar : ringChar k ≠ l := by
    rwa [← Algebra.ringChar_eq k₀ k]
  have hG (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (PZ.localizingClosure.ι ⋙ G) :=
    nativeAdicProper_preservesCoproducts k l hchar (Y ↘ S) c.g I
  have hsum (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I)
        (PX.localizingClosure.ι ⋙ nativeAdicCompactSupport l c) := by
    let := hJL I
    let := hG I
    have : PreservesColimitsOfShape (Discrete I) (JL ⋙ (PZ.localizingClosure.ι ⋙ G)) :=
      inferInstance
    exact this
  have : ∀ I : Type (u + 1),
      PreservesColimitsOfShape (Discrete I)
        (PX.localizingClosure.ι ⋙ nativeAdicCompactSupport l c) := hsum
  have h : ∀ K, PX.localizingClosure K →
      PY.localizingClosure ((nativeAdicCompactSupport l c).obj K) :=
    ObjectProperty.localizingClosure_obj_of_le PX PY (nativeAdicCompactSupport l c)
      (fun K hK ↦ PY.le_localizingClosure _
        (nativeCompactSupport_bounded k₀ k l hl f c K hK))
  refine ⟨h, inferInstance, ?_⟩
  intro I
  have : PreservesColimitsOfShape (Discrete I)
      (PX.localizingClosure.liftFullSubcategory PY.localizingClosure
        (nativeAdicCompactSupport l c) h ⋙ PY.localizingClosure.ι) :=
    preservesColimitsOfShape_of_natIso
      (PX.localizingClosure.liftFullSubcategoryCompιIso PY.localizingClosure
        (nativeAdicCompactSupport l c) h).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ PY.localizingClosure.ι

end AlgebraicGeometry.ProEtale
