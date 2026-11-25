/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # One open/closed step for a constructible condensed sheaf -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem exists_closed_complement {T : Scheme.{u}} (U : T.Opens) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      IsClosedImmersion i ∧ Set.range U.ι = (Set.range i)ᶜ := by
  refine ⟨_, U.closedComplement, Scheme.Opens.isClosedImmersion_closedComplement U, ?_⟩
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_closedComplement, compl_compl]

private lemma transport_distinguished
    {D : Type*} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (B : Pretriangulated.Triangle D) (hB : B ∈ distTriang D)
    {X Y Z : D} (e₁ : B.obj₁ ≅ X) (e₂ : B.obj₂ ≅ Y) (e₃ : B.obj₃ ≅ Z) :
    Pretriangulated.Triangle.mk (e₁.inv ≫ B.mor₁ ≫ e₂.hom)
      (e₂.inv ≫ B.mor₂ ≫ e₃.hom)
      (e₃.inv ≫ B.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map e₁.hom) ∈ distTriang D := by
  apply Pretriangulated.isomorphic_distinguished _ hB
  refine Pretriangulated.Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm
    (by simp) (by simp) ?_
  change (e₃.inv ≫ B.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map e₁.hom) ≫
    (shiftFunctor D (1 : ℤ)).map e₁.inv = e₃.inv ≫ B.mor₃
  simp only [Category.assoc, ← Functor.map_comp, e₁.hom_inv_id]
  rw [(shiftFunctor D (1 : ℤ)).map_id B.obj₁]
  rw [Category.comp_id]

private theorem open_closed_single_triangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T U Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ T) M) :
    Exists fun [_hex : PreservesFiniteColimits (CondensedRing.lowerStar Λ i)] ↦
    ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
    IsConstructibleModuleObject (condensedRingObj Λ Z) MZ ∧
    ∃ (f : (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj
            ((CondensedRing.upperStar Λ j).obj M)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj M)
      (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
        (CondensedRing.lowerStar Λ i).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj MZ))
      (h : (CondensedRing.lowerStar Λ i).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj
            ((CondensedRing.upperStar Λ j).obj M)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g h ∈ distTriang _ := by
  obtain ⟨hex, hrest⟩ := CondensedRing.condensed_open_closed_recollement Λ i j hij
  let := hex
  obtain ⟨ishriek, hadd, hleft, ash, aj, bj, ai, bi, hjshift, hishift, hrest⟩ :=
    hrest.2.2.2.2.2.2.2.2.2.2.2.2
  let := hadd
  let := hleft
  let := hjshift
  let := hishift
  obtain ⟨δ, ε, hδ, hε, htri, hrest'⟩ := hrest.2.2.2.2.2.2.2.2.2.2.2.2
  let C := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let K := (DerivedCategory.Plus.singleFunctor C 0).obj M
  let F := DerivedCategory.Plus.ι (C := C)
  let B := F.mapTriangle.obj
    (Pretriangulated.Triangle.mk (aj.counit.app K) (ai.unit.app K) (δ.app K))
  have hB : B ∈ distTriang _ := F.map_distinguished _ (htri K)
  let e₁ : B.obj₁ ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj
        ((CondensedRing.upperStar Λ j).obj M)) :=
    (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.mapIso
      (((CondensedRing.upperStar Λ j).mapDerivedCategorySingleFunctor 0).app M) ≪≫
    ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategorySingleFunctor 0).app _
  let e₂ : B.obj₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M :=
    (DerivedCategory.Plus.singleFunctorιIso _ 0).app M
  let e₃ : B.obj₃ ≅
      (CondensedRing.lowerStar Λ i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.upperStar Λ i).obj M)) :=
    (CondensedRing.lowerStar Λ i).mapDerivedCategory.mapIso
      (((CondensedRing.upperStar Λ i).mapDerivedCategorySingleFunctor 0).app M)
  exact ⟨hex, (CondensedRing.upperStar Λ i).obj M,
    CondensedRing.isConstructibleModuleObject_upperStar Λ i M hM,
    _, _, _, transport_distinguished B hB e₁ e₂ e₃⟩

private theorem piece_of_lfp_identity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj Λ T)
      ((CondensedRing.upperStar Λ (𝟙 T)).obj M)) :
    condensedLocallyClosedPiece Λ T ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have : (CondensedRing.upperStar Λ (𝟙 T)).IsEquivalence :=
    Functor.isEquivalence_of_iso (profinitePointModuleIdentity Λ T).symm
  let adj := CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 T)
  refine ⟨T, T, 𝟙 T, 𝟙 T, inferInstance, inferInstance, inferInstance,
    (CondensedRing.upperStar Λ (𝟙 T)).obj M, hP, ⟨?_⟩⟩
  exact (DerivedCategory.singleFunctor _ 0).mapIso
    ((asIso (adj.counit.app M)).symm ≪≫
      ((profinitePointModuleDirectImageIdentity Λ T).app _).symm)

private theorem nonempty_constructible_step
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ T) M)
    (U : T.Opens) (hU : (U : Set T).Nonempty)
    (hP : IsLocallyFinitelyPresented (condensedRingObj Λ U)
      ((CondensedRing.upperStar Λ U.ι).obj M))
    (P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) → Prop)
    (hpiece : ∀ U : T.Opens,
      IsLocallyFinitelyPresented (condensedRingObj Λ U)
        ((CondensedRing.upperStar Λ U.ι).obj M) →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek Λ U.ι).obj
          ((CondensedRing.upperStar Λ U.ι).obj M)))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      Exists fun [_hi : IsClosedImmersion i] ↦
      Exists fun [_hex : PreservesFiniteColimits
          (CondensedRing.lowerStar Λ i)] ↦
      ¬ Function.Surjective i ∧
      ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj Λ Z)),
        IsConstructibleModuleObject
          (condensedRingObj Λ Z) MZ ∧
        ∃ (A : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj Λ T)))
          (f : A ⟶ (DerivedCategory.singleFunctor _ 0).obj M)
          (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
            (CondensedRing.lowerStar
              Λ i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ))
          (h : (CondensedRing.lowerStar
              Λ i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
            A⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧
          P A := by
  classical
  obtain ⟨x, hx⟩ := hU
  have : TopologicalSpace.NoetherianSpace (U : Scheme) :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  obtain ⟨Z, i, hi, hij⟩ := exists_closed_complement U
  let := hi
  obtain ⟨hex, MZ, hMZ, f, g, h, hdist⟩ :=
    open_closed_single_triangle Λ i U.ι hij M hM
  let := hex
  refine ⟨_, i, inferInstance, hex, ?_, MZ, hMZ, _, f, g, h, hdist, ?_⟩
  · intro hsurj
    have hxU : x ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      exact hx
    have hxc : x ∈ Set.range i := hsurj x
    have hxnot : x ∉ Set.range i := by
      have hxc : x ∈ (Set.range i)ᶜ := (Set.ext_iff.mp hij x).mp hxU
      exact hxc
    exact hxnot hxc
  · exact hpiece U hP

private theorem single_id_direct_image_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj N ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ (𝟙 T)).obj N)) :=
  ⟨(DerivedCategory.singleFunctor _ 0).mapIso
    ((profinitePointModuleDirectImageIdentity Λ T).app N).symm⟩

private theorem constructiblePieceOver_intro
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T Z U : Scheme.{u})
    (i : Z ⟶ T) (j : U ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hP : IsLocallyFinitelyPresented (condensedRingObj Λ U) P)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (hK : Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj P)))) :
    condensedLocallyClosedPiece Λ T K := by
  exact ⟨Z, U, i, j, inferInstance, inferInstance, inferInstance, P, hP, hK⟩

private theorem piece_of_lfp_open_module
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (U : T.Opens)
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj Λ U) P) :
    condensedLocallyClosedPiece Λ T ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.openImmersionLowerShriek Λ U.ι).obj
        P)) := by
  have : TopologicalSpace.NoetherianSpace (U : Scheme) :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  apply constructiblePieceOver_intro Λ T T U (𝟙 T) U.ι P hP
  exact single_id_direct_image_iso Λ T _

private theorem generic_constructible_one_step
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj Λ T) M) :
    condensedLocallyClosedPiece Λ T ((DerivedCategory.singleFunctor _ 0).obj M) ∨
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      Exists fun [_hi : IsClosedImmersion i] ↦
      Exists fun [_hex : PreservesFiniteColimits
          (CondensedRing.lowerStar Λ i)] ↦
      ¬ Function.Surjective i ∧
      ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj Λ Z)),
        IsConstructibleModuleObject
          (condensedRingObj Λ Z) MZ ∧
        ∃ (A : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj Λ T)))
          (f : A ⟶ (DerivedCategory.singleFunctor _ 0).obj M)
          (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
            (CondensedRing.lowerStar
              Λ i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ))
          (h : (CondensedRing.lowerStar
              Λ i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
            A⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧
          condensedLocallyClosedPiece Λ T A := by
  rcases condensed_constructible_generic_lfp T Λ M hM with hP | ⟨U, hU, hP⟩
  · apply Or.inl
    apply piece_of_lfp_identity Λ T M
    exact localFinitePresentation_of_iso ((profinitePointModuleIdentity Λ T).app M).symm hP
  · apply Or.inr
    apply nonempty_constructible_step Λ T M hM U hU hP (condensedLocallyClosedPiece Λ T)
    intro V hV
    exact piece_of_lfp_open_module Λ T V _ hV

/-- A constructible sheaf is a single locally closed piece, or an extension by a
constructible sheaf supported on a proper closed subscheme.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), open/closed induction step.
(auxiliary; not a blueprint node)

Proof: if T is nonempty, choose the finite stratification in constructibility.
The union of the interiors of its locally closed strata is dense: each stratum
minus its interior is nowhere dense, and a finite union of those is nowhere dense.
Thus some stratum has nonempty interior U. Restrict that stratum's presentations
to U, with the canonical coefficient comparisons, to obtain a locally finitely
presented module there. More precisely, the base change of the stratum to U is
a surjective closed immersion; empty-complement recollement gives a coefficient-
compatible equivalence reflecting the presentations. This handles differing
nilpotent structures without identifying schemes. The complementary closed
immersion i : Z → T is proper because U is nonempty. The proved constructible
pullback theorem makes i^*M constructible. Open/closed recollement supplies exact
closed pushforward and the triangle j_!j^*M[0] → M[0] → i_*i^*M[0]. Its first
term is a piece (use the identity closed immersion); the exact functor and single
comparisons identify the third term with D(i_*) applied to MZ[0] in the ordinary
derived category. If T is empty all its module sheaves are zero, so the identity
immersions and rank-zero presentations give the first alternative. -/
theorem condensed_constructible_one_step
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E.val) T) M) :
    condensedConstructiblePiece T ℓ E ((DerivedCategory.singleFunctor _ 0).obj M) ∨
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      Exists fun [_hi : IsClosedImmersion i] ↦
      Exists fun [_hex : PreservesFiniteColimits
          (CondensedRing.lowerStar (Profinite.continuousMapRingObj E.val) i)] ↦
      ¬ Function.Surjective i ∧
      ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.val) Z)),
        IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj E.val) Z) MZ ∧
        ∃ (A : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (Profinite.continuousMapRingObj E.val) T)))
          (f : A ⟶ (DerivedCategory.singleFunctor _ 0).obj M)
          (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
            (CondensedRing.lowerStar
              (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ))
          (h : (CondensedRing.lowerStar
              (Profinite.continuousMapRingObj E.val) i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
            A⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧
          condensedConstructiblePiece T ℓ E A := by
  exact generic_constructible_one_step (Profinite.continuousMapRingObj E.val) T M hM

end AlgebraicGeometry.ProEtale
