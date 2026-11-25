/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # One open/closed step for a constructible condensed sheaf -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency true in
-- Recollement carries several nested exact-functor instance witnesses.
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
theorem condensed_locallyClosed_one_step
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
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
  classical
  let S := DerivedCategory.singleFunctor
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) 0
  have piece (U : Scheme.{u}) (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
      (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
      (hP : IsLocallyFinitelyPresented (condensedRingObj Λ U) P) :
      condensedLocallyClosedPiece Λ T (S.obj ((CondensedRing.openImmersionLowerShriek
        Λ j).obj P)) := by
    refine ⟨T, U, 𝟙 T, j, inferInstance, inferInstance, inferInstance, P, hP, ?_⟩
    exact ⟨S.mapIso ((profinitePointModuleDirectImageIdentity Λ T).app _).symm⟩
  rcases condensed_constructible_generic_lfp T Λ M hM with hlocal | ⟨U, hU, hlocal⟩
  · left
    let e : CondensedRing.openImmersionLowerShriek Λ (𝟙 T) ≅ 𝟭 _ :=
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 T)).ofNatIsoRight
        (profinitePointModuleIdentity Λ T)).leftAdjointUniq Adjunction.id
    rcases piece T (𝟙 T) M hlocal with ⟨Z, V, i, j, hi, hj, hqc, P, hP, ⟨eP⟩⟩
    exact ⟨Z, V, i, j, hi, hj, hqc, P, hP, ⟨S.mapIso (e.app M).symm ≪≫ eP⟩⟩
  · right
    have : TopologicalSpace.NoetherianSpace U.toScheme :=
      U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact U.ι := by
      exact ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
    let C : TopologicalSpace.Closeds T := ⟨(U : Set T)ᶜ, U.2.isClosed_compl⟩
    let I := Scheme.IdealSheafData.vanishingIdeal C
    let Z := I.subscheme
    let i : Z ⟶ T := I.subschemeι
    have hij : Set.range U.ι = (Set.range i)ᶜ := by
      rw [Scheme.Opens.range_ι]
      change (U : Set T) = (Set.range I.subschemeι)ᶜ
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      change (U : Set T) = ((U : Set T)ᶜ)ᶜ
      exact (compl_compl _).symm
    have hrecol := CondensedRing.condensed_open_closed_recollement Λ i U.ι hij
    let hex := hrecol.choose
    let : PreservesFiniteColimits (CondensedRing.lowerStar Λ i) := hex
    have hrec := hrecol.choose_spec
    have hsh := hrec.2.2.2.2.2.2.2.2.2.2.2.2
    obtain ⟨sh, hshadd, hshleft, ash, aj, bj, ai, bi, hjshift, hishift, htri⟩ := hsh
    -- Name the dependent existential before eliminating it: `obtain` on the projection
    -- first generalizes its type, losing the local exact-functor instance witnesses.
    have hconnect := htri.2.2.2.2.2.2.2.2.2.2.2.2
    obtain ⟨δ, ε, hδ, hε, htriangle, hrest⟩ := hconnect
    let MZ := (CondensedRing.upperStar Λ i).obj M
    have hMZ := CondensedRing.isConstructibleModuleObject_upperStar Λ i M hM
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj M
    let F := CondensedRing.openImmersionLowerShriek Λ U.ι
    let G := CondensedRing.upperStar Λ U.ι
    let H := CondensedRing.upperStar Λ i
    let J := CondensedRing.lowerStar Λ i
    let Tplus := Pretriangulated.Triangle.mk (aj.counit.app K)
      (ai.unit.app K) (δ.app K)
    let T' := DerivedCategory.Plus.ι.mapTriangle.obj Tplus
    have ht : T' ∈ distTriang _ := DerivedCategory.Plus.ι.map_distinguished _ (htriangle K)
    let A := S.obj (F.obj (G.obj M))
    let B := J.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj MZ)
    let e₁ : T'.obj₁ ≅ A :=
      DerivedCategory.Plus.ι.mapIso
        (F.mapDerivedCategoryPlus.mapIso ((G.mapDerivedCategoryPlusSingleFunctor 0).app M)
          ≪≫ (F.mapDerivedCategoryPlusSingleFunctor 0).app (G.obj M)) ≪≫
        (DerivedCategory.Plus.singleFunctorιIso _ 0).app (F.obj (G.obj M))
    let e₂ : T'.obj₂ ≅ S.obj M := (DerivedCategory.Plus.singleFunctorιIso _ 0).app M
    let e₃ : T'.obj₃ ≅ B :=
      DerivedCategory.Plus.ι.mapIso
        (J.mapDerivedCategoryPlus.mapIso ((H.mapDerivedCategoryPlusSingleFunctor 0).app M)) ≪≫
        (J.mapDerivedCategoryPlusCompatibility.app _ ) ≪≫
        J.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso _ 0).app MZ)
    let f := e₁.inv ≫ T'.mor₁ ≫ e₂.hom
    let g := e₂.inv ≫ T'.mor₂ ≫ e₃.hom
    let k := e₃.inv ≫ T'.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.hom
    have et : T' ≅ Pretriangulated.Triangle.mk f g k := by
      refine Pretriangulated.Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
      · change T'.mor₁ ≫ e₂.hom = e₁.hom ≫ (e₁.inv ≫ T'.mor₁ ≫ e₂.hom)
        rw [Iso.hom_inv_id_assoc]
      · change T'.mor₂ ≫ e₃.hom = e₂.hom ≫ (e₂.inv ≫ T'.mor₂ ≫ e₃.hom)
        rw [Iso.hom_inv_id_assoc]
      · change T'.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ (e₃.inv ≫ T'.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.hom)
        rw [Iso.hom_inv_id_assoc]
    refine ⟨Z, i, inferInstance, hex, ?_, MZ, hMZ, A, f, g, k, ?_, ?_⟩
    · intro hs
      obtain ⟨x, hx⟩ := hU
      obtain ⟨z, hz⟩ := hs x
      have hz' : x ∈ Set.range i := ⟨z, hz⟩
      have hx' : x ∈ (Set.range i)ᶜ := by rw [← hij, Scheme.Opens.range_ι]; exact hx
      exact hx' hz'
    · exact isomorphic_distinguished _ ht _ et.symm
    · exact piece U.toScheme U.ι _ hlocal

end AlgebraicGeometry.ProEtale
