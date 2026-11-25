/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension

/-!
# Distinguished triangle for canonical truncations

Source: literature/stacks-project/derived.tex, Remark 08J5 (line 4076)
(blueprint: theorem-pbc-injective-acyclicity).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace DerivedCategory

private lemma lift_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
    {F G : C ⥤ E} (hF : W.IsInvertedBy F) (hG : W.IsInvertedBy G)
    (τ : F ⟶ G) (K N : C) (f : L.obj K ⟶ L.obj N) :
    τ.app K ≫ ((Localization.fac G hG L).inv.app K ≫
      (Localization.lift G hG L).map f ≫ (Localization.fac G hG L).hom.app N) =
    ((Localization.fac F hF L).inv.app K ≫
      (Localization.lift F hF L).map f ≫ (Localization.fac F hF L).hom.app N) ≫
        τ.app N := by
  let τD := Localization.liftNatTrans L W F G
    (Localization.lift F hF L) (Localization.lift G hG L) τ
  have h := congrArg (fun t ↦ (Localization.fac F hF L).inv.app K ≫
    t ≫ (Localization.fac G hG L).hom.app N) (τD.naturality f)
  simpa [τD, Localization.liftNatTrans_app, Localization.fac, Category.assoc] using h.symm

private lemma truncation_i_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (q : ℤ)
    (i i' : K.truncLE (q - 1) ⟶ K.truncLE q)
    (hi : i ≫ K.ιTruncLE q = K.ιTruncLE (q - 1))
    (hi' : i' ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)) : i = i' := by
  have : Mono (K.ιTruncLE q) :=
    inferInstanceAs (Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE q)))
  apply (cancel_mono (K.ιTruncLE q)).1
  exact hi.trans hi'.symm

private lemma truncation_j_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (q : ℤ)
    (j j' : K.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (K.homology q))
    (hj : j.f q ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
        (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q)
    (hj' : j'.f q ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
        (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q) : j = j' := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom).1
  exact hj.trans hj'.symm

private lemma truncation_hom_subsingleton
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K L : CochainComplex A ℤ) (q : ℤ) :
    Subsingleton ((Q.obj (K.truncLE (q - 1)))⟦(1 : ℤ)⟧ ⟶
      Q.obj ((CochainComplex.singleFunctor A q).obj (L.homology q))) := by
  have : (Q.obj (K.truncLE (q - 1))).IsLE (q - 1) := inferInstance
  have : ((Q.obj (K.truncLE (q - 1)))⟦(1 : ℤ)⟧).IsLE (q - 2) :=
    TStructure.t.isLE_shift _ (q - 1) 1 (q - 2) (by omega)
  have : (Q.obj ((CochainComplex.singleFunctor A q).obj (L.homology q))).IsGE q :=
    inferInstance
  refine ⟨fun f g ↦ ?_⟩
  rw [TStructure.t.zero f (q - 2) q (by omega),
    TStructure.t.zero g (q - 2) q (by omega)]

private lemma truncation_strictlyGE
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (n r : ℤ) [K.IsStrictlyGE n] :
    (K.truncLE r).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have : Mono ((K.ιTruncLE r).f i) :=
    inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE r)).f i))
  exact IsZero.of_mono ((K.ιTruncLE r).f i) (K.isZero_of_isStrictlyGE n i hi)

private lemma truncation_isGE
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (n r : ℤ) [K.IsGE n] :
    (K.truncLE r).IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  by_cases hir : i ≤ r
  · have := K.quasiIsoAt_ιTruncLE r i hir
    exact (exactAt_iff_of_quasiIsoAt (K.ιTruncLE r) i).2
      (K.exactAt_of_isGE n i hi)
  · exact (K.truncLE r).exactAt_of_isLE r i (by omega)

/-- The canonical truncation triangle
tau_{<=q-1}K -> tau_{<=q}K -> H^q(K)[-q] -> (tau_{<=q-1}K)[1] of D(A).
The first two arrows are the canonical maps of complexes: the inclusion i_q
(characterized by its composite with the inclusion into K) and the map j_q whose
degree-q component is the quotient Ker d^q -> H^q(K). The connecting arrow k_q
exists and is unique; the triangle is functorial for every morphism of D(A), the
three truncation functors acting on D(A) through their descent along Q (the
localization lift; theorem-pbc-injective-acyclicity); and the three terms are
bounded below when K is (strictly, or in cohomology).
Source: Stacks Project, Remark 08J5; BBD, Proposition 1.1.9 and Corollaire 1.1.10 (ii)
(blueprint: theorem-pbc-injective-acyclicity).

Proof:
1. The short exact sequence 0 -> tau_{<=q-1}K -> tau_{<=q}K -> M_q(K) -> 0, with
   j_q factoring through a quasi-isomorphism M_q(K) -> H^q(K)[-q]
   (theorem-pbc-injective-acyclicity).
2. Its distinguished triangle in D(A) (lem-weil-pbc-complex-ses-triangle).
3. Transport along the quasi-isomorphism gives k_q (TR1).
4. Hom((tau_{<=q-1}K)[1], H^q(L)[-q]) = 0 (standard t-structure).
5. Uniqueness of k_q and 6. functoriality by lem-weil-pbc-triangle-morphism-extension.
7. Bounded below: cohomology of the canonical truncations. -/
theorem truncation_triangle (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (q : ℤ) :
    (∀ K : CochainComplex A ℤ,
      ∃ (i : K.truncLE (q - 1) ⟶ K.truncLE q)
        (j : K.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (K.homology q)),
        i ≫ K.ιTruncLE q = K.ιTruncLE (q - 1) ∧
        j.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q ∧
        ∃! k : Q.obj ((CochainComplex.singleFunctor A q).obj (K.homology q)) ⟶
            (Q.obj (K.truncLE (q - 1)))⟦(1 : ℤ)⟧,
          Triangle.mk (Q.map i) (Q.map j) k ∈ distTriang (DerivedCategory A)) ∧
    (∃ (h₀ : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
          ((ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⋙ Q))
        (h₁ : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
          ((ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ Q))
        (hH : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
          ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
            CochainComplex.singleFunctor A q) ⋙ Q)),
      ∀ (K L : CochainComplex A ℤ)
        (iK : K.truncLE (q - 1) ⟶ K.truncLE q)
        (jK : K.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (K.homology q))
        (iL : L.truncLE (q - 1) ⟶ L.truncLE q)
        (jL : L.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (L.homology q)),
        iK ≫ K.ιTruncLE q = K.ιTruncLE (q - 1) →
        jK.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q →
        iL ≫ L.ιTruncLE q = L.ιTruncLE (q - 1) →
        jL.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (L.homology q)).hom =
          (L.truncLEXIsoCycles q).hom ≫ L.homologyπ q →
        ∀ (kK : Q.obj ((CochainComplex.singleFunctor A q).obj (K.homology q)) ⟶
              (Q.obj (K.truncLE (q - 1)))⟦(1 : ℤ)⟧)
          (kL : Q.obj ((CochainComplex.singleFunctor A q).obj (L.homology q)) ⟶
              (Q.obj (L.truncLE (q - 1)))⟦(1 : ℤ)⟧),
          Triangle.mk (Q.map iK) (Q.map jK) kK ∈ distTriang (DerivedCategory A) →
          Triangle.mk (Q.map iL) (Q.map jL) kL ∈ distTriang (DerivedCategory A) →
          ∀ f : Q.obj K ⟶ Q.obj L,
            Q.map iK ≫
                ((Localization.fac _ h₁ Q).inv.app K ≫ (Localization.lift _ h₁ Q).map f ≫
                  (Localization.fac _ h₁ Q).hom.app L) =
              ((Localization.fac _ h₀ Q).inv.app K ≫ (Localization.lift _ h₀ Q).map f ≫
                  (Localization.fac _ h₀ Q).hom.app L) ≫ Q.map iL ∧
            Q.map jK ≫
                ((Localization.fac _ hH Q).inv.app K ≫ (Localization.lift _ hH Q).map f ≫
                  (Localization.fac _ hH Q).hom.app L) =
              ((Localization.fac _ h₁ Q).inv.app K ≫ (Localization.lift _ h₁ Q).map f ≫
                  (Localization.fac _ h₁ Q).hom.app L) ≫ Q.map jL ∧
            kK ≫ ((Localization.fac _ h₀ Q).inv.app K ≫ (Localization.lift _ h₀ Q).map f ≫
                  (Localization.fac _ h₀ Q).hom.app L)⟦(1 : ℤ)⟧' =
              ((Localization.fac _ hH Q).inv.app K ≫ (Localization.lift _ hH Q).map f ≫
                  (Localization.fac _ hH Q).hom.app L) ≫ kL) ∧
    (∀ (K : CochainComplex A ℤ) (n : ℤ),
      (K.IsStrictlyGE n →
        (K.truncLE (q - 1)).IsStrictlyGE n ∧ (K.truncLE q).IsStrictlyGE n ∧
          ((CochainComplex.singleFunctor A q).obj (K.homology q)).IsStrictlyGE (min n q)) ∧
      (K.IsGE n →
        (K.truncLE (q - 1)).IsGE n ∧ (K.truncLE q).IsGE n ∧
          ((CochainComplex.singleFunctor A q).obj (K.homology q)).IsGE (min n q))) := by
  obtain ⟨i, j, barj, hi, hses, _, _, hj, hnat⟩ :=
    CochainComplex.exists_upperTruncationStepSES (C := A)
  refine ⟨?_, ?_, ?_⟩
  · intro K
    have hb := (hj K q).2.2.2.2.2
    have : QuasiIso (barj K q) := hb
    let δ := triangleOfSESδ (hses K q)
    let k := inv (Q.map (barj K q)) ≫ δ
    have hd : Triangle.mk (Q.map (i K q)) (Q.map (j K q)) k ∈
        distTriang (DerivedCategory A) := by
      apply isomorphic_distinguished _ (triangleOfSES_distinguished (hses K q))
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (asIso (Q.map (barj K q))).symm ?_ ?_ ?_
      · simp [triangleOfSES]
      · dsimp [triangleOfSES]
        rw [(hj K q).2.2.1, Functor.map_comp]
        simp
      · dsimp [triangleOfSES, k, δ]
        simp
    refine ⟨i K q, j K q, hi K q, (hj K q).1, k, hd, ?_⟩
    intro x hx
    exact (triangle_morphism_extension _ _ hd hd (𝟙 _)).2.2
      (truncation_hom_subsingleton A K K q) x hx
  · let F₀ := (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⋙ Q
    let F₁ := (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ Q
    let FH := (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
      CochainComplex.singleFunctor A q) ⋙ Q
    let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
    have h₀ : W.IsInvertedBy F₀ := by
      intro K L s hs
      have : QuasiIso s := hs
      apply (isIso_Q_map_iff_quasiIso A _).2
      exact (CochainComplex.quasiIso_truncLEMap_iff s (q - 1)).2
        (fun _ _ ↦ inferInstance)
    have h₁ : W.IsInvertedBy F₁ := by
      intro K L s hs
      have : QuasiIso s := hs
      apply (isIso_Q_map_iff_quasiIso A _).2
      exact (CochainComplex.quasiIso_truncLEMap_iff s q).2
        (fun _ _ ↦ inferInstance)
    have hH : W.IsInvertedBy FH := by
      intro K L s hs
      have : QuasiIso s := hs
      apply (isIso_Q_map_iff_quasiIso A _).2
      change QuasiIso ((CochainComplex.singleFunctor A q).map
        (HomologicalComplex.homologyMap s q))
      infer_instance
    refine ⟨h₀, h₁, hH, ?_⟩
    let iNat : (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⟶
        (ComplexShape.embeddingUpIntLE q).truncLEFunctor A :=
      { app := fun K ↦ i K q
        naturality := fun _ _ f ↦ (hnat f q).1 }
    let jNat : (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⟶
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
          CochainComplex.singleFunctor A q :=
      { app := fun K ↦ j K q
        naturality := by
          intro K L f
          obtain ⟨g, hg, hb⟩ := (hnat f q).2
          change CochainComplex.truncLEMap f q ≫ j L q =
            j K q ≫ (CochainComplex.singleFunctor A q).map
              (HomologicalComplex.homologyMap f q)
          rw [(hj L q).2.2.1, (hj K q).2.2.1, ← Category.assoc, hg,
            Category.assoc, ← hb, Category.assoc] }
    intro K L iK jK iL jL hiK hjK hiL hjL kK kL hdK hdL f
    let a := (Localization.fac F₀ h₀ Q).inv.app K ≫
      (Localization.lift F₀ h₀ Q).map f ≫ (Localization.fac F₀ h₀ Q).hom.app L
    let b := (Localization.fac F₁ h₁ Q).inv.app K ≫
      (Localization.lift F₁ h₁ Q).map f ≫ (Localization.fac F₁ h₁ Q).hom.app L
    let c := (Localization.fac FH hH Q).inv.app K ≫
      (Localization.lift FH hH Q).map f ≫ (Localization.fac FH hH Q).hom.app L
    have hab : Q.map iK ≫ b = a ≫ Q.map iL := by
      rw [truncation_i_unique K q iK (iNat.app K) hiK (hi K q),
        truncation_i_unique L q iL (iNat.app L) hiL (hi L q)]
      exact lift_naturality W Q h₀ h₁ (Functor.whiskerRight iNat Q) K L f
    have hbc : Q.map jK ≫ c = b ≫ Q.map jL := by
      rw [truncation_j_unique K q jK (jNat.app K) hjK (hj K q).1,
        truncation_j_unique L q jL (jNat.app L) hjL (hj L q).1]
      exact lift_naturality W Q h₁ hH (Functor.whiskerRight jNat Q) K L f
    refine ⟨hab, hbc, ?_⟩
    obtain ⟨τ, _, _, _, hτ⟩ :=
      ((triangle_morphism_extension _ _ hdK hdL b).2.1
        (truncation_hom_subsingleton A K L q)).2.2 a c hab.symm hbc
    exact hτ
  · intro K n
    constructor
    · intro h
      have := h
      have : ((CochainComplex.singleFunctor A q).obj (K.homology q)).IsStrictlyGE
          (min n q) := CochainComplex.isStrictlyGE_of_ge _ (min n q) q (min_le_right _ _)
      exact ⟨truncation_strictlyGE K n (q - 1), truncation_strictlyGE K n q,
        inferInstance⟩
    · intro h
      have := h
      have : ((CochainComplex.singleFunctor A q).obj (K.homology q)).IsStrictlyGE
          (min n q) := CochainComplex.isStrictlyGE_of_ge _ (min n q) q (min_le_right _ _)
      exact ⟨truncation_isGE K n (q - 1), truncation_isGE K n q, inferInstance⟩

end DerivedCategory
