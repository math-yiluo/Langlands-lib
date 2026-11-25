/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.DerivedExchangeBoundedComparison
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! Transport of the exchange formula to arbitrary K-injective representatives. -/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- The bounded comparison formula implies the formula for arbitrary K-injective
representatives of a bounded below derived object.
Source: Stacks Project, sites-cohomology.tex, Lemma 0736 and Remark 07A7;
derived.tex, Lemmas 070I and 070K; step 7 of the explicit comparison
in prose-04-06.

Proof: choose P from injectiveObjectEquivalence, a bounded below complex of
injectives representing K. The comparison h from I to P is invertible in the
homotopy category: lift the inverse of its localized isomorphism by the
K-injective Hom bijection and use injectivity to verify the inverse identities.
Represent a homotopy inverse by a complex map v from P to I. Precompose j with
g'^* v to obtain j_P. This is a quasi-isomorphism since termwise inverse image
preserves homotopies and v is a homotopy equivalence. Apply the assumed bounded
formula to P, its canonical resolution isomorphism and j_P. Naturality of the
underived exchange shows e_P composed with g^* f_* h equals e in the homotopy
category, since v h is homotopic to the identity. Naturality of the exact
inverse-image comparison gives the same equality for source comparisons.
The target resolution isomorphism is unchanged: its expression for P becomes
t after cancelling h v under localization. Uniqueness of the K-injective
comparison to P' therefore gives the same target comparison. Precompose the
bounded equation with Q(g^* f_* h) and substitute these three equalities.
(blueprint: lem-weil-pbc-derived-exchange-unbounded-transport). -/
lemma derivedExchangeUnboundedTransport
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective]
    (s : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))
    (J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [J.IsKInjective]
    (j : (((g')^*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j]
    (bounded : ∀
    (I₀ : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [I₀.IsKInjective]
    (s₀ : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I₀))
    (j₀ : (((g')^*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).obj I₀ ⟶ J)
    [QuasiIso j₀]
    (n : ℤ) [I₀.IsStrictlyGE n],
    let B := AddCommGrpCat.{u + 1}
    let C := Sheaf X.smallEtaleTopology B
    let C' := Sheaf X'.smallEtaleTopology B
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient C' (.up ℤ)
    let qY := HomotopyCategory.quotient (Sheaf Y'.smallEtaleTopology B) (.up ℤ)
    let F := (f)_*[B]
    let F' := (f')_*[B]
    let G := (g)^*[B]
    let G' := (g')^*[B]
    let E := DerivedCategory.Plus.injectiveObjectEquivalence C
    let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
    let K' := G'.mapDerivedCategoryPlus.obj K
    let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
    let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
    let ρ := DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)
    let ρ' := DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')
    let t := G'.mapDerivedCategory.map s₀.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I₀) ≫
      DerivedCategory.Qh.map (q'.map j₀)
    let ex₀ := (NatTrans.mapHomologicalComplex
      (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)).app I₀
    let e := ex₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j₀
    ∀ h : ((q.obj I₀ ⟶ P.obj) × (q'.obj J ⟶ P'.obj)),
      s₀.hom ≫ DerivedCategory.Qh.map h.1 = ρ →
      t ≫ DerivedCategory.Qh.map h.2 = ρ' →
      let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P ≫
          F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
        DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app P' ≫
          F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      let σsrc := G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I₀)) ≫ G.mapDerivedCategory.map χ
      σsrc ≫ DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ' ) :
    let B := AddCommGrpCat.{u + 1}
    let C := Sheaf X.smallEtaleTopology B
    let C' := Sheaf X'.smallEtaleTopology B
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient C' (.up ℤ)
    let qY := HomotopyCategory.quotient (Sheaf Y'.smallEtaleTopology B) (.up ℤ)
    let F := (f)_*[B]
    let F' := (f')_*[B]
    let G := (g)^*[B]
    let G' := (g')^*[B]
    let E := DerivedCategory.Plus.injectiveObjectEquivalence C
    let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
    let K' := G'.mapDerivedCategoryPlus.obj K
    let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
    let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
    let ρ := DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)
    let ρ' := DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')
    let t := G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
      DerivedCategory.Qh.map (q'.map j)
    let ex₀ := (NatTrans.mapHomologicalComplex
      (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)).app I
    let e := ex₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j
    ∀ h : ((q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj)),
      s.hom ≫ DerivedCategory.Qh.map h.1 = ρ →
      t ≫ DerivedCategory.Qh.map h.2 = ρ' →
      let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P ≫
          F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
        DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app P' ≫
          F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      let σsrc := G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫ G.mapDerivedCategory.map χ
      σsrc ≫ DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ'  := by
  let B := AddCommGrpCat.{u + 1}
  let C := Sheaf X.smallEtaleTopology B
  let C' := Sheaf X'.smallEtaleTopology B
  let q := HomotopyCategory.quotient C (.up ℤ)
  let q' := HomotopyCategory.quotient C' (.up ℤ)
  let qY := HomotopyCategory.quotient (Sheaf Y'.smallEtaleTopology B) (.up ℤ)
  let F := (f)_*[B]
  let F' := (f')_*[B]
  let G := (g)^*[B]
  let G' := (g')^*[B]
  let E := DerivedCategory.Plus.injectiveObjectEquivalence C
  let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
  let K' := G'.mapDerivedCategoryPlus.obj K
  let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
  let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
  let I₀ : CochainComplex C ℤ := P.obj.as
  let s₀ : DerivedCategory.Plus.ι.obj K ≅ DerivedCategory.Qh.obj (q.obj I₀) :=
    DerivedCategory.Plus.ι.mapIso (E.counitIso.symm.app K)
  have : I₀.IsKInjective := by
    dsimp only [I₀, P]
    infer_instance
  obtain ⟨n, hn⟩ : CochainComplex.plus C I₀ := by
    apply (HomotopyCategory.plus_quotient_obj_iff I₀).mp
    change HomotopyCategory.plus C (q.obj I₀)
    exact P.property
  have := hn
  obtain ⟨aₕ, haₕ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective P.obj I).2
    (s₀.inv ≫ s.hom)
  obtain ⟨a, haq⟩ : ∃ a : I₀ ⟶ I, q.map a = aₕ := q.map_surjective aₕ
  rw [← haq] at haₕ
  have ha : s₀.hom ≫ DerivedCategory.Qh.map (q.map a) = s.hom := by
    rw [haₕ]
    simp
  have : IsIso (DerivedCategory.Qh.map (q.map a)) := by
    rw [haₕ]
    infer_instance
  have : QuasiIso a := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    have hi := (DerivedCategory.quotientCompQhIso C).hom.naturality a
    dsimp only [Functor.comp_map] at hi
    have : IsIso ((DerivedCategory.quotientCompQhIso C).hom.app I₀ ≫
        DerivedCategory.Q.map a) := by
      rw [← hi]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.quotientCompQhIso C).hom.app I₀) (DerivedCategory.Q.map a)
  have : IsIso (q.map a) := by
    have he := (CochainComplex.IsKInjective.quasiIso_iff a).mp inferInstance
    rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
      MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at he
    exact he
  let j₀ := (G'.mapHomologicalComplex (.up ℤ)).map a ≫ j
  have : QuasiIso j₀ := inferInstance
  dsimp only
  intro h hh₁ hh₂
  let h₀ := (q.map a ≫ h.1, h.2)
  have hh₀₁ : s₀.hom ≫ DerivedCategory.Qh.map h₀.1 =
      DerivedCategory.Plus.ι.map (E.counitIso.inv.app K) := by
    simpa only [h₀, Functor.map_comp, ← assoc, ha] using hh₁
  have ht : G'.mapDerivedCategory.map s₀.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I₀) ≫
      DerivedCategory.Qh.map (q'.map j₀) =
      G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
      DerivedCategory.Qh.map (q'.map j) := by
    dsimp only [j₀]
    rw [q'.map_comp, DerivedCategory.Qh.map_comp]
    change G'.mapDerivedCategory.map s₀.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I₀) ≫
      DerivedCategory.Qh.map ((G'.mapHomotopyCategory (.up ℤ)).map (q.map a)) ≫
      DerivedCategory.Qh.map (q'.map j) = _
    have ht := G'.mapDerivedCategoryFactorsh.hom.naturality (q.map a)
    dsimp only [Functor.comp_map] at ht
    rw [← reassoc_of% ht]
    simp only [← Functor.map_comp, ← assoc, ha]
  have hh₀₂ : (G'.mapDerivedCategory.map s₀.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I₀) ≫
      DerivedCategory.Qh.map (q'.map j₀)) ≫ DerivedCategory.Qh.map h₀.2 =
      DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K') := by
    rw [ht]
    exact hh₂
  have hb := bounded I₀ s₀ j₀ n h₀ hh₀₁ hh₀₂
  let U := DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app P ≫
    F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
  let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫ U
  let χ₀ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h₀.1) ≫ U
  let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
    DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnith.app P' ≫
      F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
  let σ := G.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫ G.mapDerivedCategory.map χ
  let σ₀ := G.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I₀)) ≫ G.mapDerivedCategory.map χ₀
  let ex := NatTrans.mapHomologicalComplex (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)
  let e := ex.app I ≫ (F'.mapHomologicalComplex (.up ℤ)).map j
  let e₀ := ex.app I₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j₀
  let b := (G.mapHomologicalComplex (.up ℤ)).map
    ((F.mapHomologicalComplex (.up ℤ)).map a)
  have hbiso : IsIso (qY.map b) := by
    change IsIso ((G.mapHomotopyCategory (.up ℤ)).map
      ((F.mapHomotopyCategory (.up ℤ)).map (q.map a)))
    infer_instance
  have he : b ≫ e = e₀ := by
    dsimp only [b, e, e₀, j₀]
    change ((((F ⋙ G).mapHomologicalComplex (.up ℤ)).map a ≫ ex.app I) ≫
      (F'.mapHomologicalComplex (.up ℤ)).map j) = _
    rw [ex.naturality]
    simp only [assoc, Functor.map_comp]
    rfl
  have hχ : χ₀ = DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (q.map a)) ≫ χ := by
    simp only [χ₀, χ, h₀, Functor.map_comp, assoc]
  have hσ : DerivedCategory.Qh.map (qY.map b) ≫ σ = σ₀ := by
    change DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map
        ((F.mapHomotopyCategory (.up ℤ)).map (q.map a))) ≫
      (G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫
        G.mapDerivedCategory.map χ) =
      G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I₀)) ≫ G.mapDerivedCategory.map χ₀
    rw [hχ]
    rw [Functor.map_comp]
    have hs := G.mapDerivedCategoryFactorsh.inv.naturality
      ((F.mapHomotopyCategory (.up ℤ)).map (q.map a))
    dsimp only [Functor.comp_map] at hs
    change DerivedCategory.Qh.map
      ((G.mapHomotopyCategory (.up ℤ)).map
        ((F.mapHomotopyCategory (.up ℤ)).map (q.map a))) ≫ _ = _
    rw [← assoc, hs, assoc]
    simp only [χ, Functor.map_comp]
  change σ ≫ DerivedCategory.Plus.ι.map
    ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
    DerivedCategory.Qh.map (qY.map e) ≫ χ'
  change σ₀ ≫ DerivedCategory.Plus.ι.map
    ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
    DerivedCategory.Qh.map (qY.map e₀) ≫ χ' at hb
  have hQe : DerivedCategory.Qh.map (qY.map b) ≫ DerivedCategory.Qh.map (qY.map e) =
      DerivedCategory.Qh.map (qY.map e₀) := by
    rw [← DerivedCategory.Qh.map_comp, ← qY.map_comp, he]
  apply (cancel_epi (DerivedCategory.Qh.map (qY.map b))).1
  rw [← assoc, hσ, hb, ← hQe, assoc]

end AlgebraicGeometry
