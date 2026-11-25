/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Totalizing an augmented CE comparison

Source: Stacks Project, Derived Categories, Tags 015J and 015K.
(blueprint: lem-weil-pbc-ce-totalize-augmented-comparison).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- A map preserving each generating image preserves their finite supremum.
private theorem factors_finset_sup {C : Type*} [Category C] [Abelian C]
    {I : Type*} (s : Finset I) {A : I → C} {X Y : C}
    (a : ∀ i, A i ⟶ X) (d : X ⟶ Y) (Q : Subobject Y)
    (h : ∀ i ∈ s, Q.Factors (a i ≫ d)) :
    Q.Factors ((s.sup (fun i ↦ imageSubobject (a i))).arrow ≫ d) := by
  let P := (Subobject.pullback d).obj Q
  have hs : s.sup (fun i ↦ imageSubobject (a i)) ≤ P := by
    apply Finset.sup_le
    intro i hi
    have hf := pullback_factors d Q (a i) (h i hi)
    exact imageSubobject_le (a i) (P.factorThru (a i) hf)
      (Subobject.factorThru_arrow _ _ _)
  apply (pullback_factors_iff d Q _).1
  exact Subobject.factors_of_le _ hs (Subobject.factors_self _)

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the sections comparisons and their dependent summand equations together.
-- The summand equation is essential: an arbitrary map of totals need not preserve this
-- filtration. The components constructed below are unique by the target monomorphisms.
private theorem etaleCE_filtration_restrictions
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    {L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (D' : EtaleTermwiseHypercohomology Y L)
    (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) :
    let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
    ∀ q : ℤ, ∃ s : (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
      (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
      s ≫ (D'.L.step q).arrow = (D.L.step q).arrow ≫ b := by
  classical
  let ΓX := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let ΓY := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor ΓX).obj D.I).flip
  let J' := ((CartanEilenbergPresentation.mappedFunctor ΓY).obj D'.I).flip
  let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
  have hgen (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n) :
      ∃ a : (J.X (m : ℤ)).X q ⟶ (J'.X (m : ℤ)).X q,
        J.ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h ≫ b.f n =
          a ≫ J'.ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h := by
    let ex := HomologicalComplex.extendXIso
      ((ΓX.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X q))
      ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl
    let ey := HomologicalComplex.extendXIso
      ((ΓY.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D'.I.X q))
      ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl
    let α := (HomologicalComplex.extendXIso
      (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q))
      ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor
        (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
          D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h
    let β := (HomologicalComplex.extendXIso
      (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D'.I.X q))
      ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor
        (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
          D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h
    refine ⟨ex.hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f
      ((D.I.X q).X m) ≫ ΓY.map ((φ.f q).f m) ≫ ey.inv, ?_⟩
    have hy : ΓY.map β ≫ D'.totalSectionsIso.inv.f n =
        ey.inv ≫ J'.ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h := by
      apply (cancel_mono (D'.totalSectionsIso.hom.f n)).1
      rw [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id]
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Category.assoc, D'.totalSectionsIso_formula m q n h]
      change _ = ey.inv ≫ ey.hom ≫ ΓY.map β
      rw [Iso.inv_hom_id_assoc]
    change _ ≫ (D.totalSectionsIso.hom.f n ≫
      (ceSectionsLift f u).f n ≫ D'.totalSectionsIso.inv.f n) = _
    rw [← Category.assoc, D.totalSectionsIso_formula m q n h]
    change (ex.hom ≫ ΓX.map α) ≫
      (globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (D.sheafTotal.X n) ≫
        ΓY.map (u.f n) ≫ D'.totalSectionsIso.inv.f n) = _
    have hn := (ceSectionsUnit f).naturality α
    change ΓX.map α ≫
        globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f (D.sheafTotal.X n) =
      globalSectionsUpperStarMap AddCommGrpCat.{uNatural + 1} f ((D.I.X q).X m) ≫
        ΓY.map ((upperStar AddCommGrpCat.{uNatural + 1} f).map α) at hn
    simp only [Category.assoc]
    rw [← Category.assoc (ΓX.map α), hn]
    simp only [Category.assoc]
    rw [← ΓY.map_comp_assoc]
    have hh : (upperStar AddCommGrpCat.{uNatural + 1} f).map α ≫ u.f n =
        (φ.f q).f m ≫ β := hu m q n h
    rw [hh]
    rw [ΓY.map_comp]
    simp only [Category.assoc]
    rw [hy]
  dsimp only
  intro p
  have hp (n : ℤ) : (D'.L.complexStep p n).Factors
      ((D.L.complexStep p n).arrow ≫ b.f n) := by
    rw [D.filtration_formula p n, D'.filtration_formula p n]
    change ((J'.secondFiltration n).step p).Factors
      (((J.secondFiltration n).step p).arrow ≫ b.f n)
    dsimp [HomologicalComplex₂.secondFiltration]
    apply factors_finset_sup (Finset.Icc p n)
      (fun i ↦ J.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) _ _
    intro i hi
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n - i by omega)
    have h : (m : ℤ) + i = n := by omega
    rw [hm, J.ιTotalOrZero_eq (ComplexShape.up ℤ) (m : ℤ) i n h]
    obtain ⟨a, ha⟩ := hgen m i n h
    rw [ha]
    apply Subobject.factors_of_factors_right
    apply Subobject.factors_of_le
      (P := imageSubobject (J'.ιTotal (ComplexShape.up ℤ) (m : ℤ) i n h))
      (J'.ιTotal (ComplexShape.up ℤ) (m : ℤ) i n h)
    · have hh := Finset.le_sup
        (f := fun k ↦ imageSubobject
          (J'.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hi
      have he : imageSubobject (J'.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) =
          imageSubobject (J'.ιTotal (ComplexShape.up ℤ) (m : ℤ) i n h) := by
        rw [hm, J'.ιTotalOrZero_eq (ComplexShape.up ℤ) (m : ℤ) i n h]
      exact (le_of_eq he.symm).trans hh
    · simpa using imageSubobject_factors_comp_self
        (J'.ιTotal (ComplexShape.up ℤ) (m : ℤ) i n h) (𝟙 _)
  have hc (n : ℤ) : ∃ a : (D.L.step p : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X n ⟶
      (D'.L.step p : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X n,
      a ≫ (D'.L.step p).arrow.f n = (D.L.step p).arrow.f n ≫ b.f n := by
    have hh := Subobject.factors_of_factors_right
      (factorThruImageSubobject ((D.L.step p).arrow.f n)) (hp n)
    simp only [DecreasingFiltration.complexStep, ← Category.assoc,
      imageSubobject_arrow_comp] at hh
    rw [imageSubobject_mono, Subobject.mk_factors_iff] at hh
    exact hh
  let s : (D.L.step p : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
      (D'.L.step p : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) :=
    { f := fun n ↦ (hc n).choose
      comm' := by
        intro n k hnk
        apply (cancel_mono ((D'.L.step p).arrow.f k)).1
        rw [Category.assoc, ← (D'.L.step p).arrow.comm n k,
          ← Category.assoc, (hc n).choose_spec, Category.assoc,
          b.comm n k, ← Category.assoc, (D.L.step p).arrow.comm n k]
        simp only [Category.assoc]
        rw [(hc k).choose_spec] }
  refine ⟨s, ?_⟩
  apply HomologicalComplex.hom_f_injective
  funext n
  exact (hc n).choose_spec

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent CE totals and representative equations together.
/-- Totalize a supplied augmented bicomplex map, retaining its summand equations.
This theorem constructs no pages and makes no choice of CE resolutions.
Source: Stacks Project, Tag 015J, finite-diagonal total comparison; Tag 015K.
(blueprint: lem-weil-pbc-ce-totalize-augmented-comparison).

Proof. Apply the finite-diagonal comparison for upperStar to the source bicomplex.
Invert this comparison, then extend φ by zero, flip and totalize it. On a nonnegative
resolution summand the extension comparison and the total-map coprojection equation
give the displayed formula. In negative resolution degree both sides vanish.
In resolution degree zero, substitute this formula into D.aug_formula. The equation
hφ identifies the result with v followed by D'.aug_formula, proving the strict square.
Conjugate the sections map by the two totalSectionsIso maps. Their coprojection
formulas and naturality of globalSectionsUpperStarMap show that this map carries the
summand of complex degree q to the target summand of degree q. Each source generating
image therefore factors through the corresponding target filtration step. Taking
the finite supremum gives degreewise restrictions. Cancel the target step inclusions
in the chain-map equation for b to prove that the restrictions commute with the
differentials; they assemble to s. This argument also covers empty diagonals. -/
theorem etaleCE_totalize_augmented_comparison
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
    (D : EtaleTermwiseHypercohomology X K) (D' : EtaleTermwiseHypercohomology Y L)
    (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0) :
    ∃ u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal,
      ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map D.aug ≫ u = v ≫ D'.aug ∧
      (∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ∧
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      (∀ q : ℤ, ∃ s : (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
          (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
        s ≫ (D'.L.step q).arrow = (D.L.step q).arrow ≫ b) := by
  classical
  let F := upperStar AddCommGrpCat.{uNatural + 1} f
  obtain ⟨e, he⟩ := Functor.cartanEilenberg_mapped_total_iso F D.I D.below
  let ψ := ((ComplexShape.embeddingUpNat.extendFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ
  let t := HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map ψ) (ComplexShape.up ℤ)
  let u := e.inv ≫ t
  have hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h := by
    intro m q n h
    dsimp [u]
    change F.map _ ≫ e.inv.f n ≫ t.f n = _
    have hh := he m q n h
    have hi : F.map
        ((HomologicalComplex.extendXIso
          (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (D.I.X q))
          ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
          (((CartanEilenbergPresentation.mappedFunctor
            (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
              D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ e.inv.f n =
        (HomologicalComplex.extendXIso
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X q))
          ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj D.I).flip).ιTotal
          (ComplexShape.up ℤ) (m : ℤ) q n h := by
      apply (cancel_mono (e.hom.f n)).1
      rw [Category.assoc, ← HomologicalComplex.comp_f, e.inv_hom_id]
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Category.assoc, hh, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hi, Category.assoc]
    dsimp [t]
    rw [HomologicalComplex₂.ιTotal_map]
    change _ ≫ (HomologicalComplex.extendMap (φ.f q)
      ComplexShape.embeddingUpNat).f (m : ℤ) ≫ _ = _
    rw [HomologicalComplex.extendMap_f (φ.f q) ComplexShape.embeddingUpNat
      (i := m) (i' := (m : ℤ)) rfl]
    simp only [Category.assoc]
    change (HomologicalComplex.extendXIso
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X q))
      ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
      (HomologicalComplex.extendXIso
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X q))
        ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
    rfl
  refine ⟨u, ?_, hu, ?_⟩
  · apply HomologicalComplex.hom_f_injective
    funext n
    change F.map (D.aug.f n) ≫ u.f n = v.f n ≫ D'.aug.f n
    rw [D.aug_formula n, D'.aug_formula n, F.map_comp]
    rw [Category.assoc]
    erw [hu 0 n n (zero_add n)]
    have hn := hφ n
    have hs (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) :
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv = 𝟙 A := by
      rfl
    have hs' (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) :
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv = 𝟙 A := by
      rfl
    simp only [hs, hs', Category.id_comp] at hn
    rw [← Category.assoc]
    erw [hn]
    simp only [Category.assoc]
    rfl
  · exact etaleCE_filtration_restrictions f D D' φ u hu

end AlgebraicGeometry.Etale
