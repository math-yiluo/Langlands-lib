/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCEStationaryPageNaturality
public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.AlgebraicGeometry.EtaleCENormalizedRepresentativeCohomology
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover

/-! # Prescribed normalized CE pages and their first-page computation

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-prescribed-normalized-first-pages).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem firstPage_descend
    {C : Type*} [Category C] [Abelian C]
    (T T' : CochainComplex C ℤ) (F : DecreasingFiltration T) (F' : DecreasingFiltration T')
    (b : T ⟶ T')
    (hb : ∀ q : ℤ, ∃ s : (F.step q : CochainComplex C ℤ) ⟶
        (F'.step q : CochainComplex C ℤ), s ≫ (F'.step q).arrow = (F.step q).arrow ≫ b)
    (p q : ℤ) {S S' V V' : C}
    (α : S ≅ filteredComplexPageObject T F 1 (q, p))
    (β : S' ≅ filteredComplexPageObject T' F' 1 (q, p))
    (M : S ⟶ S') (k : S ⟶ V) (k' : S' ⟶ V') (c : V ⟶ V')
    (hM : ∀ (A : C)
      (x : A ⟶ (F.step q : CochainComplex C ℤ).X (q + p))
      (y : A ⟶ (F'.step q : CochainComplex C ℤ).X (q + p))
      (z : A ⟶ (F.complexCycles q (q + p) 1 : C))
      (z' : A ⟶ (F'.complexCycles q (q + p) 1 : C)),
      x ≫ (F.step q).arrow.f (q + p) ≫ b.f (q + p) = y ≫ (F'.step q).arrow.f (q + p) →
      z ≫ (F.complexCycles q (q + p) 1).arrow =
        x ≫ (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
      z' ≫ (F'.complexCycles q (q + p) 1).arrow =
        y ≫ (F'.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
      z ≫ filteredComplexPageπ T F 1 (q, p) ≫ α.inv ≫ M =
        z' ≫ filteredComplexPageπ T' F' 1 (q, p) ≫ β.inv)
    (hc : ∀ (A : C)
      (x : A ⟶ (F.step q : CochainComplex C ℤ).X (q + p))
      (y : A ⟶ (F'.step q : CochainComplex C ℤ).X (q + p))
      (z : A ⟶ (F.complexCycles q (q + p) 1 : C))
      (z' : A ⟶ (F'.complexCycles q (q + p) 1 : C)),
      x ≫ (F.step q).arrow.f (q + p) ≫ b.f (q + p) = y ≫ (F'.step q).arrow.f (q + p) →
      z ≫ (F.complexCycles q (q + p) 1).arrow =
        x ≫ (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
      z' ≫ (F'.complexCycles q (q + p) 1).arrow =
        y ≫ (F'.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
      z ≫ filteredComplexPageπ T F 1 (q, p) ≫ α.inv ≫ k ≫ c =
        z' ≫ filteredComplexPageπ T' F' 1 (q, p) ≫ β.inv ≫ k') :
    M ≫ k' = k ≫ c := by
  classical
  choose s hs using hb
  have hcover := filteredComplex_differential_representatives_cover T F 1
      (q, p) (q + 1, p) (by ext <;> simp)
  dsimp only [Prod.fst, Prod.snd] at hcover
  rw [add_right_comm q 1 p] at hcover
  obtain ⟨A, x, w, z, zw, hepi, hxw, hz, hzw⟩ := hcover
  let n := q + p
  have : Epi z := hepi
  have : Epi (filteredComplexPageπ T F 1 (q, p)) := by
    unfold filteredComplexPageπ
    infer_instance
  let y := x ≫ (s q).f (q + p)
  have hsi : (s q).f (q + p) ≫ (F'.step q).arrow.f (q + p) =
      (F.step q).arrow.f (q + p) ≫ b.f (q + p) := by
    exact congrArg (fun α ↦ α.f (q + p)) (hs q)
  have hxy : x ≫ (F.step q).arrow.f (q + p) ≫ b.f (q + p) =
      y ≫ (F'.step q).arrow.f (q + p) := by
    simp only [y, Category.assoc, hsi]
  have hsi' (k l : ℤ) : (s k).f l ≫ (F'.step k).arrow.f l =
      (F.step k).arrow.f l ≫ b.f l := by
    exact congrArg (fun α ↦ α.f l) (hs k)
  have hdy : (y ≫ (F'.step q).arrow.f n) ≫ T'.d n (n + 1) =
      (w ≫ (s (q + 1)).f (n + 1)) ≫ (F'.step (q + 1)).arrow.f (n + 1) := by
    calc
      _ = (x ≫ (F.step q).arrow.f n ≫ b.f n) ≫ T'.d n (n + 1) :=
        congrArg (fun t ↦ t ≫ T'.d n (n + 1)) hxy.symm
      _ = (x ≫ (F.step q).arrow.f n ≫ T.d n (n + 1)) ≫ b.f (n + 1) := by
        simp only [Category.assoc, b.comm]
      _ = (w ≫ (F.step (q + 1)).arrow.f (n + 1)) ≫ b.f (n + 1) :=
        congrArg (fun t ↦ t ≫ b.f (n + 1)) hxw
      _ = _ := by simp only [Category.assoc, hsi']
  let R := F'.complexStep q n ⊓
    (Subobject.pullback (T'.d n (n + 1))).obj
      (F'.complexStep (q + 1) (n + 1))
  let f' := (F'.step q).arrow.f n
  let g' := (F'.complexQuotientπ q (q + 1) (by omega)).f n
  have hyR : R.Factors (y ≫ f') := by
    apply (Subobject.inf_factors _).mpr
    constructor
    · exact imageSubobject_factors_comp_self _ _
    · apply (pullback_factors_iff _ _ _).mpr
      rw [hdy]
      exact imageSubobject_factors_comp_self _ _
  let W := (Subobject.pullback f').obj (R ⊔ F'.complexStep (q + 1) n)
  have hyW : W.Factors y := (pullback_factors_iff _ _ _).mpr
    (Subobject.sup_factors_of_factors_left hyR)
  let z' := Subobject.factorThru W y hyW ≫ (Subobject.imageFactorisation g' W).F.e
  have hz' : z' ≫ (F'.complexCycles q (q + p) 1).arrow =
      y ≫ (F'.complexQuotientπ q (q + 1) (by omega)).f (q + p) := by
    change z' ≫ ((Subobject.«exists» g').obj W).arrow = _
    dsimp only [z']
    rw [Category.assoc, ← Subobject.imageFactorisation_F_m,
      (Subobject.imageFactorisation g' W).F.fac]
    simp only [← Category.assoc, Subobject.factorThru_arrow]
    rfl
  have hmap := hM A x y z z' hxy hz hz'
  have hcoh := hc A x y z z' hxy hz hz'
  apply (cancel_epi (z ≫ filteredComplexPageπ T F 1 (q, p) ≫ α.inv)).1
  calc
    _ = z' ≫ filteredComplexPageπ T' F' 1 (q, p) ≫ β.inv ≫ k' := by
      simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ k') hmap
    _ = _ := by simpa only [Category.assoc] using hcoh.symm

-- The omitted page bounds are closed numeral inequalities; avoid scanning the CE context.
local macro_rules | `(tactic| lia) => `(tactic| decide)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
-- Elaborate the dependent normalized page and CE comparison families together.
/-- Assemble presentations on prescribed CE resolutions with normalized quotient pages,
and compute a supplied map of the first page on ordinary sheaf cohomology.
This statement constructs no spectral-sequence morphism.
Source: Stacks Project, Tag 015J, lemma-two-ss-complex-functor;
Tag 015K, remark-functorial-ss; Tag 012K, lemma-spectral-sequence-filtered-complex;
Tag 06XR, cohomology through injective resolutions.
(blueprint: lem-weil-pbc-ce-prescribed-normalized-first-pages).

Proof. Use the prescribed lower bound and extension by zero to construct the flipped
finite-diagonal sections total and second filtration. In positive degree use the actual
boundary cokernels and their unique representative differential. Choose each successor
comparison by its normalization on successor cycles; this determines it uniquely.
Adjoin the graded page zero, using its canonical homology comparison to page one.
Compute page one from the injective resolution in each complex degree. Multiply the
row identification by (-1)^(pq) to absorb the total differential sign. Compare the
prescribed row with the chosen injective resolution, and identify its sections homology
with Ext by evaluation at 1 in the constant integer sheaf. Choose ordinaryComparison
through this explicit Ext identification, which is natural in coefficient morphisms.
Retain the augmentation, K-injective comparison, homology isomorphism and transported
finite homology-image filtration from exists_hypercohomology_firstPage.
For the first-page computation restrict the supplied filtered sections map to its
steps. The diagonal equation identifies the induced graded map with the sections
pullback unit followed by the supplied row comparison. The augmentation equation
identifies the resulting homology map with Ext pullback followed by the coefficient
map. The identical signs in the two row identifications commute with the additive
map and cancel. An arbitrary M with the stated representative equation equals this
row map: use an epic cover of graded cycles by filtered representatives, then cancel
the boundary cokernel projection. This proves the first-page equation for M, without
constructing or asserting any compatible maps on higher pages. Empty diagonals, zero
rows and empty schemes use the same finite-limit and cokernel constructions. -/
theorem exists_etaleCE_prescribed_normalized_first_pages
    (I : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      HomologicalComplex₂ (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
        (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      ((CochainComplex.single₀
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
         (ComplexShape.up ℤ)).obj K.obj ⟶ I X K)
    (hbelow : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((I X K).X s))
    (hrows : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ), QuasiIso ((a X K).f s))
    (hterms : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ) (r : ℕ), Injective (((I X K).X s).X r))
    (hhorizontal : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ) (r : ℕ),
      Injective (((I X K).cycles s).X r) ∧
      Injective ((image ((I X K).d (s - 1) s)).X r) ∧
      Injective (((I X K).homology s).X r))
    (hquasi : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ),
      QuasiIso (HomologicalComplex.cyclesMap (a X K) s) ∧
      QuasiIso (image.map (Arrow.homMk' ((a X K).f (s - 1)) ((a X K).f s)
        ((a X K).comm (s - 1) s))) ∧
      QuasiIso (HomologicalComplex.homologyMap (a X K) s)) :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (δ : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r),
        FilteredComplexPageDifferential (P X K).sectionsTotal (P X K).L r)
      (j : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r), (P X K).sequence.page r hr ≅ (δ X K r hr).page),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        (P X K).I = I X K) ∧
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
        FilteredComplexHomologyNormalized (P X K).sectionsTotal (P X K).L r (δ X K r hr) pq
          ((HomologicalComplex.homologyFunctor AddCommGrpCat.{uNatural + 1}
            (ComplexShape.up' (r, 1 - r)) pq).mapIso (j X K r hr).symm ≪≫
            (P X K).sequence.iso r (r + 1) pq rfl hr ≪≫
            (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1}
              (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
                (j X K (r + 1) (by omega)))) ∧
      ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      let D := P X K
      let D' := P Y L
      ∀ (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0)
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
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h),
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      (∀ q : ℤ, ∃ s : (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
          (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
        s ≫ (D'.L.step q).arrow = (D.L.step q).arrow ≫ b) →
      ∀ M : D.sequence.page 1 ⟶ D'.sequence.page 1,
        (∀ (A : AddCommGrpCat.{uNatural + 1}) (q p : ℤ)
          (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
          (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
          (z : A ⟶ (D.L.complexCycles q (q + p) 1 : AddCommGrpCat.{uNatural + 1}))
          (z' : A ⟶ (D'.L.complexCycles q (q + p) 1 : AddCommGrpCat.{uNatural + 1})),
          x ≫ (D.L.step q).arrow.f (q + p) ≫ b.f (q + p) =
            y ≫ (D'.L.step q).arrow.f (q + p) →
          z ≫ (D.L.complexCycles q (q + p) 1).arrow =
            x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
          z' ≫ (D'.L.complexCycles q (q + p) 1).arrow =
            y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
          z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, p) ≫
              (j X K 1 (by omega)).inv.f (q, p) ≫ M.f (q, p) =
            z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, p) ≫
              (j Y L 1 (by omega)).inv.f (q, p)) →
        ∀ (p : ℕ) (q : ℤ),
          M.f (q, (p : ℤ)) ≫ (D'.firstPageIso p q).hom =
            (D.firstPageIso p q).hom ≫
              AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
                (cohomologyMap f (K.obj.X q) p)) := by
  classical
  obtain ⟨P, δ, j, hI, hn, hc⟩ :=
    exists_etaleCE_normalized_representative_cohomology I a hbelow hrows hterms
      hhorizontal hquasi
  refine ⟨P, δ, j, hI, hn, ?_⟩
  intro X Y f K L v D D' φ hφ u hu b hb M hM p q
  refine firstPage_descend (C := AddCommGrpCat.{uNatural + 1})
    (S := (D.sequence.page 1 (by decide)).X (q, (p : ℤ)))
    (S' := (D'.sequence.page 1 (by decide)).X (q, (p : ℤ)))
    (V := AddCommGrpCat.of (Sheaf.H (K.obj.X q) p))
    (V' := AddCommGrpCat.of (Sheaf.H (L.obj.X q) p))
    D.sectionsTotal D'.sectionsTotal D.L D'.L b hb (p : ℤ) q
    (HomologicalComplex.Hom.isoApp (j X K 1 (by decide)) (q, (p : ℤ)))
    (HomologicalComplex.Hom.isoApp (j Y L 1 (by decide)) (q, (p : ℤ)))
    (M.f (q, (p : ℤ))) (D.firstPageIso p q).hom (D'.firstPageIso p q).hom
    (AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
      (cohomologyMap f (K.obj.X q) p)))
    ?_ ?_
  · intro A x y z z' hxy hz hz'
    exact hM A q (p : ℤ) x y z z' hxy hz hz'
  · intro A x y z z' hxy hz hz'
    exact hc f K L v φ hφ u hu A p q x y z z' hxy hz hz'

end AlgebraicGeometry.Etale
