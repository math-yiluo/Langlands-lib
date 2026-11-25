/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCERowOrdinaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleCECanonicalRowComparison
import all WeilConjectures.CategoryTheory.DoubleComplexTotal

/-! # CE row cycles under diagonal-compatible total maps

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-row-cycles-naturality).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale


set_option backward.isDefEq.respectTransparency false in
private noncomputable def rowProjection
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    D.sectionsTotal.X (q + (p : ℤ)) ⟶
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).X p := by
  let J := ((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj D.I).flip
  let R := ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (D.I.X q)
  exact J.totalDesc (fun i j hij ↦ if hj : j = q then
    (J.XXIsoOfEq _ _ _ (show i = (p : ℤ) from by
      change i + j = q + (p : ℤ) at hij; omega) hj).hom ≫
      (R.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom else 0)

set_option backward.isDefEq.respectTransparency false in
private theorem rowProjection_inclusion
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    Functor.secondFiltrationRowι
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D.I p q ≫
        rowProjection D p q = 𝟙 _ := by
  simp [Functor.secondFiltrationRowι, rowProjection, HomologicalComplex₂.XXIsoOfEq_rfl]

set_option backward.isDefEq.respectTransparency false in
private theorem rowProjection_tail
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    (D.L.step (q + 1)).arrow.f (q + (p : ℤ)) ≫ rowProjection D p q = 0 := by
  let J := ((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj D.I).flip
  let n := q + (p : ℤ)
  let m := (D.L.step (q + 1)).arrow.f n
  have hm : Mono m := by
    change Mono ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map
      (D.L.step (q + 1)).arrow)
    infer_instance
  have he : (J.secondFiltration n).step (q + 1) = Subobject.mk m := by
    rw [← D.filtration_formula, DecreasingFiltration.complexStep, imageSubobject_mono]
  let e := Subobject.isoOfEqMk ((J.secondFiltration n).step (q + 1)) m he
  have hem : e.hom ≫ m = ((J.secondFiltration n).step (q + 1)).arrow :=
    Subobject.ofLEMk_comp he.le
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, hem, comp_zero]
  apply (Subobject.bot_factors_iff_zero _).1
  apply HomologicalComplex₂.factors_finset_sup (Finset.Icc (q + 1) n)
    (fun i ↦ J.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) (rowProjection D p q) ⊥
  intro i hi
  have hiq : i ≠ q := by have := (Finset.mem_Icc.mp hi).1; omega
  rw [J.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n
    (by change (n - i) + i = n; omega)]
  have hzero : J.ιTotal (ComplexShape.up ℤ) (n - i) i n
      (by change (n - i) + i = n; omega) ≫ rowProjection D p q = 0 := by
    simp [rowProjection, J, n, hiq]
  rw [hzero]
  exact Subobject.factors_zero

set_option backward.isDefEq.respectTransparency false in
private noncomputable def rowInclusion
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q n : ℤ)
    (h : (p : ℤ) + q = n) :
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q)).X p ⟶ D.sectionsTotal.X n :=
  (HomologicalComplex.extendXIso
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q))
      ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj D.I).flip).ιTotal
      (ComplexShape.up ℤ) (p : ℤ) q n h

set_option backward.isDefEq.respectTransparency false in
private theorem rowInclusion_naturality
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (D : EtaleTermwiseHypercohomology X K)
    (D' : EtaleTermwiseHypercohomology Y L)
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
    ∀ (p : ℕ) (q n : ℤ) (h : (p : ℤ) + q = n),
      rowInclusion D p q n h ≫
        (D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv).f n =
      (ceRowSectionsMap f (φ.f q)).f p ≫ rowInclusion D' p q n h := by
  intro p q n h
  let a := (HomologicalComplex.extendXIso
    (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q))
      ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor
      (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj D.I).flip).ιTotal
      (ComplexShape.up ℤ) (p : ℤ) q n h
  let a' := (HomologicalComplex.extendXIso
    (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D'.I.X q))
      ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor
      (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj D'.I).flip).ιTotal
      (ComplexShape.up ℤ) (p : ℤ) q n h
  have hD : rowInclusion D p q n h ≫
      D.totalSectionsIso.hom.f n =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map a := by
    dsimp only [rowInclusion]
    rw [Category.assoc, D.totalSectionsIso_formula]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  have hD' : rowInclusion D' p q n h ≫
      D'.totalSectionsIso.hom.f n =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map a' := by
    dsimp only [rowInclusion]
    rw [Category.assoc, D'.totalSectionsIso_formula]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  apply (cancel_mono (D'.totalSectionsIso.hom.f n)).1
  change _ ≫ (D.totalSectionsIso.hom.f n ≫ (ceSectionsLift f u).f n ≫
      D'.totalSectionsIso.inv.f n) ≫ D'.totalSectionsIso.hom.f n = _
  have hi : D'.totalSectionsIso.inv.f n ≫ D'.totalSectionsIso.hom.f n = 𝟙 _ := by
    change (D'.totalSectionsIso.inv ≫ D'.totalSectionsIso.hom).f n = _
    rw [Iso.inv_hom_id, HomologicalComplex.id_f]
  simp only [Category.assoc, hi, Category.comp_id]
  rw [← Category.assoc, hD, hD']
  change (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map a ≫
    (ceSectionsUnit f).app _ ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map (u.f n) =
    ((ceSectionsUnit f).app _ ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).map ((φ.f q).f p)) ≫ _
  rw [← Category.assoc, (ceSectionsUnit f).naturality a]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [hu p q n]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rowProjection_naturality
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (D : EtaleTermwiseHypercohomology X K)
    (D' : EtaleTermwiseHypercohomology Y L)
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
    ∀ (p : ℕ) (q : ℤ),
      (D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv).f
          (q + (p : ℤ)) ≫ rowProjection D' p q =
        rowProjection D p q ≫ (ceRowSectionsMap f (φ.f q)).f p := by
  intro p q
  let J := ((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).obj D.I).flip
  let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  by_cases hi : 0 ≤ i
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    let R := ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X j)
    apply (cancel_epi (R.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv).1
    change (R.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv ≫
      (J.ιTotal (ComplexShape.up ℤ) (m : ℤ) j (q + (p : ℤ)) hij ≫
        b.f (q + (p : ℤ)) ≫ rowProjection D' p q) = _
    simp only [← Category.assoc]
    change (rowInclusion D m j _ hij ≫ b.f _) ≫ rowProjection D' p q = _
    rw [rowInclusion_naturality f K L D D' φ u hu m j _ hij]
    by_cases hj : j = q
    · subst j
      have hmp : m = p := by change (m : ℤ) + q = q + (p : ℤ) at hij; omega
      subst m
      change ((ceRowSectionsMap f (φ.f q)).f p ≫
        Functor.secondFiltrationRowι
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D'.I p q) ≫
          rowProjection D' p q =
        (R.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv ≫
          ((J.ιTotal (ComplexShape.up ℤ) (p : ℤ) q (q + (p : ℤ)) hij ≫
            rowProjection D p q) ≫ (ceRowSectionsMap f (φ.f q)).f p)
      rw [Category.assoc, rowProjection_inclusion, Category.comp_id]
      rw [← Category.assoc]
      change _ = (Functor.secondFiltrationRowι
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D.I p q ≫
          rowProjection D p q) ≫ _
      rw [rowProjection_inclusion, Category.id_comp]
    · have hzero : rowInclusion D m j (q + (p : ℤ)) hij ≫ rowProjection D p q = 0 := by
        simp [rowInclusion, rowProjection, hj]
      have hzero' : rowInclusion D' m j (q + (p : ℤ)) hij ≫ rowProjection D' p q = 0 := by
        simp [rowInclusion, rowProjection, hj]
      rw [Category.assoc, hzero', comp_zero]
      change 0 = (rowInclusion D m j _ hij ≫ rowProjection D p q) ≫ _
      rw [hzero, zero_comp]
  · exact (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
      (fun m hm ↦ by change (m : ℤ) = i at hm; omega)).eq_of_src _ _

-- Elaborate the filtration quotient and the cycle comparison together.
set_option backward.isDefEq.respectTransparency false in
private theorem rowProjection_representative
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (A : AddCommGrpCat.{uNatural + 1})
    (p : ℕ) (q : ℤ)
    (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
      (q + (p : ℤ)))
    (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
    (hz : z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
      x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ))) :
    z ≫ (D.rowCyclesIso p q).inv ≫
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).iCycles p =
      x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ rowProjection D p q := by
  let n := q + (p : ℤ)
  let inc := Subobject.ofLE (D.L.step (q + 1)) (D.L.step q)
    (D.L.antitone_step (by omega))
  let ev := HomologicalComplex.eval AddCommGrpCat.{uNatural + 1} (ComplexShape.up ℤ) n
  have hinc : inc.f n ≫ (D.L.step q).arrow.f n = (D.L.step (q + 1)).arrow.f n :=
    congrArg (fun t ↦ t.f n) (Subobject.ofLE_arrow
      (D.L.antitone_step (show q ≤ q + 1 by omega)))
  have hzero : ev.map inc ≫ ((D.L.step q).arrow.f n ≫ rowProjection D p q) = 0 := by
    change inc.f n ≫ ((D.L.step q).arrow.f n ≫ rowProjection D p q) = 0
    rw [← Category.assoc, hinc, rowProjection_tail]
  let a := (PreservesCokernel.iso ev inc).hom ≫
    cokernel.desc (ev.map inc) ((D.L.step q).arrow.f n ≫ rowProjection D p q) hzero
  have ha : (D.L.complexQuotientπ q (q + 1) (by omega)).f n ≫ a =
      (D.L.step q).arrow.f n ≫ rowProjection D p q := by
    change ev.map (cokernel.π inc) ≫ ((PreservesCokernel.iso ev inc).hom ≫
      cokernel.desc (ev.map inc) ((D.L.step q).arrow.f n ≫ rowProjection D p q) hzero) = _
    rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]
  have hc : (D.rowCyclesIso p q).hom ≫
      (D.L.complexCycles q n 1).arrow ≫ a =
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).iCycles p := by
    change D.rowCycleClass p q ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow ≫ a = _
    rw [← Category.assoc, D.rowCycleClass_arrow, Category.assoc, ha,
      ← Category.assoc, D.rowCycleStep_arrow, Category.assoc,
      rowProjection_inclusion, Category.comp_id]
  have hc' := congrArg (fun t ↦ (D.rowCyclesIso p q).inv ≫ t) hc
  simp only [Iso.inv_hom_id_assoc] at hc'
  rw [← hc', ← Category.assoc z, hz, Category.assoc, ha]

set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent CE and normalized page data together.
/-- The inverse canonical cycle comparison takes related filtered representatives to
related row cycles. This is a degreewise statement, before taking homology; it assumes
no augmentation compatibility and no normalization of higher spectral-sequence pages.
Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-row-cycles-naturality).

Proof. In total degree n=q+p the second filtration is the finite sum of diagonal
summands with complex index at least q. Its quotient by the next step keeps only
the summand with index q, which is the row term in resolution degree p. Project the
equality relating x and y onto that summand. The summand equation for u, transported
through totalSectionsIso_formula and the naturality of ceSectionsUnit, identifies
this projected map with the degree-p component of ceRowSectionsMap f (phi.f q).
The equations for z and zprime identify the same projections with their graded
cycle inclusions. The canonical rowCyclesIso was normalized by diagonal inclusion;
its inverse therefore takes these projections to the corresponding row cycles.
Apply monicity of the target row iCycles to conclude the stated equality of cycle
maps. The construction kills every higher-index summand by the quotient projection;
negative resolution indices vanish by extension by zero. At p=0 the row cycle
kernel calculation is unchanged, and zero rows or empty diagonals give the unique
map from or to a zero object. No ordinary cohomology or derived-functor comparison
is involved. -/
theorem etaleCE_row_cycles_naturality
    {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (D : EtaleTermwiseHypercohomology X K)
    (D' : EtaleTermwiseHypercohomology Y L)
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
      ∀ (A : AddCommGrpCat.{uNatural + 1}) (p : ℕ) (q : ℤ)
        (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
          (q + (p : ℤ)))
        (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
          (q + (p : ℤ)))
        (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
        (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
        x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
          y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
        z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
          x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
        z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
          y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
        z ≫ (D.rowCyclesIso p q).inv ≫ HomologicalComplex.cyclesMap
            (ceRowSectionsMap f (φ.f q)) p =
          z' ≫ (D'.rowCyclesIso p q).inv := by
  dsimp only
  intro A p q x y z z' hxy hz hz'
  apply (cancel_mono
    ((((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D'.I.X q)).iCycles p)).1
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  calc
    _ = (x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ rowProjection D p q) ≫
        (ceRowSectionsMap f (φ.f q)).f p := by
      simpa only [Category.assoc] using congrArg
        (fun t ↦ t ≫ (ceRowSectionsMap f (φ.f q)).f p)
        (rowProjection_representative D A p q x z hz)
    _ = (x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫
        (D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv).f
          (q + (p : ℤ))) ≫ rowProjection D' p q := by
      simp only [Category.assoc]
      rw [rowProjection_naturality f K L D D' φ u hu p q]
    _ = y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) ≫ rowProjection D' p q := by
      rw [hxy, Category.assoc]
    _ = _ := (rowProjection_representative D' A p q y z' hz').symm

end AlgebraicGeometry.Etale
