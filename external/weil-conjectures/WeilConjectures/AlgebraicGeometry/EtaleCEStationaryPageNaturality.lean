/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration

/-! # Naturality of stationary CE page quotients

Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Identifications with the actual cycle/boundary cokernels, without making any choice.
Source: Stacks Project, Tag 012K.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality). -/
abbrev EtaleCEQuotientRealization {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :=
  ∀ (q p r : ℤ) (hr : 1 ≤ r),
    ((D.sequence.page r hr).X (q, p)) ≅
      filteredComplexPageObject D.sectionsTotal D.L r (q, p)

/-- A page map is induced by the sections-total map on graded cycle representatives.
This is an equation of maps from arbitrary test objects, rather than an existence
assertion about a spectral-sequence map. Source: Stacks Project, Tags 012K and 015K.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality). -/
def EtaleCEPageMapOnRepresentatives {X Y : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    {L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (D' : EtaleTermwiseHypercohomology Y L)
    (e : EtaleCEQuotientRealization D) (e' : EtaleCEQuotientRealization D')
    (b : D.sectionsTotal ⟶ D'.sectionsTotal) (N : D.sequence ⟶ D'.sequence) : Prop :=
  ∀ (A : AddCommGrpCat.{uNatural + 1}) (q p r : ℤ) (hr : 1 ≤ r)
    (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
    (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
    (z : A ⟶ (D.L.complexCycles q (q + p) r : AddCommGrpCat.{uNatural + 1}))
    (z' : A ⟶ (D'.L.complexCycles q (q + p) r : AddCommGrpCat.{uNatural + 1})),
    x ≫ (D.L.step q).arrow.f (q + p) ≫ b.f (q + p) =
      y ≫ (D'.L.step q).arrow.f (q + p) →
    z ≫ (D.L.complexCycles q (q + p) r).arrow =
      x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
    z' ≫ (D'.L.complexCycles q (q + p) r).arrow =
      y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
    z ≫ filteredComplexPageπ D.sectionsTotal D.L r (q, p) ≫
        (e q p r hr).inv ≫ (N.hom r hr).f (q, p) =
      z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L r (q, p) ≫ (e' q p r hr).inv

-- Elaborate the dependent CE total and its filtration.
private theorem etaleCE_filtration_bounds
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :
    ∃ b : ℤ, ∀ n : ℤ,
      D.L.complexStep b n = ⊤ ∧ D.L.complexStep (n + 1) n = ⊥ := by
  obtain ⟨b, hb⟩ := D.below
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj D.I).flip
  have hzero : ∀ i j : ℤ, i < 0 ∨ j < b → IsZero ((J.X i).X j) := by
    intro i j hij
    rcases hij with hi | hj
    · change IsZero
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X j)).extend
          ComplexShape.embeddingUpNat |>.X i)
      exact HomologicalComplex.isZero_extend_X _ _ i (by
        intro r
        change (r : ℤ) ≠ i
        omega)
    · change IsZero
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (D.I.X j)).extend
          ComplexShape.embeddingUpNat |>.X i)
      exact (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1} (ComplexShape.up ℤ) i)
        |>.map_isZero ((ComplexShape.embeddingUpNat.extendFunctor _).map_isZero
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (hb j hj)))
  obtain ⟨L, hL, htop, hbot⟩ := J.boundedBelow_secondFiltration b hzero
  refine ⟨b, ?_⟩
  intro n
  constructor
  · rw [D.filtration_formula, ← hL, htop]
  · rw [D.filtration_formula, ← hL, hbot]

-- Elaborate the dependent CE total and its filtration.
private theorem etaleCE_complexStep_antitone
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (n : ℤ) :
    Antitone (fun q ↦ D.L.complexStep q n) := by
  intro p q hpq
  have h := imageSubobject_comp_le
    ((Subobject.ofLE (D.L.step q) (D.L.step p) (D.L.antitone_step hpq)).f n)
    ((D.L.step p).arrow.f n)
  simpa only [DecreasingFiltration.complexStep, ← HomologicalComplex.comp_f,
    Subobject.ofLE_arrow] using h

-- Elaborate the dependent CE total and its filtration.
private theorem etaleCE_image_factor
    {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (n : ℤ) :
    ∃ a : ∀ q : ℤ, (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).homology n ⟶
        ((D.H n).step q : AddCommGrpCat.{uNatural + 1}),
      (∀ q : ℤ, a q ≫ ((D.H n).step q).arrow =
        HomologicalComplex.homologyMap (D.L.step q).arrow n ≫ (D.c n).hom) ∧
      (∀ q : ℤ, Epi (a q)) := by
  let f := fun q ↦ HomologicalComplex.homologyMap (D.L.step q).arrow n
  have h (q : ℤ) : (D.H n).step q = imageSubobject (f q ≫ (D.c n).hom) := by
    calc
      _ = imageSubobject ((imageSubobject (f q)).arrow ≫ (D.c n).hom) := by
        rw [D.H_formula, Subobject.exists_obj_eq_imageSubobject]
      _ = imageSubobject (factorThruImageSubobject (f q) ≫
          ((imageSubobject (f q)).arrow ≫ (D.c n).hom)) :=
        (imageSubobject_comp_of_epi _ _).symm
      _ = _ := by rw [← Category.assoc, imageSubobject_arrow_comp]
  let j := fun q ↦ Subobject.isoOfEq _ _ (h q).symm
  let a := fun q ↦ factorThruImageSubobject (f q ≫ (D.c n).hom) ≫ (j q).hom
  refine ⟨a, ?_, ?_⟩
  · intro q
    dsimp only [a, j]
    simp only [Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
      imageSubobject_arrow_comp, f]
  · intro q
    dsimp only [a]
    infer_instance


private theorem comparison_transport
    {C : Type*} [Category C] {m n : ℤ} (h : m = n)
    {P Q : C} (H J : ℤ → C) (i : P ≅ H m) (j : Q ≅ J m)
    (f : P ⟶ Q) (g : ∀ n, H n ⟶ J n)
    (sq : f ≫ j.hom = i.hom ≫ g m) :
    f ≫ (j ≪≫ eqToIso (congrArg J h)).hom =
      (i ≪≫ eqToIso (congrArg H h)).hom ≫ g n := by
  subst n
  simpa using sq

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
-- Elaborate the dependent simultaneous page and presentation families.
/-- Choose the stationary comparisons naturally for all sections-total filtered maps.
No augmentation, pullback, ordinary first-page identification or CE lift is asserted.
Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality).

Proof. If b bounds the complex degree of D.I below, its extended flipped total has
zero summands in negative resolution degree and in complex degrees below b.
The filtration formula therefore makes D.L top at b and bottom at n+1 in degree n.
For fixed q,n choose R at least 1 so that q+R is past the upper tail in degree n+1,
and q-R+1 is below the lower tail in degree n-1. These inequalities persist for
larger r. The definitions of cycles and boundaries then reduce to actual cycles
in the q-th step and boundaries of the total intersected with that step, projected
onto its graded complex. The abelian subquotient theorem identifies their cokernel
canonically with the q-th graded piece of the homology-image filtration.
Transport this comparison by D.c n, using D.H_formula to identify the transported
steps with D.H n. Compose with e to define eInf; its bound uses only D,q,n.
For a filtered chain map, homology of each step maps its image into the target
image. Transport these restricted image maps by the two c-isomorphisms to obtain
t and its inclusion equation. These restrictions commute with successive step
inclusions by cancellation of the target step's monomorphism. The representative
hypothesis states exactly the naturality of the source page cokernel map. Apply
it to actual cycles in each filtration step; the canonical representative-to-image
quotient projections are epimorphic. Cancellation proves the displayed square
with cokernel.map. Changing its commutativity proof changes no map by proof
irrelevance. Zero totals and empty diagonals obey the same universal properties. -/
theorem exists_etaleCE_stationary_page_comparisons
    (D : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      EtaleTermwiseHypercohomology X K)
    (e : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      EtaleCEQuotientRealization (D X K)) :
    ∃ (R : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n : ℤ), ℤ)
      (eInf : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      ∀ {X Y : Scheme.{uNatural}}
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (b : (D X K).sectionsTotal ⟶ (D Y L).sectionsTotal)
        (N : (D X K).sequence ⟶ (D Y L).sequence),
        (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
            ((D Y L).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
          s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) →
        EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L) b N →
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
              (((D X K).c n).inv ≫
                HomologicalComplex.homologyMap
                  b n ≫ ((D Y L).c n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : R X K q n ≤ r) (hY : R Y L q n ≤ r),
            (N.hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q) := by
  classical
  choose lo hlo using fun X K ↦ etaleCE_filtration_bounds (D X K)
  choose a ha hepi using fun X K n ↦ etaleCE_image_factor (D X K) n
  let R := fun X K q n ↦ max 1 (max (n + 2 - q) (q + 1 - lo X K))
  have bounds (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (q n r : ℤ) (hR : R X K q n ≤ r) :
      (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
      (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤ := by
    have h1 : n + 2 - q ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
    have h2 : q + 1 - lo X K ≤ r :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
    constructor
    · apply bot_unique
      rw [← (hlo X K (n + 1)).2]
      exact etaleCE_complexStep_antitone (D X K) _ (by omega)
    · apply top_unique
      rw [← (hlo X K (n - 1)).1]
      exact etaleCE_complexStep_antitone (D X K) _ (by omega)
  have localComparison (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (q p r : ℤ) (hr : 1 ≤ r) (hR : R X K q (q + p) ≤ r) :=
    filteredStationary_cycle_comparison (D X K).sectionsTotal (D X K).L q p r hr
      (bounds X K q (q + p) r hR).1 (bounds X K q (q + p) r hR).2
      ((D X K).c (q + p)) ((D X K).H (q + p))
      (a X K (q + p)) (ha X K (q + p)) (hepi X K (q + p))
  choose z i hz hzi hi using localComparison
  have hRn (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (q n r : ℤ) (hR : R X K q n ≤ r) : R X K q (q + (n - q)) ≤ r := by
    simpa only [show q + (n - q) = n by omega] using hR
  let eInf : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (q n r : ℤ) (hr : 1 ≤ r) (hR : R X K q n ≤ r),
      ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q :=
    fun X K q n r hr hR ↦
    e X K q (n - q) r hr ≪≫ i X K q (n - q) r hr (hRn X K q n r hR) ≪≫
      eqToIso (congrArg (fun n ↦ ((D X K).H n).gradedPiece q)
        (show q + (n - q) = n by omega))
  refine ⟨R, eInf, ?_⟩
  intro X Y K L b N hb hN
  choose s hs using hb
  have maps (n : ℤ) : ∃ (t : ∀ q : ℤ,
      (((D X K).H n).step q : AddCommGrpCat.{uNatural + 1}) ⟶
        (((D Y L).H n).step q : AddCommGrpCat.{uNatural + 1})),
      (∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
        (((D X K).H n).step q).arrow ≫
          (((D X K).c n).inv ≫ HomologicalComplex.homologyMap b n ≫
            ((D Y L).c n).hom)) ∧
      (∀ q : ℤ, a X K n q ≫ t q =
        HomologicalComplex.homologyMap (s q) n ≫ a Y L n q) := by
    let g := ((D X K).c n).inv ≫ HomologicalComplex.homologyMap b n ≫ ((D Y L).c n).hom
    have imageSquare (q : ℤ) :
        (a X K n q ≫ (((D X K).H n).step q).arrow) ≫ g =
          (HomologicalComplex.homologyMap (s q) n ≫ a Y L n q) ≫
            (((D Y L).H n).step q).arrow := by
      simp only [Category.assoc, ha, g, Iso.hom_inv_id_assoc]
      rw [← HomologicalComplex.homologyMap_comp_assoc, ← hs,
        HomologicalComplex.homologyMap_comp, Category.assoc]
    have factors (q : ℤ) : (((D Y L).H n).step q).Factors
        ((((D X K).H n).step q).arrow ≫ g) := by
      apply (Subobject.imageSubobject_le_iff _ _).1
      rw [← imageSubobject_comp_of_epi (a X K n q)]
      apply imageSubobject_le _ (HomologicalComplex.homologyMap (s q) n ≫ a Y L n q)
      exact (imageSquare q).symm.trans (Category.assoc _ _ _)
    let t := fun q ↦ Subobject.factorThru _ _ (factors q)
    have ht (q : ℤ) : t q ≫ (((D Y L).H n).step q).arrow =
        (((D X K).H n).step q).arrow ≫ g := Subobject.factorThru_arrow _ _ _
    have hat (q : ℤ) : a X K n q ≫ t q =
        HomologicalComplex.homologyMap (s q) n ≫ a Y L n q := by
      apply (cancel_mono (((D Y L).H n).step q).arrow).1
      rw [Category.assoc, ht, ← Category.assoc, imageSquare]
    exact ⟨t, ht, hat⟩
  choose t ht hat using maps
  have comm (n j : ℤ) :
      Subobject.ofLE (((D X K).H n).step (j + 1)) (((D X K).H n).step j)
          (((D X K).H n).antitone_step (Int.le_add_one (le_refl j))) ≫ t n j =
        t n (j + 1) ≫
          Subobject.ofLE (((D Y L).H n).step (j + 1)) (((D Y L).H n).step j)
            (((D Y L).H n).antitone_step (Int.le_add_one (le_refl j))) := by
    apply (cancel_mono (((D Y L).H n).step j).arrow).1
    simp only [Category.assoc, ht, Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]
  intro n
  refine ⟨t n, ht n, ?_⟩
  intro hc q r hr hX hY
  have square (p : ℤ) (hxBound : R X K q (q + p) ≤ r)
      (hyBound : R Y L q (q + p) ≤ r)
      (hc : ∀ j : ℤ,
        Subobject.ofLE (((D X K).H (q + p)).step (j + 1))
          (((D X K).H (q + p)).step j) (by apply DecreasingFiltration.antitone_step; omega) ≫
            t (q + p) j = t (q + p) (j + 1) ≫
        Subobject.ofLE (((D Y L).H (q + p)).step (j + 1))
          (((D Y L).H (q + p)).step j) (by apply DecreasingFiltration.antitone_step; omega)) :
      (N.hom r hr).f (q, p) ≫ ((e Y L q p r hr) ≪≫ i Y L q p r hr hyBound).hom =
        ((e X K q p r hr) ≪≫ i X K q p r hr hxBound).hom ≫
          cokernel.map _ _ (t (q + p) (q + 1)) (t (q + p) q) (hc q) := by
    let zx := z X K q p r hr hxBound
    let zy := z Y L q p r hr hyBound
    let v := HomologicalComplex.cyclesMap (s q) (q + p)
    have hx := hzi X K q p r hr hxBound
    have hy := hzi Y L q p r hr hyBound
    have hrep : ((D X K).L.step q).arrow.f (q + p) ≫ b.f (q + p) =
        (s q).f (q + p) ≫ ((D Y L).L.step q).arrow.f (q + p) := by
      simpa only [HomologicalComplex.comp_f] using
        (congrArg (fun f ↦ f.f (q + p)) (hs q)).symm
    have hNrep := hN
      (((D X K).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).cycles (q + p))
      q p r hr
      (((D X K).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).iCycles (q + p))
      (v ≫ ((D Y L).L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).iCycles
        (q + p)) zx (v ≫ zy)
      (by simp only [Category.assoc, hrep, v, HomologicalComplex.cyclesMap_i_assoc])
      hx (by simpa only [Category.assoc] using congrArg (fun f ↦ v ≫ f) hy)
    have : Epi zx := hz X K q p r hr hxBound
    have : Epi (filteredComplexPageπ (D X K).sectionsTotal (D X K).L r (q, p)) := by
      unfold filteredComplexPageπ
      infer_instance
    dsimp only [Iso.trans_hom]
    apply (cancel_epi (zx ≫ filteredComplexPageπ (D X K).sectionsTotal (D X K).L r
      (q, p) ≫ (e X K q p r hr).inv)).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hleft := congrArg (fun f ↦ f ≫ (e Y L q p r hr).hom ≫
      (i Y L q p r hr hyBound).hom) hNrep
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at hleft
    rw [hleft]
    dsimp only [zx, zy, v]
    rw [hi Y L q p r hr hyBound]
    rw [← HomologicalComplex.homologyπ_naturality_assoc]
    rw [← Category.assoc (HomologicalComplex.homologyMap (s q) (q + p)),
      ← hat (q + p) q, Category.assoc]
    simpa only [Category.assoc, cokernel.map, cokernel.π_desc] using
      (congrArg (fun f ↦ f ≫ cokernel.map _ _ (t (q + p) (q + 1)) (t (q + p) q) (hc q))
        (hi X K q p r hr hxBound)).symm
  have hdeg : q + (n - q) = n := by omega
  let g := fun m ↦ cokernel.map
    (Subobject.ofLE (((D X K).H m).step (q + 1)) (((D X K).H m).step q)
      (((D X K).H m).antitone_step (Int.le_add_one (le_refl q))))
    (Subobject.ofLE (((D Y L).H m).step (q + 1)) (((D Y L).H m).step q)
      (((D Y L).H m).antitone_step (Int.le_add_one (le_refl q))))
    (t m (q + 1)) (t m q) (comm m q)
  exact comparison_transport hdeg
    (fun m ↦ ((D X K).H m).gradedPiece q)
    (fun m ↦ ((D Y L).H m).gradedPiece q)
    (e X K q (n - q) r hr ≪≫ i X K q (n - q) r hr (hRn X K q n r hX))
    (e Y L q (n - q) r hr ≪≫ i Y L q (n - q) r hr (hRn Y L q n r hY))
    ((N.hom r hr).f (q, n - q)) g
    (square (n - q) (hRn X K q n r hX) (hRn Y L q n r hY) (comm _))


end AlgebraicGeometry.Etale
