/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.EtaleComplexCoherentFiltrations
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Functorial hypercohomology quotient presentations

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-abutment-presentations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Transport a first-page colimit comparison across a final reindexing.
Source: Stacks Project, Tag 0032, final reindexing of filtered systems.
(blueprint: lem-weil-pbc-etale-complex-first-page-reindexing).

The proof uses the canonical isomorphism between a colimit and the colimit of its
whiskering by a final functor, and the first-page comparison equations. -/
theorem reindex_first_page_comparison
    {I : Type u} [SmallCategory I] {J : Type (u + 1)} [SmallCategory J]
    (R : J ⥤ I) (hR : R.Final)
    (E : I ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v : ∀ i, E.obj i ⟶ E')
    (hcomp : ∀ {i j : I} (f : i ⟶ j), E.map f ≫ v j = v i)
    (hfirst : ∀ (s t : ℤ)
      (ψ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨s, t⟩) ⟶ (E'.page 1).X ⟨s, t⟩),
      (∀ i, colimit.ι _ i ≫ ψ = ((v i).hom 1 (by omega)).f ⟨s, t⟩) → IsIso ψ) :
    ∀ (s t : ℤ)
      (ψ : colimit ((R ⋙ E) ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨s, t⟩) ⟶ (E'.page 1).X ⟨s, t⟩),
      (∀ j, colimit.ι _ j ≫ ψ = ((v (R.obj j)).hom 1 (by omega)).f ⟨s, t⟩) → IsIso ψ := by
  let := hR
  intro s t ψ hψ
  let A := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
    (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
    HomologicalComplex.eval _ _ ⟨s, t⟩
  let Q : Cocone A :=
    { pt := (E'.page 1).X ⟨s, t⟩
      ι :=
        { app := fun i ↦ ((v i).hom 1).f ⟨s, t⟩
          naturality := by
            intro i j f
            let U := SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
              (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
              HomologicalComplex.eval _ _ ⟨s, t⟩
            change U.map (E.map f) ≫ U.map (v j) = U.map (v i) ≫ 𝟙 _
            rw [Category.comp_id, ← U.map_comp, hcomp f] } }
  let : IsIso (colimit.desc A Q) := hfirst s t _ (by
    intro i
    exact colimit.ι_desc Q i)
  have heq : ψ = colimit.pre A R ≫ colimit.desc A Q := by
    apply colimit.hom_ext
    intro j
    change colimit.ι (R ⋙ A) j ≫ ψ =
      colimit.ι (R ⋙ A) j ≫ (colimit.pre A R ≫ colimit.desc A Q)
    rw [← Category.assoc, colimit.ι_pre, colimit.ι_desc]
    exact hψ j
  rw [heq]
  infer_instance

/-- Quotient presentations of a finite filtration, transported along abutment isomorphisms.
This is an argument in abelian groups, independent of how the cohomology objects are constructed. -/
private theorem exists_quotient_presentations_of_filtrations
    {I : Type u} [SmallCategory I] {J : Type (u + 1)} [SmallCategory J]
    (A : I → AddCommGrpCat.{u + 1}) (A' : AddCommGrpCat.{u + 1})
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
    (eH : ∀ i : I, H.obj (op i) ≅ A i) (eB : B.pt ≅ A')
    (β : ∀ i : I, A i ⟶ A')
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom = (eH i).hom ≫ β i)
    (V : ∀ i : I, DecreasingFiltration (A i)) (W : DecreasingFiltration A')
    (a p : ℤ) (htop : W.step a = ⊤) (hbot : W.step (max a (p + 1)) = ⊥)
    (E0 : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v0 : ∀ i : Iᵒᵖ, E0.obj i ⟶ E')
    (hstable : ∀ q : ℤ, ∃ (r : ℤ) (hr : 1 ≤ r)
      (e : ∀ i : I, ((E0.obj (op i)).page r hr).X ⟨p - q, q⟩ ≅ (V i).gradedPiece q)
      (e' : (E'.page r hr).X ⟨p - q, q⟩ ≅ W.gradedPiece q),
      ∀ i : I, ∃ (k : ∀ z : ℤ, ((V i).step z : AddCommGrpCat.{u + 1}) ⟶
          (W.step z : AddCommGrpCat.{u + 1}))
        (_hk : ∀ z : ℤ, k z ≫ (W.step z).arrow = ((V i).step z).arrow ≫ β i)
        (hc : ∀ z : ℤ,
          Subobject.ofLE ((V i).step (z + 1)) ((V i).step z)
              ((V i).antitone_step (Int.le_add_one (le_refl z))) ≫ k z =
            k (z + 1) ≫ Subobject.ofLE (W.step (z + 1)) (W.step z)
              (W.antitone_step (Int.le_add_one (le_refl z)))),
        ((v0 (op i)).hom r hr).f ⟨p - q, q⟩ ≫ e'.hom =
          (e i).hom ≫ cokernel.map _ _ (k (q + 1)) (k q) (hc q))
    (R : J ⥤ Iᵒᵖ) :
    ∃ S : ℕ → AddSubgroup B.pt,
      S 0 = ⊤ ∧ S (p + 1 - a).toNat = ⊥ ∧ Antitone S ∧
      ∀ n : ℕ, n < (p + 1 - a).toNat →
        ∃ (r : ℤ) (hr : 1 ≤ r) (T : ∀ j : J, AddSubgroup (H.obj (R.obj j)))
          (q : S n →+ (E'.page r hr).X ⟨p - a - n, a + n⟩)
          (t : ∀ j : J, T j →+ ((E0.obj (R.obj j)).page r hr).X ⟨p - a - n, a + n⟩),
          (∀ x : S n, q x = 0 ↔ (x : B.pt) ∈ S (n + 1)) ∧
          (∀ j : J, Function.Surjective (t j)) ∧
          ∀ (j : J) (y : T j),
            ∃ hy : B.ι.app (R.obj j) (y : H.obj (R.obj j)) ∈ S n,
              q ⟨B.ι.app (R.obj j) (y : H.obj (R.obj j)), hy⟩ =
                ((v0 (R.obj j)).hom r hr).f ⟨p - a - n, a + n⟩ (t j y) := by
  classical
  have hstep : ∀ {A : AddCommGrpCat.{u + 1}}
      (B : DecreasingFiltration A) (q : ℤ)
      (y : (B.step q : AddCommGrpCat.{u + 1})),
      cokernel.π (Subobject.ofLE (B.step (q + 1)) (B.step q)
        (B.antitone_step (Int.le_add_one (le_refl _)))) y = 0 ↔
        ∃ z : (B.step (q + 1) : AddCommGrpCat.{u + 1}),
          (B.step (q + 1)).arrow z = (B.step q).arrow y := by
    intro A B q y
    let j := Subobject.ofLE (B.step (q + 1)) (B.step q)
      (B.antitone_step (Int.le_add_one (le_refl _)))
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).mp
        (ShortComplex.exact_cokernel j) y h
      refine ⟨z, ?_⟩
      calc
        (B.step (q + 1)).arrow z = (B.step q).arrow (j z) := by
          exact (ConcreteCategory.congr_hom (Subobject.ofLE_arrow _) z).symm
        _ = (B.step q).arrow y := congrArg _ hz
    · rintro ⟨z, hz⟩
      have hy : j z = y := (AddCommGrpCat.mono_iff_injective (B.step q).arrow).mp
        inferInstance (by
          simpa only [← ConcreteCategory.comp_apply, j, Subobject.ofLE_arrow] using hz)
      rw [← hy]
      exact ConcreteCategory.congr_hom (cokernel.condition j) z
  have hmap : ∀ {A B A' B' : AddCommGrpCat.{u + 1}} (f : A ⟶ B) (g : A' ⟶ B')
      (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ g) (x : B),
      (cokernel.map f g a b h) (cokernel.π f x) = cokernel.π g (b x) := by
    intro A B A' B' f g a b h x
    exact ConcreteCategory.congr_hom (cokernel.π_desc f (b ≫ cokernel.π g) _) x
  let f (z : ℤ) := (W.step z).arrow ≫ eB.inv
  have hf (z : ℤ) : Function.Injective (f z) :=
    (AddCommGrpCat.mono_iff_injective (f z)).mp inferInstance
  let b (z : ℤ) := AddMonoidHom.ofInjective (f := (f z).hom) (hf z)
  let S : ℕ → AddSubgroup B.pt := fun n ↦ (f (a + n)).hom.range
  have hS0 : S 0 = ⊤ := by
    change (f (a + 0)).hom.range = ⊤
    rw [add_zero]
    have hw : IsIso (W.step a).arrow := by rw [htop]; infer_instance
    let := hw
    exact (AddCommGrpCat.epi_iff_range_eq_top (f a)).mp inferInstance
  have hSN : S (p + 1 - a).toNat = ⊥ := by
    have heq : a + ((p + 1 - a).toNat : ℤ) = max a (p + 1) := by omega
    change (f (a + ((p + 1 - a).toNat : ℤ))).hom.range = ⊥
    have hz : f (max a (p + 1)) = 0 := by
      dsimp [f]
      have hzero : (W.step (max a (p + 1))).arrow = 0 := by
        exact zero_of_source_iso_zero _
          (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero)
      simp only [hzero, zero_comp]
    rw [heq, hz]
    exact AddMonoidHom.range_zero
  have hanti : Antitone S := by
    intro m n hmn
    rintro x ⟨y, rfl⟩
    let j := Subobject.ofLE (W.step (a + n)) (W.step (a + m))
      (W.antitone_step (by omega))
    refine ⟨j y, ?_⟩
    exact ConcreteCategory.congr_hom
      (show j ≫ f (a + m) = f (a + n) by
        dsimp [f, j]
        rw [← Category.assoc, Subobject.ofLE_arrow]) y
  refine ⟨S, hS0, hSN, hanti, ?_⟩
  intro n _hn
  rw [show p - a - (n : ℤ) = p - (a + n) by omega]
  obtain ⟨r, hr, e, e', ht⟩ := hstable (a + n)
  clear hstable
  let g (i : I) := ((V i).step (a + n)).arrow ≫ (eH i).inv
  have hg (i : I) : Function.Injective (g i) :=
    (AddCommGrpCat.mono_iff_injective (g i)).mp inferInstance
  let d (i : I) := AddMonoidHom.ofInjective (f := (g i).hom) (hg i)
  let T : ∀ j : J, AddSubgroup (H.obj (R.obj j)) :=
    fun j ↦ (g (unop (R.obj j))).hom.range
  let π := cokernel.π (Subobject.ofLE (W.step (a + n + 1)) (W.step (a + n))
    (W.antitone_step (Int.le_add_one (le_refl _))))
  let q : S n →+ (E'.page r hr).X ⟨p - (a + n), a + n⟩ :=
    e'.inv.hom.comp (π.hom.comp (b (a + n)).symm.toAddMonoidHom)
  let πi (i : I) := cokernel.π
    (Subobject.ofLE ((V i).step (a + n + 1)) ((V i).step (a + n))
      ((V i).antitone_step (Int.le_add_one (le_refl _))))
  let ei (i : I) := (e i).symm
  let el := e'.symm
  let t : ∀ j : J, T j →+
      ((E0.obj (R.obj j)).page r hr).X ⟨p - (a + n), a + n⟩ :=
    fun j ↦ (ei (unop (R.obj j))).hom.hom.comp
      ((πi (unop (R.obj j))).hom.comp (d (unop (R.obj j))).symm.toAddMonoidHom)
  refine ⟨r, hr, T, q, t, ?_, ?_, ?_⟩
  · intro x
    have hzero : q x = 0 ↔ π ((b (a + n)).symm x) = 0 := by
      exact map_eq_zero_iff el.hom.hom
        ((AddCommGrpCat.mono_iff_injective el.hom).mp inferInstance)
    rw [hzero, hstep]
    have hx := AddMonoidHom.apply_ofInjective_symm (hf (a + n)) x
    have hnext : S (n + 1) = (f (a + n + 1)).hom.range := by
      change (f (a + ((n + 1 : ℕ) : ℤ))).hom.range = _
      exact congrArg (fun z ↦ (f z).hom.range) (by omega)
    rw [hnext]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      exact (congrArg eB.inv hz).trans hx
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective eB.inv).mp inferInstance
      exact hz.trans hx.symm
  · intro j
    exact ((AddCommGrpCat.epi_iff_surjective (ei (unop (R.obj j))).hom).mp
      inferInstance).comp
        (((AddCommGrpCat.epi_iff_surjective (πi (unop (R.obj j)))).mp
          inferInstance).comp (d (unop (R.obj j))).symm.surjective)
  · intro j y
    let i := unop (R.obj j)
    let z := (d i).symm y
    obtain ⟨k, hk, hc, hs⟩ := ht i
    have hz : g i z = (y : H.obj (R.obj j)) :=
      AddMonoidHom.apply_ofInjective_symm (hg i) y
    have hb : B.ι.app (R.obj j) (y : H.obj (R.obj j)) = f (a + n) (k (a + n) z) := by
      apply (AddCommGrpCat.mono_iff_injective eB.hom).mp inferInstance
      have hh := ConcreteCategory.congr_hom (hk (a + n)) z
      simp only [ConcreteCategory.comp_apply] at hh
      have hb' := ConcreteCategory.congr_hom (hB i) (y : H.obj (R.obj j))
      simp only [ConcreteCategory.comp_apply] at hb'
      have hz' : (eH i).hom (y : H.obj (R.obj j)) = ((V i).step (a + n)).arrow z := by
        rw [← hz]
        simp only [g, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
      rw [hz'] at hb'
      change eB.hom (B.ι.app (op i) (y : H.obj (R.obj j))) =
        eB.hom (eB.inv ((W.step (a + n)).arrow (k (a + n) z)))
      rw [Iso.inv_hom_id_apply]
      exact hb'.trans hh.symm
    have hy : B.ι.app (R.obj j) (y : H.obj (R.obj j)) ∈ S n :=
      ⟨k (a + n) z, hb.symm⟩
    refine ⟨hy, ?_⟩
    have hrep : (b (a + n)).symm
        ⟨B.ι.app (R.obj j) (y : H.obj (R.obj j)), hy⟩ = k (a + n) z := by
      apply hf (a + n)
      rw [AddMonoidHom.apply_ofInjective_symm]
      exact hb
    have hsq := ConcreteCategory.congr_hom hs ((ei i).hom (πi i z))
    have hmap' := hmap _ _ (k (a + n + 1)) (k (a + n)) (hc (a + n)) z
    apply (AddCommGrpCat.mono_iff_injective e'.hom).mp inferInstance
    change e'.hom (e'.inv (π ((b (a + n)).symm
      ⟨B.ι.app (R.obj j) (y : H.obj (R.obj j)), hy⟩))) =
      e'.hom (((v0 (op i)).hom r hr).f ⟨p - (a + n), a + n⟩
        ((e i).inv (πi i z)))
    rw [Iso.inv_hom_id_apply, hrep]
    simp only [ei, Iso.symm_hom, ConcreteCategory.comp_apply,
      Iso.inv_hom_id_apply] at hsq
    exact (hsq.trans hmap').symm

set_option backward.isDefEq.respectTransparency true in
set_option linter.unusedVariables false in
/-- Construct the functorial pages and abutment quotient projections, without continuity.
Source: Stacks Project, Tags 015J and 015K; Tag 0EZM, proof of
lemma-colimit-variant-complexes.
(blueprint: lem-weil-pbc-etale-complex-abutment-presentations).

Proof:
1. Choose functorial Cartan--Eilenberg presentations for the bounded-below stage
complexes and the colimit complex. Exact inverse image and degreewise colimits
preserve the bound. The identity and composition equations assemble E0 and v0.
Swap the coordinates to resolution degree first. The first-page identifications
are ordinary term cohomology, and their naturality gives first_transition and
first_comparison. Negative resolution degrees vanish.
2. Choose a small directed final reindexing of I.op. Lift its preorder to universe
u+1 and compose its equivalence with the reindexing to obtain R. Finality is
preserved. This construction uses no geometric limit or continuity hypothesis.
3. The support region is resolution degree >=0 and complex degree >=a. Homology
preserves this vanishing. In bidegree (p-a-n,a+n), both incident differentials
vanish for r>max(p-a-n+1,n), uniformly at every stage and the target.
Functorial convergence identifies that common page with the graded abutment.
4. Transport the limit abutment filtration along eB. Its steps at a+n give S;
the bounds give S 0=top and S (p+1-a).toNat=bottom and it is antitone. If p<a,
the abutment is zero, so both bounds coincide. Transport the stage steps along
eH to give T. Compose the quotient projections with the inverse convergence
isomorphisms to define q and t. Quotient exactness gives the kernel formula and
surjectivity of t. Filtered functoriality and hP,hH,hB identify the underlying
maps with the legs of B, giving membership and the last equation. -/
theorem exists_etale_complex_abutment_presentations
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (B : Cocone H)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) :
    ∃ (J : Type (u + 1)) (_ : Preorder J) (_ : IsDirected J (· ≤ ·))
      (_ : Nonempty J) (R : J ⥤ Iᵒᵖ) (_ : R.Final)
      (E0 : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v0 : ∀ i : Iᵒᵖ, E0.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E0.map f ≫ v0 j = v0 i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E0.obj (op i)).page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E0.map f.op).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v0 (op i)).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
          ((eG i).inv ≫ L.ι.app (op i)) r s)
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E0.obj i).page 1).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1).X ⟨r, s⟩))
      (S : ℕ → AddSubgroup B.pt),
      S 0 = ⊤ ∧ S (p + 1 - a).toNat = ⊥ ∧ Antitone S ∧
      ∀ n : ℕ, n < (p + 1 - a).toNat →
        ∃ (r : ℤ) (hr : 1 ≤ r) (T : ∀ j : J, AddSubgroup (H.obj (R.obj j)))
          (q : S n →+ (E'.page r hr).X ⟨p - a - n, a + n⟩)
          (t : ∀ j : J, T j →+ ((E0.obj (R.obj j)).page r hr).X ⟨p - a - n, a + n⟩),
          (∀ x : S n, q x = 0 ↔ (x : B.pt) ∈ S (n + 1)) ∧
          (∀ j : J, Function.Surjective (t j)) ∧
          ∀ (j : J) (y : T j),
            ∃ hy : B.ι.app (R.obj j) (y : H.obj (R.obj j)) ∈ S n,
              q ⟨B.ι.app (R.obj j) (y : H.obj (R.obj j)), hy⟩ =
                ((v0 (R.obj j)).hom r hr).f ⟨p - a - n, a + n⟩ (t j y) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    obtain ⟨E0, E', v0, compatible, firstIso, firstIsoLimit, first_transition,
      first_comparison, negative, negativeLimit, V, W, htop, hbot, hstable⟩ :=
      exists_etale_complex_coherent_filtrations D c F φ hidentity hcomposition a hbelow
        G eG hG p P hP L hL
    clear hidentity hcomposition hbelow hG hP hH hL
    obtain ⟨J, horder, hdirected, hnonempty, R₀, hfinal⟩ :=
      IsFiltered.exists_directed (AsSmall.{u + 1} Iᵒᵖ)
    let := horder
    let := hdirected
    let := hnonempty
    let := hfinal
    let R : J ⥤ Iᵒᵖ := R₀ ⋙ (AsSmall.equiv : Iᵒᵖ ≌ AsSmall.{u + 1} Iᵒᵖ).inverse
    have hR : R.Final := by
      dsimp [R]
      infer_instance
    obtain ⟨S, hS0, hSN, hanti, hquot⟩ := exists_quotient_presentations_of_filtrations
      _ _ H B eH eB
      (fun i ↦ P (c.π.app i) (F i) ≫ (cohomology AddCommGrpCat.{u + 1} c.pt p).map
        (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))))
      hB V W a p htop hbot E0 E' v0 hstable R
    exact ⟨J, horder.toPreorder, hdirected, hnonempty, R, hR, E0, E', v0,
      compatible, firstIso, firstIsoLimit, first_transition, first_comparison,
      negative, negativeLimit, S, hS0, hSN, hanti, hquot⟩

end AlgebraicGeometry.Etale
