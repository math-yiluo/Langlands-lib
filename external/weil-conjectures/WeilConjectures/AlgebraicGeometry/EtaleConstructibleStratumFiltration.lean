/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleGenericImmersionProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.SixFunctors.OpenClosed.Derived
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-! # Finite perfect-stratum devissage on the ordinary etale site

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.3.1,
Lemmas 6.3.3 and 6.3.9, pp. 45--47; Stacks Project, Tags 09BI and 095L
(blueprint: lem-per-etale-constructible-stratum-filtration).

Both the finite triangle tower and its replete triangulated generation formulation
are stated. The published `immersionLowerShriek` is the exact closed direct image
followed by exact open extension by zero, applied termwise on derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- A bounded constructible finite-Tor complex has a finite constructible
stratification and a triangle tower with shifted perfect local-system quotients.
Source: Bhatt--Scholze, Definition 6.3.1 and Lemma 6.3.3, pp. 45--46;
Stacks Project, Tags 09BI, 095L, 09Y5 and 005L
(blueprint: lem-per-etale-constructible-stratum-filtration).

Proof:
1. Choose stratifications making the finitely many possibly nonzero cohomology
sheaves finite locally constant (via lem-weil-pbc-constructible-etale-module-sheaf-comparison)
and refine their intersections by the ordered irreducible refinement underlying
new-det-lem-coefficient-heart-common-stratification-refinement. Realize each stratum
as the closed complement of its open prefix inside the next prefix. Irreducible images
give connected strata; Noetherianity makes the locally closed images constructible
(lem-weil-pbc-noetherian-scheme-closed-subsets-minimal). For empty X take no strata.
2. Restrict K to each stratum. Exact inverse image commutes with cohomology by
situation-conventions and
lem-weil-pbc-exact-functor-complex-cohomology. Image containment gives finite lisse
cohomology by lemma-constructible-immersion-independence. Pullback preserves the Tor
interval, as in lem-coef-etale-domain-pullback-calculus.
3. Apply lem-per-etale-lisse-ctf-perfect-local-model on every connected stratum.
This gives the etale local bounded finite-projective coefficient models; it does
not assert that the individual cohomology modules are projective.
4. Apply the unbounded open-closed triangle lem-fin-module-open-closed-triangle inside
each prefix open, then apply exact open extension by zero to X; exact derived functors
preserve distinguished triangles by situation-conventions.
The vertices are identified by lem-weil-pbc-inverse-image-composition and uniqueness of
left adjoints for lem-weil-pbc-extension-by-zero-adjunction.
5. The empty open gives the zero object; the total open gives K since the counit of
extension by zero along an isomorphism is an isomorphism. These triangles form the
tower. The quotients in this construction have shift zero, which is an allowed shift.
-/
theorem exists_etaleConstructibleStratumFiltration
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (K : DerivedCategoryModule A X)
    (_hK : DerivedCategory.isBoundedConstructible A X K)
    (_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K) :
    ∃ T : Scheme.FiniteLocallyClosedStratification X,
      (∀ i : Fin T.n, Topology.IsConstructible (T.stratum i)) ∧
      ∃ (U : Fin T.n → X.Opens)
        (c : ∀ i : Fin T.n, T.domain i ⟶ (U i).toScheme)
        (hc : ∀ i : Fin T.n, IsClosedImmersion (c i))
        (P : ∀ i : Fin T.n, DerivedCategoryModule A (T.domain i))
        (s : Fin T.n → ℤ) (F : Fin (T.n + 1) → DerivedCategoryModule A X),
        (∀ i : Fin T.n, c i ≫ (U i).ι = T.immersion i) ∧
        (∀ i : Fin T.n, ∃ a b : ℤ, (P i).IsGE a ∧ (P i).IsLE b) ∧
        (∀ i : Fin T.n, IsLocallyConstantPerfectEtaleComplex A (T.domain i) (P i)) ∧
        IsZero (F 0) ∧ Nonempty (F (Fin.last T.n) ≅ K) ∧
        ∀ i : Fin T.n,
          ∃ (f : F i.castSucc ⟶ F i.succ)
            (g : F i.succ ⟶
              ((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).obj (P i))⟦s i⟧)
            (h : ((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).obj (P i))⟦s i⟧ ⟶
              (F i.castSucc)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (DerivedCategoryModule A X) := by
  classical
  let : IsNoetherian X := ⟨⟩
  -- Refine the finitely many potentially nonzero cohomology sheaves simultaneously.
  let H (q : ℤ) := (_root_.DerivedCategory.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj K
  obtain ⟨a, b, hab, hz⟩ := _hK.2
  have hH (q : ℤ) : Scheme.IsConstructibleSheaf (H q) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (_hK.1 q)
  choose S hS using fun q : Set.Icc a b ↦ (hH q).exists_stratification
  let B := (q : Set.Icc a b) → Fin (S q).n
  let Q : B → Set X := fun t ↦ ⋂ q, (S q).stratum (t q)
  have hQl (t : B) : IsLocallyClosed (Q t) := by
    choose O Z hO hZ he using fun q ↦ (S q).isLocallyClosed_stratum (t q)
    exact ⟨⋂ q, O q, ⋂ q, Z q, isOpen_iInter_of_finite hO, isClosed_iInter hZ,
      by simp only [Q, he, Set.iInter_inter_distrib]⟩
  have hQc : (⋃ t, Q t) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx (q : Set.Icc a b) : ∃ j, x ∈ (S q).stratum j :=
      Set.mem_iUnion.mp ((S q).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    choose t ht using hx
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iInter.mpr ht⟩
  obtain ⟨n, R, hRi, hRl, hRc, hRd, hRr, hRtail⟩ :=
    ProEtale.exists_ordered_irreducible_refinement (⊤ : TopologicalSpace.Closeds X) Q hQl hQc
  have hRc' : (⋃ i, R i) = Set.univ := hRc
  let V : Fin (n + 1) → X.Opens := fun k ↦
    ⟨⋃ i : Fin n, ⋃ (_ : i.val < k.val), R i, by
      have ht := hRtail k.val
      rw [TopologicalSpace.Closeds.coe_top, ← Set.compl_eq_univ_sdiff] at ht
      simpa only [compl_compl] using ht.isOpen_compl⟩
  have hV0 : V 0 = ⊥ := by ext x; simp [V]
  have hVn : V (Fin.last n) = ⊤ := by
    ext x
    change (x ∈ ⋃ i : Fin n, ⋃ (_ : i.val < n), R i) ↔ True
    simp only [Set.mem_iUnion, iff_true]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hRc'.symm ▸ Set.mem_univ x)
    exact ⟨i, i.isLt, hi⟩
  have hVmono : Monotone V := by
    intro k l hkl x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨lt_of_lt_of_le hi hkl, hxi⟩⟩
  -- Realize each difference as the actual closed complement inside its open prefix.
  let j (i : Fin n) := X.homOfLE (hVmono (Fin.castSucc_le_succ i))
  let D (i : Fin n) := (Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range (j i))ᶜ, (j i).isOpenEmbedding.isOpen_range.isClosed_compl⟩ :
      TopologicalSpace.Closeds (V i.succ).toScheme)).subscheme
  let c (i : Fin n) : D i ⟶ (V i.succ).toScheme := (j i).closedComplement
  have hc (i : Fin n) : IsClosedImmersion (c i) := inferInstance
  let t (i : Fin n) : D i ⟶ X := c i ≫ (V i.succ).ι
  have ht (i : Fin n) : Set.range (t i) = R i := by
    have hr : Set.range (c i) = (Set.range (j i))ᶜ := (j i).range_closedComplement
    have hd : (V i.succ : Set X) \ (V i.castSucc : Set X) = R i := by
      ext x
      constructor
      · rintro ⟨hx, hn⟩
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hk, hxk⟩ := Set.mem_iUnion.mp hk
        have he : k = i := by
          apply Fin.ext
          by_contra h
          have hlt : k.val < i.val := by have := hk; simp only [Fin.val_succ] at this; omega
          exact hn (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hlt, hxk⟩⟩)
        simpa [he] using hxk
      · intro hx
        refine ⟨Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩, ?_⟩
        intro hn
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hn
        obtain ⟨hk, hxk⟩ := Set.mem_iUnion.mp hk
        exact Set.disjoint_left.mp (hRd (show k ≠ i by intro he; subst k; exact lt_irrefl _ hk))
          hxk hx
    rw [← hd]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(c i y).property, ?_⟩
      intro hy
      have hcy : c i y ∈ Set.range (c i) := Set.mem_range_self y
      rw [hr] at hcy
      exact hcy ⟨⟨_, hy⟩, Subtype.ext (by simp [j, Scheme.homOfLE_apply, t])⟩
    · rintro ⟨hx, hn⟩
      have hy : (⟨x, hx⟩ : (V i.succ).toScheme) ∈ Set.range (c i) := by
        rw [hr]
        rintro ⟨y, hy⟩
        have he : y.1 = x := by
          simpa [j, Scheme.homOfLE_apply] using congrArg Subtype.val hy
        exact hn (he ▸ y.property)
      obtain ⟨y, hy⟩ := hy
      exact ⟨y, congrArg Subtype.val hy⟩
  have hti (i : Fin n) : IsImmersion (t i) := inferInstance
  let T : Scheme.FiniteLocallyClosedStratification X := {
    n := n
    stratum := R
    isLocallyClosed_stratum := hRl
    iUnion_stratum_eq_univ := hRc'
    pairwise_disjoint_stratum := hRd
    domain := D
    immersion := t
    isImmersion := hti
    range_immersion := ht }
  have hconn (i : Fin n) : ConnectedSpace (D i) := by
    have : IsImmersion (t i) := hti i
    have : IrreducibleSpace (Set.range (t i)) :=
      Subtype.irreducibleSpace ((ht i).symm ▸ hRi i)
    have : IrreducibleSpace (D i) :=
      (t i).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance
    infer_instance
  -- Exact pullback retains boundedness, lisse cohomology and the Tor interval.
  let P (i : Fin n) := (upperStar (ModuleCat.{u + 1} A) (t i)).mapDerivedCategory.obj K
  have hPlisse (i : Fin n) (q : ℤ) : Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj (P i)) := by
    let G := upperStar (ModuleCat.{u + 1} A) (t i)
    have hG : Scheme.IsFiniteLocallyConstantSheaf (G.obj (H q)) := by
      by_cases hq : q ∈ Set.Icc a b
      · obtain ⟨r, hr⟩ := hRr i
        have hsq := hS ⟨q, hq⟩ (r ⟨q, hq⟩)
        have := hsq
        apply Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset
          (t i) ((S ⟨q, hq⟩).immersion (r ⟨q, hq⟩)) ?_ (H q)
        rw [ht, (S ⟨q, hq⟩).range_immersion]
        exact fun x hx ↦ Set.mem_iInter.mp (hr hx) ⟨q, hq⟩
      · have hzq : IsZero (H q) := hz q (by simpa only [Set.mem_Icc, not_and_or,
          not_le] using hq)
        have := G.map_isZero hzq
        exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero this
    have := hG
    exact Scheme.IsFiniteLocallyConstantSheaf.of_iso (F := G.obj (H q))
      ((G.mapDerivedCategoryHomologyFunctorIso q).app K)
  have hPz (i : Fin n) (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj (P i)) :=
    ((upperStar (ModuleCat.{u + 1} A) (t i)).map_isZero (hz q hq)).of_iso
      (((upperStar (ModuleCat.{u + 1} A) (t i)).mapDerivedCategoryHomologyFunctorIso q).app K).symm
  have hPbound (i : Fin n) : (P i).IsGE a ∧ (P i).IsLE b :=
    ⟨(_root_.DerivedCategory.isGE_iff _ _).2 (fun q hq ↦ hPz i q (.inl hq)),
      (_root_.DerivedCategory.isLE_iff _ _).2 (fun q hq ↦ hPz i q (.inr hq))⟩
  have hPbc (i : Fin n) : DerivedCategory.isBoundedConstructible A (D i) (P i) := by
    refine ⟨fun q ↦ ?_, a, b, hab, hPz i⟩
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    have := hPlisse i q
    refine ⟨Scheme.Stratification.trivial (D i), fun k ↦ ?_⟩
    exact Scheme.IsFiniteLocallyConstantSheaf.upperStar _ _
  obtain ⟨ta, tb, hTor⟩ := _hTor
  have hPTor (i : Fin n) : DerivedCategory.hasTorAmplitudeIn A (D i) ta tb (P i) := by
    apply DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) (D i) ta tb).prop_of_iso
      ((upperStar (ModuleCat.{u + 1} A) (t i)).leftDerivedFunctorIsoMapDerivedCategory.app K)
      (torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A) (t i) ta tb
        (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hTor))
  -- Package the proved finite-projective local models in the cover-based predicate.
  have hperfect (i : Fin n) : IsLocallyConstantPerfectEtaleComplex A (D i) (P i) := by
    have := hconn i
    obtain ⟨E, l, r, hEl, hEr, hEfin, I, Y, f, hf, hsurj, he⟩ :=
      etale_lisse_ctf_perfect_local_model (P i) (hPbc i) (hPlisse i) ⟨ta, tb, hPTor i⟩
    let 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage (D i) := {
      I₀ := I
      X := Y
      f := f
      mem₀ := by
        apply (Scheme.presieve₀_mem_precoverage_iff _).mpr
        exact ⟨fun x ↦ by obtain ⟨⟨j, y⟩, h⟩ := hsurj x; exact ⟨j, y, h⟩, hf⟩ }
    refine ⟨𝒰, fun j ↦ ⟨_root_.DerivedCategory.Q.obj E,
      ⟨E, l, r, hEl, hEr, hEfin, ⟨Iso.refl _⟩⟩, ?_⟩⟩
    exact ⟨(he j).some ≪≫
      ((constantSheaf (Y j).smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategoryFactors.app
        E).symm⟩
  let F (k : Fin (n + 1)) :=
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (V k).ι).mapDerivedCategory.obj
      ((upperStar (ModuleCat.{u + 1} A) (V k).ι).mapDerivedCategory.obj K)
  refine ⟨T, fun i ↦ (hRl i).isConstructible_of_noetherianSpace, (fun i ↦ V i.succ), c, hc, P,
    fun _ ↦ 0, F, fun _ ↦ rfl, fun i ↦ ⟨a, b, hPbound i⟩, hperfect, ?_, ?_, ?_⟩
  · change IsZero ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (V 0).ι).mapDerivedCategory.obj _)
    apply Functor.map_isZero
    rw [hV0]
    have : IsEmpty (⊥ : X.Opens).toScheme :=
      ⟨fun x ↦ TopologicalSpace.Opens.mem_bot.mp x.2⟩
    exact Functor.isZero_mapDerivedCategory_obj _ K fun _ ↦
      Scheme.Etale.isZero_sheaf_of_isEmpty _
  · change Nonempty ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (V (Fin.last n)).ι).mapDerivedCategory.obj _ ≅ K)
    rw [hVn]
    have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
    have : IsIso (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (⊤ : X.Opens).ι).counit :=
      Adjunction.counit_isIso_of_R_fully_faithful _
    exact ⟨asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) (⊤ : X.Opens).ι).counit.app K)⟩
  · intro i
    let G := (openImmersionLowerShriek (ModuleCat.{u + 1} A) (V i.succ).ι).mapDerivedCategory
    let L := (upperStar (ModuleCat.{u + 1} A) (V i.succ).ι).mapDerivedCategory.obj K
    -- Use unbounded recollement, retaining its right-derived closed direct image.
    obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} A)
      (j i) (c i) ((j i).range_closedComplement) L
    let Δ := G.mapTriangle.obj (Triangle.mk
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (j i)).counit.app L)
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (c i)).unit.app L) w)
    have hΔ : Δ ∈ distTriang _ := G.map_distinguished _ hw
    let epNat := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (j i) (V i.succ).ι
        (V i.castSucc).ι (X.homOfLE_ι _).symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
    let ep := epNat.app K
    -- Compare the left adjoints through the known comparison of their right adjoints.
    let eo := (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) (V i.castSucc).ι).leftAdjointUniq
        (((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) (j i)).comp
          (derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) (V i.succ).ι)).ofNatIsoRight epNat.symm)
    let e₁ : F i.castSucc ≅ Δ.obj₁ :=
      (openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (V i.castSucc).ι).mapDerivedCategory.mapIso ep ≪≫ eo.app _
    let ec := ((Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (c i) (V i.succ).ι)) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).app K
    let e₃ : Δ.obj₃ ≅ ((@immersionLowerShriek A _ _ _ _ (c i)
        (V i.succ).ι (hc i) _).obj (P i))⟦(0 : ℤ)⟧ :=
      G.mapIso ((lowerStar (ModuleCat.{u + 1} A) (c i)).rightDerivedFunctor.mapIso ec.symm) ≪≫
        ((shiftFunctorZero _ ℤ).app _).symm
    let f := e₁.hom ≫ Δ.mor₁
    let g := Δ.mor₂ ≫ e₃.hom
    let h := e₃.inv ≫ Δ.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.inv
    refine ⟨f, g, h, isomorphic_distinguished _ hΔ _ ?_⟩
    exact Triangle.isoMk _ _ e₁ (Iso.refl _) e₃.symm (by simp [f])
      (by simp [g]) (by simp [h])

end AlgebraicGeometry.Etale
