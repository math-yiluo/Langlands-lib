/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.EtaleSeparatedStratifiedFinite
import WeilConjectures.AlgebraicGeometry.ImmersionAffineConstructiblePieces
import WeilConjectures.AlgebraicGeometry.SeparatedAffineCoverCriterion
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Stratifying an etale affine cover and its overlaps

Source: Stacks Project, Etale Cohomology, `lemma-etale-stratified-finite`, proof,
second paragraph (blueprint: lem-weil-pbc-etale-affine-cover-gluing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem finite_snd_comp {X W Z T : Scheme.{u}}
    (f : W ⟶ X) (g : Z ⟶ X) (k : T ⟶ Z)
    [IsFinite (pullback.snd f g)] : IsFinite (pullback.snd f (k ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f g k]
  infer_instance

private theorem common_finite_strata {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (r : ℕ) (W : Fin r → Scheme.{u}) (f : ∀ a, W a ⟶ X)
    [∀ a, Etale (f a)] [∀ a, IsSeparated (f a)] [∀ a, QuasiCompact (f a)] :
    ∃ S : Scheme.Stratification X,
      ∀ i a, IsFinite (pullback.snd (f a) (S.immersion i)) := by
  classical
  induction r with
  | zero =>
    let S : Scheme.Stratification X := {
      n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := by
        change (⋃ _ : Fin 1, (Set.univ : Set X)) = Set.univ
        exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
      pairwise_disjoint_stratum := by intro i j h; exact (h (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := by intro i; exact Set.range_id }
    exact ⟨S, fun _ a ↦ Fin.elim0 a⟩
  | succ r ih =>
    obtain ⟨S, hS⟩ := ih (fun a ↦ W a.succ) (fun a ↦ f a.succ)
    obtain ⟨T, _, hT⟩ := Scheme.exists_etale_separated_stratified_finite (f 0)
    let T' : Scheme.Stratification X := {
      toStratification := T.toStratification
      domain := T.domain
      immersion := T.immersion
      isImmersion := T.isImmersion
      range_immersion := T.range_immersion }
    refine ⟨S.inter T', fun i a ↦ ?_⟩
    let b := finProdFinEquiv.symm i
    refine Fin.cases ?_ (fun a ↦ ?_) a
    · have := (hT b.2).1
      change IsFinite (pullback.snd (f 0)
        (pullback.fst (S.immersion b.1) (T'.immersion b.2) ≫ S.immersion b.1))
      rw [pullback.condition]
      exact finite_snd_comp _ _ _
    · have := hS b.1 a
      exact finite_snd_comp _ _ _

private theorem affine_refine_strata {X : Scheme.{u}} [IsAffine X]
    (R : Scheme.Stratification X) :
    ∃ (n : ℕ) (S : Fin n → Scheme.{u}) (ι : ∀ i, S i ⟶ X),
      (∀ i, IsAffine (S i) ∧ IsImmersion (ι i) ∧
        Topology.IsConstructible (Set.range (ι i))) ∧
      Pairwise (fun i k ↦ Disjoint (Set.range (ι i)) (Set.range (ι k))) ∧
      (⋃ i, Set.range (ι i)) = Set.univ ∧
      (∀ i, ∃ k : Fin R.n, ∃ κ : S i ⟶ R.domain k, ι i = κ ≫ R.immersion k) := by
  classical
  have hp (k : Fin R.n) := exists_finite_affine_immersion_constructible_pieces
    (inferInstance : IsAffine X) (R.immersion k) (R.stratum k)
    (R.range_immersion k).symm (R.isConstructible_stratum k)
  choose K hK Z κ E haff hκ hι hr hl hc hd hcov using hp
  let (k : Fin R.n) : Fintype (K k) := hK k
  let J := (k : Fin R.n) × K k
  let e := (Fintype.equivFin J).symm
  let S (i : Fin (Fintype.card J)) := Z (e i).1 (e i).2
  let ι (i : Fin (Fintype.card J)) : S i ⟶ X :=
    κ (e i).1 (e i).2 ≫ R.immersion (e i).1
  have hsub (k : Fin R.n) (l : K k) : E k l ⊆ R.stratum k := by
    rw [hcov k]
    exact Set.subset_iUnion (E k) l
  refine ⟨_, S, ι, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨haff _ _, hι _ _, by rw [hr]; exact hc _ _⟩
  · have hpair (p q : J) (hne : p ≠ q) : Disjoint (E p.1 p.2) (E q.1 q.2) := by
      rcases p with ⟨k, l⟩
      rcases q with ⟨k', l'⟩
      by_cases hk : k = k'
      · subst k'
        exact hd k (Set.mem_univ l) (Set.mem_univ l') (fun h ↦ hne (by cases h; rfl))
      · exact (R.pairwise_disjoint_stratum hk).mono (hsub _ _) (hsub _ _)
    intro i j hij
    rw [hr, hr]
    exact hpair (e i) (e j) (fun h ↦ hij (e.injective h))
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (R.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    rw [hcov k] at hk
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hk
    refine Set.mem_iUnion.mpr ⟨Fintype.equivFin J ⟨k, l⟩, ?_⟩
    change x ∈ Set.range (κ (e (e.symm ⟨k, l⟩)).1 (e (e.symm ⟨k, l⟩)).2 ≫
      R.immersion (e (e.symm ⟨k, l⟩)).1)
    rw [e.apply_symm_apply]
    simpa only [hr] using hl
  · intro i
    exact ⟨(e i).1, κ (e i).1 (e i).2, rfl⟩

private theorem chart_pullback_finite {X U T : Scheme.{u}}
    (j : U ⟶ X) (t : T ⟶ X) (B : U.Opens)
    [IsFinite (pullback.snd (B.ι ≫ j) t)] :
    IsFinite (((pullback.fst j t) ⁻¹ᵁ B).ι ≫ pullback.snd j t) := by
  let e := pullbackRestrictIsoRestrict (pullback.fst j t) B
  let d := pullbackRightPullbackFstIso j t B.ι
  have he : ((pullback.fst j t) ⁻¹ᵁ B).ι ≫ pullback.snd j t =
      e.inv ≫ (pullbackSymmetry _ _).hom ≫ d.hom ≫ pullback.snd (B.ι ≫ j) t := by
    simp only [e, d, pullbackRightPullbackFstIso_hom_snd,
      pullbackSymmetry_hom_comp_snd_assoc]
    rw [← Category.assoc, pullbackRestrictIsoRestrict_inv_fst]
  rw [he]
  infer_instance

private theorem closed_overlap_tensor {V : Scheme.{u}} (B C : V.Opens)
    [IsAffine B.toScheme]
    [IsClosedImmersion (V.homOfLE (inf_le_left : B ⊓ C ≤ B))] :
    ∃ φ : TensorProduct ℤ (Γ(V, B)) (Γ(V, C)) →+* Γ(V, B ⊓ C),
      Function.Surjective φ ∧ ∀ (x : Γ(V, B)) (y : Γ(V, C)),
        φ (TensorProduct.tmul ℤ x y) =
          (V.presheaf.map (homOfLE inf_le_left).op) x *
            (V.presheaf.map (homOfLE inf_le_right).op) y := by
  let r := (V.presheaf.map (homOfLE (inf_le_left : B ⊓ C ≤ B)).op).hom
  let s := (V.presheaf.map (homOfLE (inf_le_right : B ⊓ C ≤ C)).op).hom
  let φ := Algebra.TensorProduct.lift r.toIntAlgHom s.toIntAlgHom
    (fun _ _ ↦ Commute.all _ _)
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨x, hx⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine
      (V.homOfLE (inf_le_left : B ⊓ C ≤ B))).2 ((B ⊓ C).topIso.inv z)
    refine ⟨B.topIso.hom x, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (B ⊓ C).topIso.inv).1
    simpa only [r, ← Scheme.homOfLE_appTop_topIso_inv inf_le_left,
      CommRingCat.hom_inv_apply, CommRingCat.inv_hom_apply] using hx
  refine ⟨φ.toRingHom, ?_, fun x y ↦ ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := hr z
    refine ⟨TensorProduct.tmul ℤ x 1, ?_⟩
    simpa [φ] using hx
  · exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem separated_of_finite_charts {S V : Scheme.{u}} [IsAffine S]
    (f : V ⟶ S) (m : ℕ) (B : Fin m → V.Opens)
    (hcover : ⨆ a, B a = ⊤)
    (hfin : ∀ a, IsFinite ((B a).ι ≫ f))
    (hint : ∀ a b, IsFinite ((B a ⊓ B b).ι ≫ f)) : IsSeparated f := by
  have haff (a) : IsAffineOpen (B a) := by
    have := hfin a
    exact isAffine_of_isAffineHom ((B a).ι ≫ f)
  have hab (a b) : IsAffineOpen (B a ⊓ B b) := by
    have := hint a b
    exact isAffine_of_isAffineHom ((B a ⊓ B b).ι ≫ f)
  apply separated_of_affine_open_cover f (Fin m) B
  · simp only [← TopologicalSpace.Opens.coe_iSup, hcover,
      TopologicalSpace.Opens.coe_top]
  · exact haff
  · exact hab
  · intro a b
    have : IsFinite ((B a).ι ≫ f) := hfin a
    have : IsFinite ((B a ⊓ B b).ι ≫ f) := hint a b
    let e := V.homOfLE (inf_le_left : B a ⊓ B b ≤ B a)
    have : IsProper (e ≫ ((B a).ι ≫ f)) := by
      simpa [e] using (inferInstance : IsProper ((B a ⊓ B b).ι ≫ f))
    have : IsProper e := IsProper.of_comp e ((B a).ι ≫ f)
    have : IsClosedImmersion e := IsClosedImmersion.of_isPreimmersion e
      (by simpa only [Set.image_univ] using e.isClosedMap Set.univ isClosed_univ)
    have : IsAffine (B a).toScheme := haff a
    exact closed_overlap_tensor (B a) (B b)

/-- A finite affine open cover of a qcqs etale scheme over an affine base admits a
finite partition of the base into constructible locally closed affine subschemes on
which the charts and their overlaps are finite etale and the whole scheme is separated.
Source: Stacks Project, Etale Cohomology, `lemma-etale-stratified-finite`, proof,
second paragraph (blueprint: lem-weil-pbc-etale-affine-cover-gluing).

Proof:
1. Each affine chart and each overlap is separated, quasi-compact and etale over the
   affine base: use affine-morphism permanence, separated cancellation, qcqs permanence,
   and etale composition (`lem-weil-pbc-affine-morphism-permanence`,
   `lem-weil-pbc-separated-cancellation`, `lem-weil-pbc-qcqs-morphism-permanence`,
   `lem-weil-pbc-proper-fp-permanence`, `definition-torsion-sheaves--3`).
2. Apply `lem-weil-pbc-etale-separated-stratified-finite` to each chart and overlap.
3. Take a common refinement (`lemma-constructible-common-refinement`); its images are
   finite intersections of constructible locally closed sets, and finite etaleness
   persists by base change (`def-weil-pbc-finite-etale-category`, `def-pc-fibre-product`).
4. Refine into affine pieces with `lem-weil-pbc-immersion-affine-constructible-pieces`.
   Again finite etaleness persists by base change.
5. Identify the pulled-back charts and overlaps with opens of the pulled-back scheme
   (`lem-weil-pbc-open-fibre-product`). Finite morphisms over the affine stratum make
   them affine, proper and separated (`lem-weil-pbc-finite-morphism-permanence`,
   `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-proper-fp-permanence`).
6. Each overlap inclusion into a chart is proper by
   `lem-weil-pbc-proper-over-separated`, and hence a closed immersion by
   `lem-weil-pbc-proper-immersion-closed`. Its restriction on sections is surjective
   (`lem-weil-pbc-closed-immersion-affine-cover-criterion`); consequently the map from
   the tensor product of the sections of the two charts is surjective as well.
7. Apply `lem-weil-pbc-separated-affine-cover-criterion` to conclude separatedness. -/
theorem exists_etale_affine_cover_stratification
    {X U : Scheme.{u}} [IsAffine X] [CompactSpace U] [QuasiSeparatedSpace U]
    (j : U ⟶ X) [Etale j] (m : ℕ) (A : Fin m → U.Opens)
    (hA : ∀ a : Fin m, IsAffineOpen (A a)) (hcover : ⨆ a : Fin m, A a = ⊤) :
    ∃ (n : ℕ) (S : Fin n → Scheme.{u}) (ι : ∀ i : Fin n, S i ⟶ X),
      (∀ i : Fin n, IsAffine (S i) ∧ IsImmersion (ι i) ∧
        Topology.IsConstructible (Set.range (ι i))) ∧
      Pairwise (fun i k : Fin n ↦ Disjoint (Set.range (ι i)) (Set.range (ι k))) ∧
      (⋃ i : Fin n, Set.range (ι i)) = Set.univ ∧
      (∀ (i : Fin n) (a : Fin m),
        IsFinite (pullback.snd ((A a).ι ≫ j) (ι i)) ∧
        Etale (pullback.snd ((A a).ι ≫ j) (ι i))) ∧
      (∀ (i : Fin n) (a b : Fin m),
        IsFinite (pullback.snd ((A a ⊓ A b).ι ≫ j) (ι i)) ∧
        Etale (pullback.snd ((A a ⊓ A b).ι ≫ j) (ι i))) ∧
      (∀ i : Fin n, IsSeparated (pullback.snd j (ι i))) := by
  classical
  let W (c : Fin (m * m)) := (A (finProdFinEquiv.symm c).1 ⊓
    A (finProdFinEquiv.symm c).2).toScheme
  let f (c : Fin (m * m)) : W c ⟶ X :=
    (A (finProdFinEquiv.symm c).1 ⊓ A (finProdFinEquiv.symm c).2).ι ≫ j
  have hcompact (a b : Fin m) : CompactSpace (A a ⊓ A b).toScheme := by
    have hc : IsCompact ((A a ⊓ A b : U.Opens) : Set U) := by
      exact @QuasiSeparatedSpace.inter_isCompact U _ _ (A a : Set U) (A b : Set U)
        (A a).isOpen (hA a).isCompact (A b).isOpen (hA b).isCompact
    exact isCompact_iff_compactSpace.mp hc
  have hsep (a b : Fin m) : IsSeparated ((A a ⊓ A b).ι ≫ j) := by
    have : IsAffine (A a).toScheme := hA a
    have he : U.homOfLE (inf_le_left : A a ⊓ A b ≤ A a) ≫ ((A a).ι ≫ j) =
        (A a ⊓ A b).ι ≫ j := by simp
    rw [← he]
    infer_instance
  have (c : Fin (m * m)) : CompactSpace (W c) := hcompact _ _
  have (c : Fin (m * m)) : Etale (f c) := by dsimp [f]; infer_instance
  have (c : Fin (m * m)) : IsSeparated (f c) := hsep _ _
  have (c : Fin (m * m)) : QuasiCompact (f c) := inferInstance
  obtain ⟨R, hR⟩ := common_finite_strata (m * m) W f
  obtain ⟨n, S, ι, hS, hdis, hcov, hfactor⟩ := affine_refine_strata R
  have hfin (i : Fin n) (a b : Fin m) :
      IsFinite (pullback.snd ((A a ⊓ A b).ι ≫ j) (ι i)) := by
    obtain ⟨k, κ, hk⟩ := hfactor i
    let P (ab : Fin m × Fin m) : Prop :=
      IsFinite (pullback.snd ((A ab.1 ⊓ A ab.2).ι ≫ j) (R.immersion k))
    have h : P (finProdFinEquiv.symm (finProdFinEquiv (a, b))) :=
      hR k (finProdFinEquiv (a, b))
    have : IsFinite (pullback.snd ((A a ⊓ A b).ι ≫ j) (R.immersion k)) :=
      (congrArg P (finProdFinEquiv.symm_apply_apply (a, b))).mp h
    rw [hk]
    exact finite_snd_comp _ _ _
  have hchart (i : Fin n) (a : Fin m) :
      IsFinite (pullback.snd ((A a).ι ≫ j) (ι i)) := by
    have h := hfin i a a
    rw [inf_idem] at h
    exact h
  refine ⟨n, S, ι, hS, hdis, hcov, ?_, ?_, ?_⟩
  · intro i a
    exact ⟨hchart i a, inferInstance⟩
  · intro i a b
    exact ⟨hfin i a b, inferInstance⟩
  · intro i
    have : IsAffine (S i) := (hS i).1
    let p := pullback.fst j (ι i)
    let B (a : Fin m) := p ⁻¹ᵁ A a
    apply separated_of_finite_charts (pullback.snd j (ι i)) m B
    · change (⨆ a, p ⁻¹ᵁ A a) = ⊤
      rw [← p.preimage_iSup, hcover]
      rfl
    · intro a
      have := hchart i a
      exact chart_pullback_finite j (ι i) (A a)
    · intro a b
      have := hfin i a b
      change IsFinite ((p ⁻¹ᵁ A a ⊓ p ⁻¹ᵁ A b).ι ≫ pullback.snd j (ι i))
      exact chart_pullback_finite j (ι i) (A a ⊓ A b)

end AlgebraicGeometry
