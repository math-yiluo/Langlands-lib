/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The projective line over a field is a smooth integral curve

## Main statements

- `AlgebraicGeometry.ProjectiveLine.smoothOfRelativeDimension_one`: `ℙ¹_S ⟶ S` is smooth of
  relative dimension one; it is covered by the two standard opens, each an affine line.
- `AlgebraicGeometry.ProjectiveLine.isIntegral`: `ℙ¹_k` is integral for a field `k`.
- `AlgebraicGeometry.ProjectiveLine.homOfSections_eq_SpecMap_comp`: the `K`-point `[1 : t]` of
  `ℙ¹_k` is `Spec` of `k[T] → K`, `T ↦ t`, in the chart `D₊(T₀)`.
- `AlgebraicGeometry.ProjectiveLine.not_isClosed_homOfSections`: for `t` transcendental over
  `k`, the point `[1 : t]` of `ℙ¹_k` is not closed.
- `AlgebraicGeometry.ProjectiveLine.fieldRange_descResidueField_homOfSections`: the residue field
  of `ℙ¹_k` at `[1 : t]` embeds into `K` with image `k(t)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

/-- The projective line `ℙ¹_S ⟶ S` is smooth of relative dimension one: on the standard open
`D₊(Tᵢ)` it is the affine line `𝔸¹_S`. -/
instance smoothOfRelativeDimension_one (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (ProjectiveLine S ↘ S) := by
  refine smoothOfRelativeDimension_of_forall_exists_mem _ 1 fun y ↦ ?_
  have : y ∈ (⊤ : (ProjectiveLine S).Opens) := trivial
  rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨_, hi, ?_⟩
  rw [← ProjectiveSpace.standardOpenIso_hom_over]
  have h : Nat.card {j : ULift.{u} (Fin 2) // j ≠ i} = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_ulift]
    simp
  have := AffineSpace.smoothOfRelativeDimension_over {j : ULift.{u} (Fin 2) // j ≠ i} S
  rw [h] at this
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The projective line over a field is connected: its two standard opens are affine lines,
and they meet. -/
instance connectedSpace (k : Type u) [Field k] :
    ConnectedSpace (ProjectiveLine (Spec (.of k))) := by
  have hs : Ideal.span (Set.range (fun _ : ULift.{u} (Fin 2) ↦
      (1 : Γ(Spec (.of k), ⊤)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) isUnit_one
  let x : ProjectiveLine (Spec (.of k)) :=
    ProjectiveSpace.homOfSections (𝟙 _) _ hs (IsLocalRing.closedPoint k)
  have hx (i) : x ∈ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i := by
    have h : IsLocalRing.closedPoint k ∈ ProjectiveSpace.homOfSections (𝟙 _) _ hs ⁻¹ᵁ
        ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i := by
      rw [ProjectiveSpace.homOfSections_preimage_standardOpen, Scheme.basicOpen_of_isUnit _
        isUnit_one]
      trivial
    exact h
  have hconn (i) : _root_.IsConnected ((ProjectiveSpace.standardOpen (ULift.{u} (Fin 2))
      (Spec (.of k)) i : (ProjectiveLine (Spec (.of k))).Opens) :
        Set (ProjectiveLine (Spec (.of k)))) := by
    let e := ProjectiveSpace.standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) i ≪≫
      AffineSpace.SpecIso _ (.of k)
    have : (Set.range (e.inv ≫
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i).ι)) =
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i : Set _) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        show Set.range e.inv = Set.univ from Set.range_eq_univ.mpr e.inv.homeomorph.surjective,
        Set.image_univ, Scheme.Opens.range_ι]
    rw [← this]
    exact isConnected_range (e.inv ≫ _).continuous
  refine connectedSpace_iff_univ.mpr ⟨⟨x, trivial⟩, ?_⟩
  have : (Set.univ : Set (ProjectiveLine (Spec (.of k)))) =
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ : Set _) ∪
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨1⟩ : Set _) := by
    refine (Set.eq_univ_of_forall fun y ↦ ?_).symm
    have : y ∈ (⊤ : (ProjectiveLine (Spec (.of k))).Opens) := trivial
    rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
    obtain ⟨⟨i⟩, hi⟩ := this
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  rw [this]
  exact ((hconn _).union ⟨x, hx _, hx _⟩ (hconn _)).isPreconnected

/-- The projective line over a field is integral. -/
instance isIntegral (k : Type u) [Field k] : IsIntegral (ProjectiveLine (Spec (.of k))) := by
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := IsRegular.of_smooth (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  exact IsRegular.isIntegral _

/-- The projective line over a field is geometrically connected: its base change to a field `K`
is the projective line over `K` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`), which is
connected. -/
instance geometricallyConnected (k : Type u) [Field k] :
    GeometricallyConnected (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have e : Z ≅ ProjectiveLine (Spec (.of K)) :=
    h.isoIsPullback _ _ (ProjectiveSpace.isPullback_map _ y)
  exact (Scheme.homeoOfIso e.symm).connectedSpace_iff.1 inferInstance

end AlgebraicGeometry.ProjectiveLine

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

/-- **The `K`-point `[1 : t]` in the chart `D₊(T₀)`.** For a field `K` over `k` and `t ∈ K`, the
`K`-point `[1 : t]` of `ℙ¹_k` factors through the chart `D₊(T₀) ≅ Spec k[T]` as `Spec` of the
evaluation `k[T] → K`, `T ↦ t`. -/
theorem homOfSections_eq_SpecMap_comp {k K : Type u} [Field k] [Field K] (φ : k →+* K) (t : K)
    (hs : Ideal.span (Set.range fun i : ULift.{u} (Fin 2) ↦
      (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) = ⊤) :
    homOfSections (Spec.map (CommRingCat.ofHom φ))
      (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) hs =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom φ
        (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t))) ≫
        (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ ≪≫
          AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).inv ≫
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩).ι := by
  set s := fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)
  have hs0 : s ⟨0⟩ = 1 := by simp [s]
  have hB : (Spec (.of K)).basicOpen (s ⟨0⟩) = ⊤ := by
    rw [hs0]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have : IsIso ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι := Scheme.Opens.isIso_ι_of_eq_top hB
  let r : Spec (.of K) ⟶ Spec (.of (MvPolynomial {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} k)) :=
    inv ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫
      (homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs).resLE
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩) ((Spec (.of K)).basicOpen (s ⟨0⟩))
        (homOfSections_preimage_standardOpen _ s hs ⟨0⟩).ge ≫
      (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩).hom ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom
  have hover : r ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom φ) := by
    have e : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        𝔸({j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}; Spec (.of k)) ↘ Spec (.of k) := by
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
    simp only [r, Category.assoc, e, standardOpenIso_hom_over, homOfSections_resLE_ι_over,
      IsIso.inv_hom_id_assoc]
  have hX (j : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}) :
      r.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = (Scheme.ΓSpecIso _).inv t := by
    have h₁ : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom.appTop
        ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = AffineSpace.coord _ j := by
      rw [← AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      rfl
    have h₂ := homOfSections_resLE_standardOpenIso_hom (Spec.map (CommRingCat.ofHom φ)) s hs
      ⟨0⟩
    have h₃ : (Spec (.of K)).divBasicOpen (s j.1) (s ⟨0⟩) =
        ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι.appTop ((Scheme.ΓSpecIso _).inv t) := by
      have hj : j.1 = ⟨1⟩ := by
        obtain ⟨⟨a⟩, ha⟩ := j
        have : a = 1 := by grind
        subst this; rfl
      have h1 : ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι.appTop (s ⟨0⟩) = 1 :=
        (congrArg _ hs0).trans (map_one _)
      have := Scheme.divBasicOpen_mul_self (Spec (.of K)) (s j.1) (s ⟨0⟩)
      rw [h1, mul_one] at this
      rw [this, hj]
      rfl
    have hr : r = inv ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫ AffineSpace.homOfVector
        (((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫ Spec.map (CommRingCat.ofHom φ))
        (fun j ↦ (Spec (.of K)).divBasicOpen (s j.1) (s ⟨0⟩)) ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom := by
      simp only [r, ← h₂, Category.assoc]
    rw [hr, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, h₁, AffineSpace.homOfVector_appTop_coord, h₃,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id,
      Scheme.Hom.id_appTop]
    rfl
  let ψ := MvPolynomial.eval₂Hom φ (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t)
  have hψ : r = Spec.map (CommRingCat.ofHom ψ) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext1
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun j ↦ ?_)
    · have h := congrArg (fun f ↦ f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) hover
      have e₁ : (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ :=
          {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}) (R := k)))).appTop
          ((Scheme.ΓSpecIso (.of k)).inv c) = (Scheme.ΓSpecIso _).inv (MvPolynomial.C c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      have e₂ : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) =
          (Scheme.ΓSpecIso (.of K)).inv (φ c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e₁, e₂] at h
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, h]
      simp [ψ]
    · rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hX j]
      simp [ψ]
  rw [← hψ]
  simp only [r, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Hom.resLE_comp_ι, IsIso.inv_hom_id_assoc]
  rfl

/-- **A `K`-point of `ℙ¹` in a standard chart.** For a field `K` over `k` and homogeneous
coordinates `v : Fin 2 → K` with `v i ≠ 0`, the `K`-point `[v₀ : v₁]` of `ℙ¹_k` factors through
the chart `D₊(Tᵢ) ≅ Spec k[T]` as `Spec` of the evaluation `T ↦ v_j / v_i` (`j ≠ i`). -/
theorem homOfSections_eq_SpecMap_comp_of_ne_zero {k K : Type u} [Field k] [Field K]
    (φ : k →+* K) (v : ULift.{u} (Fin 2) → K) (i : ULift.{u} (Fin 2)) (hvi : v i ≠ 0)
    (hs : Ideal.span (Set.range fun j : ULift.{u} (Fin 2) ↦
      (Scheme.ΓSpecIso (.of K)).inv (v j)) = ⊤) :
    homOfSections (Spec.map (CommRingCat.ofHom φ))
      (fun j : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (v j)) hs =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom φ
        (fun j : {j : ULift.{u} (Fin 2) // j ≠ i} ↦ v j / v i))) ≫
        (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) i ≪≫
          AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ i} (.of k)).inv ≫
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i).ι := by
  set s := fun j : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (v j)
  have hsi : IsUnit (s i) := (Ne.isUnit hvi).map _
  have hB : (Spec (.of K)).basicOpen (s i) = ⊤ := Scheme.basicOpen_of_isUnit _ hsi
  have : IsIso ((Spec (.of K)).basicOpen (s i)).ι := Scheme.Opens.isIso_ι_of_eq_top hB
  let r : Spec (.of K) ⟶ Spec (.of (MvPolynomial {j : ULift.{u} (Fin 2) // j ≠ i} k)) :=
    inv ((Spec (.of K)).basicOpen (s i)).ι ≫
      (homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs).resLE
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i) ((Spec (.of K)).basicOpen (s i))
        (homOfSections_preimage_standardOpen _ s hs i).ge ≫
      (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) i).hom ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ i} (.of k)).hom
  have hover : r ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom φ) := by
    have e : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ i} (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        𝔸({j : ULift.{u} (Fin 2) // j ≠ i}; Spec (.of k)) ↘ Spec (.of k) := by
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
    simp only [r, Category.assoc, e, standardOpenIso_hom_over, homOfSections_resLE_ι_over,
      IsIso.inv_hom_id_assoc]
  have hX (j : {j : ULift.{u} (Fin 2) // j ≠ i}) :
      r.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) =
        (Scheme.ΓSpecIso _).inv (v j / v i) := by
    have h₁ : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ i} (.of k)).hom.appTop
        ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = AffineSpace.coord _ j := by
      rw [← AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      rfl
    have h₂ := homOfSections_resLE_standardOpenIso_hom (Spec.map (CommRingCat.ofHom φ)) s hs i
    have h₃ : (Spec (.of K)).divBasicOpen (s j.1) (s i) =
        ((Spec (.of K)).basicOpen (s i)).ι.appTop ((Scheme.ΓSpecIso _).inv (v j / v i)) := by
      have hu := (Spec (.of K)).isUnit_ι_appTop_basicOpen (s i)
      have := Scheme.divBasicOpen_mul_self (Spec (.of K)) (s j.1) (s i)
      refine hu.mul_right_cancel (this.trans ?_)
      rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hvi]
    have hr : r = inv ((Spec (.of K)).basicOpen (s i)).ι ≫
        ((homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs).resLE
          (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i) ((Spec (.of K)).basicOpen (s i))
          (homOfSections_preimage_standardOpen _ s hs i).ge ≫
        (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) i).hom) ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ i} (.of k)).hom := by
      simp only [r, Category.assoc]
    rw [h₂] at hr
    rw [hr, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, h₁, AffineSpace.homOfVector_appTop_coord, h₃,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id,
      Scheme.Hom.id_appTop]
    rfl
  let ψ := MvPolynomial.eval₂Hom φ (fun j : {j : ULift.{u} (Fin 2) // j ≠ i} ↦ v j / v i)
  have hψ : r = Spec.map (CommRingCat.ofHom ψ) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext1
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun j ↦ ?_)
    · have h := congrArg (fun f ↦ f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) hover
      have e₁ : (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ :=
          {j : ULift.{u} (Fin 2) // j ≠ i}) (R := k)))).appTop
          ((Scheme.ΓSpecIso (.of k)).inv c) = (Scheme.ΓSpecIso _).inv (MvPolynomial.C c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      have e₂ : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) =
          (Scheme.ΓSpecIso (.of K)).inv (φ c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e₁, e₂] at h
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, h]
      simp [ψ]
    · rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hX j]
      simp [ψ]
  rw [← hψ]
  simp only [r, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Hom.resLE_comp_ι, IsIso.inv_hom_id_assoc]
  rfl

/-- **A transcendental point of `ℙ¹` is not closed.** Let `K` be a field over `k` and `t ∈ K`
transcendental over `k`. The `K`-point `[1 : t]` of `ℙ¹_k` is not a closed point: in the chart
`D₊(T₀) = Spec k[T]` it is the prime `ker (T ↦ t) = 0`, which is not maximal. -/
theorem not_isClosed_homOfSections {k K : Type u} [Field k] [Field K] (φ : k →+* K) (t : K)
    (ht : letI := φ.toAlgebra; Transcendental k t)
    (hs : Ideal.span (Set.range fun i : ULift.{u} (Fin 2) ↦
      (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) = ⊤) (z : Spec (.of K)) :
    ¬ IsClosed
      {homOfSections (Spec.map (CommRingCat.ofHom φ))
        (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) hs z} := by
  set s := fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)
  have hs0 : s ⟨0⟩ = 1 := by simp [s]
  have hB : (Spec (.of K)).basicOpen (s ⟨0⟩) = ⊤ := by
    rw [hs0]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have : IsIso ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι := Scheme.Opens.isIso_ι_of_eq_top hB
  let r : Spec (.of K) ⟶ Spec (.of (MvPolynomial {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} k)) :=
    inv ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫
      (homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs).resLE
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩) ((Spec (.of K)).basicOpen (s ⟨0⟩))
        (homOfSections_preimage_standardOpen _ s hs ⟨0⟩).ge ≫
      (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩).hom ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom
  have hover : r ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom φ) := by
    have e : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        𝔸({j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}; Spec (.of k)) ↘ Spec (.of k) := by
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
    simp only [r, Category.assoc, e, standardOpenIso_hom_over, homOfSections_resLE_ι_over,
      IsIso.inv_hom_id_assoc]
  have hX (j : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}) :
      r.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = (Scheme.ΓSpecIso _).inv t := by
    have h₁ : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom.appTop
        ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = AffineSpace.coord _ j := by
      rw [← AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      rfl
    have h₂ := homOfSections_resLE_standardOpenIso_hom (Spec.map (CommRingCat.ofHom φ)) s hs
      ⟨0⟩
    have h₃ : (Spec (.of K)).divBasicOpen (s j.1) (s ⟨0⟩) =
        ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι.appTop ((Scheme.ΓSpecIso _).inv t) := by
      have hj : j.1 = ⟨1⟩ := by
        obtain ⟨⟨a⟩, ha⟩ := j
        have : a = 1 := by grind
        subst this; rfl
      have h1 : ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι.appTop (s ⟨0⟩) = 1 :=
        (congrArg _ hs0).trans (map_one _)
      have := Scheme.divBasicOpen_mul_self (Spec (.of K)) (s j.1) (s ⟨0⟩)
      rw [h1, mul_one] at this
      rw [this, hj]
      rfl
    have hr : r = inv ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫ AffineSpace.homOfVector
        (((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫ Spec.map (CommRingCat.ofHom φ))
        (fun j ↦ (Spec (.of K)).divBasicOpen (s j.1) (s ⟨0⟩)) ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom := by
      simp only [r, ← h₂, Category.assoc]
    rw [hr, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, h₁, AffineSpace.homOfVector_appTop_coord, h₃,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id,
      Scheme.Hom.id_appTop]
    rfl
  let ψ := MvPolynomial.eval₂Hom φ (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t)
  have hψ : r = Spec.map (CommRingCat.ofHom ψ) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext1
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun j ↦ ?_)
    · have h := congrArg (fun f ↦ f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) hover
      have e₁ : (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ :=
          {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}) (R := k)))).appTop
          ((Scheme.ΓSpecIso (.of k)).inv c) = (Scheme.ΓSpecIso _).inv (MvPolynomial.C c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      have e₂ : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) =
          (Scheme.ΓSpecIso (.of K)).inv (φ c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e₁, e₂] at h
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, h]
      simp [ψ]
    · rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hX j]
      simp [ψ]
  have hinj : Function.Injective ψ := by
    let := φ.toAlgebra
    have : AlgebraicIndependent k (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t) := by
      have : Unique {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} :=
        ⟨⟨⟨⟨1⟩, by decide⟩⟩, fun ⟨⟨a⟩, ha⟩ ↦ by
          have : a = 1 := by grind
          subst this; rfl⟩
      exact algebraicIndependent_unique_type_iff.mpr ht
    exact this
  intro hz
  set g := homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs
  let D := standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩
  let B := (Spec (.of K)).basicOpen (s ⟨0⟩)
  let w : D.toScheme := g.resLE D B (homOfSections_preimage_standardOpen _ s hs ⟨0⟩).ge
    (inv B.ι z)
  have hw : D.ι w = g z := by
    simp only [w]
    rw [← Scheme.Hom.comp_apply]
    simp only [D, B, Scheme.Hom.resLE_comp_ι]
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
  have hwc : IsClosed ({w} : Set D.toScheme) := by
    have : ({w} : Set D.toScheme) = D.ι ⁻¹' {g z} := by
      ext a
      simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hw]
      exact D.ι.isOpenEmbedding.injective.eq_iff.symm
    rw [this]
    exact hz.preimage D.ι.continuous
  let e := standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ ≪≫
    AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)
  have hrz : r z = e.hom w := rfl
  have hc : IsClosed ({r z} : Set _) := by
    rw [hrz, ← Set.image_singleton]
    exact e.hom.homeomorph.isClosedMap _ hwc
  replace hc : (r z).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hc
  have hbot : (r z).asIdeal = ⊥ := by
    rw [hψ]
    change Ideal.comap ψ z.asIdeal = ⊥
    have : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
    rw [this, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ψ).mp hinj]
  rw [hbot, ← Ring.isField_iff_maximal_bot] at hc
  have : Unique {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} :=
    ⟨⟨⟨⟨1⟩, by decide⟩⟩, fun ⟨⟨a⟩, ha⟩ ↦ by
      have : a = 1 := by grind
      subst this; rfl⟩
  exact Polynomial.not_isField k
    ((MvPolynomial.uniqueAlgEquiv (R := k)
      {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}).symm.toMulEquiv.isField hc)

end AlgebraicGeometry.ProjectiveLine

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

/-- The field generated by the image of a ring map `ψ : A → K` from a ring to a field contains
the image of every residue field of `Spec A` under the induced embedding: for a `K`-point
`Spec.map ψ`, the image of `κ(ψ⁻¹(0)) ⟶ K` is the field generated by `ψ(A)`. -/
theorem fieldRange_descResidueField_SpecMap {A : CommRingCat.{u}} {K : Type u} [Field K]
    (ψ : A ⟶ .of K) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (Spec.map ψ))).hom.fieldRange =
      Subfield.closure (Set.range ψ) := by
  set y := (Spec.map ψ) (IsLocalRing.closedPoint K)
  set f := Scheme.stalkClosedPointTo (Spec.map ψ)
  have hres : (Spec A).residue y ≫ Scheme.descResidueField f = f :=
    Scheme.residue_descResidueField f
  have hgerm (a : A) : f ((Spec A).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso A).inv a)) =
      ψ a := by
    rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    obtain ⟨s, rfl⟩ := (Spec A).residue_surjective y r
    rw [← CommRingCat.comp_apply, hres]
    let := (Spec A).presheaf.algebra_section_stalk (U := ⊤) ⟨y, trivial⟩
    have := (isAffineOpen_top (Spec A)).isLocalization_stalk ⟨y, trivial⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective
      ((isAffineOpen_top (Spec A)).primeIdealOf ⟨y, trivial⟩).asIdeal.primeCompl s
    have hb := IsLocalization.map_units ((Spec A).presheaf.stalk y) b
    have hmk := IsLocalization.mk'_spec ((Spec A).presheaf.stalk y) a b
    have hfb : f (algebraMap _ ((Spec A).presheaf.stalk y) (b : Γ(Spec A, ⊤))) ≠ 0 :=
      ((hb.map f.hom).ne_zero)
    have e : f (IsLocalization.mk' ((Spec A).presheaf.stalk y) a b) =
        f (algebraMap _ _ a) * (f (algebraMap _ _ (b : Γ(Spec A, ⊤))))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hfb, ← map_mul, hmk]
    rw [e]
    have hmem (c : Γ(Spec A, ⊤)) : f (algebraMap _ ((Spec A).presheaf.stalk y) c) ∈
        Subfield.closure (Set.range ψ) := by
      rw [show c = (Scheme.ΓSpecIso A).inv ((Scheme.ΓSpecIso A).hom c) from
        (Iso.hom_inv_id_apply _ _).symm]
      change f ((Spec A).presheaf.germ ⊤ y trivial _) ∈ _
      rw [hgerm]
      exact Subfield.subset_closure ⟨_, rfl⟩
    exact mul_mem (hmem a) (inv_mem (hmem b))
  · refine Subfield.closure_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    refine ⟨(Spec A).residue y ((Spec A).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso A).inv a)),
      ?_⟩
    rw [← CommRingCat.comp_apply, hres, hgerm]

/-- **The residue field of the point `[1 : t]`.** For a field `K` over `k` and `t ∈ K`, the
residue field of `ℙ¹_k` at the image of the `K`-point `[1 : t]` embeds into `K` with image the
subfield `k(t)` generated by `k` and `t`. -/
theorem fieldRange_descResidueField_homOfSections {k K : Type u} [Field k] [Field K]
    (φ : k →+* K) (t : K)
    (hs : Ideal.span (Set.range fun i : ULift.{u} (Fin 2) ↦
      (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) = ⊤) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (homOfSections
      (Spec.map (CommRingCat.ofHom φ))
      (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down))
        hs))).hom.fieldRange =
      Subfield.closure (Set.range φ ∪ {t}) := by
  set j := (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ ≪≫
    AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).inv ≫
      (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩).ι
  set ψ := MvPolynomial.eval₂Hom φ (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t)
  suffices key : ∀ h : Spec (.of K) ⟶ ProjectiveLine (Spec (.of k)),
      h = Spec.map (CommRingCat.ofHom ψ) ≫ j →
        (Scheme.descResidueField (Scheme.stalkClosedPointTo h)).hom.fieldRange =
          Subfield.closure (Set.range φ ∪ {t}) from
    key _ (homOfSections_eq_SpecMap_comp φ t hs)
  rintro h rfl
  have hc := Scheme.descResidueField_stalkClosedPointTo_comp (f := j)
    (Spec.map (CommRingCat.ofHom ψ))
  erw [hc]
  have hsurj := (ConcreteCategory.bijective_of_isIso (j.residueFieldMap
    ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint K)))).2
  have e : (j.residueFieldMap ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint K)) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom ψ)))).hom.fieldRange =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom ψ)))).hom.fieldRange := by
    ext y
    simp only [RingHom.mem_fieldRange, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := hsurj x
      exact ⟨x', rfl⟩
  refine e.trans ?_
  rw [fieldRange_descResidueField_SpecMap]
  apply le_antisymm
  · refine Subfield.closure_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    change ψ a ∈ _
    induction a using MvPolynomial.induction_on with
    | C c => exact Subfield.subset_closure (Or.inl ⟨c, by simp [ψ]⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      exact mul_mem hp (Subfield.subset_closure (Or.inr (by simp [ψ])))
  · refine Subfield.closure_le.mpr ?_
    rintro _ (⟨c, rfl⟩ | h)
    · exact Subfield.subset_closure ⟨MvPolynomial.C c, by simp [ψ]⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact Subfield.subset_closure ⟨MvPolynomial.X ⟨⟨1⟩, by decide⟩, by simp [ψ]⟩

end AlgebraicGeometry.ProjectiveLine
