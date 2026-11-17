import Langlands.Geometry.Analytic.AnalytificationCenter
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The quotient argument for scheme analytification gluing

The local restriction hypotheses in this file are explicit prerequisites.
-/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.GluingReduction

open CategoryTheory _root_.AlgebraicGeometry Topology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The local inputs to the quotient gluing argument: restriction maps preserve
identity and composition, are open embeddings, and have the expected center range. -/
def RestrictionGluingData : Prop :=
  (∀ (U : X.affineOpens) (x : LocalSpace K f U), localMap K f (le_refl U.1) x = x) ∧
  (∀ {U V W : X.affineOpens} (hVU : (V : X.Opens) ≤ U) (hWV : (W : X.Opens) ≤ V)
    (x : LocalSpace K f W),
    localMap K f hVU (localMap K f hWV x) = localMap K f (hWV.trans hVU) x) ∧
  (∀ {U V : X.affineOpens} (h : (V : X.Opens) ≤ U),
    IsOpenEmbedding (localMap K f h)) ∧
  (∀ {U V : X.affineOpens} (h : (V : X.Opens) ≤ U),
    Set.range (localMap K f h) = localCenter K f U ⁻¹' (V : Set X))

/-- Two chart points admit a common affine refinement if they are restrictions
of one point in an affine open contained in both charts. -/
def CommonRefinement (p q : Σ U : X.affineOpens, LocalSpace K f U) : Prop :=
  ∃ (W : X.affineOpens) (hWp : (W : X.Opens) ≤ p.1) (hWq : (W : X.Opens) ≤ q.1)
    (z : LocalSpace K f W), localMap K f hWp z = p.2 ∧ localMap K f hWq z = q.2

variable {K f}

theorem commonRefinement_refl (D : RestrictionGluingData K f)
    (p : Σ U : X.affineOpens, LocalSpace K f U) : CommonRefinement K f p p :=
  ⟨p.1, le_rfl, le_rfl, p.2, D.1 p.1 p.2, D.1 p.1 p.2⟩

theorem commonRefinement_symm {p q : Σ U : X.affineOpens, LocalSpace K f U}
    (h : CommonRefinement K f p q) : CommonRefinement K f q p := by
  obtain ⟨W, hWp, hWq, z, hzp, hzq⟩ := h
  exact ⟨W, hWq, hWp, z, hzq, hzp⟩

theorem commonRefinement_trans (D : RestrictionGluingData K f)
    {p q r : Σ U : X.affineOpens, LocalSpace K f U}
    (hpq : CommonRefinement K f p q) (hqr : CommonRefinement K f q r) :
    CommonRefinement K f p r := by
  obtain ⟨A, hAp, hAq, a, hap, haq⟩ := hpq
  obtain ⟨B, hBq, hBr, b, hbq, hbr⟩ := hqr
  have hc : localCenter K f A a = localCenter K f B b := by
    rw [← localCenter_localMap K f hAq a, haq, ← hbq,
      localCenter_localMap K f hBq b]
  have haA : localCenter K f A a ∈ (A : X.Opens) := center_ι_mem K f A a
  have haB : localCenter K f A a ∈ (B : X.Opens) :=
    hc.symm ▸ center_ι_mem K f B b
  obtain ⟨S, hS, haS, hSAB⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    X.isBasis_affineOpens (show localCenter K f A a ∈ (A : X.Opens) ⊓ B from ⟨haA, haB⟩)
  let W : X.affineOpens := ⟨S, hS⟩
  have hWA : (W : X.Opens) ≤ A := hSAB.trans inf_le_left
  have hWB : (W : X.Opens) ≤ B := hSAB.trans inf_le_right
  have ha_range : a ∈ Set.range (localMap K f hWA) := by
    rw [D.2.2.2 hWA]
    exact haS
  have hb_range : b ∈ Set.range (localMap K f hWB) := by
    rw [D.2.2.2 hWB]
    change localCenter K f B b ∈ (W : X.Opens)
    rw [← hc]
    exact haS
  obtain ⟨za, hza⟩ := ha_range
  obtain ⟨zb, hzb⟩ := hb_range
  have hzaq : localMap K f (hWA.trans hAq) za = q.2 := by
    rw [← D.2.1 hAq hWA, hza, haq]
  have hzbq : localMap K f (hWB.trans hBq) zb = q.2 := by
    rw [← D.2.1 hBq hWB, hzb, hbq]
  have hz : za = zb := (D.2.2.1 (hWA.trans hAq)).injective (hzaq.trans hzbq.symm)
  refine ⟨W, hWA.trans hAp, hWB.trans hBr, za, ?_, ?_⟩
  · rw [← D.2.1 hAp hWA, hza, hap]
  · rw [hz, ← D.2.1 hBr hWB, hzb, hbr]

theorem commonRefinement_of_glue (D : RestrictionGluingData K f)
    {p q : Σ U : X.affineOpens, LocalSpace K f U} (h : Glue K f p q) :
    CommonRefinement K f p q := by
  cases h with
  | @mk U V h y => exact ⟨V, le_rfl, h, y, D.1 V y, rfl⟩

theorem commonRefinement_of_eqvGen (D : RestrictionGluingData K f)
    {p q : Σ U : X.affineOpens, LocalSpace K f U} (h : Relation.EqvGen (Glue K f) p q) :
    CommonRefinement K f p q := by
  induction h with
  | rel p q h => exact commonRefinement_of_glue D h
  | refl p => exact commonRefinement_refl D p
  | symm p q h ih => exact commonRefinement_symm ih
  | trans p q r h₁ h₂ ih₁ ih₂ => exact commonRefinement_trans D ih₁ ih₂

/-- Equality in the quotient has a witness in a single common affine chart. -/
theorem ι_eq_iff_common_refinement (D : RestrictionGluingData K f)
    {U V : X.affineOpens} (x : LocalSpace K f U) (y : LocalSpace K f V) :
    ι K f U x = ι K f V y ↔ CommonRefinement K f ⟨U, x⟩ ⟨V, y⟩ := by
  constructor
  · intro h
    exact commonRefinement_of_eqvGen D (Quot.eqvGen_exact h)
  · rintro ⟨W, hWU, hWV, z, hzU, hzV⟩
    dsimp only at hzU hzV
    rw [← hzU, ι_localMap, ← hzV, ι_localMap]

theorem injective_ι (D : RestrictionGluingData K f) (U : X.affineOpens) :
    Function.Injective (ι K f U) := by
  intro x y h
  obtain ⟨W, hWU, hWV, z, hzx, hzy⟩ :=
    (ι_eq_iff_common_refinement D x y).mp h
  exact hzx.symm.trans hzy

theorem preimage_image_ι (D : RestrictionGluingData K f)
    (U V : X.affineOpens) (s : Set (LocalSpace K f U)) :
    ι K f V ⁻¹' (ι K f U '' s) =
      ⋃ (W : X.affineOpens) (hWU : (W : X.Opens) ≤ U) (hWV : (W : X.Opens) ≤ V),
        localMap K f hWV '' (localMap K f hWU ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨W, hWU, hWV, z, hzU, hzV⟩ :=
      (ι_eq_iff_common_refinement D y x).mp hyx
    dsimp only at hzU hzV
    refine Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr
      ⟨hWU, Set.mem_iUnion.mpr ⟨hWV, z, ?_, hzV⟩⟩⟩
    simpa only [Set.mem_preimage, hzU] using hy
  · intro hx
    obtain ⟨W, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hWU, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hWV, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    refine ⟨localMap K f hWU z, hz, ?_⟩
    rw [ι_localMap, ← hzx, ι_localMap]

theorem isOpenMap_ι (D : RestrictionGluingData K f) (U : X.affineOpens) :
    IsOpenMap (ι K f U) := by
  intro s hs
  apply (isOpen_iff K f _).mpr
  intro V
  rw [preimage_image_ι D U V s]
  exact isOpen_iUnion fun W => isOpen_iUnion fun hWU => isOpen_iUnion fun hWV =>
    (D.2.2.1 hWV).isOpenMap _ (hs.preimage (localMap K f hWU).continuous)

/-- Once the local restriction hypotheses hold, all charts are open embeddings
into the actual quotient space. -/
theorem isOpenEmbedding_ι (D : RestrictionGluingData K f) (U : X.affineOpens) :
    IsOpenEmbedding (ι K f U) :=
  .of_continuous_injective_isOpenMap (ι K f U).continuous
    (injective_ι D U) (isOpenMap_ι D U)

theorem range_ι_inter (D : RestrictionGluingData K f) (U V : X.affineOpens) :
    Set.range (ι K f U) ∩ Set.range (ι K f V) =
      ⋃ (W : X.affineOpens) (_ : (W : X.Opens) ≤ (U : X.Opens) ⊓ V),
        Set.range (ι K f W) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨W, hWU, hWV, w, hwU, hwV⟩ :=
      (ι_eq_iff_common_refinement D y z).mp (hy.trans hz.symm)
    dsimp only at hwU hwV
    refine Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr
      ⟨le_inf hWU hWV, w, ?_⟩⟩
    rw [← ι_localMap K f hWU, hwU, hy]
  · intro hx
    obtain ⟨W, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hW, w, hw⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨localMap K f (hW.trans inf_le_left) w,
      (ι_localMap K f _ w).trans hw⟩,
      ⟨localMap K f (hW.trans inf_le_right) w,
      (ι_localMap K f _ w).trans hw⟩⟩

theorem surjective_ι_top [IsAffine X] :
    Function.Surjective (ι K f ⟨⊤, isAffineOpen_top X⟩) := by
  intro x
  obtain ⟨U, y, rfl⟩ := exists_ι K f x
  exact ⟨localMap K f (show (U : X.Opens) ≤ ⊤ from le_top) y, ι_localMap K f _ y⟩

theorem isHomeomorph_ι_top (D : RestrictionGluingData K f) [IsAffine X] :
    IsHomeomorph (ι K f ⟨⊤, isAffineOpen_top X⟩) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(isOpenEmbedding_ι D _).isEmbedding, surjective_ι_top⟩

end Langlands.Analytic.SchemeAnalytification.GluingReduction
