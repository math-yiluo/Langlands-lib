/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Compactification.BoundarySeparationData
public import WeilConjectures.Compactification.EliminationOfIndeterminacy
public import WeilConjectures.Compactification.StrictTransformBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.Topology.Spectral.Prespectral
public import WeilConjectures.Topology.SpectralSpace.ConstructibleSeparation

/-!

# Isomorphism near the closure of a boundary piece

This file proves the **isomorphism near a boundary closure** (Stacks Project Tag 0F3W;
blueprint `thm:0F3W`, `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`):

- `AlgebraicGeometry.exists_admissibleBlowup_isIso_strictTransformMap_near_closure`: a
  proper morphism which is an isomorphism over a neighbourhood of a closed piece `T` of
  `U` acquires, after a `U`-admissible blow-up, a strict transform which is an
  isomorphism over a neighbourhood of the closure of `T`.
- `AlgebraicGeometry.isoNearClosureBlowup`: the blow-up `IsoBl_{U,T}(q)` of blueprint
  `lemma-extending-isomorphism-over-closure-closed--1`, assembled from its named steps
  (constructible separation, separation blow-up, elimination over the separated region, extension of
  the centre, composition), and
  `AlgebraicGeometry.exists_isIso_strictTransformMap_isoNearClosureBlowup`: it does the job.

It is used for the improved comparison projection of the two-open compactification
theorem, and rests on elimination of indeterminacy
(`WeilConjectures.Compactification.EliminationOfIndeterminacy`, Tag 081S).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
namespace AlgebraicGeometry

/-! ### The isomorphism-near-closure construction

The named steps of blueprint `lemma-extending-isomorphism-over-closure-closed--1`, in the form used
by the formal proof. Throughout, `q : Z ⟶ X` is proper, `U` is a quasi-compact open of the qcqs
scheme `X`, `T ⊆ U` is closed in `U`, and `q` is an isomorphism over an open neighbourhood `N`
of `T`; `M = q.maximalIsomorphismOpen` is the maximal open over which `q` is an isomorphism
(`lemma-extending-isomorphism-over-closure-closed--1`), so `E = U \ M` is the blueprint's
exceptional set. -/

section IsoNearClosureConstruction

/-- `T` lies in the maximal isomorphism open of `q`. -/
lemma subset_maximalIsomorphismOpen_of_isIso {X Z : Scheme.{u}} (q : Z ⟶ X) {T : Set X}
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    T ⊆ (q.maximalIsomorphismOpen : Set X) :=
  hTN.trans fun _ hx ↦ q.le_maximalIsomorphismOpen hN hx

/-- The maximal isomorphism open of `q` lies in the image of `q`. -/
lemma maximalIsomorphismOpen_subset_range {X Z : Scheme.{u}} (q : Z ⟶ X) :
    (q.maximalIsomorphismOpen : Set X) ⊆ Set.range q := by
  intro x hx
  have hqM : IsIso (q ∣_ q.maximalIsomorphismOpen) := q.isIso_restrict_maximalIsomorphismOpen
  obtain ⟨z, hz⟩ := (Scheme.homeoOfIso (asIso (q ∣_ q.maximalIsomorphismOpen))).surjective
    ⟨x, hx⟩
  refine ⟨(q ⁻¹ᵁ q.maximalIsomorphismOpen).ι z, ?_⟩
  calc q ((q ⁻¹ᵁ q.maximalIsomorphismOpen).ι z)
      = ((q ⁻¹ᵁ q.maximalIsomorphismOpen).ι ≫ q) z := (Scheme.Hom.comp_apply _ _ _).symm
    _ = ((q ∣_ q.maximalIsomorphismOpen) ≫ q.maximalIsomorphismOpen.ι) z := by
        rw [morphismRestrict_ι]
    _ = q.maximalIsomorphismOpen.ι ((q ∣_ q.maximalIsomorphismOpen) z) :=
        Scheme.Hom.comp_apply _ _ _
    _ = x := congrArg Subtype.val (by simpa using hz)

variable {X Z : Scheme.{u}} {U : X.Opens} (hU : IsCompact (U : Set X)) (q : Z ⟶ X)
  {T : Set X} (hT : IsClosed (U.ι ⁻¹' T)) {N : X.Opens} (hTN : T ⊆ (N : Set X))
  (hN : IsIso (q ∣_ N))

/-- **Step 1 of the isomorphism-near-closure construction: constructible separation data**
`(T_c, E_c)` in `U` of the closed subsets `T` and `E = U \ M`
(`PrespectralSpace.constructibleSeparation`, blueprint
`lemma-extending-isomorphism-over-closure-closed--1`). The two pieces are closed in `U`, have
quasi-compact complements, contain `T` resp. `E`, and are disjoint.
(blueprint: `lemma-extending-isomorphism-over-closure-closed--1`) -/
noncomputable def isoNearClosureSeparation : Set U.toScheme × Set U.toScheme :=
  haveI : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  PrespectralSpace.constructibleSeparation hT
    (q.maximalIsomorphismOpen.isOpen.isClosed_compl.preimage U.ι.continuous)
    (Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h₂ (subset_maximalIsomorphismOpen_of_isIso q hTN hN h₁))

lemma isClosed_isoNearClosureSeparation_fst :
    IsClosed (isoNearClosureSeparation hU q hT hTN hN).1 := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.isClosed_constructibleSeparation_fst _ _ _

lemma isClosed_isoNearClosureSeparation_snd :
    IsClosed (isoNearClosureSeparation hU q hT hTN hN).2 := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.isClosed_constructibleSeparation_snd _ _ _

lemma isCompact_compl_isoNearClosureSeparation_fst :
    IsCompact (isoNearClosureSeparation hU q hT hTN hN).1ᶜ := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.isCompact_compl_constructibleSeparation_fst _ _ _

lemma isCompact_compl_isoNearClosureSeparation_snd :
    IsCompact (isoNearClosureSeparation hU q hT hTN hN).2ᶜ := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.isCompact_compl_constructibleSeparation_snd _ _ _

lemma preimage_subset_isoNearClosureSeparation_fst :
    U.ι ⁻¹' T ⊆ (isoNearClosureSeparation hU q hT hTN hN).1 := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.subset_constructibleSeparation_fst _ _ _

lemma preimage_compl_subset_isoNearClosureSeparation_snd :
    U.ι ⁻¹' (q.maximalIsomorphismOpen : Set X)ᶜ ⊆ (isoNearClosureSeparation hU q hT hTN hN).2 := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.subset_constructibleSeparation_snd _ _ _

lemma disjoint_isoNearClosureSeparation :
    Disjoint (isoNearClosureSeparation hU q hT hTN hN).1
      (isoNearClosureSeparation hU q hT hTN hN).2 := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  exact PrespectralSpace.disjoint_constructibleSeparation _ _ _

/-- The quasi-compact open `V₂ = U \ E_c` of `X`: it contains `T` and `q` is an isomorphism
over it. -/
noncomputable def isoNearClosureIsoLocus : X.Opens :=
  U.ι ''ᵁ (⟨(isoNearClosureSeparation hU q hT hTN hN).2ᶜ,
    (isClosed_isoNearClosureSeparation_snd hU q hT hTN hN).isOpen_compl⟩ : U.toScheme.Opens)

lemma isoNearClosureIsoLocus_le : isoNearClosureIsoLocus hU q hT hTN hN ≤ U := by
  rintro x ⟨y, -, rfl⟩
  have : U.ι y ∈ Set.range U.ι := ⟨y, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

lemma isoNearClosureIsoLocus_le_maximalIsomorphismOpen :
    isoNearClosureIsoLocus hU q hT hTN hN ≤ q.maximalIsomorphismOpen := by
  rintro x ⟨y, hy, rfl⟩
  by_contra hcon
  exact hy (preimage_compl_subset_isoNearClosureSeparation_snd hU q hT hTN hN hcon)

lemma isCompact_isoNearClosureIsoLocus :
    IsCompact (isoNearClosureIsoLocus hU q hT hTN hN : Set X) :=
  (isCompact_compl_isoNearClosureSeparation_snd hU q hT hTN hN).image U.ι.continuous

lemma isIso_restrict_isoNearClosureIsoLocus :
    IsIso (q ∣_ isoNearClosureIsoLocus hU q hT hTN hN) :=
  Scheme.Hom.isIso_restrict_of_le (isoNearClosureIsoLocus_le_maximalIsomorphismOpen hU q hT hTN hN)
    q.isIso_restrict_maximalIsomorphismOpen

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- **Step 2 of the isomorphism-near-closure construction: the separation blow-up**
`X₁ = CSepBl_U(T_c, E_c)` (`constructibleSeparationBlowup`, blueprint
`lemma-separation-closures--1`), in which the closures of the inverse images of
`T_c` and `E_c` are disjoint. (blueprint: `lemma-extending-isomorphism-over-closure-closed--1`) -/
noncomputable def isoNearClosureSeparationBlowup : IsAdmissible X U :=
  constructibleSeparationBlowup hU (isClosed_isoNearClosureSeparation_fst hU q hT hTN hN)
    (isClosed_isoNearClosureSeparation_snd hU q hT hTN hN)
    (isCompact_compl_isoNearClosureSeparation_fst hU q hT hTN hN)
    (isCompact_compl_isoNearClosureSeparation_snd hU q hT hTN hN)
    (disjoint_isoNearClosureSeparation hU q hT hTN hN)

lemma disjoint_closure_isoNearClosureSeparationBlowup :
    Disjoint
      (closure ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹'
        (U.ι '' (isoNearClosureSeparation hU q hT hTN hN).1)))
      (closure ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹'
        (U.ι '' (isoNearClosureSeparation hU q hT hTN hN).2))) :=
  disjoint_closure_preimage_constructibleSeparationBlowup hU _ _ _ _ _

lemma isProper_isoNearClosureSeparationBlowup :
    IsProper (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap :=
  (isoNearClosureSeparationBlowup hU q hT hTN hN).isProper_blowupMap

lemma compactSpace_isoNearClosureSeparationBlowup :
    CompactSpace (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup :=
  have := isProper_isoNearClosureSeparationBlowup hU q hT hTN hN
  QuasiCompact.compactSpace_of_compactSpace
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap

lemma quasiSeparatedSpace_isoNearClosureSeparationBlowup :
    QuasiSeparatedSpace (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup :=
  have := isProper_isoNearClosureSeparationBlowup hU q hT hTN hN
  quasiSeparatedSpace_of_quasiSeparated
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap

/-- **Step 3 of the isomorphism-near-closure construction: a second constructible
separation**, now in `X₁`, of the (disjoint, closed) closures of the inverse images of `T_c`
and `E_c`. -/
noncomputable def isoNearClosureNbhdSeparation :
    Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup ×
      Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup :=
  haveI := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  PrespectralSpace.constructibleSeparation isClosed_closure isClosed_closure
    (disjoint_closure_isoNearClosureSeparationBlowup hU q hT hTN hN)

/-- The quasi-compact open `A ⊆ X₁`, the complement of the second piece of
`isoNearClosureNbhdSeparation`: it contains the closure of the inverse image of `T_c` and
misses the closure of the inverse image of `E_c`. It replaces the blueprint's open
`X₀ = X₁ \ closure(E_c)`, which need not be quasi-compact. -/
noncomputable def isoNearClosureNbhd :
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup.Opens :=
  ⟨(isoNearClosureNbhdSeparation hU q hT hTN hN).2ᶜ, by
    have := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
    exact (PrespectralSpace.isClosed_constructibleSeparation_snd _ _ _).isOpen_compl⟩

lemma isCompact_isoNearClosureNbhd :
    IsCompact (isoNearClosureNbhd hU q hT hTN hN :
      Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup) := by
  have := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  exact PrespectralSpace.isCompact_compl_constructibleSeparation_snd _ _ _

lemma closure_preimage_subset_isoNearClosureNbhd (hTU : T ⊆ (U : Set X)) :
    closure ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹' T) ⊆
      (isoNearClosureNbhd hU q hT hTN hN :
        Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup) := by
  have := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  have hTimg : T ⊆ U.ι '' (isoNearClosureSeparation hU q hT hTN hN).1 := by
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact hTU hx
    exact ⟨y, preimage_subset_isoNearClosureSeparation_fst hU q hT hTN hN hx, rfl⟩
  intro x hx
  have hx₁ := PrespectralSpace.subset_constructibleSeparation_fst isClosed_closure isClosed_closure
    (disjoint_closure_isoNearClosureSeparationBlowup hU q hT hTN hN)
    ((closure_mono (Set.preimage_mono hTimg)) hx)
  exact fun hx₂ ↦ Set.disjoint_left.mp (PrespectralSpace.disjoint_constructibleSeparation
    isClosed_closure isClosed_closure
    (disjoint_closure_isoNearClosureSeparationBlowup hU q hT hTN hN)) hx₁ hx₂

/-- Every point of `A` over `U` lies over `V₂`. -/
lemma mem_isoNearClosureIsoLocus_of_mem_isoNearClosureNbhd
    (x : (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup)
    (hxA : x ∈ (isoNearClosureNbhd hU q hT hTN hN :
      Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup))
    (hxU : (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap x ∈ (U : Set X)) :
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap x ∈
      (isoNearClosureIsoLocus hU q hT hTN hN : Set X) := by
  have := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  by_contra hcon
  obtain ⟨y, hy⟩ : (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap x ∈
      Set.range U.ι := by
    rw [Scheme.Opens.range_ι]; exact hxU
  have hyE : y ∈ (isoNearClosureSeparation hU q hT hTN hN).2 := by
    by_contra hy₂
    exact hcon (hy ▸ ⟨y, hy₂, rfl⟩)
  exact hxA (PrespectralSpace.subset_constructibleSeparation_snd isClosed_closure
    isClosed_closure (disjoint_closure_isoNearClosureSeparationBlowup hU q hT hTN hN)
    (subset_closure (Set.mem_preimage.mpr ⟨y, hyE, hy⟩)))

/-- **Step 4 of the isomorphism-near-closure construction: the canonical lift**
`lam₁ : Bl_{𝓘·𝒪_Z}(Z) ⟶ X₁` of `q` to the separation blow-up `X₁ = Bl_𝓘(X)` (Stacks
Project Tag 0806; it is the strict transform of `q`, Tag 080E). -/
noncomputable def isoNearClosureLift :
    ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap q).blowup ⟶
      (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup :=
  ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.exists_lift_blowup
    (t := ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap q).blowupMap ≫ q)
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap
          q).isInvertible_comap_blowupMap)).choose

lemma isoNearClosureLift_comp :
    isoNearClosureLift hU q hT hTN hN ≫
        (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap =
      ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap q).blowupMap ≫ q :=
  ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.exists_lift_blowup
    (t := ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap q).blowupMap ≫ q)
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap
          q).isInvertible_comap_blowupMap)).choose_spec

variable [IsProper q]

lemma isProper_isoNearClosureLift : IsProper (isoNearClosureLift hU q hT hTN hN) := by
  set B₁ := isoNearClosureSeparationBlowup hU q hT hTN hN
  have hcqft : (B₁.I.comap q).ofFiniteType := B₁.finiteType.comap q
  have : IsProper (B₁.I.comap q).blowupMap :=
    (B₁.I.comap q).isProper_blowupMap fun V ↦ hcqft V le_top
  have := isProper_isoNearClosureSeparationBlowup hU q hT hTN hN
  have : IsProper (isoNearClosureLift hU q hT hTN hN ≫ B₁.I.blowupMap) := by
    rw [isoNearClosureLift_comp]; infer_instance
  exact IsProper.of_comp (isoNearClosureLift hU q hT hTN hN) B₁.I.blowupMap

omit [IsProper q] in
/-- The canonical lift is an isomorphism over the locus above `V₂`. -/
lemma isIso_isoNearClosureLift_restrict :
    IsIso (isoNearClosureLift hU q hT hTN hN ∣_
      ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹ᵁ
        isoNearClosureIsoLocus hU q hT hTN hN)) := by
  set B₁ := isoNearClosureSeparationBlowup hU q hT hTN hN
  set V₂ := isoNearClosureIsoLocus hU q hT hTN hN
  have hdisjV₂ : Disjoint (V₂ : Set X) (B₁.I.support : Set X) :=
    B₁.disjoint_support.mono_left fun _ hx ↦ isoNearClosureIsoLocus_le hU q hT hTN hN hx
  have hπ₁V₂ : IsIso (B₁.I.blowupMap ∣_ V₂) := B₁.I.isIso_blowupMap_restrict hdisjV₂
  have hqV₂ : IsIso (q ∣_ V₂) := isIso_restrict_isoNearClosureIsoLocus hU q hT hTN hN
  have hπZV₂ : IsIso ((B₁.I.comap q).blowupMap ∣_ (q ⁻¹ᵁ V₂)) := by
    refine (B₁.I.comap q).isIso_blowupMap_restrict ?_
    rw [Set.disjoint_left]
    intro z hz hzs
    rw [Scheme.IdealSheafData.coe_support_comap] at hzs
    exact Set.disjoint_left.mp hdisjV₂ hz hzs
  refine isIso_morphismRestrict_of_comp _ B₁.I.blowupMap
    (isoNearClosureLift_comp hU q hT hTN hN) V₂ hπ₁V₂ ?_
  rw [morphismRestrict_comp]
  infer_instance

/-- **Step 5 of the isomorphism-near-closure construction: elimination over the separated
region**: the elimination-of-indeterminacy blow-up (`eliminationBlowup`, blueprint
`theorem-elimination-indeterminacy--1`) of the canonical lift `lam₁` over the quasi-compact
open of `X₁` above `V₂`, over which `lam₁` is an isomorphism.
(blueprint: `lemma-extending-isomorphism-over-closure-closed--1`) -/
noncomputable def isoNearClosureElimination :
    IsAdmissible (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup
      ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹ᵁ
        isoNearClosureIsoLocus hU q hT hTN hN) :=
  haveI := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  haveI := quasiSeparatedSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  haveI := isProper_isoNearClosureSeparationBlowup hU q hT hTN hN
  haveI := isProper_isoNearClosureLift hU q hT hTN hN
  eliminationBlowup ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap.isCompact_preimage
    (isCompact_isoNearClosureIsoLocus hU q hT hTN hN)) (isoNearClosureLift hU q hT hTN hN)
    (isIso_isoNearClosureLift_restrict hU q hT hTN hN)

lemma isOpenImmersion_strictTransformMap_isoNearClosureElimination :
    IsOpenImmersion (strictTransformMap (isoNearClosureLift hU q hT hTN hN)
      (isoNearClosureElimination hU q hT hTN hN).I.blowupMap
      (isoNearClosureElimination hU q hT hTN hN).preservedOpen) := by
  have := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  have := quasiSeparatedSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  have := isProper_isoNearClosureSeparationBlowup hU q hT hTN hN
  have := isProper_isoNearClosureLift hU q hT hTN hN
  exact isOpenImmersion_strictTransformMap_eliminationBlowup _ _ _

/-- The restriction of the elimination centre to `A` is admissible for the locus above `U`. -/
lemma disjoint_support_comap_isoNearClosureElimination :
    Disjoint (((isoNearClosureNbhd hU q hT hTN hN).ι ⁻¹ᵁ
        ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹ᵁ U) :
          (isoNearClosureNbhd hU q hT hTN hN).toScheme.Opens) :
            Set (isoNearClosureNbhd hU q hT hTN hN).toScheme)
      (((isoNearClosureElimination hU q hT hTN hN).I.comap
        (isoNearClosureNbhd hU q hT hTN hN).ι).support :
          Set (isoNearClosureNbhd hU q hT hTN hN).toScheme) := by
  set A := isoNearClosureNbhd hU q hT hTN hN
  rw [Set.disjoint_left]
  intro y hyU hyJ
  rw [Scheme.IdealSheafData.coe_support_comap] at hyJ
  have hyA : A.ι y ∈ (A : Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup) := by
    have : A.ι y ∈ Set.range A.ι := ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  exact Set.disjoint_left.mp (isoNearClosureElimination hU q hT hTN hN).disjoint_support
    (mem_isoNearClosureIsoLocus_of_mem_isoNearClosureNbhd hU q hT hTN hN _ hyA hyU) hyJ

/-- The extension step (Stacks Project Tag 080M, blueprint
`lemma-products-composites-u-admissible-blow--3`): a finite-type ideal on `X₁` restricting on `A` to
the elimination centre and avoiding the locus above `U`. -/
theorem exists_isoNearClosureExtendedCentre :
    ∃ D : (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup.IdealSheafData,
      D.ofFiniteType ∧ D.comap (isoNearClosureNbhd hU q hT hTN hN).ι =
        (isoNearClosureElimination hU q hT hTN hN).I.comap (isoNearClosureNbhd hU q hT hTN hN).ι ∧
      Disjoint (((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹ᵁ U :
          (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup.Opens) :
            Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup)
        (D.support : Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup) := by
  have := compactSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  have := quasiSeparatedSpace_isoNearClosureSeparationBlowup hU q hT hTN hN
  have := isProper_isoNearClosureSeparationBlowup hU q hT hTN hN
  exact Scheme.IdealSheafData.exists_finiteType_comap_eq_of_disjoint
    (isCompact_isoNearClosureNbhd hU q hT hTN hN)
    ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap.isCompact_preimage hU) _
    ((isoNearClosureElimination hU q hT hTN hN).finiteType.comap_of_isOpenImmersion _)
    (disjoint_support_comap_isoNearClosureElimination hU q hT hTN hN)

/-- **Step 6 of the isomorphism-near-closure construction: the extended centre** on `X₁`,
selected from `exists_isoNearClosureExtendedCentre`: the elimination blow-up of the open `A`
extended to an admissible blow-up of `X₁` (blueprint
`lemma-products-composites-u-admissible-blow--3`). (blueprint:
`lemma-extending-isomorphism-over-closure-closed--1`) -/
noncomputable def isoNearClosureExtendedCentre :
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup.IdealSheafData :=
  (exists_isoNearClosureExtendedCentre hU q hT hTN hN).choose

lemma isoNearClosureExtendedCentre_spec :
    (isoNearClosureExtendedCentre hU q hT hTN hN).ofFiniteType ∧
      (isoNearClosureExtendedCentre hU q hT hTN hN).comap (isoNearClosureNbhd hU q hT hTN hN).ι =
        (isoNearClosureElimination hU q hT hTN hN).I.comap (isoNearClosureNbhd hU q hT hTN hN).ι ∧
      Disjoint (((isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ⁻¹ᵁ U :
          (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup.Opens) :
            Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup)
        ((isoNearClosureExtendedCentre hU q hT hTN hN).support :
          Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup) :=
  (exists_isoNearClosureExtendedCentre hU q hT hTN hN).choose_spec

/-- **Step 7 of the isomorphism-near-closure construction: the composite centre** `K` on `X`,
selected from the composition theorem for blow-ups with base change
(`Scheme.IdealSheafData.exists_blowup_comp_base_change`, Stacks Project Tag 080B) applied to
the separation centre and the extended centre on `X₁`.
(blueprint: `lemma-extending-isomorphism-over-closure-closed--1`) -/
noncomputable def isoNearClosureCentre : X.IdealSheafData :=
  (Scheme.IdealSheafData.exists_blowup_comp_base_change
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I
    (isoNearClosureSeparationBlowup hU q hT hTN hN).finiteType
    (isoNearClosureExtendedCentre hU q hT hTN hN)
    (isoNearClosureExtendedCentre_spec hU q hT hTN hN).1).choose

/-- The composite centre is of finite type, has support `supp 𝓘 ∪ π₁(supp D)`, its blow-up is
identified with `Bl_D(X₁)` over `X`, and the blow-up of its pullback along `q` is identified
with the blow-up of the pullback of `D` along the canonical lift `lam₁`. -/
theorem isoNearClosureCentre_spec :
    (isoNearClosureCentre hU q hT hTN hN).ofFiniteType ∧
      ((isoNearClosureCentre hU q hT hTN hN).support : Set X) =
        ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.support : Set X) ∪
          (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap ''
            ((isoNearClosureExtendedCentre hU q hT hTN hN).support :
              Set (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowup) ∧
      ∃ al : (isoNearClosureCentre hU q hT hTN hN).blowup ≅
          (isoNearClosureExtendedCentre hU q hT hTN hN).blowup,
        al.hom ≫ (isoNearClosureExtendedCentre hU q hT hTN hN).blowupMap ≫
            (isoNearClosureSeparationBlowup hU q hT hTN hN).I.blowupMap =
          (isoNearClosureCentre hU q hT hTN hN).blowupMap ∧
        ∃ be : ((isoNearClosureCentre hU q hT hTN hN).comap q).blowup ≅
            ((isoNearClosureExtendedCentre hU q hT hTN hN).comap
              (isoNearClosureLift hU q hT hTN hN)).blowup,
          be.hom ≫ ((isoNearClosureExtendedCentre hU q hT hTN hN).comap
              (isoNearClosureLift hU q hT hTN hN)).blowupMap ≫
              ((isoNearClosureSeparationBlowup hU q hT hTN hN).I.comap q).blowupMap =
            ((isoNearClosureCentre hU q hT hTN hN).comap q).blowupMap := by
  obtain ⟨hKft, hKsupp, al, hal, hbc⟩ := (Scheme.IdealSheafData.exists_blowup_comp_base_change
    (isoNearClosureSeparationBlowup hU q hT hTN hN).I
    (isoNearClosureSeparationBlowup hU q hT hTN hN).finiteType
    (isoNearClosureExtendedCentre hU q hT hTN hN)
    (isoNearClosureExtendedCentre_spec hU q hT hTN hN).1).choose_spec
  obtain ⟨be, hbe, -⟩ := hbc q _ (isoNearClosureLift_comp hU q hT hTN hN)
  exact ⟨hKft, hKsupp, al, hal, be, hbe⟩

lemma disjoint_support_isoNearClosureCentre :
    Disjoint (U : Set X) ((isoNearClosureCentre hU q hT hTN hN).support : Set X) := by
  rw [Set.disjoint_left]
  intro x hxU hxK
  rw [(isoNearClosureCentre_spec hU q hT hTN hN).2.1] at hxK
  rcases hxK with hx | ⟨x', hx', rfl⟩
  · exact Set.disjoint_left.mp (isoNearClosureSeparationBlowup hU q hT hTN hN).disjoint_support
      hxU hx
  · exact Set.disjoint_left.mp (isoNearClosureExtendedCentre_spec hU q hT hTN hN).2.2 hxU hx'

/-- **The isomorphism-near-closure blow-up** `IsoBl_{U,T}(q) ⟶ X`: for a proper morphism
`q : Z ⟶ X` over a qcqs scheme `X` which is an isomorphism over an open neighbourhood `N` of a
piece `T` closed in the quasi-compact open `U`, the `U`-admissible blow-up of `X` assembled
from the named steps:

1. constructible separation data `(T_c, E_c)` in `U` of `T` and of the complement `E` of the
   maximal isomorphism open (`isoNearClosureSeparation`);
2. the separation blow-up `X₁ = CSepBl_U(T_c, E_c)` (`isoNearClosureSeparationBlowup`);
3. a second constructible separation in `X₁`, giving a quasi-compact open `A ⊆ X₁` around the
   closure of the inverse image of `T_c` and away from that of `E_c`
   (`isoNearClosureNbhd`);
4. the canonical lift `lam₁` of `q` to `X₁` (`isoNearClosureLift`), an isomorphism above
   `V₂ = U \ E_c`;
5. the elimination-of-indeterminacy blow-up of `lam₁` over the locus above `V₂`
   (`isoNearClosureElimination`);
6. its restriction to `A`, extended to a `U`-admissible centre `D` on `X₁`
   (`isoNearClosureExtendedCentre`);
7. the composite centre `K` of `X₁ ⟶ X` and `Bl_D(X₁) ⟶ X₁` (`isoNearClosureCentre`).

Difference from the blueprint: the blueprint eliminates over `X₀ = X₁ \ closure(E_c)` and
extends from `X₀`. The formalization performs the elimination over the quasi-compact open of
`X₁` above `V₂` and extends from the quasi-compact open `A ⊆ X₀` produced by a second
constructible separation (step 3), since the extension of admissible blow-ups (Tag 080M) needs a
quasi-compact open; `A` still contains the closure of the inverse image of `T`, which is all
that is used. (blueprint: `lemma-extending-isomorphism-over-closure-closed--1`) -/
noncomputable def isoNearClosureBlowup : IsAdmissible X U where
  I := isoNearClosureCentre hU q hT hTN hN
  finiteType := (isoNearClosureCentre_spec hU q hT hTN hN).1
  disjoint_support := disjoint_support_isoNearClosureCentre hU q hT hTN hN

end IsoNearClosureConstruction
/-! ### The final step of the isomorphism-near-closure argument -/

/-- The final step of the isomorphism near a boundary closure, for arbitrary data of the shape
produced by the construction `isoNearClosureBlowup`: a `U`-admissible blow-up `X₁ ⟶ X` with an
open `A ⊆ X₁` containing the closure of the inverse image of `T`, the canonical lift `lam₁` of
`q` to `X₁`, an admissible blow-up `B'` of `X₁` along which the strict transform of `lam₁` is
an open immersion, an extension `D` of the restriction of the centre of `B'` to `A` which is
`U`-admissible, and a composite centre `K` of `X₁` and `D` (Tag 080B) with its base change
along `q`.

Tag 080E (`Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`) turns the strict
transform of `q` along `K.blowupMap` into the canonical lift `(K.comap q).blowup ⟶ K.blowup`,
and the localization of canonical lifts
(`Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens`) identifies that lift over the
copy of `A` with the open immersion produced by `B'`. The neighbourhood is the range of the
resulting partial section; it contains the closure of the inverse image of `T` because that
closure lies over `A` and inside the (closed, since `q` is proper) range of the strict
transform. -/
theorem exists_isIso_strictTransformMap_of_isoNearClosureData {X Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens} (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hTrange : T ⊆ Set.range q)
    (B₁ : IsAdmissible X U) (A : B₁.I.blowup.Opens)
    (hTA : closure (B₁.I.blowupMap ⁻¹' T) ⊆ (A : Set B₁.I.blowup))
    (lam₁ : (B₁.I.comap q).blowup ⟶ B₁.I.blowup)
    (hlam₁ : lam₁ ≫ B₁.I.blowupMap = (B₁.I.comap q).blowupMap ≫ q)
    {V : B₁.I.blowup.Opens} (B' : IsAdmissible B₁.I.blowup V)
    (hB' : IsOpenImmersion (strictTransformMap lam₁ B'.I.blowupMap B'.preservedOpen))
    (D : B₁.I.blowup.IdealSheafData) (hDA : D.comap A.ι = B'.I.comap A.ι)
    (hDdisj : Disjoint ((B₁.I.blowupMap ⁻¹ᵁ U : B₁.I.blowup.Opens) : Set B₁.I.blowup)
      (D.support : Set B₁.I.blowup))
    (K : X.IdealSheafData) (hKft : K.ofFiniteType)
    (hKsupp : (K.support : Set X) =
      (B₁.I.support : Set X) ∪ B₁.I.blowupMap '' (D.support : Set B₁.I.blowup))
    (al : K.blowup ≅ D.blowup) (hal : al.hom ≫ D.blowupMap ≫ B₁.I.blowupMap = K.blowupMap)
    (be : (K.comap q).blowup ≅ (D.comap lam₁).blowup)
    (hbe : be.hom ≫ (D.comap lam₁).blowupMap ≫ (B₁.I.comap q).blowupMap = (K.comap q).blowupMap) :
    ∃ N' : K.blowup.Opens, closure (K.blowupMap ⁻¹' T) ⊆ (N' : Set K.blowup) ∧
      IsIso (strictTransformMap q K.blowupMap K.support.compl ∣_ N') := by
  have := B₁.isProper_blowupMap
  have hcqft : (B₁.I.comap q).ofFiniteType := B₁.finiteType.comap q
  have : IsProper (B₁.I.comap q).blowupMap :=
    (B₁.I.comap q).isProper_blowupMap fun V ↦ hcqft V le_top
  have : IsProper (lam₁ ≫ B₁.I.blowupMap) := by rw [hlam₁]; infer_instance
  have : IsProper lam₁ := IsProper.of_comp lam₁ B₁.I.blowupMap
  obtain ⟨eC, -, heC⟩ := B'.I.exists_blowup_comap_iso_strictTransform lam₁
  set lamC : (B'.I.comap lam₁).blowup ⟶ B'.I.blowup :=
    eC.hom ≫ strictTransformMap lam₁ B'.I.blowupMap B'.I.support.compl with hlamCdef
  have : IsOpenImmersion lamC := by
    have := hB'
    rw [hlamCdef]
    infer_instance
  -- the restriction of the centre of `B'` to `A`, which `D` extends
  set JA : A.toScheme.IdealSheafData := B'.I.comap A.ι with hJAdef
  have hKdisj : Disjoint (U : Set X) (K.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    rw [hKsupp] at hxK
    rcases hxK with hx | ⟨x', hx', rfl⟩
    · exact Set.disjoint_left.mp B₁.disjoint_support hxU hx
    · exact Set.disjoint_left.mp hDdisj hxU hx'
  have hKcqft : (K.comap q).ofFiniteType := hKft.comap q
  have : IsProper K.blowupMap := K.isProper_blowupMap fun V ↦ hKft V le_top
  have : IsProper (K.comap q).blowupMap :=
    (K.comap q).isProper_blowupMap fun V ↦ hKcqft V le_top
  -- Step 8: the canonical lifts on the composite blow-up and their comparison.
  obtain ⟨eK, -, heK⟩ := K.exists_blowup_comap_iso_strictTransform q
  set st : K.strictTransform q ⟶ K.blowup :=
    strictTransformMap q K.blowupMap K.support.compl with hstdef
  set lamK : (K.comap q).blowup ⟶ K.blowup := eK.hom ≫ st with hlamKdef
  have hlamK : lamK ≫ K.blowupMap = (K.comap q).blowupMap ≫ q := heK
  have : IsProper (lamK ≫ K.blowupMap) := by rw [hlamK]; infer_instance
  have : IsProper lamK := IsProper.of_comp lamK K.blowupMap
  obtain ⟨lamD, hlamD⟩ := D.exists_lift_blowup (t := (D.comap lam₁).blowupMap ≫ lam₁)
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (D.comap lam₁).isInvertible_comap_blowupMap)
  have hcompat : be.inv ≫ lamK = lamD ≫ al.inv := by
    have hbeinv : be.inv ≫ (K.comap q).blowupMap =
        (D.comap lam₁).blowupMap ≫ (B₁.I.comap q).blowupMap := by
      rw [← hbe, Iso.inv_hom_id_assoc]
    have halinv : al.inv ≫ K.blowupMap = D.blowupMap ≫ B₁.I.blowupMap := by
      rw [← hal, Iso.inv_hom_id_assoc]
    refine K.hom_ext_of_isInvertible_comap
      (t := be.inv ≫ (K.comap q).blowupMap ≫ q) ?_ ?_ ?_
    · simp only [Scheme.IdealSheafData.comap_comp]
      exact ((K.comap q).isInvertible_comap_blowupMap).comap_of_isOpenImmersion be.inv
    · rw [Category.assoc, hlamK]
    · rw [Category.assoc, halinv, ← Category.assoc, hlamD, Category.assoc, hlam₁,
        ← Category.assoc, ← Category.assoc be.inv, hbeinv]
  have hlamKal : lamK ≫ al.hom = be.hom ≫ lamD := by
    calc lamK ≫ al.hom = (be.hom ≫ be.inv ≫ lamK) ≫ al.hom := by
          rw [Iso.hom_inv_id_assoc]
      _ = be.hom ≫ (be.inv ≫ lamK) ≫ al.hom := by rw [Category.assoc]
      _ = be.hom ≫ (lamD ≫ al.inv) ≫ al.hom := by rw [hcompat]
      _ = be.hom ≫ lamD := by rw [Category.assoc, al.inv_hom_id, Category.comp_id]
  -- Step 8b: localizing the two lifts over `A`; they agree there by construction.
  obtain ⟨mu, hmu⟩ := JA.exists_lift_blowup
    (t := (JA.comap (lam₁ ∣_ A)).blowupMap ≫ (lam₁ ∣_ A))
    (by rw [Scheme.IdealSheafData.comap_comp]
        exact (JA.comap (lam₁ ∣_ A)).isInvertible_comap_blowupMap)
  obtain ⟨hC, hC', hCOI, hC'OI, hCsq, -, -⟩ :=
    Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens B'.I lam₁ A rfl heC hmu
  have := hCOI
  have := hC'OI
  have : IsOpenImmersion mu := by
    have : IsOpenImmersion (mu ≫ hC) := by
      rw [← hCsq]
      infer_instance
    exact IsOpenImmersion.of_comp mu hC
  obtain ⟨hD, hD', hDOI, hD'OI, hDsq, hDrange, hD'range⟩ :=
    Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens D lam₁ A hDA hlamD hmu
  have := hDOI
  have := hD'OI
  -- Step 9: the partial section of the strict transform over the copy of `A`.
  set m : (JA.comap (lam₁ ∣_ A)).blowup ⟶ (K.comap q).blowup := hD' ≫ be.inv with hmdef
  have : IsOpenImmersion m := by rw [hmdef]; infer_instance
  have hjeq : m ≫ lamK = mu ≫ hD ≫ al.inv := by
    rw [hmdef, Category.assoc, hcompat, ← Category.assoc, hDsq, Category.assoc]
  have : IsOpenImmersion (m ≫ lamK) := by rw [hjeq]; infer_instance
  have hD'pre : Set.range hD' = lamD ⁻¹' Set.range hD := by
    rw [hD'range, hDrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  have hD'pre' : Set.range hD' = lamD ⁻¹' Set.range (mu ≫ hD) := by
    refine subset_antisymm ?_ ?_
    · rintro - ⟨w, rfl⟩
      exact ⟨w, by rw [← Scheme.Hom.comp_apply, ← hDsq, Scheme.Hom.comp_apply]⟩
    · intro x hx
      rw [hD'pre]
      obtain ⟨w, hw⟩ := hx
      exact ⟨mu w, by rw [← Scheme.Hom.comp_apply]; exact hw⟩
  have hmrange : Set.range m = lamK ⁻¹' Set.range (m ≫ lamK) := by
    refine subset_antisymm ?_ ?_
    · rintro - ⟨w, rfl⟩
      exact ⟨w, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · intro y hy
      rw [hjeq] at hy
      obtain ⟨w, hw⟩ := hy
      have hbeinvhom : be.inv (be.hom y) = y := by
        rw [← Scheme.Hom.comp_apply, be.hom_inv_id]
        rfl
      have hx : lamD (be.hom y) ∈ Set.range (mu ≫ hD) := by
        refine ⟨w, al.inv.isOpenEmbedding.injective ?_⟩
        calc al.inv ((mu ≫ hD) w)
            = ((mu ≫ hD) ≫ al.inv) w := (Scheme.Hom.comp_apply _ _ _).symm
          _ = lamK y := hw
          _ = lamK (be.inv (be.hom y)) := by rw [hbeinvhom]
          _ = (be.inv ≫ lamK) (be.hom y) := (Scheme.Hom.comp_apply _ _ _).symm
          _ = (lamD ≫ al.inv) (be.hom y) := by rw [hcompat]
          _ = al.inv (lamD (be.hom y)) := Scheme.Hom.comp_apply _ _ _
      obtain ⟨w', hw'⟩ := hD'pre'.ge hx
      exact ⟨w', by rw [hmdef, Scheme.Hom.comp_apply, hw', hbeinvhom]⟩
  -- the closure of the inverse image of `T` lies in the range of the partial section
  have hclosedK : IsClosed (Set.range lamK) := by
    rw [← Set.image_univ]
    exact lamK.isClosedMap _ isClosed_univ
  have hTrangeK : K.blowupMap ⁻¹' T ⊆ Set.range lamK := by
    intro x hx
    have h1 : K.blowupMap x ∈ (K.support.compl : X.Opens) :=
      Set.disjoint_left.mp hKdisj (hTU hx)
    obtain ⟨t, ht⟩ := mem_range_strictTransformMap_of_mem_of_mem_range q K.blowupMap
      K.support.compl h1 (hTrange hx)
    have hsurj : Function.Surjective ⇑eK.hom := by
      have := (Scheme.homeoOfIso eK).surjective
      rwa [Scheme.coe_homeoOfIso] at this
    obtain ⟨t', rfl⟩ := hsurj t
    exact ⟨t', by rw [hlamKdef, Scheme.Hom.comp_apply]; exact ht⟩
  have hclosureA : closure (K.blowupMap ⁻¹' T) ⊆
      (al.hom ≫ D.blowupMap) ⁻¹' (A : Set B₁.I.blowup) := by
    have hg : (al.hom ≫ D.blowupMap) ≫ B₁.I.blowupMap = K.blowupMap := by
      rw [Category.assoc, hal]
    have hpre : K.blowupMap ⁻¹' T =
        (al.hom ≫ D.blowupMap) ⁻¹' (B₁.I.blowupMap ⁻¹' T) := by
      rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hg]
    rw [hpre]
    refine (Continuous.closure_preimage_subset
      (al.hom ≫ D.blowupMap).continuous _).trans (Set.preimage_mono ?_)
    exact hTA
  have hclosure : closure (K.blowupMap ⁻¹' T) ⊆ Set.range (m ≫ lamK) := by
    intro y hy
    obtain ⟨y₀, rfl⟩ : y ∈ Set.range lamK := closure_minimal hTrangeK hclosedK hy
    have hyA : D.blowupMap (al.hom (lamK y₀)) ∈ (A : Set B₁.I.blowup) := by
      have := hclosureA hy
      rwa [Set.mem_preimage, Scheme.Hom.comp_apply] at this
    have hkey : al.hom (lamK y₀) = lamD (be.hom y₀) := by
      calc al.hom (lamK y₀) = (lamK ≫ al.hom) y₀ := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (be.hom ≫ lamD) y₀ := by rw [hlamKal]
        _ = lamD (be.hom y₀) := Scheme.Hom.comp_apply _ _ _
    rw [hkey] at hyA
    have hmem : be.hom y₀ ∈ Set.range hD' := by
      rw [hD'range, Set.mem_preimage, Scheme.Hom.comp_apply]
      exact hyA
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, ?_⟩
    have hbeinvhom : be.inv (be.hom y₀) = y₀ := by
      rw [← Scheme.Hom.comp_apply, be.hom_inv_id]
      rfl
    calc (m ≫ lamK) w = lamK (m w) := Scheme.Hom.comp_apply _ _ _
      _ = lamK (be.inv (hD' w)) := by rw [hmdef]; rfl
      _ = lamK (be.inv (be.hom y₀)) := by rw [hw]
      _ = lamK y₀ := by rw [hbeinvhom]
  -- Step 10: conclude.
  have hmst : (m ≫ eK.hom) ≫ st = m ≫ lamK := by rw [hlamKdef, Category.assoc]
  have : IsOpenImmersion ((m ≫ eK.hom) ≫ st) := by rw [hmst]; infer_instance
  refine ⟨((m ≫ eK.hom) ≫ st).opensRange, ?_, ?_⟩
  · change closure (K.blowupMap ⁻¹' T) ⊆ Set.range ((m ≫ eK.hom) ≫ st)
    rw [hmst]
    exact hclosure
  · change IsIso (st ∣_ ((m ≫ eK.hom) ≫ st).opensRange)
    refine isIso_morphismRestrict_opensRange_of_range_eq st (m ≫ eK.hom) ?_
    have hsurj : Function.Surjective ⇑eK.hom := by
      have := (Scheme.homeoOfIso eK).surjective
      rwa [Scheme.coe_homeoOfIso] at this
    rw [hmst]
    ext t
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [← Scheme.Hom.comp_apply, hmst]⟩
    · intro ht
      obtain ⟨t₀, rfl⟩ := hsurj t
      have : lamK t₀ ∈ Set.range (m ≫ lamK) := by
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hlamKdef] at ht
      obtain ⟨w, hw⟩ := hmrange.ge this
      exact ⟨w, by rw [hmdef] at hw ⊢; rw [Scheme.Hom.comp_apply, hw]⟩

/-- **The isomorphism-near-closure blow-up does its job** (Stacks Project Tag 0F3W;
blueprint: `lemma-extending-isomorphism-over-closure-closed`): after the blow-up `IsoBl_{U,T}(q)`
(`isoNearClosureBlowup`), the strict transform of `q` is an isomorphism over an open
neighbourhood of the closure of the inverse image of `T`. The proof feeds the named steps of
the construction into `exists_isIso_strictTransformMap_of_isoNearClosureData`. -/
theorem exists_isIso_strictTransformMap_isoNearClosureBlowup {X Z : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ N' : (isoNearClosureBlowup hU q hT hTN hN).I.blowup.Opens,
      closure ((isoNearClosureBlowup hU q hT hTN hN).I.blowupMap ⁻¹' T) ⊆
        (N' : Set (isoNearClosureBlowup hU q hT hTN hN).I.blowup) ∧
      IsIso (strictTransformMap q (isoNearClosureBlowup hU q hT hTN hN).I.blowupMap
        (isoNearClosureBlowup hU q hT hTN hN).preservedOpen ∣_ N') := by
  obtain ⟨-, hDA, hDdisj⟩ := isoNearClosureExtendedCentre_spec hU q hT hTN hN
  obtain ⟨hKft, hKsupp, al, hal, be, hbe⟩ := isoNearClosureCentre_spec hU q hT hTN hN
  exact exists_isIso_strictTransformMap_of_isoNearClosureData q hTU
    (fun _ hx ↦ maximalIsomorphismOpen_subset_range q
      (subset_maximalIsomorphismOpen_of_isIso q hTN hN hx))
    _ _ (closure_preimage_subset_isoNearClosureNbhd hU q hT hTN hN hTU) _
    (isoNearClosureLift_comp hU q hT hTN hN) _
    (isOpenImmersion_strictTransformMap_isoNearClosureElimination hU q hT hTN hN) _ hDA hDdisj
    _ hKft hKsupp al hal be hbe

/-- **Isomorphism near the closure of a boundary piece** (Stacks Project Tag 0F3W;
blueprint: `def:nagata-isomorphism-near-closure`,
`lemma:nagata-isomorphism-near-closure`; used for the improved comparison projection of
the two-open compactification theorem): a proper morphism which is an isomorphism over a
neighbourhood of a closed piece `T` of `U` acquires, after a `U`-admissible blow-up, a strict
transform which is an isomorphism over a neighbourhood of the closure of `T`. A witness is the
constructed blow-up `isoNearClosureBlowup`
(`exists_isIso_strictTransformMap_isoNearClosureBlowup`). -/
theorem exists_admissibleBlowup_isIso_strictTransformMap_near_closure
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (q : Z ⟶ X) [IsProper q]
    {T : Set X} (hTU : T ⊆ (U : Set X)) (hT : IsClosed (U.ι ⁻¹' T))
    {N : X.Opens} (hTN : T ⊆ (N : Set X)) (hN : IsIso (q ∣_ N)) :
    ∃ (B : IsAdmissible X U) (N' : B.I.blowup.Opens),
      closure (B.I.blowupMap ⁻¹' T) ⊆ (N' : Set B.I.blowup) ∧
      IsIso (strictTransformMap q B.I.blowupMap B.preservedOpen ∣_ N') :=
  ⟨isoNearClosureBlowup hU q hT hTN hN,
    exists_isIso_strictTransformMap_isoNearClosureBlowup hU q hTU hT hTN hN⟩

/-- **A proper open immersion with dense image is an isomorphism** (blueprint:
`lemma-nagata-proper-open-dense-iso`): if `q : Z ⟶ X` is proper and an open immersion, and its
image contains a scheme-theoretically dense quasi-compact open `D` of `X`, then `q` is an
isomorphism. The image of `q` is open, and closed because `q` is universally closed; it contains
the dense set `D`, hence is everything. -/
theorem isIso_of_isProper_of_isOpenImmersion {X Z : Scheme.{u}} (q : Z ⟶ X) [IsProper q]
    [IsOpenImmersion q] (D : X.Opens) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (hD : D ≤ q.opensRange) : IsIso q := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top q ?_
  have hclosed : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
  have hdense : closure (D : Set X) = Set.univ := by
    simpa using D.ι.denseRange.closure_range
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.eq_univ_iff_forall]
  intro x
  have : closure (D : Set X) ⊆ Set.range q := hclosed.closure_subset_iff.mpr (by
    intro y hy; exact (hD hy : y ∈ q.opensRange))
  exact this (hdense ▸ Set.mem_univ x)

end AlgebraicGeometry
