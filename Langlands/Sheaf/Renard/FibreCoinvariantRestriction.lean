import Langlands.Sheaf.Renard.CoinvariantStatements
import Langlands.Sheaf.Renard.InverseImageStalks
import Langlands.Sheaf.CompactGerms

/-!
# Restriction of compact sections along an equivariant closed embedding
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Topology

namespace Langlands.Sheaf.Renard.FibreCoinvariantRestriction

open CategoryTheory Opposite TopologicalSpace
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions

variable {G X Z : Type} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [TopologicalSpace Z] [MulAction G X] [MulAction G Z]
  [ContinuousSMul G X] [ContinuousSMul G Z]
  (f : C(Z, X)) (hf : ∀ (g : G) (z : Z), f (g • z) = g • f z)

/-- The equivariant inverse image along `f`. -/
abbrev res (F : ActionSheaf G X) : ActionSheaf G Z := (actionInverseImage f hf).obj F

/-- The whole source lies in the preimage of the whole target. -/
def topHom :
    (ActionOpens.top : ActionOpens G Z) ⟶ (DirectImage.preimage f hf).obj ActionOpens.top :=
  ActionOpens.inclusionHom (fun _ _ => trivial)

/-- Restriction of global sections along `f`, by the inverse-image unit. -/
def globalRestrict (F : ActionSheaf G X) :
    F.obj.obj (op ActionOpens.top) ⟶ (res f hf F).obj.obj (op ActionOpens.top) :=
  (InverseImageStalks.unit f hf F).app (op ActionOpens.top) ≫
    (res f hf F).obj.map (topHom f hf).op

/-- The germ of a restricted section is the stalk comparison of the original germ. -/
theorem germ_globalRestrict (F : ActionSheaf G X) (a : F.obj.obj (op ActionOpens.top)) (z : Z) :
    (CompactSections.ordinary (res f hf F).obj).Γgerm z ((globalRestrict f hf F).hom a) =
      (InverseImageStalks.stalkIso f hf F z).hom
        ((CompactSections.ordinary F.obj).Γgerm (f z) a) := by
  change (CompactSections.ordinary (res f hf F).obj).germ ⊤ z trivial
      ((CompactSections.ordinary (res f hf F).obj).map
        (homOfLE (fun _ _ => trivial) :
          (⊤ : Opens Z) ⟶ (Opens.map (TopCat.ofHom f)).obj ⊤).op
        ((InverseImageStalks.unit f hf F).app (op ActionOpens.top) a)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  exact (congrArg (fun k => k.hom a)
    (InverseImageStalks.germ_stalkIso_hom f hf F z ⊤ trivial)).symm

/-- Restricted sections are supported in the preimage of the original support. -/
theorem support_globalRestrict_subset (F : ActionSheaf G X)
    (a : F.obj.obj (op ActionOpens.top)) :
    CompactSupport.support (CompactSections.ordinary (res f hf F).obj)
        ((globalRestrict f hf F).hom a) ⊆
      f ⁻¹' CompactSupport.support (CompactSections.ordinary F.obj) a := by
  intro z hz
  by_contra ha
  apply hz
  change (CompactSections.ordinary (res f hf F).obj).Γgerm z ((globalRestrict f hf F).hom a) = 0
  rw [germ_globalRestrict,
    show (CompactSections.ordinary F.obj).Γgerm (f z) a = 0 from not_not.mp ha, map_zero]

/-- Restriction of compactly supported sections along a closed embedding. -/
def compactRestrict (hfc : IsClosedEmbedding f) (F : ActionSheaf G X) :
    CompactSupport.submodule (CompactSections.ordinary F.obj) →ₗ[ℂ]
      CompactSupport.submodule (CompactSections.ordinary (res f hf F).obj) :=
  (globalRestrict f hf F).hom.restrict (fun a ha =>
    (hfc.isCompact_preimage ha).of_isClosed_subset (CompactSupport.isClosed_support _ _)
      (support_globalRestrict_subset f hf F a))

theorem compactRestrict_val (hfc : IsClosedEmbedding f) (F : ActionSheaf G X)
    (a : CompactSupport.submodule (CompactSections.ordinary F.obj)) :
    (compactRestrict f hf hfc F a).val = (globalRestrict f hf F).hom a.val := rfl

/-- Restriction commutes with the group operators. -/
theorem globalRestrict_action (F : ActionSheaf G X) (g : G)
    (a : F.obj.obj (op ActionOpens.top)) :
    (globalRestrict f hf F).hom (globalRepresentation F g a) =
      globalRepresentation (res f hf F) g ((globalRestrict f hf F).hom a) := by
  apply TopCat.Presheaf.section_ext (underlying (res f hf F)) ⊤
  intro z _
  change (CompactSections.ordinary (res f hf F).obj).Γgerm z _ =
    (CompactSections.ordinary (res f hf F).obj).Γgerm z _
  rw [germ_globalRestrict, CompactSectionActions.global_germ_transport,
    CompactSectionActions.global_germ_transport, germ_globalRestrict]
  have key : ∀ (x' : X) (h : g⁻¹ • f z = x'),
      (Godement.stalkPull F.obj g⁻¹ (f z) x' h).hom
          ((CompactSections.ordinary F.obj).Γgerm x' a) =
        (Godement.stalkPull F.obj g⁻¹ (f z) (g⁻¹ • f z) rfl).hom
          ((CompactSections.ordinary F.obj).Γgerm (g⁻¹ • f z) a) := by
    rintro x' rfl
    rfl
  rw [← key (f (g⁻¹ • z)) (hf g⁻¹ z).symm]
  exact congrArg (fun k => k.hom ((CompactSections.ordinary F.obj).Γgerm (f (g⁻¹ • z)) a))
    (InverseImageStalks.preimageStalkMap_transport f hf (InverseImageStalks.unit f hf F)
      g⁻¹ z (g⁻¹ • z) rfl)

/-- Restriction of compact sections intertwines the two compact-section representations. -/
theorem compactRestrict_action (hfc : IsClosedEmbedding f) (F : ActionSheaf G X) (g : G)
    (a : CompactSupport.submodule (CompactSections.ordinary F.obj)) :
    compactRestrict f hf hfc F (CompactSections.representation F.obj g a) =
      CompactSections.representation (res f hf F).obj g (compactRestrict f hf hfc F a) :=
  Subtype.ext (globalRestrict_action f hf F g a.val)

/-- Restriction of global sections is natural in the original sheaf. -/
theorem globalRestrict_naturality {F F' : ActionSheaf G X} (φ : F ⟶ F') :
    globalRestrict f hf F ≫ ((actionInverseImage f hf).map φ).hom.app (op ActionOpens.top) =
      φ.hom.app (op ActionOpens.top) ≫ globalRestrict f hf F' := by
  have h := NatTrans.congr_app (InverseImageStalks.unit_naturality f hf φ) (op ActionOpens.top)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [globalRestrict, globalRestrict, Category.assoc,
    ((actionInverseImage f hf).map φ).hom.naturality, ← Category.assoc]
  erw [h]
  rw [Category.assoc]

/-- Restriction of compact sections is natural in the original sheaf. -/
theorem compactRestrict_naturality (hfc : IsClosedEmbedding f) {F F' : ActionSheaf G X}
    (φ : F ⟶ F') (a : CompactSupport.submodule (CompactSections.ordinary F.obj)) :
    compactRestrict f hf hfc F' (CompactSections.map φ a) =
      CompactSections.map ((actionInverseImage f hf).map φ) (compactRestrict f hf hfc F a) :=
  Subtype.ext (congrArg (fun k => k.hom a.val) (globalRestrict_naturality f hf φ)).symm

section Surjective

variable (F : ActionSheaf G X)

/-- `σ` over `K` has the same restricted germs as `b` at every point of `f ⁻¹' K`. -/
def Good (b : (res f hf F).obj.obj (op ActionOpens.top)) (K : Opens X)
    (σ : (CompactSections.ordinary F.obj).obj (op K)) : Prop :=
  ∀ (z : Z) (hz : f z ∈ K),
    (CompactSections.ordinary (res f hf F).obj).Γgerm z b =
      (InverseImageStalks.stalkIso f hf F z).hom
        ((CompactSections.ordinary F.obj).germ K (f z) hz σ)

/-- Subtracting a restricted section keeps a matching section, corrected by restriction. -/
theorem good_sub {b : (res f hf F).obj.obj (op ActionOpens.top)} {K : Opens X}
    {σ : (CompactSections.ordinary F.obj).obj (op K)} (h : Good f hf F b K σ)
    (a : F.obj.obj (op ActionOpens.top)) :
    Good f hf F (b - (globalRestrict f hf F).hom a) K
      (σ - (CompactSections.ordinary F.obj).map (homOfLE le_top : K ⟶ ⊤).op a) := by
  intro z hz
  rw [map_sub, germ_globalRestrict, h z hz, map_sub, map_sub,
    TopCat.Presheaf.germ_res_apply]
  rfl

/-- Every point has a compact open neighbourhood with a matching section. -/
theorem exists_good (hfc : IsClosedEmbedding f) (hX : Langlands.Topology.IsLocallyProfinite X)
    (b : (res f hf F).obj.obj (op ActionOpens.top)) (z : Z) :
    ∃ K : Opens X, f z ∈ K ∧ IsCompact (K : Set X) ∧ ∃ σ, Good f hf F b K σ := by
  obtain ⟨U, hU, τ, hτ⟩ := (CompactSections.ordinary F.obj).exists_germ_eq
    ((InverseImageStalks.stalkIso f hf F z).inv
      ((CompactSections.ordinary (res f hf F).obj).Γgerm z b))
  have h1 : (CompactSections.ordinary (res f hf F).obj).germ ⊤ z trivial b =
      (CompactSections.ordinary (res f hf F).obj).germ ((Opens.map (TopCat.ofHom f)).obj U) z hU
        ((InverseImageStalks.unit f hf F).app (op ⟨U⟩) τ) := by
    refine Eq.trans ?_
      (congrArg (fun k => k.hom τ) (InverseImageStalks.germ_stalkIso_hom f hf F z U hU))
    change _ = (InverseImageStalks.stalkIso f hf F z).hom
      ((CompactSections.ordinary F.obj).germ U (f z) hU τ)
    rw [hτ, Iso.inv_hom_id_apply]
    rfl
  obtain ⟨W, hzW, iU, iV, hW⟩ :=
    (CompactSections.ordinary (res f hf F).obj).germ_eq (U := ⊤) z trivial hU b _ h1
  obtain ⟨W', hW'o, hW'eq⟩ := hfc.isInducing.isOpen_iff.mp W.isOpen
  have hzW' : f z ∈ W' := by
    change z ∈ f ⁻¹' W'
    rw [hW'eq]
    exact hzW
  obtain ⟨V, hzV, hVo, hVc, hVsub⟩ := hX.hasCompactOpenNeighborhoodBasis (f z)
    ((U : Set X) ∩ W') ((U.isOpen.inter hW'o).mem_nhds ⟨hU, hzW'⟩)
  have hVU : (⟨V, hVo⟩ : Opens X) ≤ U := fun x hx => (hVsub hx).1
  refine ⟨⟨V, hVo⟩, hzV, hVc, (CompactSections.ordinary F.obj).map (homOfLE hVU).op τ, ?_⟩
  intro z' hz'
  have hz'W : z' ∈ W := by
    change z' ∈ (W : Set Z)
    rw [← hW'eq]
    exact (hVsub hz').2
  rw [TopCat.Presheaf.germ_res_apply]
  change (CompactSections.ordinary (res f hf F).obj).germ ⊤ z' trivial b = _
  rw [← TopCat.Presheaf.germ_res_apply _ iU z' hz'W, hW, TopCat.Presheaf.germ_res_apply]
  exact (congrArg (fun k => k.hom τ)
    (InverseImageStalks.germ_stalkIso_hom f hf F z' U (hVU hz'))).symm

/-- Finite induction: matching sections over a finite cover of the support give a preimage. -/
theorem exists_restrict_aux (hX : Langlands.Topology.IsLocallyProfinite X)
    (Kf : Z → Opens X) (hKc : ∀ z, IsCompact (Kf z : Set X)) (t : Finset Z) :
    ∀ b : (res f hf F).obj.obj (op ActionOpens.top),
      CompactSupport.support (CompactSections.ordinary (res f hf F).obj) b ⊆
          ⋃ z ∈ t, f ⁻¹' (Kf z : Set X) →
        (∀ z ∈ t, ∃ σ, Good f hf F b (Kf z) σ) →
          ∃ a ∈ CompactSupport.submodule (CompactSections.ordinary F.obj),
            (globalRestrict f hf F).hom a = b := by
  classical
  let := hX.t2Space
  induction t using Finset.induction_on with
  | empty =>
    intro b hb _
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    symm
    apply TopCat.Presheaf.section_ext (underlying (res f hf F)) ⊤
    intro z _
    have hz : z ∉ CompactSupport.support (CompactSections.ordinary (res f hf F).obj) b := by
      intro h
      simpa using hb h
    rw [map_zero]
    exact not_not.mp hz
  | insert z₀ t hz₀ ih =>
    intro b hb hgood
    obtain ⟨σ, hσ⟩ := hgood z₀ (Finset.mem_insert_self z₀ t)
    let e := CompactGerms.compactExtension (underlying F) (Kf z₀) (hKc z₀).isClosed (hKc z₀) σ
    have he_in : ∀ (x : X) (hx : x ∈ Kf z₀),
        (CompactSections.ordinary F.obj).Γgerm x e.val =
          (CompactSections.ordinary F.obj).germ (Kf z₀) x hx σ := by
      intro x hx
      have h := TopCat.Presheaf.germ_res_apply (CompactSections.ordinary F.obj)
        (homOfLE le_top : Kf z₀ ⟶ ⊤) x hx e.val
      have h2 : (CompactSections.ordinary F.obj).map (homOfLE le_top : Kf z₀ ⟶ ⊤).op e.val = σ :=
        CompactGerms.restrict_extend (underlying F) (Kf z₀) (hKc z₀).isClosed σ
      rw [h2] at h
      exact h.symm
    have he_out : ∀ x : X, x ∉ Kf z₀ → (CompactSections.ordinary F.obj).Γgerm x e.val = 0 := by
      intro x hx
      by_contra hne
      exact hx (CompactGerms.support_extend_subset (underlying F) (Kf z₀) (hKc z₀).isClosed σ hne)
    let b' := b - (globalRestrict f hf F).hom e.val
    have hb'in : ∀ z (hz : f z ∈ Kf z₀),
        (CompactSections.ordinary (res f hf F).obj).Γgerm z b' = 0 := by
      intro z hz
      rw [map_sub, germ_globalRestrict, hσ z hz, he_in _ hz, sub_self]
    have hb'out : ∀ z, f z ∉ Kf z₀ →
        (CompactSections.ordinary (res f hf F).obj).Γgerm z b' =
          (CompactSections.ordinary (res f hf F).obj).Γgerm z b := by
      intro z hz
      rw [map_sub, germ_globalRestrict, he_out _ hz, map_zero, sub_zero]
    have hsupp : CompactSupport.support (CompactSections.ordinary (res f hf F).obj) b' ⊆
        ⋃ z ∈ t, f ⁻¹' (Kf z : Set X) := by
      intro z hz
      by_cases hK : f z ∈ Kf z₀
      · exact absurd (hb'in z hK) hz
      · have hzb : z ∈ CompactSupport.support (CompactSections.ordinary (res f hf F).obj) b := by
          change _ ≠ 0
          rw [← hb'out z hK]
          exact hz
        have := hb hzb
        simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_preimage, exists_prop] at this
        obtain ⟨w, hw, hzw⟩ := this
        rcases hw with rfl | hw
        · exact absurd hzw hK
        · simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
          exact ⟨w, hw, hzw⟩
    obtain ⟨a', ha', hra'⟩ := ih b' hsupp (fun z hz => by
      obtain ⟨τ, hτ⟩ := hgood z (Finset.mem_insert_of_mem hz)
      exact ⟨_, good_sub f hf F hτ e.val⟩)
    let ev : (CompactSections.ordinary F.obj).obj (op ⊤) := e.val
    have hev : ev ∈ CompactSupport.submodule (CompactSections.ordinary F.obj) := e.property
    refine ⟨a' + ev, Submodule.add_mem _ ha' hev, ?_⟩
    rw [map_add, hra']
    exact sub_add_cancel b _

/-- Restriction of compact sections along a closed embedding is surjective. -/
theorem compactRestrict_surjective (hfc : IsClosedEmbedding f)
    (hX : Langlands.Topology.IsLocallyProfinite X) :
    Function.Surjective (compactRestrict f hf hfc F) := by
  rintro ⟨b, hb⟩
  choose Kf hzK hKc σ hgood using exists_good f hf F hfc hX b
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hb (fun z => f ⁻¹' (Kf z : Set X))
    (fun z _ => ((Kf z).isOpen.preimage f.continuous).mem_nhds (hzK z))
  obtain ⟨a, ha, hab⟩ := exists_restrict_aux f hf F hX Kf hKc t b ht
    (fun z _ => ⟨σ z, hgood z⟩)
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩

end Surjective

end Langlands.Sheaf.Renard.FibreCoinvariantRestriction
