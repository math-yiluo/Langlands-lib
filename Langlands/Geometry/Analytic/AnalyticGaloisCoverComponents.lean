import Langlands.Geometry.Analytic.AnalyticGaloisCover
import Langlands.Geometry.Analytic.ContinuousDomainEmbeddings
import Langlands.Geometry.Analytic.DistinguishedOpenNeighborhoods
import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof

/-! # Pointed restrictions of finite analytic Galois coverings -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.AnalyticGaloisCover

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}
  {Γ : Type z} [Group Γ] (c : AnalyticGaloisCover Γ p)

/-- The subgroup `H` preserves the open `S`, and translates by elements
outside `H` are disjoint from `S`. -/
def IsDeckComponent (H : Subgroup Γ) (S : Opens (localizedSpaceFunctor.obj Y)) : Prop :=
  ∀ (γ : Γ) (y : localizedSpaceFunctor.obj Y), y ∈ S →
    (localizedSpaceFunctor.map (c.deck γ).asIso.hom y ∈ S ↔ γ ∈ H)

/-- The open image of the chosen source open. -/
def componentImage (S : Opens (localizedSpaceFunctor.obj Y)) : Opens (localizedSpaceFunctor.obj X) :=
  ⟨localizedSpaceFunctor.map p '' (S : Set (localizedSpaceFunctor.obj Y)),
    etaleOpenMap K p c.etale_map _ S.isOpen⟩

variable (S : Opens (localizedSpaceFunctor.obj Y)) (H : Subgroup Γ)

local notation "D" => openDomain (presentationOf Y) (S : Set (localizedSpaceFunctor.obj Y)) S.isOpen
local notation "E" => openDomain (presentationOf X)
  (c.componentImage S : Set (localizedSpaceFunctor.obj X)) (Opens.isOpen (c.componentImage S))
local notation "j" => domainι Y D
local notation "i" => domainι X E

/-- The covering map restricted to a source open and its image. -/
def componentMap : domainObj Y D ⟶ domainObj X E :=
  domainRestrict D E p (fun y hy => ⟨y, hy, rfl⟩)

@[reassoc (attr := simp)]
theorem componentMap_comp : c.componentMap S ≫ i = j ≫ p :=
  domainRestrict_comp _ _ _ _

variable (hS : c.IsDeckComponent H S)

private def componentDeck : H →* Aut (domainObj Y D) :=
  (invariantDomainAction (analyticActionOfAut (c.deck.comp H.subtype)) D
    (fun γ y hy => (hS γ y hy).2 γ.property)).ρAut

@[reassoc]
private theorem componentDeck_hom_comp (γ : H) :
    (c.componentDeck S H hS γ).asIso.hom ≫ j = j ≫ (c.deck γ).asIso.hom :=
  (invariantDomainInclusion (analyticActionOfAut (c.deck.comp H.subtype)) D
    (fun γ y hy => (hS γ y hy).2 γ.property)).comm γ

private theorem componentDeck_over (γ : H) :
    (c.componentDeck S H hS γ).asIso.hom ≫ c.componentMap S = c.componentMap S := by
  apply (cancel_mono i).mp
  rw [Category.assoc, c.componentMap_comp, c.componentDeck_hom_comp_assoc, c.deck_over]

/-- A deck component carries a Galois covering of its image with deck group `H`. -/
def restrictComponent : AnalyticGaloisCover H (c.componentMap S) := by
  let R := (localizedSpaceFunctor.map c.fst ⁻¹' (S : Set (localizedSpaceFunctor.obj Y))) ∩
    (localizedSpaceFunctor.map c.snd ⁻¹' (S : Set (localizedSpaceFunctor.obj Y)))
  have hR : IsOpen R := (S.isOpen.preimage (localizedSpaceFunctor.map c.fst).hom.continuous).inter
    (S.isOpen.preimage (localizedSpaceFunctor.map c.snd).hom.continuous)
  let Q := (presentationOf c.relation).openDomain R hR
  let k := domainι c.relation Q
  let a := domainRestrict Q D c.fst (fun _ ht => ht.1)
  let b := domainRestrict Q D c.snd (fun _ ht => ht.2)
  have ha : a ≫ j = k ≫ c.fst := domainRestrict_comp _ _ _ _
  have hb : b ≫ j = k ≫ c.snd := domainRestrict_comp _ _ _ _
  have hcomm : a ≫ c.componentMap S = b ≫ c.componentMap S := by
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, c.componentMap_comp, ← Category.assoc,
      ← Category.assoc, ha, hb, Category.assoc, Category.assoc, c.isPullback.w]
  have hpb : IsPullback a b (c.componentMap S) (c.componentMap S) := by
    apply IsPullback.mk' hcomm
    · intro T m n hma hmb
      apply (cancel_mono k).mp
      apply c.isPullback.hom_ext
      · simpa only [Category.assoc, ← ha] using congrArg (· ≫ j) hma
      · simpa only [Category.assoc, ← hb] using congrArg (· ≫ j) hmb
    · intro T m n hmn
      have h : (m ≫ j) ≫ p = (n ≫ j) ≫ p := by
        simpa only [Category.assoc, c.componentMap_comp] using congrArg (· ≫ i) hmn
      obtain ⟨t, hta, htb⟩ := c.isPullback.exists_lift _ _ h
      have ht (x : localizedSpaceFunctor.obj T) : localizedSpaceFunctor.map t x ∈ Q.carrier := by
        have h₁ := congrArg (fun f => localizedSpaceFunctor.map f x) hta
        have h₂ := congrArg (fun f => localizedSpaceFunctor.map f x) htb
        simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h₁ h₂
        change localizedSpaceFunctor.map c.fst (localizedSpaceFunctor.map t x) ∈ S ∧
          localizedSpaceFunctor.map c.snd (localizedSpaceFunctor.map t x) ∈ S
        rw [h₁, h₂]
        exact ⟨(localizedSpaceFunctor.map m x).property, (localizedSpaceFunctor.map n x).property⟩
      refine ⟨domainLift Q t ht, ?_, ?_⟩
      · apply (cancel_mono j).mp
        rwa [Category.assoc, ha, ← Category.assoc, domainLift_comp]
      · apply (cancel_mono j).mp
        rwa [Category.assoc, hb, ← Category.assoc, domainLift_comp]
  let graph (γ : H) := analyticDeckGraph hpb (c.componentDeck S H hS γ) (c.componentDeck_over S H hS γ)
  have hgraph (γ : H) : graph γ ≫ k = j ≫ c.graph γ := by
    apply c.isPullback.hom_ext
    · rw [Category.assoc, ← ha, ← Category.assoc, show graph γ ≫ a = 𝟙 _ from hpb.lift_fst _ _ _,
        Category.id_comp, Category.assoc, c.graph_fst, Category.comp_id]
    · rw [Category.assoc, ← hb, ← Category.assoc,
        show graph γ ≫ b = (c.componentDeck S H hS γ).asIso.hom from hpb.lift_snd _ _ _,
        c.componentDeck_hom_comp, Category.assoc, c.graph_snd]
  have hgraphPoint (γ : H) (y : localizedSpaceFunctor.obj (domainObj Y D)) :
      (localizedSpaceFunctor.map (graph γ) y).val = localizedSpaceFunctor.map (c.graph γ) y.val := by
    have h := hgraph γ
    change _ ≫ domainι c.relation Q = _ at h
    change @Eq (localizedSpaceFunctor.obj c.relation) _ _
    simpa only [Functor.map_comp, TopCat.comp_app, domainι_apply] using
      congrArg (fun f => localizedSpaceFunctor.map f y) h
  refine ⟨?_, ?_, c.componentDeck S H hS, c.componentDeck_over S H hS,
    domainObj c.relation Q, a, b, hpb, ?_, ?_⟩
  · apply etale_of_comp_domainι _
    rw [c.componentMap_comp]
    exact etale_comp (etaleOpenDomainStatement Y _ S.isOpen) c.etale_map
  · intro x
    obtain ⟨y, hyS, hy⟩ := x.property
    let y' : localizedSpaceFunctor.obj (domainObj Y D) := ⟨y, hyS⟩
    have h := congrArg (fun f => localizedSpaceFunctor.map f y') (c.componentMap_comp S)
    simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h
    exact ⟨y', Subtype.ext (h.trans hy)⟩
  · intro t
    obtain ⟨γ, y, hy⟩ := c.covers t.val
    change localizedSpaceFunctor.map (c.graph γ) y = t.val at hy
    have hfst : localizedSpaceFunctor.map c.fst t.val = y := by
      rw [← hy, ← TopCat.comp_app, ← Functor.map_comp, c.graph_fst, localizedSpaceFunctor.map_id]
      rfl
    have hsnd : localizedSpaceFunctor.map c.snd t.val = localizedSpaceFunctor.map (c.deck γ).asIso.hom y := by
      rw [← hy, ← TopCat.comp_app, ← Functor.map_comp, c.graph_snd]
    have hyS : y ∈ S := hfst ▸ (show localizedSpaceFunctor.map c.fst t.val ∈ S from t.property.1)
    have hγS : localizedSpaceFunctor.map (c.deck γ).asIso.hom y ∈ S :=
      hsnd ▸ (show localizedSpaceFunctor.map c.snd t.val ∈ S from t.property.2)
    let γ' : H := ⟨γ, (hS γ y hyS).1 hγS⟩
    let y' : localizedSpaceFunctor.obj (domainObj Y D) := ⟨y, hyS⟩
    exact ⟨γ', y', Subtype.ext ((hgraphPoint γ' y').trans hy)⟩
  · intro γ δ hγδ
    apply disjoint_left.mpr
    rintro t ⟨y, rfl⟩ ⟨z, hz⟩
    refine Set.disjoint_left.mp (c.disjoint_graphs (fun h => hγδ (Subtype.ext h)))
      ⟨y.val, rfl⟩ ⟨z.val, ?_⟩
    exact ((hgraphPoint δ z).symm.trans (congrArg Subtype.val hz)).trans (hgraphPoint γ y)

/-- The deck automorphisms of the component intertwine the original deck
automorphisms along the inclusion. -/
@[reassoc (attr := simp)]
theorem restrictComponent_deck_hom_comp (γ : H) :
    ((c.restrictComponent S H hS).deck γ).asIso.hom ≫ j = j ≫ (c.deck γ).asIso.hom :=
  c.componentDeck_hom_comp S H hS γ

private theorem distinguished_preimage {U : Set (localizedSpaceFunctor.obj Y)}
    (hU : IsDistinguishedOpen Y U) (f : Y ⟶ Y) :
    IsDistinguishedOpen Y (localizedSpaceFunctor.map f ⁻¹' U) :=
  ⟨hU.1.preimage (localizedSpaceFunctor.map f).hom.continuous,
    (domainPreimage f ⟨Uᶜ, hU.2⟩).is_domain⟩

private theorem distinguished_iInter {I : Type z} [Finite I]
    {W : I → Set (localizedSpaceFunctor.obj Y)} (hW : ∀ k, IsDistinguishedOpen Y (W k)) :
    IsDistinguishedOpen Y (⋂ k, W k) := by
  classical
  let := Fintype.ofFinite I
  have aux (s : Finset I) : IsDistinguishedOpen Y (⋂ k ∈ s, W k) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, iInter_false, iInter_univ]
      refine ⟨isOpen_univ, ?_⟩
      change (presentationOf Y).presentation.atlas.IsOriginalChartDomain
        (Set.univ : Set (presentationOf Y).presentation.space)ᶜ
      rw [Set.compl_univ]
      exact (presentationOf Y).presentation.atlas.isOriginalChartDomain_empty
    | insert k s _ ih =>
      have h : (⋂ l ∈ insert k s, W l) = W k ∩ ⋂ l ∈ s, W l := by
        ext x
        simp only [mem_iInter, Finset.mem_insert, mem_inter_iff]
        constructor
        · intro hx
          exact ⟨hx k (Or.inl rfl), fun l hl => hx l (Or.inr hl)⟩
        · rintro ⟨hxk, hxs⟩ l (rfl | hl)
          · exact hxk
          · exact hxs l hl
      exact h.symm ▸ (hW k).inter ih
  simpa only [Finset.mem_univ, iInter_true] using aux Finset.univ

/-- A point in a finite Galois cover of Hausdorff source has arbitrarily small
open deck components with compact closure and analytic-domain complement.
Their subgroup is the stabilizer of the chosen ordinary point. -/
theorem exists_distinguishedDeckComponent [T2Space (localizedSpaceFunctor.obj Y)] [Finite Γ]
    (y : localizedSpaceFunctor.obj Y) (N : Opens (localizedSpaceFunctor.obj Y)) (hy : y ∈ N) :
    letI := localizedSpaceAction c.deck
    ∃ S : Opens (localizedSpaceFunctor.obj Y), y ∈ S ∧ IsDistinguishedOpen Y S ∧
      closure (S : Set (localizedSpaceFunctor.obj Y)) ⊆ N ∧
      IsCompact (closure (S : Set (localizedSpaceFunctor.obj Y))) ∧
      c.IsDeckComponent (MulAction.stabilizer Γ y) S := by
  classical
  let := localizedSpaceAction c.deck
  let H := MulAction.stabilizer Γ y
  let I := {γ : Γ // γ ∉ H}
  have hsep (γ : I) : ∃ U V : Set (localizedSpaceFunctor.obj Y), IsOpen U ∧ IsOpen V ∧
      y ∈ U ∧ (γ.val • y) ∈ V ∧ Disjoint U V :=
    t2_separation (fun h => γ.property (MulAction.mem_stabilizer_iff.mpr h.symm))
  choose U V hU hV hyU hyV hUV using hsep
  let W := (N : Set (localizedSpaceFunctor.obj Y)) ∩
    ⋂ γ : I, U γ ∩ localizedSpaceFunctor.map (c.deck γ.val).asIso.hom ⁻¹' V γ
  have hW : IsOpen W := N.isOpen.inter <| isOpen_iInter_of_finite fun γ =>
    (hU γ).inter ((hV γ).preimage (localizedSpaceFunctor.map (c.deck γ.val).asIso.hom).hom.continuous)
  have hyW : y ∈ W := ⟨hy, mem_iInter.mpr fun γ => ⟨hyU γ, hyV γ⟩⟩
  obtain ⟨W₀, _, hW₀, hyW₀, h₀, hc₀, _⟩ := hasStableDistinguishedOpenNeighborhoods
    (isContinuousAction_one (X := Y) (G := PUnit.{1})) y W hW hyW
  let B : Set (localizedSpaceFunctor.obj Y) :=
    ⋂ k : H, localizedSpaceFunctor.map (c.deck k.val).asIso.hom ⁻¹' W₀
  have hB : IsDistinguishedOpen Y B := distinguished_iInter (fun k : H =>
    distinguished_preimage hW₀ (c.deck k.val).asIso.hom)
  have hBW : B ⊆ W₀ := by
    intro x hx
    have hx₁ := mem_iInter.mp hx (1 : H)
    change (1 : Γ) • x ∈ W₀ at hx₁
    rwa [one_smul] at hx₁
  have hyB : y ∈ B := by
    apply mem_iInter.mpr
    intro k
    change k.val • y ∈ W₀
    rwa [MulAction.mem_stabilizer_iff.mp k.property]
  refine ⟨⟨B, hB.1⟩, hyB, hB, ?_, ?_, ?_⟩
  · exact (closure_mono hBW).trans (h₀.trans inter_subset_left)
  · exact hc₀.of_isClosed_subset isClosed_closure (closure_mono hBW)
  · intro γ x hx
    change (γ • x ∈ B ↔ γ ∈ H)
    constructor
    · intro hxγ
      by_contra hγ
      let t : I := ⟨γ, hγ⟩
      have hxW : x ∈ W := h₀ (subset_closure (hBW hx))
      have hxγW : γ • x ∈ W := h₀ (subset_closure (hBW hxγ))
      exact Set.disjoint_left.mp (hUV t) (mem_iInter.mp hxγW.2 t).1
        (mem_iInter.mp hxW.2 t).2
    · intro hγ
      apply mem_iInter.mpr
      intro k
      change k.val • (γ • x) ∈ W₀
      rw [← mul_smul]
      exact mem_iInter.mp hx (k * ⟨γ, hγ⟩)

/-- In a deck component of a point stabilizer, the chosen fibre contains only
its chosen ordinary point. -/
theorem eq_of_mem_stabilizerComponent {y x : localizedSpaceFunctor.obj Y}
    (hy : y ∈ S) (hx : x ∈ S)
    (h : localizedSpaceFunctor.map p y = localizedSpaceFunctor.map p x)
    (hS : letI := localizedSpaceAction c.deck
      c.IsDeckComponent (MulAction.stabilizer Γ y) S) : x = y := by
  let := localizedSpaceAction c.deck
  obtain ⟨γ, hγ⟩ := c.fibre_transitive y x h
  have hmem := (hS γ y hy).1 (hγ.symm ▸ hx)
  exact hγ.symm.trans (MulAction.mem_stabilizer_iff.mp hmem)

end Langlands.Analytic.SaturatedAtlasPresentation.AnalyticGaloisCover
