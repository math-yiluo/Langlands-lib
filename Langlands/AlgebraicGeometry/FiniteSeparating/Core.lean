import Langlands.AlgebraicGeometry.FiniteSeparatingSectionsStatement
import Langlands.AlgebraicGeometry.LinearSystemMorphismProof
import Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.AlgebraicGeometry.Modules.SectionResidueComparison
import Langlands.AlgebraicGeometry.FiniteSeparating.Span
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio
import Langlands.AlgebraicGeometry.LinearSystem.DualNumberPoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finitely many separating sections, assuming the local criterion

`finiteSeparatingSections_of` derives `FiniteSeparatingSectionsStatement` from
`ProperRationalImmersionLocalClosedImmersionStatement`, using the published proof
`linearSystemMorphism`.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteSeparating

section Jacobson

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K))

/-- An open containing every rational point is everything. -/
lemma eq_top_of_forall_rationalPoint_mem [LocallyOfFiniteType p] (U : X.Opens)
    (hU : ∀ x : Spec (CommRingCat.of K) ⟶ X, IsRationalPoint p x →
      x (IsLocalRing.closedPoint K) ∈ U) : U = ⊤ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, z ∉ U := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun z _ ↦ h z)
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints (Z := (U : Set X)ᶜ) ⟨z, hz⟩
    U.isOpen.isClosed_compl.isLocallyClosed
  have hcc' : IsClosed {c} := hcc
  apply hc
  have := hU _ (pointOfClosedPoint_comp p c hcc')
  have h : (pointOfClosedPoint p c hcc') (IsLocalRing.closedPoint K) = c :=
    pointOfClosedPoint_apply p c hcc' _
  rw [h] at this
  exact this

end Jacobson

/-- Morphisms that agree after `f`, one of them landing in `f⁻¹ V` where `f` restricts to a
monomorphism, are equal. -/
lemma eq_of_comp_eq_of_mono {X Y T : Scheme.{u}} {f : X ⟶ Y} {V : Y.Opens} [Mono (f ∣_ V)]
    {g₁ g₂ : T ⟶ X} (h₁ : ∀ τ, f (g₁ τ) ∈ V) (H : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ := by
  have h₂ : ∀ τ, f (g₂ τ) ∈ V := fun τ ↦ by
    have := h₁ τ
    rwa [← Scheme.Hom.comp_apply, H, Scheme.Hom.comp_apply] at this
  have r₁ : Set.range g₁ ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨τ, rfl⟩
    exact h₁ τ
  have r₂ : Set.range g₂ ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨τ, rfl⟩
    exact h₂ τ
  have key : IsOpenImmersion.lift _ _ r₁ = IsOpenImmersion.lift _ _ r₂ := by
    rw [← cancel_mono (f ∣_ V), ← cancel_mono V.ι, Category.assoc, Category.assoc,
      morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, H]
  calc g₁ = IsOpenImmersion.lift _ _ r₁ ≫ (f ⁻¹ᵁ V).ι := (IsOpenImmersion.lift_fac _ _ _).symm
    _ = IsOpenImmersion.lift _ _ r₂ ≫ (f ⁻¹ᵁ V).ι := by rw [key]
    _ = g₂ := IsOpenImmersion.lift_fac _ _ _

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of K)} (L : LineBundle X)

/-- Finitely many sections without common zero. -/
lemma exists_finset_forall_mem [IsProper p] (hL : SeparatesPointsAndTangents p L) :
    ∃ S₀ : Finset (GlobalSections L.obj), ∀ z : X, ∃ σ ∈ S₀,
      z ∈ trivializationOpen L.obj σ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have htop : (⨆ σ : GlobalSections L.obj, trivializationOpen L.obj σ) = ⊤ := by
    apply eq_top_of_forall_rationalPoint_mem p
    intro x hx
    obtain ⟨σ, hσ⟩ := hL.1 x hx
    rw [LinearSystem.vanishesAlong_iff_not_mem, not_not] at hσ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨σ, hσ⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun σ : GlobalSections L.obj ↦ (trivializationOpen L.obj σ : Set X))
    (fun σ ↦ (trivializationOpen L.obj σ).isOpen) (fun z _ ↦ by
      have hz : z ∈ (⨆ σ : GlobalSections L.obj, trivializationOpen L.obj σ) := by
        rw [htop]; trivial
      obtain ⟨σ, hσ⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact Set.mem_iUnion.mpr ⟨σ, hσ⟩)
  refine ⟨t, fun z ↦ ?_⟩
  obtain ⟨σ, hσ, hz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  exact ⟨σ, hσ, hz⟩

variable (p) in
/-- The union of the nonvanishing loci of the combinations of `S` vanishing at `x`. -/
def awayOpen (S : Finset (GlobalSections L.obj)) (x : Spec (CommRingCat.of K) ⟶ X) : X.Opens :=
  ⨆ (σ : GlobalSections L.obj) (_ : InSpan p L S σ ∧ VanishesAlong L x σ),
    trivializationOpen L.obj σ

omit [IsAlgClosed K] in
lemma mem_awayOpen_iff {S : Finset (GlobalSections L.obj)} {x : Spec (CommRingCat.of K) ⟶ X}
    {z : X} : z ∈ awayOpen p L S x ↔
      ∃ σ, (InSpan p L S σ ∧ VanishesAlong L x σ) ∧ z ∈ trivializationOpen L.obj σ := by
  simp only [awayOpen, TopologicalSpace.Opens.mem_iSup, exists_prop]

omit [IsAlgClosed K] in
lemma awayOpen_mono {S S' : Finset (GlobalSections L.obj)} (h : S ⊆ S')
    (x : Spec (CommRingCat.of K) ⟶ X) : awayOpen p L S x ≤ awayOpen p L S' x := fun z hz ↦ by
  obtain ⟨σ, hσ, hz⟩ := (mem_awayOpen_iff L).mp hz
  exact (mem_awayOpen_iff L).mpr ⟨σ, ⟨hσ.1.mono h, hσ.2⟩, hz⟩

omit [IsAlgClosed K] in
/-- Some finite enlargement of `S₀` separates `x` from all other rational points. -/
lemma exists_separates_points [IsProper p] (hL : SeparatesPointsAndTangents p L)
    {x : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x)
    (S₀ : Finset (GlobalSections L.obj)) :
    ∃ S, S₀ ⊆ S ∧ ∀ y, IsRationalPoint p y → x ≠ y →
      ∃ σ, InSpan p L S σ ∧ VanishesAlong L x σ ∧ ¬ VanishesAlong L y σ := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  obtain ⟨_, ⟨S, hS, rfl⟩, hmax⟩ := (wellFounded_gt (α := X.Opens)).has_min
    {O | ∃ S, S₀ ⊆ S ∧ awayOpen p L S x = O} ⟨_, S₀, subset_rfl, rfl⟩
  refine ⟨S, hS, fun y hy hxy ↦ ?_⟩
  obtain ⟨σ₁, h₁x, h₁y⟩ := hL.2.1 x y hx hy hxy
  by_cases hmem : y (IsLocalRing.closedPoint K) ∈ awayOpen p L S x
  · obtain ⟨σ, ⟨hσS, hσx⟩, hσy⟩ := (mem_awayOpen_iff L).mp hmem
    exact ⟨σ, hσS, hσx, by rw [LinearSystem.vanishesAlong_iff_not_mem, not_not]; exact hσy⟩
  · exfalso
    refine hmax (awayOpen p L (insert σ₁ S) x)
      ⟨insert σ₁ S, hS.trans (Finset.subset_insert _ _), rfl⟩ ?_
    refine lt_of_le_of_ne (awayOpen_mono L (Finset.subset_insert _ _) x) fun heq ↦ hmem ?_
    rw [heq, mem_awayOpen_iff L]
    refine ⟨σ₁, ⟨inSpan_of_mem (Finset.mem_insert_self _ _), h₁x⟩, ?_⟩
    rwa [LinearSystem.vanishesAlong_iff_not_mem, not_not] at h₁y

variable (p) in
/-- The ideal of `Γ(U, ⊤)` generated by the ratios to `s₀` of the combinations of `S`
vanishing at `x`. -/
def ratioIdeal (U : X.Opens) (s₀ : GlobalSections L.obj) (S : Finset (GlobalSections L.obj))
    (x : Spec (CommRingCat.of K) ⟶ X) : Ideal Γ(U, ⊤) :=
  Ideal.span ((fun σ ↦ LinearSystem.sectionRatio L U.ι σ s₀) ''
    {σ | InSpan p L S σ ∧ VanishesAlong L x σ})

omit [IsAlgClosed K] in
/-- Some finite enlargement of `S₁` separates `x` from all nonzero tangent vectors at `x`. -/
lemma exists_separates_tangents [IsProper p] (hL : SeparatesPointsAndTangents p L)
    {x : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x)
    (S₁ : Finset (GlobalSections L.obj)) :
    ∃ S, S₁ ⊆ S ∧ ∀ t, IsNonzeroTangentVectorAt p x t →
      ∃ σ, InSpan p L S σ ∧ VanishesAlong L x σ ∧ ¬ VanishesAlong L t σ := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨s₀, hs₀⟩ := hL.1 x hx
  rw [LinearSystem.vanishesAlong_iff_not_mem, not_not] at hs₀
  obtain ⟨U, hU, hxU, hUs⟩ := exists_isAffineOpen_mem_and_subset hs₀
  have : IsAffine U := hU
  have : IsNoetherianRing Γ(U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U⟩
  have hUι : ∀ τ, U.ι τ ∈ trivializationOpen L.obj s₀ := fun τ ↦ by
    have hτ : U.ι τ ∈ Set.range U.ι := ⟨τ, rfl⟩
    rw [Scheme.Opens.range_ι] at hτ
    exact hUs hτ
  obtain ⟨_, ⟨S, hS, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian Γ(U, ⊤) Γ(U, ⊤))
    {I | ∃ S, S₁ ⊆ S ∧ ratioIdeal p L U s₀ S x = I} ⟨_, S₁, subset_rfl, rfl⟩
  refine ⟨S, hS, fun t ht ↦ ?_⟩
  obtain ⟨σ₁, h₁x, h₁t⟩ := hL.2.2 x hx t ht
  by_contra hcon
  push Not at hcon
  have htU : ∀ τ, t τ ∈ U := LinearSystem.forall_mem_of_augmentation_comp ht.1.2 hxU
  have hrange : Set.range t ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨τ, rfl⟩
    exact htU τ
  have ht' : IsOpenImmersion.lift U.ι t hrange ≫ U.ι = t := IsOpenImmersion.lift_fac _ _ _
  have htrat : ∀ τ, t τ ∈ trivializationOpen L.obj s₀ := fun τ ↦ hUs (htU τ)
  have hvan : ∀ σ, VanishesAlong L t σ ↔
      (IsOpenImmersion.lift U.ι t hrange).appTop (LinearSystem.sectionRatio L U.ι σ s₀) = 0 := by
    intro σ
    rw [LinearSystem.vanishesAlong_iff_sectionRatio_eq_zero htrat,
      ← LinearSystem.sectionRatio_comp hUι, ht']
  have hJ : ratioIdeal p L U s₀ S x ≤ RingHom.ker (IsOpenImmersion.lift U.ι t hrange).appTop.hom := by
    rw [ratioIdeal, Ideal.span_le]
    rintro _ ⟨σ, ⟨hσS, hσx⟩, rfl⟩
    exact RingHom.mem_ker.mpr ((hvan σ).mp (hcon σ hσS hσx))
  have hJ' : ratioIdeal p L U s₀ (insert σ₁ S) x = ratioIdeal p L U s₀ S x := by
    have hle : ratioIdeal p L U s₀ S x ≤ ratioIdeal p L U s₀ (insert σ₁ S) x :=
      Ideal.span_mono (Set.image_mono fun σ hσ ↦
        ⟨hσ.1.mono (Finset.subset_insert _ _), hσ.2⟩)
    by_contra hne
    exact hmax _ ⟨insert σ₁ S, hS.trans (Finset.subset_insert _ _), rfl⟩
      (lt_of_le_of_ne hle (Ne.symm hne))
  have h₁mem : LinearSystem.sectionRatio L U.ι σ₁ s₀ ∈ ratioIdeal p L U s₀ S x := by
    rw [← hJ']
    exact Ideal.subset_span ⟨σ₁, ⟨inSpan_of_mem (Finset.mem_insert_self _ _), h₁x⟩, rfl⟩
  exact h₁t ((hvan σ₁).mpr (RingHom.mem_ker.mp (hJ h₁mem)))

/-- If the span of `S` (with no common zero) separates at `x`, it separates at all rational
points of a neighbourhood of `x`. -/
lemma exists_open_separatesAt
    (hLoc : ProperRationalImmersionLocalClosedImmersionStatement.{u}) [IsProper p]
    {S : Finset (GlobalSections L.obj)}
    (hbpf : ∀ z : X, ∃ σ ∈ S, z ∈ trivializationOpen L.obj σ)
    {x : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x) (hS : SeparatesAt p L S x) :
    ∃ W : X.Opens, x (IsLocalRing.closedPoint K) ∈ W ∧
      ∀ x', IsRationalPoint p x' → x' (IsLocalRing.closedPoint K) ∈ W →
        SeparatesAt p L S x' := by
  have hs : ∀ z : X, ∃ i, z ∈ nonvanishingLocus L.obj (enum S i) := by
    intro z
    obtain ⟨σ, hσ, hz⟩ := hbpf z
    obtain ⟨i, hi⟩ := exists_enum_eq hσ
    refine ⟨i, ?_⟩
    rw [hi, lineBundleResidueOpenComparison X L σ]
    exact hz
  obtain ⟨φ, hφ, h1, h2⟩ := linearSystemMorphism K X p L S.card (enum S) hs
  have : IsProper (φ ≫ projectiveSpaceToSpec K S.card) := by rw [hφ]; infer_instance
  have : IsProper φ := IsProper.of_comp (f := φ) (g := projectiveSpaceToSpec K S.card)
  obtain ⟨V, hxV, hV⟩ := hLoc K X (ProjectiveSpace K S.card) p (projectiveSpaceToSpec K S.card)
    φ hφ x hx (fun y hy hyx ↦ by
      by_contra hne
      obtain ⟨σ, hσS, hσx, hσy⟩ := hS.1 y hy (Ne.symm hne)
      obtain ⟨c, rfl⟩ := (inSpan_iff S σ).mp hσS
      exact hσy ((h1 x y hx hy).mp hyx.symm c hσx))
    (fun t ht htx ↦ by
      by_contra hne
      obtain ⟨σ, hσS, hσx, hσt⟩ := hS.2 t ⟨ht, hne⟩
      obtain ⟨c, rfl⟩ := (inSpan_iff S σ).mp hσS
      exact hσt ((h2 x t hx ht).mp htx c hσx))
  have : IsClosedImmersion (φ ∣_ V) := hV
  refine ⟨φ ⁻¹ᵁ V, hxV, fun x' hx' hx'W ↦ ⟨fun y hy hne ↦ ?_, fun t ht ↦ ?_⟩⟩
  · by_contra hcon
    push Not at hcon
    apply hne
    refine eq_of_comp_eq_of_mono (f := φ) (V := V) (fun τ ↦ ?_)
      ((h1 x' y hx' hy).mpr fun c hc ↦ hcon _ ((inSpan_iff S _).mpr ⟨c, rfl⟩) hc)
    exact LinearSystem.forall_mem_of_mem hx'W τ
  · by_contra hcon
    push Not at hcon
    apply ht.2
    refine eq_of_comp_eq_of_mono (f := φ) (V := V) (fun τ ↦ ?_)
      ((h2 x' t hx' ht.1).mpr fun c hc ↦ hcon _ ((inSpan_iff S _).mpr ⟨c, rfl⟩) hc)
    exact LinearSystem.forall_mem_of_augmentation_comp ht.1.2 hx'W τ

end Langlands.AlgebraicGeometry.FiniteSeparating

namespace Langlands.AlgebraicGeometry

open FiniteSeparating

/-- The finite-family statement follows from the local closed-immersion criterion,
using the published linear-system morphism. -/
theorem finiteSeparatingSections_of
    (hLoc : ProperRationalImmersionLocalClosedImmersionStatement.{u}) :
    FiniteSeparatingSectionsStatement.{u} := by
  intro K _ _ X p L hp hL
  classical
  obtain ⟨S₀, hS₀⟩ := exists_finset_forall_mem L hL
  have hloc : ∀ x : {x : Spec (CommRingCat.of K) ⟶ X // IsRationalPoint p x},
      ∃ S : Finset (GlobalSections L.obj), S₀ ⊆ S ∧ ∃ W : X.Opens,
        x.1 (IsLocalRing.closedPoint K) ∈ W ∧ ∀ x', IsRationalPoint p x' →
          x' (IsLocalRing.closedPoint K) ∈ W → SeparatesAt p L S x' := by
    rintro ⟨x, hx⟩
    obtain ⟨S₁, h01, hS₁⟩ := exists_separates_points L hL hx S₀
    obtain ⟨S₂, h12, hS₂⟩ := exists_separates_tangents L hL hx S₁
    have hsep : SeparatesAt p L S₂ x := ⟨fun y hy hne ↦
      let ⟨σ, h₁, h₂, h₃⟩ := hS₁ y hy hne
      ⟨σ, h₁.mono h12, h₂, h₃⟩, hS₂⟩
    obtain ⟨W, hxW, hW⟩ := exists_open_separatesAt L hLoc
      (fun z ↦ let ⟨σ, hσ, hz⟩ := hS₀ z; ⟨σ, h01.trans h12 hσ, hz⟩) hx hsep
    exact ⟨S₂, h01.trans h12, W, hxW, hW⟩
  choose Sx _ Wx hxW hW using hloc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have htop : (⨆ x, Wx x) = ⊤ := eq_top_of_forall_rationalPoint_mem p _ fun x hx ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (Wx x : Set X))
    (fun x ↦ (Wx x).isOpen) (fun z _ ↦ by
      have hz : z ∈ (⨆ x, Wx x) := by rw [htop]; trivial
      obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact Set.mem_iUnion.mpr ⟨x, hx⟩)
  let S := S₀ ∪ F.biUnion Sx
  have hsepS : ∀ x', IsRationalPoint p x' → SeparatesAt p L S x' := by
    intro x' hx'
    obtain ⟨x, hxF, hx'W⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ (x' (IsLocalRing.closedPoint K))))
    exact (hW x x' hx' hx'W).mono
      ((Finset.subset_biUnion_of_mem Sx hxF).trans Finset.subset_union_right)
  refine ⟨S.card, enum S, fun z ↦ ?_, fun x y hx hy hne ↦ ?_, fun x hx t ht ↦ ?_⟩
  · obtain ⟨σ, hσ, hz⟩ := hS₀ z
    obtain ⟨i, hi⟩ := exists_enum_eq (Finset.mem_union_left _ hσ)
    refine ⟨i, ?_⟩
    rw [hi, lineBundleResidueOpenComparison X L σ]
    exact hz
  · obtain ⟨σ, hσS, hσx, hσy⟩ := (hsepS x hx).1 y hy hne
    obtain ⟨c, rfl⟩ := (inSpan_iff S σ).mp hσS
    exact ⟨c, hσx, hσy⟩
  · obtain ⟨σ, hσS, hσx, hσt⟩ := (hsepS x hx).2 t ht
    obtain ⟨c, rfl⟩ := (inSpan_iff S σ).mp hσS
    exact ⟨c, hσx, hσt⟩

end Langlands.AlgebraicGeometry
