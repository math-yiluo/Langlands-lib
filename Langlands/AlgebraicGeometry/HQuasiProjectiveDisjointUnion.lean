import Langlands.AlgebraicGeometry.HQuasiProjective
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateEmbedding
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finite disjoint unions of H-quasi-projective schemes

If a scheme `X` over `Spec A` is covered by finitely many pairwise disjoint opens, each of which
is H-quasi-projective over `Spec A`, then `X` is H-quasi-projective over `Spec A`. The immersions
of the pieces are composed with coordinate embeddings into one projective space, using disjoint
blocks of coordinates, and glued. Every H-quasi-projective scheme is quasi-compact, so the finite
version also gives a version for arbitrary disjoint open covers.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.AlgebraicGeometry

variable {A : Type u} [CommRing A]

instance compactSpace_projectiveSpace (n : ℕ) : CompactSpace (ProjectiveSpace A n) :=
  QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceToSpec A n)

/-- An H-quasi-projective scheme is quasi-compact. -/
theorem IsHQuasiProjective.compactSpace {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of A)}
    (hp : IsHQuasiProjective p) : CompactSpace X := by
  obtain ⟨n, i, -, hqc, -⟩ := hp
  exact QuasiCompact.compactSpace_of_compactSpace i

/-- A morphism from an empty scheme is H-quasi-projective. -/
theorem isHQuasiProjective_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (p : X ⟶ Spec (CommRingCat.of A)) : IsHQuasiProjective p :=
  ⟨0, isInitialOfIsEmpty.to _, inferInstance, inferInstance, isInitialOfIsEmpty.hom_ext _ _⟩

/-- The pullback of two disjoint opens is empty. -/
lemma isEmpty_pullback_of_disjoint {X : Scheme.{u}} {U V : X.Opens} (h : Disjoint U V) :
    IsEmpty (pullback (C := Scheme.{u}) U.ι V.ι) := by
  refine ⟨fun z => ?_⟩
  have hz : U.ι (pullback.fst U.ι V.ι z) = V.ι (pullback.snd U.ι V.ι z) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have h1 : U.ι (pullback.fst U.ι V.ι z) ∈ U := (pullback.fst U.ι V.ι z).2
  have h2 : U.ι (pullback.fst U.ι V.ι z) ∈ V := by
    rw [hz]; exact (pullback.snd U.ι V.ι z).2
  have h3 : U.ι (pullback.fst U.ι V.ι z) ∈ U ⊓ V := ⟨h1, h2⟩
  rw [h.eq_bot] at h3
  simp at h3

/-- The opens of a cover by pairwise disjoint opens `V θ` that contain a point `x ∈ V θ'` are
exactly the `V θ'`. -/
lemma mem_iff_of_disjoint {X : Scheme.{u}} {ι : Type v} {V : ι → X.Opens}
    (hdisj : Pairwise fun θ θ' => Disjoint (V θ) (V θ')) {θ θ' : ι} {x : X} (hx : x ∈ V θ') :
    x ∈ V θ ↔ θ = θ' := by
  refine ⟨fun h => ?_, fun h => h ▸ hx⟩
  by_contra hne
  have h3 : x ∈ V θ ⊓ V θ' := ⟨h, hx⟩
  rw [(hdisj hne).eq_bot] at h3
  simp at h3

/-- If `X` over `Spec A` is covered by finitely many pairwise disjoint opens, each of which is
H-quasi-projective over `Spec A`, then `X` is H-quasi-projective over `Spec A`. -/
theorem isHQuasiProjective_of_disjoint_cover {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of A)}
    {ι : Type v} [Finite ι] (V : ι → X.Opens)
    (hdisj : Pairwise fun θ θ' => Disjoint (V θ) (V θ')) (hcov : ⨆ θ, V θ = ⊤)
    (hV : ∀ θ, IsHQuasiProjective ((V θ).ι ≫ p)) : IsHQuasiProjective p := by
  classical
  have := Fintype.ofFinite ι
  have hcpt : ∀ θ, CompactSpace (V θ) := fun θ => (hV θ).compactSpace
  have hmem : ∀ x : X, ∃ θ, x ∈ V θ := fun x => by
    have hx : x ∈ (⨆ θ, V θ) := hcov ▸ trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  choose n i hi hqc hcomm using hV
  -- disjoint blocks of coordinates in one projective space
  let κ := Σ θ, Fin (n θ + 1)
  let N := Fintype.card κ
  let eq : Option κ ≃ Fin (N + 1) :=
    Fintype.equivFinOfCardEq (by simp [N, κ, Fintype.card_option])
  let e : ∀ θ, Fin (n θ + 1) → Fin (N + 1) := fun θ k => eq (some ⟨θ, k⟩)
  have he : ∀ θ, Function.Injective (e θ) := fun θ =>
    eq.injective.comp ((Option.some_injective _).comp sigma_mk_injective)
  have hblock : ∀ {θ θ' : ι} (j : Fin (n θ' + 1)) (k : Fin (n θ + 1)), θ ≠ θ' →
      e θ' j ≠ e θ k := fun j k hne h =>
    hne (congrArg Sigma.fst (Option.some_injective _ (eq.injective h))).symm
  have hnone : ∀ θ (j : Fin (n θ + 1)), e θ j ≠ eq none := fun θ j h => by
    simpa using eq.injective h
  let c : ∀ θ, ProjectiveSpace A (n θ) ⟶ ProjectiveSpace A N := fun θ =>
    coordinateEmbedding A (he θ)
  -- glue the embeddings of the pieces
  let 𝒰 := X.openCoverOfIsOpenCover V hcov
  let f : ∀ θ, 𝒰.X θ ⟶ ProjectiveSpace A N := fun θ => i θ ≫ c θ
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [(cancel_mono (𝒰.f x)).1 pullback.condition]
    · have : IsEmpty (pullback (C := Scheme.{u}) (𝒰.f x) (𝒰.f y)) :=
        isEmpty_pullback_of_disjoint (hdisj hxy)
      exact isInitialOfIsEmpty.hom_ext _ _
  let g := 𝒰.glueMorphisms f hf
  have hg : ∀ θ, (V θ).ι ≫ g = i θ ≫ c θ := fun θ => 𝒰.ι_glueMorphisms f hf θ
  have hcomm' : g ≫ projectiveSpaceToSpec A N = p := by
    refine 𝒰.hom_ext _ _ fun θ => ?_
    change (V θ).ι ≫ _ = (V θ).ι ≫ _
    rw [reassoc_of% (hg θ), coordinateEmbedding_toSpec, hcomm θ]
  have hXc : CompactSpace X := by
    refine ⟨?_⟩
    have huniv : (Set.univ : Set X) = ⋃ θ, (V θ : Set X) := by
      ext x
      simpa using hmem x
    rw [huniv]
    refine isCompact_iUnion fun θ => ?_
    rw [← Scheme.Opens.range_ι]
    exact isCompact_range (V θ).ι.continuous
  -- the open cover of the target by the coordinate blocks
  let W : Option ι → (ProjectiveSpace A N).Opens := fun o =>
    o.elim (projectiveSpaceCoordinateOpen A N (eq none))
      (fun θ => ⨆ k, projectiveSpaceCoordinateOpen A N (e θ k))
  have hW : iSup W = ⊤ := by
    rw [eq_top_iff, ← iSup_projectiveSpaceCoordinateOpen A N]
    refine iSup_le fun k => ?_
    obtain ⟨o, rfl⟩ := eq.surjective k
    cases o with
    | none => exact le_iSup W none
    | some s =>
      exact (le_iSup (fun j => projectiveSpaceCoordinateOpen A N (e s.1 j)) s.2).trans
        (le_iSup W (some s.1))
  have key : ∀ (θ' : ι) (y : (V θ').toScheme) (o : Option ι),
      g ((V θ').ι y) ∈ W o ↔ o = some θ' := by
    intro θ' y o
    rw [← Scheme.Hom.comp_apply, hg θ', Scheme.Hom.comp_apply,
      ← Scheme.Hom.mem_preimage (c θ')]
    cases o with
    | none =>
      change i θ' y ∈ c θ' ⁻¹ᵁ projectiveSpaceCoordinateOpen A N (eq none) ↔ _
      rw [coordinateEmbedding_preimage_eq_bot A (he θ') _ (hnone θ')]
      simp
    | some θ =>
      change i θ' y ∈ c θ' ⁻¹ᵁ (⨆ k, projectiveSpaceCoordinateOpen A N (e θ k)) ↔ _
      rw [Scheme.Hom.preimage_iSup, TopologicalSpace.Opens.mem_iSup]
      by_cases h : θ = θ'
      · subst h
        simp only [c, coordinateEmbedding_preimage_apply]
        have hy : i θ y ∈ (⨆ k, projectiveSpaceCoordinateOpen A (n θ) k) := by
          rw [iSup_projectiveSpaceCoordinateOpen]; trivial
        simpa [TopologicalSpace.Opens.mem_iSup] using hy
      · have hk : ∀ k, c θ' ⁻¹ᵁ projectiveSpaceCoordinateOpen A N (e θ k) = ⊥ := fun k =>
          coordinateEmbedding_preimage_eq_bot A (he θ') _ fun j => hblock j k h
        simp only [hk]
        simp [h]
  have hpre : ∀ o, g ⁻¹ᵁ W o = o.elim ⊥ V := by
    intro o
    ext x
    obtain ⟨θ', hx⟩ := hmem x
    have := key θ' ⟨x, hx⟩ o
    rw [Scheme.Opens.ι_apply] at this
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, this]
    cases o with
    | none => simp
    | some θ =>
      change _ ↔ x ∈ V θ
      rw [mem_iff_of_disjoint hdisj hx, Option.some_inj]
  have hsome : ∀ θ, g ⁻¹ᵁ W (some θ) = V θ := fun θ => hpre (some θ)
  refine ⟨N, g, ?_, ?_, hcomm'⟩
  · refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun o => ?_
    cases o with
    | none =>
      have hx : ∀ z : X, z ∈ g ⁻¹ᵁ W none → False := fun z hz => by
        rw [hpre] at hz
        simp at hz
      have : IsEmpty (g ⁻¹ᵁ W none) := ⟨fun x => hx _ x.2⟩
      infer_instance
    | some θ =>
      have h1 : (g ∣_ W (some θ)) ≫ (W (some θ)).ι =
          (Scheme.isoOfEq X (hsome θ)).hom ≫ i θ ≫ c θ := by
        rw [morphismRestrict_ι, ← hg θ, ← Category.assoc, Scheme.isoOfEq_hom_ι]
      have : IsImmersion ((g ∣_ W (some θ)) ≫ (W (some θ)).ι) := by
        rw [h1]; infer_instance
      exact IsImmersion.of_comp _ (W (some θ)).ι
  · have : QuasiCompact (g ≫ projectiveSpaceToSpec A N) := by
      rw [hcomm']; infer_instance
    exact QuasiCompact.of_comp g (projectiveSpaceToSpec A N)

/-- A quasi-compact scheme with an immersion into an H-projective scheme over `Spec A` is
H-quasi-projective over `Spec A`. -/
theorem isHQuasiProjective_of_isImmersion_of_isHProjective {X Y : Scheme.{u}} [CompactSpace X]
    (k : X ⟶ Y) [IsImmersion k] {q : Y ⟶ Spec (CommRingCat.of A)} (hq : IsHProjective q) :
    IsHQuasiProjective (k ≫ q) := by
  obtain ⟨n, c, hc, hcq⟩ := hq
  have : IsClosedImmersion c := hc
  refine ⟨n, k ≫ c, inferInstance, ?_, by rw [Category.assoc, hcq]⟩
  have : QuasiCompact ((k ≫ c) ≫ projectiveSpaceToSpec A n) := inferInstance
  exact QuasiCompact.of_comp (k ≫ c) (projectiveSpaceToSpec A n)

/-- If a quasi-compact scheme `X` over `Spec A` is covered by pairwise disjoint opens, each of
which is H-quasi-projective over `Spec A`, then `X` is H-quasi-projective over `Spec A`. -/
theorem isHQuasiProjective_of_disjoint_cover_of_compactSpace {X : Scheme.{u}} [CompactSpace X]
    {p : X ⟶ Spec (CommRingCat.of A)} {ι : Type v} (V : ι → X.Opens)
    (hdisj : Pairwise fun θ θ' => Disjoint (V θ) (V θ')) (hcov : ⨆ θ, V θ = ⊤)
    (hV : ∀ θ, IsHQuasiProjective ((V θ).ι ≫ p)) : IsHQuasiProjective p := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun θ => (V θ : Set X))
    (fun θ => (V θ).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ θ, V θ) := hcov ▸ trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hx)
  refine isHQuasiProjective_of_disjoint_cover (ι := t) (fun θ => V θ)
    (fun θ θ' h => hdisj fun h' => h (Subtype.ext h')) ?_ (fun θ => hV θ)
  rw [eq_top_iff]
  intro x _
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
  obtain ⟨θ, hθ, hx⟩ := hx
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨⟨θ, hθ⟩, hx⟩

/-- Each member of a cover by pairwise disjoint opens is closed. -/
lemma isClosed_of_disjoint_cover {X : Scheme.{u}} {ι : Type v} {V : ι → X.Opens}
    (hdisj : Pairwise fun θ θ' => Disjoint (V θ) (V θ')) (hcov : ⨆ θ, V θ = ⊤) (θ : ι) :
    IsClosed (V θ : Set X) := by
  have e : (V θ : Set X)ᶜ = ⋃ (θ' : ι) (_ : θ' ≠ θ), (V θ' : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_iUnion, exists_prop]
    have hx : x ∈ (⨆ θ, V θ) := hcov ▸ trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨θ', hx⟩ := hx
    constructor
    · intro hn
      exact ⟨θ', fun e => hn (e ▸ hx), hx⟩
    · rintro ⟨θ'', hne, hx''⟩ hxθ
      exact hne ((mem_iff_of_disjoint hdisj hx'').mp hxθ).symm
  rw [← isOpen_compl_iff, e]
  exact isOpen_biUnion fun θ' _ => (V θ').isOpen

/-- A quasi-compact scheme over `Spec A` with an immersion `j` into a scheme `H` over `Spec A`
that is covered by pairwise disjoint H-projective opens is H-quasi-projective over `Spec A`. -/
theorem isHQuasiProjective_of_isImmersion_of_disjoint_cover {X H : Scheme.{u}} [CompactSpace X]
    (j : X ⟶ H) [IsImmersion j] (πH : H ⟶ Spec (CommRingCat.of A)) {ι : Type v}
    (U : ι → H.Opens) (hdisj : Pairwise fun θ θ' => Disjoint (U θ) (U θ'))
    (hcov : ⨆ θ, U θ = ⊤) (hU : ∀ θ, IsHProjective ((U θ).ι ≫ πH)) :
    IsHQuasiProjective (j ≫ πH) := by
  let V : ι → X.Opens := fun θ => j ⁻¹ᵁ U θ
  have hVdisj : Pairwise fun θ θ' => Disjoint (V θ) (V θ') := fun θ θ' h => by
    simp only [V, disjoint_iff, ← Scheme.Hom.preimage_inf, (hdisj h).eq_bot,
      Scheme.Hom.preimage_bot]
  have hVcov : ⨆ θ, V θ = ⊤ := by
    simp only [V, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  refine isHQuasiProjective_of_disjoint_cover_of_compactSpace V hVdisj hVcov fun θ => ?_
  have : CompactSpace (V θ) := isCompact_iff_compactSpace.mp
    (isClosed_of_disjoint_cover hVdisj hVcov θ).isCompact
  have e : (V θ).ι ≫ j ≫ πH = (j ∣_ U θ) ≫ (U θ).ι ≫ πH := by
    rw [morphismRestrict_ι_assoc]
  rw [e]
  have : IsImmersion (j ∣_ U θ) := IsZariskiLocalAtTarget.restrict ‹_› (U θ)
  exact isHQuasiProjective_of_isImmersion_of_isHProjective (j ∣_ U θ) (hU θ)

end Langlands.AlgebraicGeometry
