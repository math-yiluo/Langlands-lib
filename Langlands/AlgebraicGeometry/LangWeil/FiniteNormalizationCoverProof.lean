import Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverAffine

/-! # Finite normalization covers over Noetherian bases

Proof of `FiniteNormalizationCoverStatement`. Finitely many affine charts `V ⊆ f⁻¹ W`
cover the quasi-compact source; the affine pieces of each chart, transported along the
open immersions `Spec Γ(X, V) → X` and `Spec Γ(S, W) → S`, form the cover. -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

open NormalizationCoverConstruction

/-- A locally finite type, quasi-compact morphism to a Noetherian scheme has a finite
normalization cover. -/
theorem finiteNormalizationCover : FiniteNormalizationCoverStatement.{u} := by
  intro S X f hS hf hqc
  have key : ∀ x : X, ∃ (W : S.Opens) (_ : IsAffineOpen W) (V : X.Opens) (_ : IsAffineOpen V)
      (_ : V ≤ f ⁻¹ᵁ W), x ∈ V := by
    intro x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (f ⁻¹ᵁ W : Set X) from hxW)
        (f ⁻¹ᵁ W).2
    exact ⟨W, hW, V, hV, hVW, hxV⟩
  choose W hW V hV e hxV using key
  have hloc : ∀ x : X, ∃ s : Set (Piece f), s.Finite ∧
      ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ X), Set.range y ⊆ V x →
        ∃ p ∈ s, ∃ z : Spec (.of K) ⟶ p.source, z ≫ p.sourceMap = y := by
    intro x
    let := (f.appLE (W x) (V x) (e x)).hom.toAlgebra
    have : IsNoetherianRing Γ(S, W x) := IsLocallyNoetherian.component_noetherian ⟨W x, hW x⟩
    have : Algebra.FiniteType Γ(S, W x) Γ(X, V x) := f.finiteType_appLE (hW x) (hV x) (e x)
    obtain ⟨s₀, hs₀, hcov₀⟩ := exists_finite_affine_pieces Γ(S, W x) Γ(X, V x)
    have h : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, W x) Γ(X, V x))) ≫ (hW x).fromSpec =
        (hV x).fromSpec ≫ f :=
      IsAffineOpen.SpecMap_appLE_fromSpec f (hW x) (hV x) (e x)
    refine ⟨(fun p => p.comp (hV x).fromSpec (hW x).fromSpec h) '' s₀, hs₀.image _,
      fun K _ y hy => ?_⟩
    obtain ⟨p, hp, z, hz⟩ := hcov₀ K
      (IsOpenImmersion.lift (hV x).fromSpec y (by rwa [IsAffineOpen.range_fromSpec]))
    refine ⟨_, ⟨p, hp, rfl⟩, z, ?_⟩
    change z ≫ p.sourceMap ≫ (hV x).fromSpec = y
    rw [← Category.assoc, hz, IsOpenImmersion.lift_fac]
  choose s hs hcov using hloc
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((V x : X.Opens) : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine nonempty_cover_of_pieces (⋃ x ∈ t, s x) (t.finite_toSet.biUnion fun x _ => hs x)
    fun K _ y => ?_
  have : Unique (Spec (.of K)) := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (y default)))
  have hy : Set.range y ⊆ V x := by
    rintro _ ⟨w, rfl⟩
    rwa [Subsingleton.elim w default]
  obtain ⟨p, hp, z, hz⟩ := hcov x K y hy
  exact ⟨p, Set.mem_biUnion hx hp, z, hz⟩

end Langlands.AlgebraicGeometry.LangWeil
