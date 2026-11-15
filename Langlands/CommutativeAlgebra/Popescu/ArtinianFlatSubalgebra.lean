import Mathlib
import Langlands.CommutativeAlgebra.Popescu.ArtinianFlatSubalgebraStatement
import Langlands.CommutativeAlgebra.Popescu.ArtinianFlatInduction
import Langlands.CommutativeAlgebra.Popescu.ArtinianFlatConstruction

/-! # Proof of Stacks 07FG: Artinian local algebras as unions of flat EFT subalgebras -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open IsLocalRing MvPolynomial ArtinianFlat

/-- Stacks, Smoothing Ring Maps, Lemma 16.11.1 (07FG). -/
theorem artinianFlatSubalgebra : ArtinianFlatSubalgebraStatement.{u} := by
  intro k L _ _ _ p _ _ _ _ hH1 E
  classical
  have hV := fg_ker_mapBaseChange hH1
  obtain ⟨d, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal L))
  have ht' : Ideal.span (Set.range t) = maximalIdeal L := ht
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal L) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal L).mp inferInstance
  have hn' : maximalIdeal L ^ n = ⊥ := by rw [hn, Ideal.zero_eq_bot]
  have ht0 : ∀ i, residue L (t i) = 0 := fun i ↦ by
    rw [residue_eq_zero_iff, ← ht']
    exact Ideal.subset_span ⟨i, rfl⟩
  have hnil : ∀ x ∈ maximalIdeal L, IsNilpotent x := fun x hx ↦
    ⟨n, by have := Ideal.pow_mem_pow hx n; rwa [hn', Ideal.mem_bot] at this⟩
  -- The claim: a section `σ` and a finitely generated `F` with `k ⊂ σ(F)[t]`.
  obtain ⟨σ, hσ, F, ⟨SF, hSF⟩, hk⟩ := coeffClaim_residue p hV t ht'
  let Ψ : MvPolynomial (Fin d) (ResidueField L) →+* L := eval₂Hom σ t
  have hsurj : Function.Surjective Ψ :=
    eval₂_surjective (residue L) σ hσ t ht0 (n := n) (by rw [ker_residue, hn'])
      (by rw [ker_residue, ht'])
  obtain ⟨G, hG⟩ : (RingHom.ker Ψ).FG := IsNoetherian.noetherian _
  let pre : L → MvPolynomial (Fin d) (ResidueField L) := fun x ↦ (hsurj x).choose
  have hpre : ∀ x, Ψ (pre x) = x := fun x ↦ (hsurj x).choose_spec
  -- Enlarge `F` by the coefficients of the relations and of preimages of `E`.
  let T : Finset (ResidueField L) := (G ∪ E.image pre).biUnion MvPolynomial.coeffs
  let F₁ : IntermediateField k (ResidueField L) :=
    IntermediateField.adjoin k ((SF ∪ T : Finset (ResidueField L)) : Set (ResidueField L))
  have hFF₁ : F ≤ F₁ := by
    rw [← hSF]
    exact IntermediateField.adjoin.mono k _ _ (Finset.coe_subset.mpr Finset.subset_union_left)
  have hTF₁ : ∀ c ∈ T, c ∈ F₁ := fun c hc ↦
    IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr (Finset.mem_union_right _ hc))
  have hlift : ∀ P ∈ G ∪ E.image pre,
      ∃ Q : MvPolynomial (Fin d) F₁, map (algebraMap F₁ (ResidueField L)) Q = P := by
    intro P hP
    have : P ∈ Set.range (map (algebraMap F₁ (ResidueField L))) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      exact ⟨⟨c, hTF₁ c (Finset.mem_biUnion.mpr ⟨P, hP, hc⟩)⟩, rfl⟩
    exact this
  let Ψ₁ : MvPolynomial (Fin d) F₁ →+* L := eval₂Hom (σ.comp (algebraMap F₁ (ResidueField L))) t
  have hΨ₁ : ∀ Q, Ψ₁ Q = Ψ (map (algebraMap F₁ (ResidueField L)) Q) := fun Q ↦ by
    simp only [Ψ₁, Ψ, coe_eval₂Hom, eval₂_map]
  -- The subalgebra `A = σ(F₁)[t]`.
  let A : Subalgebra k L :=
    { carrier := Set.range Ψ₁
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      algebraMap_mem' := fun a ↦ by
        obtain ⟨h, hh⟩ := hk a
        refine ⟨map ((IntermediateField.inclusion hFF₁ : F →ₐ[k] F₁) : F →+* F₁) h, ?_⟩
        rw [← hh]
        exact eval₂_map _ t (σ.comp (algebraMap F₁ (ResidueField L))) h }
  have hA : ∀ x, x ∈ A ↔
      ∃ h : MvPolynomial (Fin d) F₁, eval₂ (σ.comp (algebraMap F₁ (ResidueField L))) t h = x :=
    fun x ↦ Iff.rfl
  have hres : ∀ x ∈ A, residue L x ∈ F₁ := by
    rintro _ ⟨h, rfl⟩
    rw [show Ψ₁ h = eval₂ (σ.comp (algebraMap F₁ (ResidueField L))) t h from rfl,
      residue_eval₂ (residue L) σ hσ t ht0]
    exact (constantCoeff h).2
  have hσA : ∀ c ∈ F₁, σ c ∈ A := fun c hc ↦ ⟨C ⟨c, hc⟩, eval₂_C _ _ _⟩
  have hunit := isUnit_of_residue_ne_zero A σ hσ F₁ hres hσA hnil
  have : IsLocalRing A := isLocalRing_of_residue A hunit
  have hmem := mem_maximalIdeal_iff_of_residue A hunit
  have hΨA : ∀ h, Ψ₁ h ∈ A := fun h ↦ ⟨h, rfl⟩
  have : IsNoetherianRing A :=
    isNoetherianRing_of_surjective (MvPolynomial (Fin d) F₁) A (Ψ₁.codRestrict A hΨA)
      (by
        rintro ⟨_, h, rfl⟩
        exact ⟨h, rfl⟩)
  have htA : ∀ i, t i ∈ A := fun i ↦ ⟨X i, eval₂_X _ _ _⟩
  have hker : RingHom.ker Ψ ≤
      (RingHom.ker Ψ₁).map (map (algebraMap F₁ (ResidueField L))) := by
    rw [← hG, Submodule.span_le]
    intro P hP
    obtain ⟨Q, rfl⟩ := hlift P (Finset.mem_union_left _ hP)
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, hΨ₁]
    have : map (algebraMap F₁ (ResidueField L)) Q ∈ RingHom.ker Ψ := by
      rw [← hG]
      exact Submodule.subset_span hP
    exact this
  refine ⟨A, inferInstance, ?_, isArtinianRing_of_residue A hmem hn',
    essFiniteType_of_residue σ hσ F₁ (SF ∪ T) rfl t ht0 A hA hunit hn', ?_,
    map_maximalIdeal_eq A hmem t ht' htA⟩
  · intro e he
    obtain ⟨Q, hQ⟩ := hlift (pre e) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))
    exact ⟨Q, by rw [hΨ₁, hQ]; exact hpre e⟩
  · have := free_of_ker_le σ t A hA hsurj hker
    infer_instance

end Langlands.CommutativeAlgebra.Popescu
