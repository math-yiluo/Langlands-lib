import Langlands.Geometry.Analytic.KeyLemma.QuasiEtaleStrongNearLifts
import Langlands.Geometry.Analytic.QuasiEtaleAutomorphismLiftStatement
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RigidityTransport

/-! # Lifts of near-identity automorphisms to compact quasi-étale spaces -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Test relations transport along an isomorphism `e : V ≅ W`: for finitely many test triples on
`W` there are finitely many test triples on `V` such that near morphisms into `V` have near
composites with `e`. -/
theorem exists_isNear_iso_postcomp {V W : LocalizedCategory.{u, v, w} (K := K)} (e : V ≅ W)
    (E : Finset (TestTriple (presentationOf W))) :
    ∃ F : Finset (TestTriple (presentationOf V)),
      ∀ (Z : LocalizedCategory.{u, v, w} (K := K)) (φ ψ : Z ⟶ V),
        (∀ τ ∈ F, IsNear τ φ ψ) → ∀ τ ∈ E, IsNear τ (φ ≫ e.hom) (ψ ≫ e.hom) := by
  classical
  let h' : localizedSpaceFunctor.obj V ≃ₜ localizedSpaceFunctor.obj W :=
    TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e)
  choose F _ hF using fun τ : E =>
    exists_isNear_postcomp e.hom τ.1 (h'.isCompact_preimage.mpr τ.1.isCompact_locus)
  exact ⟨Finset.univ.biUnion F, fun Z φ ψ h τ hτ => hF ⟨τ, hτ⟩ Z φ ψ fun τ₁ hτ₁ =>
    h τ₁ (Finset.mem_biUnion.mpr ⟨⟨τ, hτ⟩, Finset.mem_univ _, hτ₁⟩)⟩

/-- Near lifts of strong maps give near lifts of near-identity endomorphisms in the localized
category: for a strong map `g : T ⟶ B` with `HasStrongNearLifts g` and finitely many test triples
`E` on `T` there are finitely many test triples `D` on `B` such that every endomorphism `σ` of
`B` that is `D`-near the identity is covered by an endomorphism of `T` that is `E`-near the
identity. -/
theorem exists_nearLift_of_hasStrongNearLifts {T B : SaturatedAtlasPresentation.{u, v, w} K}
    {g : T ⟶ B} (hg : HasStrongNearLifts g) (E : Finset (TestTriple T)) :
    ∃ D : Finset (TestTriple B),
      ∀ σ : localizationFunctor.obj B ⟶ localizationFunctor.obj B,
        (∀ τ ∈ D, IsNear (X := localizationFunctor.obj B) τ σ (𝟙 _)) →
          ∃ ψ : localizationFunctor.obj T ⟶ localizationFunctor.obj T,
            ψ ≫ localizationFunctor.map g = localizationFunctor.map g ≫ σ ∧
              ∀ τ ∈ E, IsNear (X := localizationFunctor.obj T) τ ψ (𝟙 _) := by
  obtain ⟨D, hD⟩ := hg E
  refine ⟨D, fun σ hσ => ?_⟩
  have h₁ : ∀ τ ∈ D, IsNear (X := localizationFunctor.obj B) τ (localizationFunctor.map g)
      (localizationFunctor.map g ≫ σ) := fun τ hτ => by
    have := (hσ τ hτ).symm.precomp (localizationFunctor.map g)
    rwa [Category.comp_id] at this
  have h₂ : ∀ τ ∈ D, IsNear (X := localizationFunctor.obj B) τ (localizationFunctor.map g)
      (localizationFunctor.map g) := fun τ _ => by
    have := (isNear_id (X := localizationFunctor.obj B) τ).precomp (localizationFunctor.map g)
    rwa [Category.comp_id] at this
  obtain ⟨S, t, ht, x₀, x₁, x₂, h0, h1, -, hn⟩ :=
    exists_strongNear_numerators (X := localizationFunctor.obj B)
      (Y := localizationFunctor.obj T) D _ _ _ h₁ h₂
  have hx₀ : x₀ = t ≫ g := by
    apply localizationFunctor_map_injective
    exact h0.symm.trans (localizationFunctor.map_comp t g).symm
  have hy : ∀ τ ∈ D, StrongNear τ x₁ (t ≫ g) := fun τ hτ => by
    rw [← hx₀]
    exact (hn τ hτ).1.symm
  obtain ⟨S', r, hr, x', hx'g, hx'E⟩ := hD S t x₁ hy
  have hrt : (r ≫ t).IsQuasiIso := (quasiIsomorphisms (K := K)).comp_mem _ _ hr ht
  have e1 : localizationFunctor.map x' ≫ localizationFunctor.map g =
      localizationFunctor.map (r ≫ t) ≫ localizationFunctor.map g ≫ σ := by
    have h3 : localizationFunctor.map (r ≫ x₁) =
        localizationFunctor.map r ≫ localizationFunctor.map x₁ := localizationFunctor.map_comp r x₁
    have h4 : localizationFunctor.map (r ≫ t) =
        localizationFunctor.map r ≫ localizationFunctor.map t := localizationFunctor.map_comp r t
    refine (localizationFunctor.map_comp x' g).symm.trans
      ((congrArg localizationFunctor.map hx'g).trans (h3.trans ?_))
    exact (congrArg (fun k : localizationFunctor.obj S ⟶ localizationFunctor.obj B =>
        localizationFunctor.map r ≫ k) h1.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k : localizationFunctor.obj S' ⟶ localizationFunctor.obj T =>
          k ≫ localizationFunctor.map g ≫ σ) h4.symm))
  refine ⟨(localizedQuasiIso (r ≫ t) hrt).inv ≫ localizationFunctor.map x', ?_, fun τ hτ => ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k : localizationFunctor.obj S' ⟶ localizationFunctor.obj B =>
        (localizedQuasiIso (r ≫ t) hrt).inv ≫ k) e1).trans
        (localizedQuasiIso_inv_hom_id_assoc _ _ _))
  · exact ⟨S', r ≫ t, hrt, x', r ≫ t, rfl, (localizedQuasiIso_inv_hom_id (r ≫ t) hrt).symm,
      hx'E τ hτ⟩

/-- **Existence in Berkovich's Key Lemma 7.2 for near-identity automorphisms.** For a
quasi-étale morphism `f : U ⟶ X` with compact `U` and finitely many test triples `E` on `U`,
there are finitely many test triples `D` on `X` such that every automorphism of `X` that is
`D`-near the identity is covered by an endomorphism of `U` that is `E`-near the identity. -/
theorem quasiEtaleAutomorphismLift : QuasiEtaleAutomorphismLiftStatement.{u, v} K := by
  intro X U f _ hf hU E
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let eL : localizationFunctor.obj (ofSaturation A) ≅ U := Arrow.leftFunc.mapIso e
  let eR : localizationFunctor.obj (ofSaturation B) ≅ X := Arrow.rightFunc.mapIso e
  obtain ⟨hUc, hUt⟩ := hU
  let hh := TopCat.homeoOfIso (localizedSpaceFunctor.mapIso eL)
  have : CompactSpace A.space := hh.symm.compactSpace
  have : T2Space A.space := hh.symm.t2Space
  have hw : eL.hom ≫ f = localizationFunctor.map g ≫ eR.hom := Arrow.w e.hom
  obtain ⟨EA, hEA⟩ := exists_isNear_iso_postcomp eL E
  obtain ⟨DB, hDB⟩ := exists_nearLift_of_hasStrongNearLifts hg.hasStrongNearLifts EA
  obtain ⟨D, hD⟩ := exists_isNear_iso_postcomp eR.symm DB
  refine ⟨D, fun σ hσ => ?_⟩
  have hσ' : ∀ τ ∈ DB, IsNear (X := localizationFunctor.obj (ofSaturation B)) τ
      (eR.hom ≫ σ.hom ≫ eR.inv) (𝟙 _) := fun τ hτ => by
    have := (hD X σ.hom (𝟙 X) hσ τ hτ).precomp eR.hom
    simpa using this
  obtain ⟨ψ₀, hψ₀g, hψ₀E⟩ := hDB _ hσ'
  refine ⟨eL.inv ≫ ψ₀ ≫ eL.hom, ?_, fun τ hτ => ?_⟩
  · have h2 : ψ₀ ≫ localizationFunctor.map g ≫ eR.hom =
        localizationFunctor.map g ≫ eR.hom ≫ σ.hom := by
      rw [← Category.assoc, hψ₀g]
      simp
    calc (eL.inv ≫ ψ₀ ≫ eL.hom) ≫ f = eL.inv ≫ ψ₀ ≫ localizationFunctor.map g ≫ eR.hom := by
          rw [Category.assoc, Category.assoc, hw]
      _ = eL.inv ≫ (eL.hom ≫ f) ≫ σ.hom := by
          rw [h2, hw]
          simp only [Category.assoc]
      _ = f ≫ σ.hom := by simp
  · have := (hEA _ ψ₀ (𝟙 _) hψ₀E τ hτ).precomp eL.inv
    simpa using this

end Langlands.Analytic.SaturatedAtlasPresentation
