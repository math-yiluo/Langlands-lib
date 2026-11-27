import Langlands.AbelianScheme.PolarizedFiniteLevel.Degree

/-! # The prescribed-degree locus of an isogeny of abelian schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {S T : Scheme.{u}} {A B : AbelianScheme S}

/-- On an abelian-scheme fibre, the native degree equals the rank at the identity. -/
lemma finrank_eq_finrank_unitSection [IsLocallyNoetherian S]
    (f : A ⟶ B) (hf : IsIsogeny f) (y : B.X.left) :
    (hom f).finrank y = (hom f).finrank (unitSection B (B.X.hom y)) := by
  apply (isLocallyConstant_finrank_of_isIsogeny f hf).apply_eq_of_isPreconnected
    (B.X.hom.isConnected_preimage_singleton (B.X.hom y)).isPreconnected (by rfl)
  change B.X.hom (unitSection B (B.X.hom y)) = B.X.hom y
  rw [← Scheme.Hom.comp_apply, unitSection_comp]
  rfl

/-- The prescribed native degree of an isogeny is represented by an open subscheme of the base. -/
theorem exists_degreeSquare_locus [IsLocallyNoetherian S] (f : A ⟶ B)
    (hf : IsIsogeny f) (d : ℕ) :
    ∃ U : S.Opens, ∀ (T : Scheme.{u}) (t : T ⟶ S),
      (∃ t' : T ⟶ U.toScheme, t' ≫ U.ι = t) ↔ HasDegreeSquare ((baseChange t).map f) d := by
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  let p : S → ℕ := (hom f).finrank ∘ unitSection B
  let U : S.Opens := ⟨p ⁻¹' {(d ^ 2)},
    (isLocallyConstant_finrank_of_isIsogeny f hf).comp_continuous (unitSection B).continuous _⟩
  refine ⟨U, fun T t ↦ ?_⟩
  have hrank (y : ((baseChange t).obj B).X.left) :
      (hom ((baseChange t).map f)).finrank y = p (t (((baseChange t).obj B).X.hom y)) := by
    have h := congrArg (fun a : pullback B.X.hom t ⟶ S ↦ a y) (pullback.condition (f := B.X.hom) (g := t))
    calc
      _ = (hom f).finrank (pullback.fst B.X.hom t y) :=
        Scheme.Hom.finrank_of_isPullback _ _ _ _ (hom_baseChange_isPullback t f) y
      _ = p (B.X.hom (pullback.fst B.X.hom t y)) := finrank_eq_finrank_unitSection f hf _
      _ = _ := congrArg p h
  constructor
  · rintro ⟨t', rfl⟩ y
    rw [hrank, Scheme.Hom.comp_apply]
    exact (t' (((baseChange (t' ≫ U.ι)).obj B).X.hom y)).2
  · intro ht
    have hU : Set.range t ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have h := ht (unitSection ((baseChange t).obj B) x)
      have hu : (((baseChange t).obj B).X.hom) (unitSection ((baseChange t).obj B) x) = x := by
        rw [← Scheme.Hom.comp_apply, unitSection_comp]
        rfl
      rw [hrank, hu] at h
      exact h
    exact ⟨IsOpenImmersion.lift U.ι t hU, IsOpenImmersion.lift_fac _ _ _⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
