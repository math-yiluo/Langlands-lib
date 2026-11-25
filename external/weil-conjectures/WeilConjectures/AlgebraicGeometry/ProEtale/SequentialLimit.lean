/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.RingTheory.Spectrum.Prime.Colimit

/-!
# Sequential limits of covers in the affine pro-étale site

Let `⋯ ⟶ W₂ ⟶ W₁ ⟶ W₀` be a sequence of surjective morphisms in the affine pro-étale site
`S.AffineProEt`. The spectrum `W_∞ = Spec (colim Γ(Wₙ))` of the colimit of the rings of global
sections is again an object of the affine pro-étale site, maps compatibly to every `Wₙ`, and is
surjective onto `W₀` (`AlgebraicGeometry.Scheme.AffineProEt.exists_compatible_surjective`). In
other words, sequential limits of covers are covers: this is the geometric input of the
repleteness of the pro-étale topos (Bhatt–Scholze, Proposition 4.2.8), which makes countable
products of pro-étale sheaves exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}} (W : ℕ → S.AffineProEt) (π : ∀ n, W (n + 1) ⟶ W n)

/-- The sequence of rings of global sections `Γ(W₀) ⟶ Γ(W₁) ⟶ ⋯` of a sequence of morphisms in
the affine pro-étale site. -/
noncomputable def ringSeq : ℕ ⥤ CommRingCat.{u} :=
  Functor.ofSequence fun n ↦ (π n).left.appTop

lemma ringSeq_map_succ (n : ℕ) :
    (ringSeq W π).map (homOfLE (Nat.le_succ n)) = (π n).left.appTop :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Each map `Γ(W₀) ⟶ Γ(Wₙ)` of the sequence of rings of global sections is ind-étale. -/
lemma indEtale_ringSeq_map (n : ℕ) :
    ((ringSeq W π).map (homOfLE (Nat.zero_le n))).hom.IndEtale := by
  induction n with
  | zero =>
    rw [show homOfLE (Nat.zero_le 0) = 𝟙 (0 : ℕ) from rfl, CategoryTheory.Functor.map_id]
    have := indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (𝟙 (W 0)))
    exact (Scheme.Hom.id_appTop (X := (W 0).left)) ▸ this
  | succ n ih =>
    rw [show homOfLE (Nat.zero_le (n + 1)) = homOfLE (Nat.zero_le n) ≫ homOfLE n.le_succ from rfl,
      Functor.map_comp, ringSeq_map_succ, CommRingCat.hom_comp]
    exact RingHom.IndEtale.comp (indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (π n))) ih

variable {W π}

/-- The transition maps of the sequence of rings of global sections induce surjections on prime
spectra when the morphisms `Wₙ₊₁ ⟶ Wₙ` are surjective. -/
lemma comap_ringSeq_map_surjective (hπ : ∀ n, Surjective (π n).left) (n : ℕ) :
    Function.Surjective
      (PrimeSpectrum.comap ((ringSeq W π).map (homOfLE (Nat.le_succ n))).hom) := by
  rw [ringSeq_map_succ]
  have heq : Spec.map (π n).left.appTop =
      (W (n + 1)).left.isoSpec.inv ≫ (π n).left ≫ (W n).left.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have : Surjective (Spec.map (π n).left.appTop) := by
    rw [heq]
    have := hπ n
    infer_instance
  exact this.surj

variable (W π) in
/-- The colimit inclusion `Γ(W₀) ⟶ colim Γ(Wₙ)` is ind-étale: it is the filtered colimit of the
ind-étale maps `Γ(W₀) ⟶ Γ(Wₙ)` (`indEtale_ringSeq_map`). The colimit is reindexed along
`ULift ℕ ≌ ℕ` to match the universe of `RingHom.IndEtale.of_isColimit`. -/
lemma indEtale_colimit_ι_zero : (colimit.ι (ringSeq W π) 0).hom.IndEtale := by
  let e : ULift.{u} ℕ ≌ ℕ := ULift.orderIso.equivalence
  have : IsFiltered (ULift.{u} ℕ) := IsFiltered.of_equivalence e.symm
  let D := e.functor ⋙ ringSeq W π
  let t : (Functor.const (ULift.{u} ℕ)).obj ((ringSeq W π).obj 0) ⟶ D :=
    { app i := (ringSeq W π).map (homOfLE (Nat.zero_le i.down))
      naturality i j g := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D,
          Functor.comp_map, ← Functor.map_comp]
        rfl }
  let c : D ⟶ (Functor.const (ULift.{u} ℕ)).obj (colimit (ringSeq W π)) :=
    Functor.whiskerLeft e.functor (colimit.cocone (ringSeq W π)).ι
  have hc : IsColimit (Cocone.mk _ c) :=
    (colimit.isColimit (ringSeq W π)).whiskerEquivalence e
  refine RingHom.IndEtale.of_isColimit (t := t) _ (ULift.{u} ℕ) D hc fun i ↦
    ⟨indEtale_ringSeq_map W π i.down, ?_⟩
  exact colimit.w (ringSeq W π) (homOfLE (Nat.zero_le i.down))

variable (W π) in
/-- The limit object `W_∞ = Spec (colim Γ(Wₙ))` of a sequence in the affine pro-étale site. -/
noncomputable def seqLimit : S.AffineProEt :=
  mk ((Spec.map (colimit.ι (ringSeq W π) 0) ≫ (W 0).left.isoSpec.inv) ≫ (W 0).hom) <|
    proAffineEtale.comp_mem _ _
      ((MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr
        (proAffineEtale_Spec_iff.mpr (indEtale_colimit_ι_zero W π))) (W 0).prop

/-- The maps `Spec (colim Γ(Wₙ)) ⟶ Wₙ` are compatible with the transition maps. -/
lemma spec_map_ι_succ_comp (n : ℕ) :
    (Spec.map (colimit.ι (ringSeq W π) (n + 1)) ≫ (W (n + 1)).left.isoSpec.inv) ≫ (π n).left =
      Spec.map (colimit.ι (ringSeq W π) n) ≫ (W n).left.isoSpec.inv := by
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, ← ringSeq_map_succ,
    colimit.w]

lemma spec_map_ι_comp_hom (n : ℕ) :
    (Spec.map (colimit.ι (ringSeq W π) n) ≫ (W n).left.isoSpec.inv) ≫ (W n).hom =
      (Spec.map (colimit.ι (ringSeq W π) 0) ≫ (W 0).left.isoSpec.inv) ≫ (W 0).hom := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← ih, ← MorphismProperty.Over.w (π n), ← Category.assoc,
      spec_map_ι_succ_comp]

variable (W π) in
/-- The projection `W_∞ ⟶ Wₙ`. -/
noncomputable def seqLimitπ (n : ℕ) : seqLimit W π ⟶ W n :=
  MorphismProperty.Over.homMk (Spec.map (colimit.ι (ringSeq W π) n) ≫ (W n).left.isoSpec.inv)
    (spec_map_ι_comp_hom n) trivial

lemma seqLimitπ_comp (n : ℕ) : seqLimitπ W π (n + 1) ≫ π n = seqLimitπ W π n :=
  MorphismProperty.Over.Hom.ext (spec_map_ι_succ_comp n)

/-- **Sequential limits of covers are covers** in the affine pro-étale site: for a sequence of
surjections `⋯ ⟶ W₁ ⟶ W₀`, the object `W_∞ = Spec (colim Γ(Wₙ))` maps compatibly to every `Wₙ`
and surjectively onto `W₀`. -/
theorem exists_compatible_surjective (hπ : ∀ n, Surjective (π n).left) :
    ∃ (V : S.AffineProEt) (p : ∀ n, V ⟶ W n), (∀ n, p (n + 1) ≫ π n = p n) ∧
      Surjective (p 0).left := by
  refine ⟨seqLimit W π, seqLimitπ W π, seqLimitπ_comp, ?_⟩
  have : Surjective (Spec.map (colimit.ι (ringSeq W π) 0)) :=
    ⟨PrimeSpectrum.comap_colimit_ι_zero_surjective _ (comap_ringSeq_map_surjective hπ)⟩
  change Surjective (Spec.map (colimit.ι (ringSeq W π) 0) ≫ (W 0).left.isoSpec.inv)
  infer_instance

end AlgebraicGeometry.Scheme.AffineProEt
