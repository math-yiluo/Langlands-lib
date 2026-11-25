/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherNormalization
public import WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep

/-!
# The Deligne–Laumon direct-image bound

This file states the two main results of the blueprint section
`chap-The-Deligne-Laumon-theorem-in-general`: for a separated finite-type morphism `f : X ⟶ Y` of
schemes of finite type over `k₀ = 𝔽_q` and a constructible Weil sheaf `F` mixed of weights at most
`w`, the sheaf `Rʳf₀!F` is mixed of weights at most `w + r` for every `r`; and the derived form,
that `Rf₀!K` is mixed of weights at most `w` whenever the bounded constructible Weil complex `K` is.

## Implementation notes

- For `AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`: Noetherian induction on the
  closed subsets of the source, glued by the open–closed reduction. On a nonempty reduced closed
  subscheme, an integral affine open maps into an affine open of the target through a domain
  `A'`; over a principal open of `Spec A'` the map factors through a finite morphism to an
  iterated relative affine line
  (`AlgebraicGeometry.exists_isFinite_toIteratedAffineLine_basicOpen`).
  The finite morphism and the remaining immersion into the target are quasi-finite, and each
  affine-line projection is handled by the relative affine-line step
  `AlgebraicGeometry.hasDirectImageWeightBound_affineLine`; the composition lemma assembles them.
  Composing with immersions of the target avoids any stratification of the target.
- For `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek`: the finite
  hypercohomology spectral sequence `Rᵃf₀!𝓗ᵇ(K) ⇒ 𝓗ᵃ⁺ᵇ(Rf₀!K)`, whose left-hand term is mixed of
  weights at most `w + a + b` by the theorem above
  (`AlgebraicGeometry.HasDirectImageWeightBound.isMixedOfWeightsAtMost_derivedLowerShriek`).

## Main statements

- `AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`: blueprint
  `theorem-direct-image-mixed-sheaf--1` and `theorem-direct-image-mixed-sheaf--1`.
- `AlgebraicGeometry.exists_hasDirectImageWeightBound_opensι_comp`: the generic step of its
  Noetherian induction.
- `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek`: blueprint
  `theorem-weights-rf-shriek--1`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), Théorème
  3.3.1.
- [Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*][laumon1987], Publ. Math. IHÉS **65** (1987).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

section Generic

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ} {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 400000 in
-- The Noether normalisation step elaborates slowly.
set_option synthInstance.maxHeartbeats 80000 in
-- Instance search for the quasi-finiteness of the composite immersions is slow in the presence
-- of the many morphism-property instances in scope.
/-- Let `g₀ : T ⟶ Y₀` be a morphism of finite type from an integral affine scheme to an affine
scheme, followed by an immersion `a : Y₀ ⟶ Y`. Then the direct-image weight assertion holds for
`g₀ ≫ a` restricted to some nonempty affine open `V` of `T` (blueprint:
`theorem-direct-image-mixed-sheaf--1`, the generic step on an integral affine source).

Factor the ring map `A ⟶ B` of `g₀` as `A ↠ A' ↪ B` with `A'` a domain. Generic Noether
normalization (`lemma-relative-noether-normalization-over-stratification`) gives a principal open
`D(s)` of `Spec A'` over which `Spec B ⟶ Spec A'` factors as a finite morphism to `𝔸ᵈ_{D(s)}`
followed by `d` affine-line projections. The finite morphism and the immersion `D(s) ⟶ Y` are
quasi-finite, so the quasi-finite lemma, the relative affine-line step and the composition lemma
apply. -/
theorem exists_hasDirectImageWeightBound_opensι_comp_of_isAffine {T Y₀ : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [IsAffine T] [IsIntegral T] [IsAffine Y₀]
    (g₀ : T ⟶ Y₀) [LocallyOfFiniteType g₀] (a : Y₀ ⟶ Y) [IsImmersion a]
    [(g₀ ≫ a).IsOver (Spec (CommRingCat.of k₀))] :
    ∃ V : T.Opens, IsAffineOpen V ∧ (V : Set T).Nonempty ∧ ∀ [QuasiCompact (V.ι ≫ g₀ ≫ a)],
      HasDirectImageWeightBound k₀ ι (V.ι ≫ g₀ ≫ a) := by
  classical
  -- The ring map `φ : A ⟶ B` of `g₀`, factored as `A ↠ A' = A ⧸ ker φ ↪ B`.
  set φ := g₀.appTop
  let A' := Γ(Y₀, ⊤) ⧸ RingHom.ker φ.hom
  have : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime _
  let mk : Γ(Y₀, ⊤) ⟶ CommRingCat.of A' := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let ψ : CommRingCat.of A' ⟶ Γ(T, ⊤) := CommRingCat.ofHom (RingHom.kerLift φ.hom)
  have hψ : Function.Injective ψ.hom := RingHom.kerLift_injective _
  have hφ : mk ≫ ψ = φ := by ext; rfl
  have hg₀ : T.isoSpec.hom ≫ Spec.map ψ ≫ Spec.map mk = g₀ ≫ Y₀.isoSpec.hom := by
    rw [← Spec.map_comp, hφ, Scheme.isoSpec_hom_naturality]
  -- `Spec A' ⟶ Spec B` is of finite type.
  have : LocallyOfFiniteType (Spec.map ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    have : φ.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
      inferInstance
    rw [← hφ] at this
    exact RingHom.FiniteType.of_comp_finiteType this
  -- Generic Noether normalization over a principal open `D(s₀)` of `Spec A'`.
  have : Nonempty (⊤ : (Spec (CommRingCat.of A')).Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  obtain ⟨s₀, hs₀, d, H⟩ :=
    exists_isFinite_toIteratedAffineLine_basicOpen (Spec.map ψ) (isAffineOpen_top _)
  obtain ⟨ν, hνfin, hν, -⟩ := H s₀ dvd_rfl hs₀
  have hD : IsAffineOpen ((Spec (CommRingCat.of A')).basicOpen s₀) :=
    (isAffineOpen_top _).basicOpen s₀
  have hV' : IsAffineOpen (Spec.map ψ ⁻¹ᵁ (Spec (CommRingCat.of A')).basicOpen s₀) :=
    hD.preimage _
  refine ⟨T.isoSpec.hom ⁻¹ᵁ (Spec.map ψ ⁻¹ᵁ (Spec (CommRingCat.of A')).basicOpen s₀),
    hV'.preimage _, ?_, ?_⟩
  · -- `V'` is a nonempty principal open of the integral scheme `Spec B`.
    have hne : Spec.map ψ ⁻¹ᵁ (Spec (CommRingCat.of A')).basicOpen s₀ ≠ ⊥ := by
      rw [Ne, Scheme.preimage_basicOpen, basicOpen_eq_bot_iff]
      intro h0
      have hinj : Function.Injective (Spec.map ψ).appTop.hom := by
        intro x y hxy
        have := congrArg (Scheme.ΓSpecIso _).hom.hom hxy
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
          Scheme.ΓSpecIso_naturality] at this
        exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1 (hψ this)
      exact hs₀ (hinj (h0.trans (map_zero _).symm))
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
    exact ⟨T.isoSpec.inv x, by simpa [← Scheme.Hom.comp_apply] using hx⟩
  intro _
  have hg₀' : T.isoSpec.inv ≫ g₀ = Spec.map ψ ≫ Spec.map mk ≫ Y₀.isoSpec.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hg₀, Iso.hom_inv_id, Category.comp_id]
  -- Structure morphisms to `Spec k₀` along the factorization.
  let : (Spec (CommRingCat.of A')).Over (Spec (CommRingCat.of k₀)) :=
    ⟨Spec.map mk ≫ Y₀.isoSpec.inv ≫ a ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  let : (Spec Γ(T, ⊤)).Over (Spec (CommRingCat.of k₀)) :=
    ⟨T.isoSpec.inv ≫ T ↘ Spec (CommRingCat.of k₀)⟩
  let D := (Spec (CommRingCat.of A')).basicOpen s₀
  let V' := Spec.map ψ ⁻¹ᵁ D
  let c : D.toScheme ⟶ Y := D.ι ≫ Spec.map mk ≫ Y₀.isoSpec.inv ≫ a
  let e : (T.isoSpec.hom ⁻¹ᵁ V').toScheme ⟶ V' := T.isoSpec.hom ∣_ V'
  let : (iteratedAffineLine D d).Over (Spec (CommRingCat.of k₀)) :=
    ⟨iteratedAffineLineProj D d ≫ D.toScheme ↘ Spec (CommRingCat.of k₀)⟩
  have : (iteratedAffineLineProj D d).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : c.IsOver (Spec (CommRingCat.of k₀)) := ⟨by simp only [c, Category.assoc]; rfl⟩
  have : ν.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change ν ≫ iteratedAffineLineProj D d ≫ D.ι ≫ Spec.map mk ≫ Y₀.isoSpec.inv ≫ a ≫ _ =
      V'.ι ≫ T.isoSpec.inv ≫ _
    rw [reassoc_of% hν, morphismRestrict_ι_assoc, ← comp_over (g₀ ≫ a), ← reassoc_of% hg₀']
    simp only [Category.assoc]
    rfl⟩
  have : e.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change e ≫ V'.ι ≫ T.isoSpec.inv ≫ _ = (T.isoSpec.hom ⁻¹ᵁ V').ι ≫ _
    rw [morphismRestrict_ι_assoc, Iso.hom_inv_id_assoc]⟩
  have : IsAffine D := hD
  have : IsAffine V' := hV'
  have : IsSeparated (D.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c]; infer_instance
  have : LocallyOfFiniteType (D.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c]; infer_instance
  have : IsSeparated (iteratedAffineLine D d ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (iteratedAffineLineProj D d)]; infer_instance
  have : LocallyOfFiniteType (iteratedAffineLine D d ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (iteratedAffineLineProj D d)]; infer_instance
  have : QuasiCompact (iteratedAffineLine D d ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (iteratedAffineLineProj D d)]; infer_instance
  have : LocallyOfFiniteType (V'.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over ν]; infer_instance
  have : QuasiCompact c := by
    have : QuasiCompact (c ≫ Y ↘ Spec (CommRingCat.of k₀)) := by
      rw [comp_over c]; infer_instance
    exact QuasiCompact.of_comp c (Y ↘ Spec (CommRingCat.of k₀))
  have key : e ≫ ν ≫ iteratedAffineLineProj D d ≫ c =
      (T.isoSpec.hom ⁻¹ᵁ V').ι ≫ g₀ ≫ a := by
    simp only [c, e, V', D]
    rw [reassoc_of% hν, morphismRestrict_ι_assoc, morphismRestrict_ι_assoc,
      ← reassoc_of% hg₀', Iso.hom_inv_id_assoc]
  exact .of_eq key (HasDirectImageWeightBound.comp (.of_locallyQuasiFinite e)
    (HasDirectImageWeightBound.comp (.of_locallyQuasiFinite ν)
      ((hasDirectImageWeightBound_iteratedAffineLineProj D d).comp
        (.of_locallyQuasiFinite c))))

/-- Let `g : T ⟶ Y` be a separated morphism of finite type from a nonempty reduced `k₀`-scheme.
Then the direct-image weight assertion holds for `g` restricted to some nonempty open `U` of `T`
(blueprint: `theorem-direct-image-mixed-sheaf--1`, the generic step of the Noetherian induction).

Take an affine open `U₁` inside an irreducible open of `T` and mapping into an affine open `W` of
`Y`; `U₁` is integral, and `exists_hasDirectImageWeightBound_opensι_comp_of_isAffine` applies. -/
theorem exists_hasDirectImageWeightBound_opensι_comp {T : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [IsReduced T] [Nonempty T] (g : T ⟶ Y)
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] :
    ∃ U : T.Opens, (U : Set T).Nonempty ∧ ∀ [QuasiCompact (U.ι ≫ g)],
      HasDirectImageWeightBound k₀ ι (U.ι ≫ g) := by
  have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over g]; infer_instance
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over g]; infer_instance
  have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
  -- A nonempty irreducible open `o` of `T`, and an affine open `U₁ ⊆ o` mapping into an affine
  -- open `W` of `Y`.
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {t}
    isIrreducible_singleton
  obtain ⟨o, ho, ⟨x, hxo⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  obtain ⟨U₁, hU₁, hxU₁, hU₁o⟩ := exists_isAffineOpen_mem_and_subset
    (x := x) (U := ⟨o, ho⟩ ⊓ g ⁻¹ᵁ W) ⟨hxo, hxW⟩
  have hU₁W : U₁ ≤ g ⁻¹ᵁ W := fun y hy ↦ (hU₁o hy).2
  have : IsAffine U₁ := hU₁
  have : IsAffine W := hW
  have : IrreducibleSpace U₁ := Subtype.irreducibleSpace
    ⟨⟨x, hxU₁⟩, (hZ.1.2.open_subset U₁.isOpen fun y hy ↦ hoZ (hU₁o hy).1)⟩
  have : IsIntegral U₁ := isIntegral_of_irreducibleSpace_of_isReduced _
  let g₁ := g.resLE W U₁ hU₁W
  have : (g₁ ≫ W.ι).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc, comp_over g]; rfl⟩
  obtain ⟨V, hV, hVne, H⟩ :=
    exists_hasDirectImageWeightBound_opensι_comp_of_isAffine (k₀ := k₀) (ι := ι) g₁ W.ι
  refine ⟨U₁.ι ''ᵁ V, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hVne
    exact ⟨U₁.ι y, y, hy, rfl⟩
  intro _
  let e := U₁.ι.isoImage V
  have : IsAffine V := hV
  have : QuasiCompact (V.ι ≫ g₁ ≫ W.ι) := by
    have : QuasiCompact ((V.ι ≫ g₁ ≫ W.ι) ≫ Y ↘ Spec (CommRingCat.of k₀)) := by
      rw [comp_over]; infer_instance
    exact QuasiCompact.of_comp _ (Y ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (V.ι ≫ g₁ ≫ W.ι)]; infer_instance
  have he : e.inv ≫ V.ι ≫ U₁.ι = (U₁.ι ''ᵁ V).ι := by
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc]
  have : e.inv.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change e.inv ≫ V.ι ≫ U₁.ι ≫ _ = (U₁.ι ''ᵁ V).ι ≫ _
    rw [reassoc_of% he]⟩
  have key : e.inv ≫ V.ι ≫ g₁ ≫ W.ι = (U₁.ι ''ᵁ V).ι ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, reassoc_of% he]
  exact .of_eq key (HasDirectImageWeightBound.comp (.of_locallyQuasiFinite e.inv) H)

end Generic

-- The hypotheses that the base `Y` is separated of finite type over `k₀` do not occur in the two
-- statements below, so they are spelled out rather than taken from a `variable` block, which would
-- not include them.
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

/-- For a separated finite-type morphism `f : X ⟶ Y` of schemes of finite type over `k₀ = 𝔽_q` and
a constructible Weil sheaf `F` on `X` mixed of weights at most `w`, the sheaf `Rʳf₀!F` is mixed of
weights at most `w + r`, for every `r` (blueprint: `theorem-direct-image-mixed-sheaf--1`,
`theorem-direct-image-mixed-sheaf--1`).

Noetherian induction on the closed subsets of `X`: for a reduced closed subscheme `T` of `X`, the
assertion holds for `T ⟶ Y` over a nonempty open `U` of `T`
(`exists_hasDirectImageWeightBound_opensι_comp`) and, by induction, over the reduced complement of
`U`; the open–closed reduction `lemma-weight-bounds-partitions--1` glues the two. -/
theorem hasDirectImageWeightBound_over_finiteField (ι : PadicAlgCl l →+* ℂ) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] : HasDirectImageWeightBound k₀ ι f := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f]; infer_instance
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f]; infer_instance
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  -- Noetherian induction on the closed subsets of `X`.
  have key : ∀ (Z : Closeds X) (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      [IsReduced T] (i : T ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))],
      Set.range i ⊆ Z → HasDirectImageWeightBound k₀ ι (i ≫ f) := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
    intro T _ _ i _ _ hiZ
    have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
    cases isEmpty_or_nonempty T
    · exact .of_locallyQuasiFinite _
    obtain ⟨U, ⟨u, hu⟩, H⟩ :=
      exists_hasDirectImageWeightBound_opensι_comp (k₀ := k₀) (ι := ι) (i ≫ f)
    -- The reduced closed complement `T'` of `U`.
    let C : Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
    let i' := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over
        (Spec (CommRingCat.of k₀)) := ⟨i' ≫ T ↘ Spec (CommRingCat.of k₀)⟩
    have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have hrange : Set.range i' = C := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let Z' : Closeds X := ⟨i '' C, i.isClosedEmbedding.isClosedMap _ C.isClosed⟩
    have hZ' : Z' < Z := by
      refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiZ ⟨t, ht⟩) fun h ↦ ?_
      have : i u ∈ (Z' : Set X) := h ▸ hiZ ⟨u, rfl⟩
      obtain ⟨t, ht, hti⟩ := this
      exact ht (i.isClosedEmbedding.injective hti ▸ hu)
    have h₂ := ih Z' hZ' _ (i' ≫ i) (by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]; exact subset_rfl)
    have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace (U : Set T))
    exact .of_openClosed (j := U.ι) (i := i') (f := i ≫ f)
      (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl) H
      (.of_eq (Category.assoc _ _ _) h₂)
  -- `X` is the union of the empty open and its reduction.
  let i := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme.Over
      (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : X.Opens).ι := inferInstance
  exact .of_openClosed (j := (⊥ : X.Opens).ι) (i := i) (f := f)
    (by rw [Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact isCompl_bot_top)
    (.of_locallyQuasiFinite _) (key ⊤ _ i (Set.subset_univ _))


/-- If `K` is a bounded constructible Weil complex on `X` mixed of weights at most `w`, then
`Rf₀!K` is mixed of weights at most `w` (blueprint: `theorem-weights-rf-shriek--1`,
`theorem-weights-rf-shriek--1`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ} {w : ℝ}
    {K : WeilComplex k₀ l X} (hK : K.IsMixedOfWeightsAtMost ι w) (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    ((WeilComplex.derivedLowerShriek k₀ l f).obj K).IsMixedOfWeightsAtMost ι w :=
  (hasDirectImageWeightBound_over_finiteField ι f).isMixedOfWeightsAtMost_derivedLowerShriek hK

end AlgebraicGeometry
