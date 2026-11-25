/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux
public import WeilConjectures.AlgebraicGeometry.GenericFiber.RadicialSmoothing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Assembling the generic curve model over a base

The predicate `AlgebraicGeometry.IsGenericCurveModel F` for a morphism `F : X ⟶ S` records the
conclusion of `proposition-proper-direct-image-finite-coefficients` over the base `S` (without the
projective embeddings of the curve pieces, which are recovered from finiteness over an affine base):
the reduction `T` of `X` receives a finite surjection `ν : ∐ Yₐ ⟶ T` from smooth curve families and
finite étale families, which is an isomorphism outside a closed subscheme of `T` finite over `S`.

`AlgebraicGeometry.isGenericCurveModel_morphismRestrict` assembles such a model over an open `V`
of an integral base from finitely many finite morphisms `pₐ : Yₐ ⟶ X₀` whose generic fibres are
smooth of relative dimension `0` or `1`, provided that over `V` the `Yₐ` are smooth, `∐ Yₐ ⟶ X₀`
is surjective and is a closed immersion over an open `W₀` whose complement has finite fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The conclusion of `proposition-proper-direct-image-finite-coefficients` over a base `S` for
`F : X ⟶ S` (without projective embeddings): a reduced scheme `T` with a surjective closed immersion
`t : T ⟶ X`, finitely many `Yₐ` with a finite surjection `ν : ∐ Yₐ ⟶ T`, each `Yₐ` smooth of
relative dimension one over `S` or finite étale over `S`, and a closed subscheme `d : D ⟶ T` finite
over `S` outside of which `ν` is an isomorphism. -/
def IsGenericCurveModel {X S : Scheme.{u}} (F : X ⟶ S) : Prop :=
  ∃ (T : Scheme.{u}) (t : T ⟶ X) (_ : IsClosedImmersion t) (_ : Surjective t) (_ : IsReduced T)
    (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u}) (ν : ∐ Y ⟶ T) (_ : IsFinite ν)
    (_ : Surjective ν) (D : Scheme.{u}) (d : D ⟶ T) (_ : IsClosedImmersion d),
    IsFinite (d ≫ t ≫ F) ∧
    IsIso (ν ∣_ ⟨(Set.range d.base)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩) ∧
    ∀ a : ι, IsFinite (Sigma.ι Y a ≫ ν) ∧
      (SmoothOfRelativeDimension 1 (Sigma.ι Y a ≫ ν ≫ t ≫ F) ∨
      (IsFinite (Sigma.ι Y a ≫ ν ≫ t ≫ F) ∧ Etale (Sigma.ι Y a ≫ ν ≫ t ≫ F)))

/-- A cartesian square version of `smoothOfRelativeDimension_of_pullback_snd`. -/
lemma smoothOfRelativeDimension_of_isPullback {Y S P : Scheme.{u}} [IrreducibleSpace S]
    {g : Y ⟶ S} [Smooth g] {L : Type u} [Field L] {j : Spec (.of L) ⟶ S}
    (hj : ∀ x, j x = genericPoint S) {a : P ⟶ Y} {gL : P ⟶ Spec (.of L)}
    (H : IsPullback a gL g j) (d : ℕ) [SmoothOfRelativeDimension d gL] :
    SmoothOfRelativeDimension d g := by
  have : SmoothOfRelativeDimension d (pullback.snd g j) := by
    rw [← H.isoPullback_inv_snd]
    have : SmoothOfRelativeDimension (0 + d) (H.isoPullback.inv ≫ gL) :=
      smoothOfRelativeDimension_comp 0 d _ _
    rwa [zero_add] at this
  exact smoothOfRelativeDimension_of_pullback_snd g j hj d

/-- **Assembling the generic curve model over an open of the base.** Let `S₀` be integral and
locally noetherian, `F₀ : X₀ ⟶ S₀` proper, `pₐ : Yₐ ⟶ X₀` finitely many finite morphisms whose
base changes `gₐ` along a morphism `j : Spec L ⟶ S₀` to the generic point are smooth of relative
dimension `dₐ ≤ 1`, `W₀ ⊆ X₀` open and `V ⊆ S₀` an open containing the generic point. Suppose
that over `V` the `Yₐ` are smooth, `∐ Yₐ ⟶ X₀` is surjective and is a closed immersion over
`W₀`, and that the complement of `W₀` has finite fibres over `V`. Then `F₀ ∣_ V` admits a generic
curve model, with `T` the reduction of `F₀⁻¹(V)`. -/
theorem isGenericCurveModel_morphismRestrict {S₀ X₀ : Scheme.{u}} [IsIntegral S₀]
    [IsLocallyNoetherian S₀] (F₀ : X₀ ⟶ S₀) [IsProper F₀]
    {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}} (p : ∀ a, Y a ⟶ X₀) [∀ a, IsFinite (p a)]
    {L : Type u} [Field L] (j : Spec (.of L) ⟶ S₀) (hj : ∀ x, j x = genericPoint S₀)
    {Y₀ : ι → Scheme.{u}} (g : ∀ a, Y₀ a ⟶ Spec (.of L)) (h : ∀ a, Y₀ a ⟶ Y a)
    (H : ∀ a, IsPullback (h a) (g a) (p a ≫ F₀) j) (d : ι → ℕ) (hd : ∀ a, d a ≤ 1)
    (hg : ∀ a, SmoothOfRelativeDimension (d a) (g a))
    (W₀ : X₀.Opens) (V : S₀.Opens) (hηV : genericPoint S₀ ∈ V)
    (hsm : ∀ a, Smooth ((p a ≫ F₀) ∣_ V))
    (hci : IsClosedImmersion (Sigma.desc p ∣_ (W₀ ⊓ F₀ ⁻¹ᵁ V)))
    (hsurj : ∀ x, F₀ x ∈ V → x ∈ Set.range (Sigma.desc p))
    (hfin : ∀ s ∈ V, {x | F₀ x = s ∧ x ∉ W₀}.Finite) :
    IsGenericCurveModel (F₀ ∣_ V) := by
  classical
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  -- the generic point of `V`
  have hjV : Set.range j ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hj]
    exact hηV
  let j' : Spec (.of L) ⟶ V.toScheme := IsOpenImmersion.lift V.ι j hjV
  have hj'V : j' ≫ V.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hj' (x : Spec (.of L)) : j' x = genericPoint V := by
    apply V.ι.isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion V.ι, ← Scheme.Hom.comp_apply, hj'V, hj]
  -- the restricted objects
  let X' : X₀.Opens := F₀ ⁻¹ᵁ V
  let F' : X'.toScheme ⟶ V.toScheme := F₀ ∣_ V
  let Y' (a : ι) : Scheme.{u} := (p a ⁻¹ᵁ X').toScheme
  let p' (a : ι) : Y' a ⟶ X'.toScheme := p a ∣_ X'
  let ν₀ := Sigma.desc p
  let ν' : ∐ Y' ⟶ X'.toScheme := Sigma.desc p'
  have Hσ : IsPullback (Limits.Sigma.map fun a ↦ (p a ⁻¹ᵁ X').ι) ν' ν₀ X'.ι :=
    isPullback_sigmaDesc p p' (fun a ↦ (p a ⁻¹ᵁ X').ι) X'.ι
      fun a ↦ (isPullback_morphismRestrict (p a) X').flip
  have hcomp (a : ι) : p' a ≫ F' = (p a ≫ F₀) ∣_ V :=
    (morphismRestrict_comp (p a) F₀ V).symm
  -- smoothness and relative dimension of the pieces over `V`
  have hrel (a : ι) : SmoothOfRelativeDimension (d a) (p' a ≫ F') := by
    rw [hcomp]
    have := hsm a
    have := hg a
    obtain ⟨q, hq⟩ := isPullback_morphismRestrict_lift (π := j') (by rw [hj'V]; exact H a)
    exact smoothOfRelativeDimension_of_isPullback hj' hq (d a)
  have hred (a : ι) : IsReduced (Y' a) := by
    have := SmoothOfRelativeDimension.smooth (d a) (p' a ≫ F')
    have := Smooth.geometricallyReduced (p' a ≫ F')
    exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (p' a ≫ F')
  have : ∀ i, IsReduced ((sigmaOpenCover Y').X i) := fun i ↦ hred i
  have : IsReduced (∐ Y') := IsReduced.of_openCover (𝒰 := sigmaOpenCover Y')
  -- the reduction `T` of `X'` and the comparison map `ν`
  let T := X'.toScheme.nilradical.subscheme
  let t : T ⟶ X'.toScheme := X'.toScheme.nilradical.subschemeι
  obtain ⟨hTred, htci, htsurj, -⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X'.toScheme
  obtain ⟨ν, hν⟩ := exists_comp_nilradical_subschemeι ν'
  have hν'fin : IsFinite ν' := inferInstance
  have hνfin : IsFinite ν := by
    have : IsFinite (ν ≫ t) := by rw [hν]; exact hν'fin
    exact IsFinite.of_comp ν t
  have hν's : Surjective ν' := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨z, hz⟩ := hsurj (X'.ι x) x.2
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := ν₀) (g := X'.ι) z x hz
    exact ⟨Hσ.isoPullback.inv w, by
      rw [← Scheme.Hom.comp_apply, Hσ.isoPullback_inv_snd]
      exact hw₂⟩
  have hνs : Surjective ν := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := hν's.surj (t x)
    refine ⟨y, t.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hν]
    exact hy
  -- the open `W'` of `X'` and the closed subscheme `D` of `T`
  let W' : X'.toScheme.Opens := X'.ι ⁻¹ᵁ W₀
  let Z : TopologicalSpace.Closeds T := ⟨(t ⁻¹ᵁ W' : Set T)ᶜ, (t ⁻¹ᵁ W').isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let D := I.subscheme
  let dd : D ⟶ T := I.subschemeι
  have hrange : Set.range dd = (t ⁻¹ᵁ W' : Set T)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hopen : (⟨(Set.range dd.base)ᶜ, dd.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
      T.Opens) = t ⁻¹ᵁ W' := by
    ext x
    change x ∈ (Set.range dd)ᶜ ↔ _
    rw [hrange, compl_compl]
  have hX'W : X'.ι ⁻¹ᵁ (W₀ ⊓ F₀ ⁻¹ᵁ V) = W' := by
    ext x
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, x.2⟩⟩
  refine ⟨T, t, htci, htsurj, hTred, ι, inferInstance, Y', ν, hνfin, hνs, D, dd, inferInstance,
    ?_, ?_, fun a ↦ ?_⟩
  · -- finiteness of `D` over `V`
    have : IsProper F' := inferInstance
    have : IsProper (dd ≫ t ≫ F') := inferInstance
    have : LocallyQuasiFinite (dd ≫ t ≫ F') := by
      refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun s ↦ ?_
      refine ((hfin (V.ι s) s.2).preimage
        (f := fun y ↦ X'.ι (t (dd y))) ?_).subset ?_
      · intro y₁ _ y₂ _ hy
        exact dd.isClosedEmbedding.injective (t.isClosedEmbedding.injective
          (X'.ι.isOpenEmbedding.injective hy))
      · intro y hy
        refine ⟨?_, ?_⟩
        · rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι]
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
          rw [Scheme.Hom.comp_apply, ← hy]
          rfl
        · have hy' : dd y ∈ Set.range dd := ⟨y, rfl⟩
          rw [hrange] at hy'
          exact hy'
    exact IsFinite.of_isProper_of_locallyQuasiFinite _
  · -- `ν` is an isomorphism outside `D`
    rw [hopen]
    have hci' : IsClosedImmersion (ν' ∣_ W') := by
      obtain ⟨a', -, Ha'⟩ :=
        AlgebraicGeometry.IsPullback.exists_isPullback_morphismRestrict Hσ (W₀ ⊓ F₀ ⁻¹ᵁ V)
      have : IsClosedImmersion (ν' ∣_ (X'.ι ⁻¹ᵁ (W₀ ⊓ F₀ ⁻¹ᵁ V))) :=
        MorphismProperty.of_isPullback Ha' hci
      exact Scheme.Hom.restrict_of_le _ _ hX'W.ge this
    have : IsClosedImmersion (ν ∣_ (t ⁻¹ᵁ W') ≫ t ∣_ W') := by
      have h2 := (morphismProperty_restrict_congr @IsClosedImmersion hν W').mpr hci'
      rwa [morphismRestrict_comp] at h2
    have : IsClosedImmersion (ν ∣_ (t ⁻¹ᵁ W')) := IsClosedImmersion.of_comp _ (t ∣_ W')
    have : Surjective (ν ∣_ (t ⁻¹ᵁ W')) := IsZariskiLocalAtTarget.restrict hνs _
    exact isIso_of_isClosedImmersion_of_surjective _
  · -- the pieces
    have he₀ : (Sigma.ι Y' a ≫ ν) ≫ t = p' a := by
      rw [Category.assoc, hν]
      simp [ν']
    have he : Sigma.ι Y' a ≫ ν ≫ t ≫ F' = p' a ≫ F' := by
      rw [← he₀]
      simp
    refine ⟨?_, ?_⟩
    · have : IsFinite ((Sigma.ι Y' a ≫ ν) ≫ t) := by rw [he₀]; infer_instance
      exact IsFinite.of_comp _ t
    rw [he]
    have := hrel a
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd a) with h0 | h1
    · right
      rw [h0] at this
      have : Etale (p' a ≫ F') := (Etale.iff_smoothOfRelativeDimension_zero _).mpr this
      exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, this⟩
    · left
      rwa [h1] at this

end AlgebraicGeometry
