import Langlands.AlgebraicGeometry.SmoothDvrGlobalSections
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Special-fibre functions under an isomorphism on global functions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrSpecialFiberSectionEmbedding

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual quotient-residue-field map on spectra. -/
abbrev residueMap (R : Type u) [CommRing R] [IsLocalRing R] :=
  Spec.algebraMap R (IsLocalRing.ResidueField R)

lemma range_residueMap : Set.range (residueMap R) = {IsLocalRing.closedPoint R} := by
  have hpoint : ∀ t, residueMap R t = IsLocalRing.closedPoint R := by
    intro t
    have ht : t = (⟨⊥, inferInstance⟩ : PrimeSpectrum (IsLocalRing.ResidueField R)) :=
      Subsingleton.elim _ _
    rw [ht]
    apply PrimeSpectrum.ext
    change RingHom.ker (algebraMap R (IsLocalRing.ResidueField R)) = IsLocalRing.maximalIdeal R
    exact Ideal.mk_ker
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact hpoint t
  · intro hx
    subst x
    exact ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), hpoint _⟩

lemma residueMap_appTop_uniformizer {π : R} (hπ : Irreducible π) :
    (residueMap R).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) = 0 := by
  have heq : CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (residueMap R).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))).hom).1
  rw [map_zero]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (residueMap R).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField R))).hom) π = 0
  rw [← heq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit)

/-- The uniformizer pulls back to zero on every actual quotient-residue fibre;
no reducedness of that fibre is needed. -/
lemma pullback_fst_appTop_scalar (Y : Over (Spec (CommRingCat.of R)))
    {π : R} (hπ : Irreducible π) :
    (pullback.fst Y.hom (residueMap R)).appTop (SmoothDvrGlobalSections.scalar Y π) = 0 := by
  change (pullback.fst Y.hom (residueMap R)).appTop
    (Y.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)) = 0
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, residueMap_appTop_uniformizer hπ,
    map_zero]

variable {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    [Smooth X.hom] [IsAffine Y.left]

/-- An isomorphism on global functions induces an injection on the actual
special-fibre global functions when its source is smooth over the DVR. -/
theorem appTop_injective (hf : Function.Bijective f.left.appTop) :
    Function.Injective (((Over.pullback (residueMap R)).map f).left.appTop) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let jX := pullback.fst X.hom (residueMap R)
  let jY := pullback.fst Y.hom (residueMap R)
  let fs := ((Over.pullback (residueMap R)).map f).left
  have hclosed : IsClosedImmersion (residueMap R) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)
  have : IsClosedImmersion jY := MorphismProperty.pullback_fst _ _ inferInstance
  have hsurj : Function.Surjective jY.appTop := by
    exact jY.app_surjective ⊤ (isAffineOpen_top Y.left)
  have hmap : fs ≫ jY = jX ≫ f.left := by
    simp only [fs, jX, jY, Over.pullback_map_left, pullback.lift_fst]
  have hsec : jY.appTop ≫ fs.appTop = f.left.appTop ≫ jX.appTop :=
    congrArg Scheme.Hom.appTop hmap
  have hscalar : f.left.appTop (SmoothDvrGlobalSections.scalar Y π) =
      SmoothDvrGlobalSections.scalar X π := by
    simp only [SmoothDvrGlobalSections.scalar, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, Over.w f]
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  obtain ⟨a₀, ha₀⟩ := hsurj a
  have hz : jX.appTop (f.left.appTop a₀) = 0 := by
    rw [← CommRingCat.comp_apply, ← hsec, CommRingCat.comp_apply, ha₀]
    exact ha
  have hvan : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R →
      x ∉ X.left.basicOpen (f.left.appTop a₀) := by
    intro x hxs hxb
    have hx : x ∈ Set.range jX := by
      rw [Scheme.Pullback.range_fst, range_residueMap]
      exact hxs
    obtain ⟨z, rfl⟩ := hx
    have hzb : z ∈ (pullback X.hom (residueMap R)).basicOpen
        (jX.appTop (f.left.appTop a₀)) := by
      rw [← Scheme.preimage_basicOpen_top]
      exact hxb
    rw [hz, Scheme.basicOpen_zero] at hzb
    exact hzb
  obtain ⟨g, hg⟩ := SmoothDvrGlobalSections.exists_eq_scalar_mul_of_vanishing X hπ _ hvan
  obtain ⟨g₀, hg₀⟩ := hf.2 g
  have ha₀div : a₀ = SmoothDvrGlobalSections.scalar Y π * g₀ := by
    apply hf.1
    rw [map_mul, hscalar, hg₀]
    exact hg
  rw [← ha₀, ha₀div, map_mul, pullback_fst_appTop_scalar Y hπ, zero_mul]

/-- The actual embedding on global functions induced by the special-fibre map. -/
def sectionEmbedding (hf : Function.Bijective f.left.appTop) :
    Γ(((Over.pullback (residueMap R)).obj Y).left, ⊤) ↪
      Γ(((Over.pullback (residueMap R)).obj X).left, ⊤) :=
  ⟨((Over.pullback (residueMap R)).map f).left.appTop, appTop_injective f hf⟩

@[simp]
theorem sectionEmbedding_apply (hf : Function.Bijective f.left.appTop)
    (a : Γ(((Over.pullback (residueMap R)).obj Y).left, ⊤)) :
    sectionEmbedding f hf a = ((Over.pullback (residueMap R)).map f).left.appTop a := rfl

end Langlands.AlgebraicGeometry.DvrSpecialFiberSectionEmbedding
