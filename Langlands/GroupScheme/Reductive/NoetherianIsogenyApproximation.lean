import Langlands.GroupScheme.Reductive.AffineFibrewiseIsogenyReduction

/-! # Noetherian models and the remaining approximation input for isogenies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Over a field, a quasi-compact, locally quasi-finite flat surjective group
homomorphism is finite, hence an isogeny. -/
theorem isogeny_of_quasiFinite_flat_surjective_over_field
    {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (f : G ⟶ H) [QuasiCompact f.hom.hom.left]
    [LocallyQuasiFinite f.hom.hom.left]
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] : IsIsogeny f := by
  have : LocallyQuasiFinite (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  have : QuasiCompact (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  have : IsFinite (kernel f).X.hom := IsFinite.of_locallyQuasiFinite _
  exact ⟨isFinite_of_finite_kernel f, inferInstance, inferInstance⟩

/-- Quasi-compact, locally quasi-finite flat surjective homomorphisms are
isogenies on every residue-field fibre. -/
theorem isFibrewiseIsogeny_of_quasiFinite_flat_surjective
    {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
    [QuasiCompact f.hom.hom.left] [LocallyQuasiFinite f.hom.hom.left]
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] : IsFibrewiseIsogeny f := by
  intro s
  have hp := (baseChange_map_isPullback (S.fromSpecResidueField s) f).flip
  have : QuasiCompact
      ((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback hp inferInstance
  have : LocallyQuasiFinite
      ((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback hp inferInstance
  have : Flat ((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback hp inferInstance
  have : Surjective ((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback hp inferInstance
  exact isogeny_of_quasiFinite_flat_surjective_over_field _

/-- For smooth groups with quasi-compact source and quasi-separated target,
fibrewise isogeny is equivalent to local quasi-finiteness, flatness, and
surjectivity. -/
theorem isFibrewiseIsogeny_iff_quasiFinite_flat_surjective
    {S : Scheme.{u}} {G H : GroupScheme S}
    [Smooth G.X.hom] [Smooth H.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated H.X.hom] (f : G ⟶ H) :
    IsFibrewiseIsogeny f ↔
      LocallyQuasiFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧
        Surjective f.hom.hom.left := by
  constructor
  · intro hf
    exact ⟨locallyQuasiFinite_of_isogeny_fibres f hf,
      flat_of_isogeny_fibres f hf, surjective_of_isogeny_fibres f hf⟩
  · rintro ⟨hquasi, hflat, hsurj⟩
    let := hquasi
    let := hflat
    let := hsurj
    have : QuasiCompact (f.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    have : QuasiCompact f.hom.hom.left := QuasiCompact.of_comp _ H.X.hom
    exact isFibrewiseIsogeny_of_quasiFinite_flat_surjective f

/-- A model of the supplied homomorphism over a noetherian subring of its
base ring, preserving reductivity and its three quasi-finite fpqc properties. -/
structure NoetherianQuasiFiniteModel
    {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H) where
  coefficients : Subring R
  noetherian : IsNoetherianRing coefficients
  source : GroupScheme (Spec (CommRingCat.of coefficients))
  target : GroupScheme (Spec (CommRingCat.of coefficients))
  source_reductive : IsReductive source
  target_reductive : IsReductive target
  hom : source ⟶ target
  quasiFinite : LocallyQuasiFinite hom.hom.hom.left
  flat : Flat hom.hom.hom.left
  surjective : Surjective hom.hom.hom.left
  sourceIso : G ≅
    (baseChange (Spec.map (CommRingCat.ofHom coefficients.subtype))).obj source
  targetIso : H ≅
    (baseChange (Spec.map (CommRingCat.ofHom coefficients.subtype))).obj target
  recovery : f ≫ targetIso.hom = sourceIso.hom ≫
    (baseChange (Spec.map (CommRingCat.ofHom coefficients.subtype))).map hom

/-- The noetherian approximation input for the reductive isogeny argument.
Only local quasi-finiteness, flatness and surjectivity are preserved; no
finiteness of the original homomorphism is assumed or concluded here. -/
def ReductiveQuasiFiniteNoetherianModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ f : G ⟶ H, LocallyQuasiFinite f.hom.hom.left →
      Flat f.hom.hom.left → Surjective f.hom.hom.left →
      Nonempty (NoetherianQuasiFiniteModel f)

/-- The DVR criterion proves the supplied homomorphism is an isogeny once
a noetherian quasi-finite flat surjective model has been supplied. -/
theorem isogeny_of_noetherianQuasiFiniteModel
    (hdvr : DvrFibrewiseIsogenyStatement.{u})
    {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H)
    (M : NoetherianQuasiFiniteModel f) : IsIsogeny f := by
  let := M.noetherian
  let := M.source_reductive.isAffineHom
  let := M.target_reductive.isAffineHom
  let := M.quasiFinite
  let := M.flat
  let := M.surjective
  have : QuasiCompact (M.hom.hom.hom.left ≫ M.target.X.hom) := by
    rw [Over.w M.hom.hom.hom]
    infer_instance
  have : QuasiCompact M.hom.hom.hom.left :=
    QuasiCompact.of_comp _ M.target.X.hom
  have hf := isFibrewiseIsogeny_of_quasiFinite_flat_surjective M.hom
  have hi := isogeny_of_fibrewise_of_dvr_criterion
    (R := M.coefficients) hdvr M.source_reductive M.target_reductive M.hom hf
  have ht := ((isIsogeny_of_isIso M.sourceIso.hom).comp
    (hi.baseChange (Spec.map (CommRingCat.ofHom M.coefficients.subtype)))).comp
      (isIsogeny_of_isIso M.targetIso.inv)
  change IsIsogeny
    ((M.sourceIso.hom ≫
      (baseChange (Spec.map (CommRingCat.ofHom M.coefficients.subtype))).map M.hom) ≫
        M.targetIso.inv) at ht
  rw [← M.recovery, Category.assoc, Iso.hom_inv_id, Category.comp_id] at ht
  exact ht

/-- The noetherian model existence and DVR criterion imply the criterion
over every affine base ring. -/
theorem affineReductiveFibrewiseIsogeny_of_noetherianModel_and_dvr
    (hmodel : ReductiveQuasiFiniteNoetherianModelStatement.{u})
    (hdvr : DvrFibrewiseIsogenyStatement.{u}) :
    AffineReductiveFibrewiseIsogenyStatement.{u} := by
  intro R _ G H hG hH f hf
  let := hG.smooth
  let := hH.smooth
  obtain ⟨M⟩ := hmodel R G H hG hH f
    (locallyQuasiFinite_of_isogeny_fibres f hf)
    (flat_of_isogeny_fibres f hf) (surjective_of_isogeny_fibres f hf)
  exact isogeny_of_noetherianQuasiFiniteModel hdvr f M

/-- The remaining approximation input and the DVR criterion imply the
unchanged arbitrary-base fibrewise-isogeny statement. -/
theorem reductiveFibrewiseIsogeny_of_noetherianModel_and_dvr
    (hmodel : ReductiveQuasiFiniteNoetherianModelStatement.{u})
    (hdvr : DvrFibrewiseIsogenyStatement.{u}) :
    ReductiveFibrewiseIsogenyStatement.{u} :=
  reductiveFibrewiseIsogeny_of_affine
    (affineReductiveFibrewiseIsogeny_of_noetherianModel_and_dvr hmodel hdvr)

end Langlands.GroupScheme
