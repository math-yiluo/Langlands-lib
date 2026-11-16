import Langlands.CommutativeAlgebra.StrictHenselianDvrExtensionStatement
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.FibrewiseIsogenyBaseChange
import Langlands.GroupScheme.Reductive.NoetherianDvrIsogenyReduction
import Langlands.GroupScheme.Reductive.StrictHenselianDvrFibrewiseIsogenyReduction

/-! # Descent of the fibrewise-isogeny criterion from strictly Henselian DVRs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- The fibrewise-isogeny criterion over all domain DVRs. -/
def DvrFibrewiseIsogenyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ f : G ⟶ H, IsFibrewiseIsogeny f → IsIsogeny f

/-- An fpqc change of base reflects isogenies of the specified homomorphism. -/
theorem isogeny_of_fpqc_baseChange {S S' : Scheme.{u}}
    (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    {G H : GroupScheme S} (f : G ⟶ H)
    (hf : IsIsogeny ((baseChange b).map f)) : IsIsogeny f := by
  have hp := baseChange_map_isPullback b f
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst H.X.hom b) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.1,
    MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.2.1,
    MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.2.2⟩

/-- A faithfully flat extension of the base ring reflects isogenies. -/
theorem isogeny_of_faithfullyFlat_baseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A]
    {G H : GroupScheme (Spec (CommRingCat.of R))} (f : G ⟶ H)
    (hf : IsIsogeny ((baseChange (Spec.algebraMap R A)).map f)) : IsIsogeny f := by
  have hb := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R A))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat (Spec.algebraMap R A) := hb.1
  let : Surjective (Spec.algebraMap R A) := hb.2
  exact isogeny_of_fpqc_baseChange (Spec.algebraMap R A) f hf

/-- A supplied faithfully flat strictly Henselian DVR cover lets the local
criterion prove the isogeny of the original map over the original DVR. -/
theorem isogeny_of_strictHenselian_dvr_cover
    (hlocal : StrictHenselianDvrFibrewiseIsogenyStatement.{u})
    {R A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    [Algebra R A] [Module.FaithfullyFlat R A]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : G ⟶ H) (hf : IsFibrewiseIsogeny f) : IsIsogeny f := by
  apply isogeny_of_faithfullyFlat_baseChange (A := A) f
  exact hlocal A _ _ (hG.baseChange (Spec.algebraMap R A))
    (hH.baseChange (Spec.algebraMap R A)) _
    (hf.baseChange (Spec.algebraMap R A))

/-- Existence of strictly Henselian faithfully flat DVR extensions and the
strictly Henselian criterion imply the criterion over all domain DVRs. -/
theorem dvrFibrewiseIsogeny_of_strictHenselian_and_extension
    (hext : Langlands.CommutativeAlgebra.StrictHenselianDvrExtensionStatement.{u})
    (hlocal : StrictHenselianDvrFibrewiseIsogenyStatement.{u}) :
    DvrFibrewiseIsogenyStatement.{u} := by
  intro R _ _ _ G H hG hH f hf
  obtain ⟨A, _, _, _, _, _, _, hff⟩ := hext R
  let := hff
  exact isogeny_of_strictHenselian_dvr_cover (A := A) hlocal hG hH f hf

/-- The DVR criterion applies to all DVR-valued points of an arbitrary base. -/
theorem IsFibrewiseIsogeny.isDvrwiseIsogeny
    (hdvr : DvrFibrewiseIsogenyStatement.{u})
    {S : Scheme.{u}} {G H : GroupScheme S}
    (hG : IsReductive G) (hH : IsReductive H)
    {f : G ⟶ H} (hf : IsFibrewiseIsogeny f) : IsDvrwiseIsogeny f := by
  intro R _ _ _ b
  exact hdvr R _ _ (hG.baseChange b) (hH.baseChange b) _ (hf.baseChange b)

/-- Over a noetherian affine base, the DVR criterion finishes the
fibrewise-isogeny proof for reductive groups. -/
theorem isogeny_of_fibrewise_of_dvr_criterion
    (hdvr : DvrFibrewiseIsogenyStatement.{u})
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : G ⟶ H) (hf : IsFibrewiseIsogeny f) : IsIsogeny f := by
  let := hG.smooth
  let := hH.smooth
  let := hG.isAffineHom
  let := hH.isAffineHom
  exact isogeny_of_fibrewise_and_dvrwise f hf (hf.isDvrwiseIsogeny hdvr hG hH)

end Langlands.GroupScheme
