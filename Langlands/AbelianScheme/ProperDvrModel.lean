import Langlands.AbelianScheme.FieldAbelianSchemeGeometry
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.AffineStalkModelNeighbourhood
import Langlands.AlgebraicGeometry.KernelFlatBaseChange
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosure
import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.BaseChange
import Mathlib.RingTheory.Flat.TorsionFree

/-! # A proper flat DVR model of the generic abelian variety -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.AlgebraicGeometry.Picard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.AlgebraicGeometry

/-- A proper flat model with the supplied scheme as its actual generic fibre. -/
structure ProperDvrModel {V K : Type u} [CommRing V] [Field K] [Algebra V K]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K)) where
  carrier : Scheme.{u}
  toBase : carrier ⟶ Spec (CommRingCat.of V)
  proper : IsProper toBase
  flat : Flat toBase
  genericInclusion : X ⟶ carrier
  genericPullback : IsPullback genericInclusion p toBase (Spec.algebraMap V K)

private theorem flat_over_dvr {V : Type u} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of V)) [IsDominant p] : Flat p := by
  have hcover (x : X) : ∃ U : X.affineOpens, x ∈ U.1 :=
    Opens.mem_iSup.mp (by rw [iSup_affineOpens_eq_top]; trivial)
  choose U hU using hcover
  have htop : (⨆ x, (U x).1) = ⊤ :=
    top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩
  apply (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Flat) _ htop).mpr
  intro x
  have : Nonempty (U x).1 := ⟨⟨x, hU x⟩⟩
  have : IsDominant (U x).1.ι :=
    Opens.isDominant_ι ((U x).1.2.dense ⟨x, hU x⟩)
  let f := (U x).2.fromSpec ≫ p
  have hf : IsDominant f := by
    change IsDominant ((U x).2.isoSpec.inv ≫ (U x).1.ι ≫ p)
    infer_instance
  let φ := Spec.preimage f
  have hφ : IsDominant (Spec.map φ) := by simpa only [φ, Spec.map_preimage] using hf
  have hinj : Function.Injective φ.hom := by
    rw [RingHom.injective_iff_ker_eq_bot]
    have hd : DenseRange (PrimeSpectrum.comap φ.hom) := hφ.denseRange
    simpa using (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.hom).mp hd
  let : Algebra V Γ(X, (U x).1) := φ.hom.toAlgebra
  have : Module.IsTorsionFree V Γ(X, (U x).1) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Flat f := by
    rw [← Spec.map_preimage f, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat V Γ(X, (U x).1))
  exact (MorphismProperty.cancel_left_of_respectsIso @Flat (U x).2.isoSpec.inv _).mp this

/-- The schematic closure of an integral projective generic fibre gives a
proper flat model with that prescribed generic fibre. -/
def ProperDvrModel.ofEmbedding {V K : Type u} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (CommRingCat.of K)}
    {n : ℕ} (i : X ⟶ ProjectiveSpace K n) [IsClosedImmersion i]
    (hi : i ≫ projectiveSpaceToSpec K n = p) :
    ProperDvrModel (V := V) p := by
  let η := Spec.algebraMap V K
  let b := ProjectiveSpace.baseChangeMap V K n
  have hproj : IsPullback b (projectiveSpaceToSpec K n) (projectiveSpaceToSpec V n) η :=
    ProjectiveSpace.baseChangeMap_isPullback V K n
  have : IsOpenImmersion η := isOpenImmersion_spec_fractionRing_of_dvr V K
  have : IsOpenImmersion b :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hproj.flip inferInstance
  have : QuasiCompact η :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have : QuasiCompact b :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hproj.flip inferInstance
  let u := i ≫ b
  have : QuasiCompact u := by dsimp [u]; infer_instance
  have hi₀ : IsPullback (𝟙 X) i u b := IsPullback.of_horiz_isIso_mono ⟨by simp [u]⟩
  have hb : u.ker.comap b = i.ker :=
    KernelFlatBaseChange.ker_comap_of_flat_of_isPullback hi₀
  have hclosure : IsPullback u.toImage i u.imageι b :=
    (isPullback_of_isClosedImmersion i u.imageι u.toImage b
      u.toImage_imageι.symm
      (by rwa [Scheme.IdealSheafData.ker_subschemeι])).flip
  let q := u.imageι ≫ projectiveSpaceToSpec V n
  have hgeneric : IsPullback u.toImage p q η := by
    simpa only [hi, q] using hclosure.paste_vert hproj
  have : IsIntegral u.image := isIntegral_schematicImage u
  have : Surjective p := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ x⟩⟩
  have : IsDominant η :=
    isDominant_specMap_of_injective (algebraMap V K) (IsFractionRing.injective V K)
  have : IsDominant (u.toImage ≫ q) := by rw [hgeneric.w]; infer_instance
  have : IsDominant q := IsDominant.of_comp u.toImage q
  exact
    { carrier := u.image
      toBase := q
      proper := inferInstance
      flat := flat_over_dvr q
      genericInclusion := u.toImage
      genericPullback := hgeneric }

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry

/-- The underlying scheme of an abelian variety has a proper flat model
over its given discrete valuation ring. -/
def properDvrModel (V K : Type u) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) :
    ProperDvrModel (V := V) B.X.hom := by
  let ample := GroupScheme.fieldAmpleExistence K B.toCommGroupScheme.toGrp
    B.smooth B.proper B.geometricallyConnected
  let hp := (exists_closedImmersionBySections_iff_isHProjective B.X.hom).mp
    (properAmpleClosedImmersionBySections K B.X.left B.X.hom B.proper ample)
  let n := Classical.choose hp
  let i := Classical.choose (Classical.choose_spec hp)
  have hi := Classical.choose_spec (Classical.choose_spec hp)
  let : IsIntegral B.X.left := B.field_isIntegral
  let : IsClosedImmersion i := hi.1
  exact ProperDvrModel.ofEmbedding i hi.2

end Langlands.AbelianScheme
