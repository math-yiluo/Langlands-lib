import Langlands.GroupScheme.FlatPidAffinizationGroupStatement
import Langlands.GroupScheme.HenselianDvrSmoothTranslation
import Langlands.GroupScheme.DvrOpenAffinization
import Langlands.AlgebraicGeometry.SmoothDvrPrincipalOpen
import Langlands.AlgebraicGeometry.SmoothGenericMonomorphism
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat

/-! # The local smooth-DVR affinization construction -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped CategoryTheory.MonObj

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.SmoothDvrLocalAffinization

section BaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (X : Over (Spec (CommRingCat.of R))) [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- The actual spectrum-of-functions comparison for flat affine base change. -/
def baseChangeSpecIso :
    Spec Γ(pullback X.hom (Spec.algebraMap R A), ⊤) ≅
      pullback (canonicalAffinization X).hom (Spec.algebraMap R A) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat X.hom A)).flip.isoPullback

/-- The comparison identifies the canonical map with the actual base-changed map. -/
theorem toSpecΓ_comp_baseChangeSpecIso :
    (pullback X.hom (Spec.algebraMap R A)).toSpecΓ ≫ (baseChangeSpecIso (A := A) X).hom =
      ((Over.pullback (Spec.algebraMap R A)).map (toCanonicalAffinization X)).left := by
  let P := pullback X.hom (Spec.algebraMap R A)
  let h := (isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat X.hom A)).flip
  change P.toSpecΓ ≫ h.isoPullback.hom = _
  dsimp only [canonicalAffinization, Spec.algebraMap]
  apply pullback.hom_ext
  · rw [Category.assoc, h.isoPullback_hom_fst]
    simp only [Over.pullback_map_left]
    trans pullback.fst X.hom (Spec.algebraMap R A) ≫ X.left.toSpecΓ
    · exact (Scheme.toSpecΓ_naturality (pullback.fst X.hom (Spec.algebraMap R A))).symm
    · exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, h.isoPullback_hom_snd]
    simp only [Over.pullback_map_left]
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    exact (pullback.lift_snd _ _ _).symm

/-- If the source base change is affine, the actual base-changed canonical map
is an isomorphism. -/
theorem isIso_baseChange_toCanonicalAffinization
    [IsAffine (pullback X.hom (Spec.algebraMap R A))] :
    IsIso ((Over.pullback (Spec.algebraMap R A)).map (toCanonicalAffinization X)).left := by
  have h₁ : IsIso (pullback X.hom (Spec.algebraMap R A)).toSpecΓ := inferInstance
  have h₂ : IsIso (baseChangeSpecIso (A := A) X).hom := inferInstance
  rw [← toSpecΓ_comp_baseChangeSpecIso (A := A) X]
  exact IsIso.comp_isIso

end BaseChange

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom]
    [IsAffine (pullback G.X.hom (Spec.algebraMap R K))]
    [GrpObj (canonicalAffinization G.X)] [IsMonHom (toCanonicalAffinization G.X)]

/-- Given the actual compatible affinization group and a fibre-dense affine
open, the original smooth group is isomorphic to its canonical affinization. -/
def canonicalIso {W : G.X.left.Opens} (hW : IsAffineOpen W)
    (hdense : ∀ x : G.X.left, G.X.hom x = IsLocalRing.closedPoint R →
      ∃ y ∈ W, G.X.hom y = IsLocalRing.closedPoint R ∧ y ⤳ x) :
    G.X.left ≅ Spec Γ(G.X.left, ⊤) := by
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : QuasiSeparatedSpace G.X.left := quasiSeparatedSpace_of_quasiSeparated G.X.hom
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  let H : GroupScheme (Spec (CommRingCat.of R)) := { X := canonicalAffinization G.X }
  let c : G ⟶ H := Grp.homMk (toCanonicalAffinization G.X)
  have : IsAffine H.X.left := inferInstanceAs (IsAffine (Spec Γ(G.X.left, ⊤)))
  have hgen : IsIso ((baseChange (Spec.algebraMap R K)).map c).hom.hom.left :=
    isIso_baseChange_toCanonicalAffinization (A := K) G.X
  have hs : ∃ x : G.X.left, G.X.hom x = IsLocalRing.closedPoint R := by
    let e : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X := 1
    refine ⟨e.left (IsLocalRing.closedPoint R), ?_⟩
    change (e.left ≫ G.X.hom) (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R
    rw [Over.w e]
    rfl
  let d := SmoothDvrPrincipalOpen.affinePrincipalOpenMeetingClosedFibre G.X K hW hdense hs
  have hchart : Smooth ((G.X.left.basicOpen d.1).ι ≫ c.hom.hom.left) := by
    have : IsIso (G.X.left.toSpecΓ ∣_ PrimeSpectrum.basicOpen d.1) := d.2.2.1
    change Smooth ((G.X.left.basicOpen d.1).ι ≫ G.X.left.toSpecΓ)
    rw [← G.X.left.toSpecΓ_preimage_basicOpen d.1, ← morphismRestrict_ι]
    infer_instance
  have : Smooth c.hom.hom.left :=
    HenselianDvrSmoothTranslation.smooth_of_generic_and_chart K c
      (by let := hgen; infer_instance) (G.X.left.basicOpen d.1) d.2.2.2 hchart
  have : IsDominant (Spec.algebraMap R K) := by
    apply (isDominant_iff _).mpr
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  have : Mono ((Over.pullback (Spec.algebraMap R K)).map c.hom.hom) := by
    have : IsIso ((Over.forget (Spec (CommRingCat.of K))).map
        ((Over.pullback (Spec.algebraMap R K)).map c.hom.hom)) := hgen
    have : IsIso ((Over.pullback (Spec.algebraMap R K)).map c.hom.hom) :=
      isIso_of_reflects_iso _ (Over.forget _)
    infer_instance
  have : IsOpenImmersion c.hom.hom.left :=
    SmoothGenericMonomorphism.isOpenImmersion_of_mono_baseChange (Spec.algebraMap R K) c.hom.hom
  have hf : Function.Bijective c.hom.hom.left.appTop := by
    change Function.Bijective G.X.left.toSpecΓ.appTop
    rw [Scheme.toSpecΓ_appTop]
    exact ConcreteCategory.bijective_of_isIso _
  exact DvrOpenAffinization.isoOfGeneric c K hf hgen

@[simp]
theorem canonicalIso_hom {W : G.X.left.Opens} (hW : IsAffineOpen W)
    (hdense : ∀ x : G.X.left, G.X.hom x = IsLocalRing.closedPoint R →
      ∃ y ∈ W, G.X.hom y = IsLocalRing.closedPoint R ∧ y ⤳ x) :
    (canonicalIso K G hW hdense).hom = G.X.left.toSpecΓ := rfl

include K in
/-- Relative affineness from those two concrete construction inputs. -/
theorem isAffineHom {W : G.X.left.Opens} (hW : IsAffineOpen W)
    (hdense : ∀ x : G.X.left, G.X.hom x = IsLocalRing.closedPoint R →
      ∃ y ∈ W, G.X.hom y = IsLocalRing.closedPoint R ∧ y ⤳ x) :
    IsAffineHom G.X.hom := by
  have : IsAffine G.X.left := IsAffine.of_isIso (canonicalIso K G hW hdense).hom
  exact isAffineHom_of_isAffine _

end Langlands.GroupScheme.SmoothDvrLocalAffinization
