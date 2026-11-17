import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.AffinePinnedScalingDifferential
import Langlands.GroupScheme.Reductive.AffinePinnedWeightTransport
import Langlands.GroupScheme.Reductive.AlignedWeightLineUnits

/-! # Pinning correction of affine unpinned isomorphisms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The existence half of the unchanged affine pinned Isomorphism Theorem. -/
def AffinePinnedIsomorphismExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G H : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (hH : IsReductive H)
    (I I' : Type u) [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (J J' : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ)),
    haveI := hG.isAffineHom
    haveI := hH.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i →
    IsFibrewiseRootDatumOf I G i P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    IsClosedSubgroup i' →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i' →
    IsFibrewiseRootDatumOf I' H i' Q →
    (∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    ∀ (b : P.Base) (b' : Q.Base)
      (X : ∀ a : b.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I G i (P.root a))
      (Y : ∀ a' : b'.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I' H i' (Q.root a'))
      (f : RootPairing.Equiv Q P)
      (hf : ∀ j' : J', j' ∈ b'.support ↔ f.indexEquiv j' ∈ b.support),
      ∃ φ : G ≅ H,
        (∃ τ : splitTorus (Spec (CommRingCat.of R)) I ≅
            splitTorus (Spec (CommRingCat.of R)) I',
          i ≫ φ.hom = τ.hom ≫ i' ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
            ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom.hom) j' ^ m j' =
              ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j) ∧
        ∀ a' : b'.support,
          Lie.targetMapLinear φ.hom (CommRingCat.of R)
              (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val =
            (Y a' 1).val


/-- Unpinned affine isomorphism existence implies pinned affine isomorphism existence. -/
theorem affinePinnedIsomorphismExistence_of_unpinned
    (hU : AffineSplitIsomorphismTheoremStatement.{u}) :
    AffinePinnedIsomorphismExistenceStatement.{u} := by
  intro R _ G H hG hH I I' _ _ i i' J J' P Q
  let := hG.isAffineHom
  let := hH.isAffineHom
  intro hi hmax hP hfree hi' hmax' hQ hfree' b b' X Y f hf
  obtain ⟨phi0, tau, hsquare, hchar⟩ :=
    hU R G H hG hH I I' i i' J J' P Q hi hmax hP hfree hi' hmax' hQ hfree' f
  let : Finite J' := hQ.finite
  let : Fintype J' := Fintype.ofFinite J'
  let M : AffinePinnedModel :=
    { ring := R
      group := H
      reductive := hH
      coordinates := I'
      inclusion := i'
      closed := hi'
      maximal := hmax'
      rootIndex := J'
      rootDatum := Q
      fibrewiseRootDatum := hQ
      rootLines := hfree'
      basis := b'
      pinning := Y }
  have hunit : ∀ a' : b'.support, ∃ c : Rˣ,
      Lie.targetMapLinear phi0.hom (CommRingCat.of R)
          (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val =
        @SMul.smul (CommRingCat.of R) (Additive (lieKernel H (CommRingCat.of R)))
          (lieKernelSMul H) (c : CommRingCat.of R) (Y a' 1).val := by
    intro a'
    let a : b.support := ⟨f.indexEquiv a', (hf a').mp a'.property⟩
    have hroot := f.root_weightMap_apply Q P a'
    let E := splitTorus.exponentWeightSpaceTransportEquiv phi0 tau hsquare
      (P.root a) (Q.root a') (fun A _ _ x =>
        splitTorus.exponentValue_transport_of_points tau (P.root a) (Q.root a')
          (fun U x => by simpa only [hroot] using hchar U x (Q.root a')) A x)
    obtain ⟨c, hc, -⟩ := Langlands.Algebra.existsUnique_unit_smul_of_lineEquiv
      (X a) (Y a') E
    refine ⟨c, ?_⟩
    exact congrArg Subtype.val hc
  choose c hc using hunit
  let sigma := M.rootScalingIso (fun a' => (c a')⁻¹)
  have htorus : i' ≫ sigma.hom = i' :=
    M.rootScalingIso_inclusion (fun a' => (c a')⁻¹)
  have hvector (a' : b'.support) :
      Lie.targetMapLinear sigma.hom (CommRingCat.of R) (Y a' 1).val =
        @SMul.smul (CommRingCat.of R) (Additive (lieKernel H (CommRingCat.of R)))
          (lieKernelSMul H) (↑((c a')⁻¹) : CommRingCat.of R) (Y a' 1).val :=
    M.rootScalingIso_rootVector (fun a' => (c a')⁻¹) a'
  refine ⟨phi0 ≪≫ sigma, ⟨tau, ?_, hchar⟩, ?_⟩
  · rw [Iso.trans_hom, ← Category.assoc, hsquare, Category.assoc, htorus]
  · intro a'
    rw [Iso.trans_hom, Lie.targetMapLinear_comp, LinearMap.comp_apply,
      hc a']
    erw [LinearMap.map_smul, hvector a', smul_smul]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- Choose the actual pinning-corrected isomorphism together with every target equation. -/
def affinePinnedIsomorphismOfUnpinned
    (hU : AffineSplitIsomorphismTheoremStatement.{u}) :
  ∀ (R : Type u) [CommRing R] (G H : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (hH : IsReductive H)
    (I I' : Type u) [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (J J' : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ)),
    haveI := hG.isAffineHom
    haveI := hH.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i →
    IsFibrewiseRootDatumOf I G i P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    IsClosedSubgroup i' →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') i' →
    IsFibrewiseRootDatumOf I' H i' Q →
    (∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    ∀ (b : P.Base) (b' : Q.Base)
      (X : ∀ a : b.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I G i (P.root a))
      (Y : ∀ a' : b'.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I' H i' (Q.root a'))
      (f : RootPairing.Equiv Q P)
      (hf : ∀ j' : J', j' ∈ b'.support ↔ f.indexEquiv j' ∈ b.support),
      { φ : G ≅ H //
        (∃ τ : splitTorus (Spec (CommRingCat.of R)) I ≅
            splitTorus (Spec (CommRingCat.of R)) I',
          i ≫ φ.hom = τ.hom ≫ i' ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
            ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom.hom) j' ^ m j' =
              ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j) ∧
        ∀ a' : b'.support,
          Lie.targetMapLinear φ.hom (CommRingCat.of R)
              (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val =
            (Y a' 1).val } := by
  intro R _ G H hG hH I I' _ _ i i' J J' P Q
  let := hG.isAffineHom
  let := hH.isAffineHom
  intro hi hmax hP hfree hi' hmax' hQ hfree' b b' X Y f hf
  let hex := affinePinnedIsomorphismExistence_of_unpinned hU
    R G H hG hH I I' i i' J J' P Q
    hi hmax hP hfree hi' hmax' hQ hfree' b b' X Y f hf
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

end Langlands.GroupScheme
