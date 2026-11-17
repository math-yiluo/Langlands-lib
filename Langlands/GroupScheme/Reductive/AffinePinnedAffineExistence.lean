import Langlands.GroupScheme.Reductive.AffinePinnedAffineCorrection
import Langlands.GroupScheme.Reductive.AffinePinnedCentralizer
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Fppf pinning correction over a common affine base -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

/-- Global units on an affine spectrum in coefficient-ring coordinates. -/
def affineUnitSectionsEquiv (A : Type u) [CommRing A] :
    (Γ(Spec (CommRingCat.of A), ⊤))ˣ ≃* Aˣ :=
  Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv

/-- Restricting affine global units is the actual coefficient algebra map. -/
theorem affineUnitSectionsEquiv_restrict (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    (x : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) :
    affineUnitSectionsEquiv B
      (Units.map (algebraBaseMap A B).appTop.hom.toMonoidHom x) =
      Units.map (algebraMap A B).toMonoidHom (affineUnitSectionsEquiv A x) := by
  apply Units.ext
  change ((algebraBaseMap A B).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) x.val =
    algebraMap A B ((Scheme.ΓSpecIso (CommRingCat.of A)).hom x.val)
  rw [Scheme.ΓSpecIso_naturality]
  rfl

variable (N : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra N.ring A]

/-- Any simple-root unit tuple has an actual fppf torus lift whose inverse
values are retained on every coefficient test of its possibly nonaffine cover. -/
theorem exists_fppf_inverse_simpleRoot_values
    (c : N.basis.support → Aˣ) :
    ∃ (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of A))
      (t : Over.mk p ⟶ (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B]
        (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)
        (s : N.basis.support),
        splitTorus.exponentValue N.coordinates
          (splitTorus.algebraPointsEquiv N.coordinates B (affineSectionPoint p B a hA t))
          (Multiplicative.ofAdd (N.rootDatum.root s)) =
          Units.map (algebraMap A B).toMonoidHom (c s)⁻¹ := by
  let d : N.basis.support → (Γ(Spec (CommRingCat.of A), ⊤))ˣ :=
    fun s => (affineUnitSectionsEquiv A).symm (c s)⁻¹
  obtain ⟨W, b, t, hflat, hsurj, hlfp, ht⟩ :=
    (N.scalarExtension A).exists_fppf_simpleRoot_values
      (splitTorus (Spec (CommRingCat.of A)) N.coordinates) (Iso.refl _)
      (Over.mk (𝟙 _)) d
  have hb : b.left = W.hom := by
    have h := Over.w b
    change b.left ≫ 𝟙 _ = W.hom at h
    simpa only [Category.comp_id] using h
  refine ⟨W.left, W.hom, t, hb ▸ hflat, hb ▸ hsurj, hb ▸ hlfp, ?_⟩
  intro B _ _ a hA s
  let U : Over (Spec (CommRingCat.of A)) :=
    (algSpec (CommRingCat.of A)).obj (op (CommAlgCat.of (CommRingCat.of A) B))
  let a' : U ⟶ W := Over.homMk a hA.symm
  have h := ht U a' s
  change Gm.pointsEquiv (Spec (CommRingCat.of A)) U
      ((a' ≫ t ≫ (𝟙 _)) ≫
        (splitTorus.exponentCharacterOnTorus (Spec (CommRingCat.of A))
          (splitTorus (Spec (CommRingCat.of A)) N.coordinates) (Iso.refl _)
          (N.rootDatum.root s)).hom.hom) =
    splitTorus.unitsRestrict N.basis.support (a' ≫ b) d s at h
  have hp := splitTorus.pointsEquiv_exponentCharacterOnTorus
    (Spec (CommRingCat.of A)) (splitTorus (Spec (CommRingCat.of A)) N.coordinates)
    (Iso.refl _) (N.rootDatum.root s) U (a' ≫ t)
  have hprod : (∏ i, splitTorus.pointsEquiv N.coordinates U (a' ≫ t) i ^
      N.rootDatum.root s i) = splitTorus.unitsRestrict N.basis.support (a' ≫ b) d s := by
    apply hp.symm.trans
    simpa only [Iso.refl_hom, Grp.id_hom_hom, Category.assoc, Category.comp_id] using h
  have h' := congrArg (affineUnitSectionsEquiv B) hprod
  have hab : (a' ≫ b).left = algebraBaseMap A B := by
    change a ≫ b.left = _
    rw [hb, ← hA]
  rw [show splitTorus.unitsRestrict N.basis.support (a' ≫ b) d s =
    Units.map (algebraBaseMap A B).appTop.hom.toMonoidHom (d s) by rw [← hab]; rfl,
    affineUnitSectionsEquiv_restrict, MulEquiv.apply_symm_apply] at h'
  change (∏ i, affineUnitSectionsEquiv B
    (splitTorus.pointsEquiv N.coordinates U (a' ≫ t) i) ^ N.rootDatum.root s i) = _
  simpa only [map_prod, map_zpow] using h'

/-- Every affine coefficient base admits an inverse-simple-root torus lift,
with its prescribed values on every compatible affine test. -/
def AffineInverseSimpleRootValuesStatement : Prop :=
  ∀ (N : AffinePinnedModel.{u}) (A : Type u) [CommRing A] [Algebra N.ring A]
    (c : N.basis.support → Aˣ),
    ∃ (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of A))
      (t : Over.mk p ⟶ (splitTorus (Spec (CommRingCat.of A)) N.coordinates).X),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      ∀ (B : Type u) [CommRing B] [Algebra A B]
        (a : Spec (CommRingCat.of B) ⟶ W) (hA : algebraBaseMap A B = a ≫ p)
        (s : N.basis.support),
        splitTorus.exponentValue N.coordinates
          (splitTorus.algebraPointsEquiv N.coordinates B (affineSectionPoint p B a hA t))
          (Multiplicative.ofAdd (N.rootDatum.root s)) =
          Units.map (algebraMap A B).toMonoidHom (c s)⁻¹

theorem affineInverseSimpleRootValuesStatement : AffineInverseSimpleRootValuesStatement.{u} :=
  fun N A _ _ c => exists_fppf_inverse_simpleRoot_values N A c

end Langlands.GroupScheme.AffinePinnedModel
