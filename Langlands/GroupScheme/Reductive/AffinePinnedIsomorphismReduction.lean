import Langlands.GroupScheme.Reductive.AffinePinnedExistenceReduction
import Langlands.GroupScheme.Reductive.AffinePinnedUniqueness

/-! # Reduction of affine pinned full faithfulness to unpinned existence -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Affine pinned full faithfulness follows from unpinned affine isomorphism existence. -/
theorem affinePinnedIsomorphismTheorem_of_unpinned
    (hU : AffineSplitIsomorphismTheoremStatement.{u}) :
    AffinePinnedIsomorphismTheoremStatement.{u} := by
  intro R _ G H hG hH I I' _ _ i i' J J' P Q
  let := hG.isAffineHom
  let := hH.isAffineHom
  intro hi hmax hP hfree hi' hmax' hQ hfree' b b' X Y f hf
  obtain ⟨phi, hphi⟩ := affinePinnedIsomorphismExistence_of_unpinned hU
    R G H hG hH I I' i i' J J' P Q
    hi hmax hP hfree hi' hmax' hQ hfree' b b' X Y f hf
  exact ⟨phi, hphi, fun psi hpsi => affinePinnedIsomorphism_unique
    R G H hG hH I I' i i' J J' P Q hi hmax hP hfree
    b b' X Y f hf psi phi hpsi hphi⟩

/-- The actual compatible pinned isomorphism is a unique element of its subtype. -/
@[instance_reducible]
noncomputable def uniqueAffinePinnedIsomorphismOfUnpinned
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
      Unique { φ : G ≅ H //
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
  let hex := affinePinnedIsomorphismTheorem_of_unpinned hU
    R G H hG hH I I' i i' J J' P Q
    hi hmax hP hfree hi' hmax' hQ hfree' b b' X Y f hf
  exact { default := ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
          uniq := fun psi => Subtype.ext ((Classical.choose_spec hex).2
            psi.val psi.property) }

end Langlands.GroupScheme
