import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Statement: the pinned Isomorphism Theorem for split reductive groups over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Pinned Isomorphism Theorem over an affine base, full faithfulness** (Conrad,
*Reductive group schemes* (2014), Theorem 6.1.17, first sentence, full faithfulness of the
functor from pinned split reductive groups to based root data, over `Spec R`). Let `G` and
`H` be reductive group schemes over `Spec R`, split by closed coordinate split tori
`i : 𝔾_m^I → G` and `i' : 𝔾_m^{I'} → H` that are maximal on every residue-field fibre, with
root data `P` and `Q` on the coordinate lattices that are the root data of the tori on
every field-valued fibre, and with root spaces free of rank one over `R`. Pin them by bases
`b` of `P` and `b'` of `Q` and by trivializations `X a : R ≃ 𝔤_a` and `Y a' : R ≃ 𝔥_{a'}`
of the simple root spaces. Then every equivalence of root data `f : Q ≃ P` that matches
the bases arises from exactly one isomorphism `φ : G ≅ H` that is compatible with the
splittings (via an isomorphism of tori `τ` whose pullback of characters is `f.weightMap`)
and with the pinnings (the Lie algebra map of `φ` sends the pinning vector `X a` to the
pinning vector `Y a'` whenever `a` corresponds to `a'` under `f`). -/
def AffinePinnedIsomorphismTheoremStatement : Prop :=
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
      ∃! φ : G ≅ H,
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

end Langlands.GroupScheme
