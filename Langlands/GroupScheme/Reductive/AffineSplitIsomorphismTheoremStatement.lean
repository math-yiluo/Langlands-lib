import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Statement: the Isomorphism Theorem for split reductive groups over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isomorphism Theorem over an affine base** (Conrad, *Reductive group schemes* (2014),
Theorem 6.1.17, "in particular" clause, over `Spec R`). Let `G` and `H` be reductive group
schemes over `Spec R`, split in the sense of Conrad's Definition 5.1.1 by closed coordinate
split tori `i : 𝔾_m^I → G` and `i' : 𝔾_m^{I'} → H`, maximal on every residue-field fibre, with
root data `P` and `Q` on the coordinate lattices that are the root data of the tori on every
field-valued fibre, and with root spaces free of rank one over `R`. Every equivalence of root
data `f : Q ≃ P` arises from an isomorphism `φ : G ≅ H` compatible with the splittings: there
is an isomorphism of tori `τ : 𝔾_m^I ≅ 𝔾_m^{I'}` with `i ≫ φ = τ ≫ i'` that pulls back the
character `t ↦ ∏ tⱼ ^ mⱼ` of `𝔾_m^{I'}` to the character of `𝔾_m^I` with exponent
vector `f m`. -/
def AffineSplitIsomorphismTheoremStatement : Prop :=
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
    ∀ f : RootPairing.Equiv Q P,
      ∃ (φ : G ≅ H) (τ : splitTorus (Spec (CommRingCat.of R)) I ≅
          splitTorus (Spec (CommRingCat.of R)) I'),
        i ≫ φ.hom = τ.hom ≫ i' ∧
        ∀ (U : Over (Spec (CommRingCat.of R)))
          (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
          ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom.hom) j' ^ m j' =
            ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j

end Langlands.GroupScheme
