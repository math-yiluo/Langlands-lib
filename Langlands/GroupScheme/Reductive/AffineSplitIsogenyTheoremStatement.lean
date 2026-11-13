import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.AbelianScheme.Isogeny
import Langlands.LinearAlgebra.RootDatumIsogeny

/-! # Statement: the Isogeny Theorem for split reductive groups over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isogeny Theorem over an affine base** (Conrad, *Reductive group schemes* (2014),
Theorem 6.1.16(1), existence part, over `Spec R`). Let `G` and `H` be reductive group schemes
over `Spec R`, split in the sense of Conrad's Definition 5.1.1 by closed coordinate split tori
`i : 𝔾_m^I → G` and `i' : 𝔾_m^{I'} → H`, maximal on every residue-field fibre, with root data
`P` and `Q` on the coordinate lattices that are the root data of the tori on every field-valued
fibre, and with root spaces free of rank one over `R`. Let `f` be an isogeny of root data from
`Q` to `P` with characteristic exponent `p` (a `p`-morphism from the root datum of `G` to that
of `H` in Conrad's Definition 6.1.8), such that `p = 0` in `R` whenever some root factor of `f`
is not `1`. Then `f` is induced by an isogeny `φ : G → H` compatible with the splittings: `φ`
carries the torus of `G` into the torus of `H` through a homomorphism of tori
`τ : 𝔾_m^I → 𝔾_m^{I'}` that pulls back the character `t ↦ ∏ tⱼ ^ mⱼ` of `𝔾_m^{I'}` to the
character of `𝔾_m^I` with exponent vector `f.weightMap m`. -/
def AffineSplitIsogenyTheoremStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G H : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (hH : IsReductive H)
    (I I' : Type u) [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (J J' : Type u) [Finite J] [Finite J']
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    [P.IsReduced] [Q.IsReduced],
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
    ∀ (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
      (∀ j' : J', f.rootFactor j' ≠ 1 → (p : R) = 0) →
      ∃ (φ : G ⟶ H) (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶
          splitTorus (Spec (CommRingCat.of R)) I'),
        IsIsogeny φ ∧
        i ≫ φ = τ ≫ i' ∧
        ∀ (U : Over (Spec (CommRingCat.of R)))
          (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
          ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
            ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j

end Langlands.GroupScheme
