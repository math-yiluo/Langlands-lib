import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.LinearAlgebra.RootDatumIsogeny

/-! # Statement: quasi-finite surjections of split reductive groups respect the splittings -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Quasi-finite surjections between split reductive groups are compatible with the
splittings** (Conrad, *Reductive group schemes* (2014), Proposition 6.1.7, over `Spec R`).
Let `G` and `H` be reductive group schemes over `Spec R`, split in the sense of Conrad's
Definition 5.1.1 by closed coordinate split tori `i : 𝔾_m^I → G` and `i' : 𝔾_m^{I'} → H`,
maximal on every residue-field fibre, with root data `P` and `Q` on the coordinate lattices
that are the root data of the tori on every field-valued fibre, and with root spaces free of
rank one over `R`. Let `φ : G → H` be a locally quasi-finite surjective homomorphism that
carries the torus of `G` into the torus of `H` through a homomorphism of tori
`τ : 𝔾_m^I → 𝔾_m^{I'}`. Then:

1. every point of `Spec R` has an open neighbourhood `V` with an isogeny of root data
   `f : Q → P` of some characteristic exponent `p`, with `p = 0` on `V` whenever some root
   factor of `f` is not `1`, such that over every test scheme mapping into `V` the map `τ`
   pulls the character `t ↦ ∏ tⱼ ^ mⱼ` of `𝔾_m^{I'}` back to the character of `𝔾_m^I` with
   exponent vector `f.weightMap m`;
2. if `Spec R` is connected, such an `f` exists with `V` the whole of `Spec R`. -/
def AffineSplitSurjectionRootDatumStatement : Prop :=
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
    ∀ (φ : G ⟶ H) (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶
        splitTorus (Spec (CommRingCat.of R)) I'),
      LocallyQuasiFinite φ.hom.hom.left →
      Surjective φ.hom.hom.left →
      i ≫ φ = τ ≫ i' →
      (∀ s : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, s ∈ V ∧
        ∃ (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
          (∀ j' : J', f.rootFactor j' ≠ 1 → (p : Γ(Spec (CommRingCat.of R), V)) = 0) ∧
          ∀ (U : Over (Spec (CommRingCat.of R))), U.hom ⁻¹ᵁ V = ⊤ →
            ∀ (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
              ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
                ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j) ∧
      (ConnectedSpace (Spec (CommRingCat.of R)) →
        ∃ (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
          (∀ j' : J', f.rootFactor j' ≠ 1 → (p : R) = 0) ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
            ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
              ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j)

end Langlands.GroupScheme
