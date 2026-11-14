import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Statement: normalizer points of a split maximal torus map onto the Weyl group -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Normalizer points of a split maximal torus and the Weyl group** (Conrad, *Reductive group
schemes* (2014), Example 6.4.3). Let `R` be a ring with connected nonempty spectrum `S`, and
let `G` be a split reductive group over `S`: a closed split maximal torus `i : 𝔾_m^I ⟶ G`, one
finite reduced root datum `P` on the coordinate lattices `ℤ^I` realized on every field fibre,
and root spaces free of rank one. Say that `n ∈ G(S)` *induces* `w ∈ Aut P` when conjugation
by `n` restricts along `i` to the automorphism of `𝔾_m^I` whose pullback on characters is
`w`. Then the sequence `1 → T(S) → N_G(T)(S) → W(Φ) → 1` is exact:

1. every element of the Weyl group `W(P)` is induced by a point of `G(S)`;
2. every point of `G(S)` normalizing `i` induces an element of `W(P)`;
3. every point of `G(S)` centralizing `i` is a point of the torus.

Moreover, if `R` is a domain, some finite subgroup of the normalizer points contains, for each
element of `W(P)`, a point inducing it. -/
def AffineSplitNormalizerWeylStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [ConnectedSpace (Spec (CommRingCat.of R))]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Fintype I] (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
    haveI := hG.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i →
    IsFibrewiseRootDatumOf I G i P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    let Induces : (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X) → RootPairing.Aut P → Prop :=
      fun n w =>
        ∃ σ : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ≅
            splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I,
          IsNormalizingPoint (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i n σ ∧
            ∀ (U : Over (Spec (CommRingCat.of R)))
              (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I → ℤ),
              ∏ j, splitTorus.pointsEquiv I U
                  (x ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) j ^ m j =
                ∏ j, splitTorus.pointsEquiv I U x j ^ (w • m) j
    (∀ w ∈ P.weylGroup, ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X, Induces n w) ∧
      (∀ n ∈ normalizerPoints (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i,
        ∃ w ∈ P.weylGroup, Induces n w) ∧
      (∀ n ∈ centralizerPoints (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i,
        ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
          n = t ≫ i.hom.hom) ∧
      (IsDomain R →
        ∃ H : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ G.X),
          H ≤ normalizerPoints (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i ∧
            Finite H ∧ ∀ w ∈ P.weylGroup, ∃ n ∈ H, Induces n w)

end Langlands.GroupScheme
