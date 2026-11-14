import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.AutomorphicActionPointIso
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Statement: automorphisms of a pinned split reductive group over a connected affine base -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Automorphisms of a pinned split reductive group over a connected affine base**
(Conrad, *Reductive group schemes* (2014), Theorem 7.1.9(3), on points over the base). Let
`S = Spec R` be connected and `G` a split reductive group over `S`, with split maximal torus
`i : 𝔾_m^I → G`, root datum `P`, base `b` and pinning `X`. Let `p : G ⟶ Gad` be an fppf
quotient of `G` by its centre and `c` the action of `Gad` on `G` induced by conjugation.
Then the action of `Gad(S)` is an injective homomorphism `inn : Gad(S) → Aut G`, and there
is a homomorphism `π : Aut G → Aut P` with kernel the image of `inn` and image the based
automorphisms of `P`. Each based automorphism `θ` is induced by exactly one automorphism
`σ` of `G` that preserves the torus and the pinning, and `π σ = θ` for it. -/
def AffinePinnedAutomorphismGroupStatement : Prop :=
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
    ∀ (b : P.Base)
      (X : ∀ a : b.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I G i (P.root a))
      (Gad : GroupScheme (Spec (CommRingCat.of R))) (p : G ⟶ Gad),
      RelativeRoot.IsFppfQuotient (center G) p →
    ∀ c : AutomorphicAction Gad G, c.restrict p = AutomorphicAction.conjugation (𝟙 G) →
    let Based : RootPairing.Aut P → Prop := fun θ =>
      ∀ j : J, j ∈ b.support ↔ θ.indexEquiv j ∈ b.support
    let Pinned : CategoryTheory.Aut G → RootPairing.Aut P → Prop := fun σ θ =>
      ∃ hθ : Based θ,
        (∃ τ : splitTorus (Spec (CommRingCat.of R)) I ≅ splitTorus (Spec (CommRingCat.of R)) I,
          i ≫ σ.hom = τ.hom ≫ i ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I → ℤ),
            ∏ j, splitTorus.pointsEquiv I U (x ≫ τ.hom.hom.hom) j ^ θ.weightMap m j =
              ∏ j, splitTorus.pointsEquiv I U x j ^ m j) ∧
        ∀ a : b.support,
          Lie.targetMapLinear σ.hom (CommRingCat.of R) (X a 1).val =
            (X ⟨θ.indexEquiv a, (hθ a).mp a.property⟩ 1).val
    ∃ (inn : (Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Gad.X) →* CategoryTheory.Aut G)
      (π : CategoryTheory.Aut G →* RootPairing.Aut P),
      (∀ x, inn x = c.basePointIso x) ∧
      Function.Injective inn ∧
      π.ker = inn.range ∧
      (∀ θ, θ ∈ π.range ↔ Based θ) ∧
      (∀ θ, Based θ → ∃! σ, Pinned σ θ) ∧
      ∀ σ θ, Pinned σ θ → π σ = θ

end Langlands.GroupScheme
