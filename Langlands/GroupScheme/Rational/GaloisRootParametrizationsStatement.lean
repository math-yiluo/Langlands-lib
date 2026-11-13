import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct
import Langlands.GroupScheme.GaloisPointRational

/-! # Compatible parametrizations of a Galois-stable family of roots -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A Galois-stable indexed root family of a descended split maximal torus
admits root parametrizations intertwining coefficient conjugation. -/
def GaloisRootParametrizationsStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    letI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))
    ∀ (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)),
      p.inclusion = CommGroupScheme.groupHom eT.hom ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map i →
      ∀ (J : Type u) (ρ : (K ≃ₐ[k] K) →* Equiv.Perm J) (α : J → p.rootIndex),
        (∀ (σ : K ≃ₐ[k] K) (c : J),
          characterLattice.congr eT (p.rootDatum.root (α (ρ σ c))) =
            characterLattice.galoisRepresentation k K T σ
              (characterLattice.congr eT (p.rootDatum.root (α c)))) →
        ∃ x : (c : J) → p.RootParametrization (α c),
          ∀ (σ : K ≃ₐ[k] K) (c : J) (s : K),
            GaloisPointComparison.rationalConjugate k K G σ ((x c).rationalPoint s) =
              (x (ρ σ c)).rationalPoint (σ s)

end Langlands.GroupScheme
