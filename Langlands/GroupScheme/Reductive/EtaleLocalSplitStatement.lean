import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality

/-! # Statement: reductive group schemes split étale-locally on the base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reductive group schemes split étale-locally** (Conrad, *Reductive group schemes*
(2014), Lemma 5.1.3). For every reductive group scheme `G` over a scheme `S` and every point
`s` of `S` there is an étale morphism `f : Spec R → S` from an affine scheme whose image
contains `s`, such that `G_R` is split in the sense of Conrad's Definition 5.1.1: it has a
closed coordinate split torus `𝔾_m^I → G_R` that is a maximal torus on every residue-field
fibre, a finite reduced root datum `P` on the coordinate lattices `I → ℤ` that is the actual
root datum of the torus on every field-valued fibre (so roots and coroots are constant), and
for every root `α` of `P` the actual weight space of the torus on `Lie(G_R)` with exponent
`P.root α` is free of rank one over `R`. -/
def EtaleLocalSplitReductiveStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (hG : IsReductive G) (s : S),
    haveI := hG.isAffineHom
    ∃ (R : Type u) (_ : CommRing R) (f : Spec (CommRingCat.of R) ⟶ S),
      haveI : IsAffineHom ((GroupScheme.baseChange f).obj G).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom f))
      Etale f ∧ (∃ x : Spec (CommRingCat.of R), f.base x = s) ∧
      ∃ (I : Type u) (_ : Fintype I)
        (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ (GroupScheme.baseChange f).obj G),
        IsClosedSubgroup i ∧
        IsFibrewiseMaximalTorus
          (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i ∧
        ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
          IsFibrewiseRootDatumOf I ((GroupScheme.baseChange f).obj G) i P ∧
          ∀ α : J, Nonempty
            (splitTorus.exponentWeightSpace I ((GroupScheme.baseChange f).obj G) i (P.root α)
              ≃ₗ[CommRingCat.of R] CommRingCat.of R)

end Langlands.GroupScheme
