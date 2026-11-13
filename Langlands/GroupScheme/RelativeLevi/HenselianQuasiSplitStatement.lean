import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Basic

/-! # Statement: reductive groups over henselian local rings with finite residue field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reductive groups over henselian local rings with finite residue field** (Conrad,
*Reductive group schemes* (2014), Corollary 5.2.14). Let `R` be a henselian local ring with
finite residue field and `G` a reductive group scheme over `Spec R`. Then `G` is quasi-split
over `R`, and there is a local ring `R'` that is a finite étale `R`-algebra such that `G_{R'}`
is split in the sense of Conrad's Definition 5.1.1: it has a closed coordinate split torus
`𝔾_m^I → G_{R'}` that is a maximal torus on every residue-field fibre, a root datum `P` on
the coordinate lattices that is the root datum of the torus on every field-valued fibre, and
for every root `α` of `P` the weight space of the torus on `Lie(G_{R'})` with exponent
`P.root α` is free of rank one over `R'`. -/
def HenselianFiniteResidueQuasiSplitStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G),
    IsRelativeQuasiSplit G ∧
    haveI := hG.isAffineHom
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧ Module.Finite R R' ∧
      haveI : IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap R R')).obj G).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom _))
      ∃ (I : Type u) (_ : Fintype I)
        (i : splitTorus (Spec (CommRingCat.of R')) I ⟶
          (GroupScheme.baseChange (Spec.algebraMap R R')).obj G),
        IsClosedSubgroup i ∧
        IsFibrewiseMaximalTorus
          (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R')) I) i ∧
        ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
          IsFibrewiseRootDatumOf I ((GroupScheme.baseChange (Spec.algebraMap R R')).obj G) i P ∧
          ∀ α : J, Nonempty
            (splitTorus.exponentWeightSpace I
                ((GroupScheme.baseChange (Spec.algebraMap R R')).obj G) i (P.root α)
              ≃ₗ[CommRingCat.of R'] CommRingCat.of R')

end Langlands.GroupScheme
