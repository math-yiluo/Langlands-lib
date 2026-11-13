import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: Zariski-local conjugacy of Borel subgroups of split reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Zariski-local conjugacy of Borel subgroups in the split case** (Conrad, *Reductive group
schemes* (2014), Corollary 5.2.13), over an affine base `Spec R`. Let `G` be a reductive group
scheme over `Spec R` that is split in the sense of Conrad's Definition 5.1.1 by a closed
coordinate split torus `t : 𝔾_m^I → G`, maximal on every residue-field fibre, with a root datum
`P` on the coordinate lattices that is the root datum of the torus on every field-valued fibre,
and with root spaces free of rank one over `R`.
1. For every Borel subgroup `i : B ⟶ G` and every point `s`, there are an open neighbourhood
   `V` of `s` and `g ∈ G(V)` such that the conjugate `g B_V g⁻¹` contains `T_V`.
2. For any two Borel subgroups `i`, `i'` of `G` containing `T` and every point `s`, there are an
   open neighbourhood `V` of `s` and a point `n ∈ N_G(T)(V)` with `n B_V n⁻¹ = B'_V`. -/
def SplitBorelZariskiLocalConjugacyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (I : Type u) [Fintype I] (t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
    haveI := hG.isAffineHom
    IsClosedSubgroup t →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t →
    IsFibrewiseRootDatumOf I G t P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G t (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    (∀ (B : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G), IsRelativeBorelSubgroup i →
      ∀ s : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, s ∈ V ∧
        ∃ g : Over.mk (𝟙 V.toScheme) ⟶ ((GroupScheme.baseChange V.ι).obj G).X,
          SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map t) ≤
            SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i ≫
              (((GroupScheme.baseChange V.ι).obj G).innerIso g).hom)) ∧
    (∀ (B B' : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G) (i' : B' ⟶ G),
      IsRelativeBorelSubgroup i → IsRelativeBorelSubgroup i' →
      SubgroupFunctor.range t ≤ SubgroupFunctor.range i →
      SubgroupFunctor.range t ≤ SubgroupFunctor.range i' →
      ∀ s : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, s ∈ V ∧
        ∃ n : Over.mk (𝟙 V.toScheme) ⟶ ((GroupScheme.baseChange V.ι).obj G).X,
          n ∈ (SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map t)).normalizer.carrier
            (Over.mk (𝟙 V.toScheme)) ∧
          SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i ≫
              (((GroupScheme.baseChange V.ι).obj G).innerIso n).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i'))

end Langlands.GroupScheme
