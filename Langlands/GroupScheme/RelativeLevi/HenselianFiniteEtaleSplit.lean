import Langlands.GroupScheme.RelativeLevi.HenselianFiniteEtaleSplitReduction
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementProof

/-! # Finite étale splitting data over a Henselian local ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A chosen local finite étale splitting algebra, coordinate maximal torus,
and full root datum with rank-one actual root exponent spaces. -/
def henselianFiniteEtaleSplitData
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G) :
    haveI := hG.isAffineHom
    Σ' (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : Algebra.Etale R R') (_ : Module.Finite R R'),
      haveI : IsAffineHom ((baseChange (Spec.algebraMap R R')).obj G).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom _))
      Σ' (I : Type u) (_ : Fintype I)
        (i : splitTorus (Spec (CommRingCat.of R')) I ⟶
          (baseChange (Spec.algebraMap R R')).obj G)
        (_ : IsClosedSubgroup i)
        (_ : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
        (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        IsFibrewiseRootDatumOf I ((baseChange (Spec.algebraMap R R')).obj G) i P ∧
        ∀ α : J, Nonempty (splitTorus.exponentWeightSpace I
          ((baseChange (Spec.algebraMap R R')).obj G) i (P.root α) ≃ₗ[R'] R') := by
  apply Classical.choice
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨A, hA, f, hf, hx, I, hI, i, hic, hi⟩ :=
    exists_etale_affine_split_maximalTorus _ G hG (IsLocalRing.closedPoint R)
  let : CommRing A := hA
  let : Fintype I := hI
  obtain ⟨R', hR', hlR', aR', he, hm, g, hfac⟩ :=
    Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement R A f hf hx
  let : CommRing R' := hR'
  let : IsLocalRing R' := hlR'
  let : Algebra R R' := aR'
  obtain ⟨j, hjc, hjm, J, P, hP, hline⟩ :=
    localSplitDataOfFactoredNeighbourhood G hG f I i hic hi g hfac
  exact ⟨⟨R', hR', hlR', aR', he, hm, I, hI, j, hjc, hjm, J, P, hP, hline⟩⟩

end Langlands.GroupScheme
