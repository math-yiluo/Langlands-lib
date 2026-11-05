import Langlands.GroupScheme.Torus.FiniteFieldGeometricMaximalStatement
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalFieldIso
import Langlands.GroupScheme.Torus.FrobeniusConjugate
import Langlands.GroupScheme.Torus.GeometricFrobeniusDescent
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.GeometricConnectedness

/-! # Geometric maximal-torus data from explicit geometric conjugacy -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An actual torus inclusion over the original field, maximal both there and
after the specified field extension. -/
structure GeometricMaximalTorusData
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  isMaximalTorus : IsMaximalTorus inclusion
  isMaximalTorus_baseChange :
    IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj torus)
      ((baseChange (algebraBaseMap k K)).map inclusion)

section FiniteField

variable (k Ω : Type u) [Field k] [Fintype k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Geometric conjugacy supplies a torus maximal over the original finite field
and over the specified algebraic algebraically closed extension. -/
theorem exists_geometricMaximalTorus_of_conjugacy
    (hconj : MaximalToriAreConjugate ((baseChange (algebraBaseMap k Ω)).obj G)) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j : T₀.toGrp ⟶ G),
      IsMaximalTorus j ∧
        IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀)
          ((baseChange (algebraBaseMap k Ω)).map j) := by
  let : Smooth ((baseChange (algebraBaseMap k Ω)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (algebraBaseMap k Ω))
    infer_instance
  let : IsAffineHom ((baseChange (algebraBaseMap k Ω)).obj G).X.hom :=
    TorusExistence.isAffineHom_baseChange Ω G
  obtain ⟨T, i, hi⟩ :=
    TorusExistence.exists_isMaximalTorus ((baseChange (algebraBaseMap k Ω)).obj G)
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω
  let a := galoisBaseMap k Ω σ
  let e := descentBaseChangeIso (algebraBaseMap k Ω) a
    (galoisBaseMap_over k Ω σ) G
  have hFi : IsMaximalTorus
      (T := (CommGroupScheme.baseChange a).obj T)
      ((baseChange a).map i ≫ e.hom) :=
    (hi.baseChange_fieldIso σ.toRingEquiv).comp_iso e
  have hc : SubgroupConjugate ((baseChange a).map i ≫ e.hom) i :=
    hconj _ _ _ _ hFi hi
  let j := frobeniusStableConjugate k Ω G i hc
  have hj : IsMaximalTorus j := hi.frobeniusStableConjugate k Ω G hc
  have hT : IsSplitTorus T.toGrp :=
    SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
      Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning T.toGrp hi.1
  have hF : SubgroupFunctor.galoisTransport k Ω G σ (SubgroupFunctor.range j) =
      SubgroupFunctor.range j := by
    change SubgroupFunctor.descentTransport _ _ _ _ _ = _
    rw [SubgroupFunctor.descentTransport_range]
    exact frobeniusStableConjugate_range_eq k Ω G i hc
  obtain ⟨T₀, j₀, _, hj₀, hjΩ, _⟩ :=
    hj.exists_descent_of_frobenius_range_eq hT hF
  exact ⟨T₀, j₀, hj₀, hjΩ⟩

/-- Choose actual geometric maximal-torus data from the explicit conjugacy
property of the geometric ambient group. -/
def geometricMaximalTorusDataOfConjugacy
    (hconj : MaximalToriAreConjugate ((baseChange (algebraBaseMap k Ω)).obj G)) :
    GeometricMaximalTorusData k Ω G :=
  Classical.choice <| by
    obtain ⟨T, i, hi, hiΩ⟩ := exists_geometricMaximalTorus_of_conjugacy k Ω G hconj
    exact ⟨⟨T, i, hi, hiΩ⟩⟩

end FiniteField

/-- The exact finite-field geometric existence target follows from the explicit
general maximal-torus conjugacy statement. -/
theorem finiteFieldGeometricMaximalTorus_of_maximalTorusConjugacy
    (hconj : MaximalTorusConjugacyStatement.{u}) :
    FiniteFieldGeometricMaximalTorusStatement.{u} := by
  intro k _ _ G _ _ _
  let : Fintype k := Fintype.ofFinite k
  let Ω := AlgebraicClosure k
  let b := algebraBaseMap k Ω
  let : Smooth ((baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom ((baseChange b).obj G).X.hom :=
    TorusExistence.isAffineHom_baseChange Ω G
  let : ConnectedSpace ((baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have hc : MaximalToriAreConjugate ((baseChange b).obj G) := by
    intro T T' i i' hi hi'
    obtain ⟨g, e, he⟩ := hconj Ω ((baseChange b).obj G) T T' i i' hi hi'
    let e' : T.toGrp ≅ T'.toGrp :=
      { hom := CommGroupScheme.groupHom e.hom
        inv := CommGroupScheme.groupHom e.inv
        hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
        inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
    exact ⟨g, e', he⟩
  let D := geometricMaximalTorusDataOfConjugacy k Ω G hc
  exact ⟨D.torus, D.inclusion, D.isMaximalTorus, D.isMaximalTorus_baseChange⟩

end Langlands.GroupScheme
