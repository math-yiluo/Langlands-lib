import Langlands.Global.AdelicGroupPointTopology
import Langlands.GroupScheme.AffinePointPiProducts

/-! # The actual archimedean point group as a product over infinite places -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

namespace Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Points over the actual completion at an infinite place. -/
abbrev InfinitePlaceGroupPoints (v : InfinitePlace F) :=
  G.affinePoints (CommAlgCat.of F v.Completion)

namespace InfinitePlaceGroupPoints

/-- The existing regular-function evaluation topology at a completion. -/
instance topologicalSpace (v : InfinitePlace F) :
    TopologicalSpace (InfinitePlaceGroupPoints F G v) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of F v.Completion)

end InfinitePlaceGroupPoints

namespace InfiniteAdelicGroupPoints

variable [IsAffine G.X.left]

/-- The infinite adelic point group decomposes over the actual archimedean completions. -/
def completions : InfiniteAdelicGroupPoints F G ≃ₜ*
    ((v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) :=
  G.affinePointsPiHomeomorph (fun v : InfinitePlace F => CommAlgCat.of F v.Completion)

/-- Projection to an actual completion, as a continuous group homomorphism. -/
def atPlace (v : InfinitePlace F) :
    InfiniteAdelicGroupPoints F G →ₜ* InfinitePlaceGroupPoints F G v where
  toMonoidHom := G.affinePointsEval
    (fun v : InfinitePlace F => CommAlgCat.of F v.Completion) v
  continuous_toFun := (continuous_apply v).comp (completions F G).continuous

/-- Assemble local archimedean points in the original infinite adelic point group. -/
def assemble (x : (v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) :
    InfiniteAdelicGroupPoints F G := (completions F G).symm x

@[simp]
theorem completions_apply (x : InfiniteAdelicGroupPoints F G) (v : InfinitePlace F) :
    completions F G x v = atPlace F G v x := rfl

@[simp]
theorem atPlace_assemble
    (x : (v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) (v : InfinitePlace F) :
    atPlace F G v (assemble F G x) = x v :=
  congrFun ((completions F G).apply_symm_apply x) v

@[simp]
theorem assemble_projections (x : InfiniteAdelicGroupPoints F G) :
    assemble F G (fun v => atPlace F G v x) = x :=
  (completions F G).symm_apply_apply x

@[simp]
theorem atPlace_evaluation (x : InfiniteAdelicGroupPoints F G)
    (a : Γ(G.X.left, ⊤)) (v : InfinitePlace F) :
    G.affinePointEvaluation (CommAlgCat.of F v.Completion) (atPlace F G v x) a =
      G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) x a v :=
  G.affinePointsEval_evaluation
    (fun v : InfinitePlace F => CommAlgCat.of F v.Completion) x a v

@[simp]
theorem assemble_evaluation
    (x : (v : InfinitePlace F) → InfinitePlaceGroupPoints F G v)
    (a : Γ(G.X.left, ⊤)) (v : InfinitePlace F) :
    G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (assemble F G x) a v =
      G.affinePointEvaluation (CommAlgCat.of F v.Completion) (x v) a :=
  G.affinePointPi_evaluation
    (fun v : InfinitePlace F => CommAlgCat.of F v.Completion) x a v

theorem continuous_assemble :
    Continuous (assemble F G) := (completions F G).symm.continuous

theorem assemble_mul
    (x y : (v : InfinitePlace F) → InfinitePlaceGroupPoints F G v) :
    assemble F G (x * y) = assemble F G x * assemble F G y :=
  (completions F G).symm.map_mul x y

end InfiniteAdelicGroupPoints

namespace GeneralLinearGroupPoints

variable (n : ℕ)

local instance generalLinearIsAffine :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- The actual local general-linear point group is the existing matrix group over
the actual completion, with its existing topology. -/
def infinitePlaceHomeomorph (v : InfinitePlace F) :
    InfinitePlaceGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) v ≃ₜ*
        Matrix.GeneralLinearGroup (Fin n) v.Completion :=
  GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F v.Completion)

/-- The general completion projection agrees with coefficient evaluation on the
original infinite adelic matrix group. -/
theorem infinitePlaceHomeomorph_atPlace
    (x : InfiniteAdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (v : InfinitePlace F) :
    infinitePlaceHomeomorph F n v (InfiniteAdelicGroupPoints.atPlace F _ v x) =
      Matrix.GeneralLinearGroup.map
        (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v)
        (infiniteHomeomorph F n x) :=
  GroupScheme.GeneralLinear.affinePointsEquiv_naturality (n := Fin n)
    (R := CommRingCat.of F) (S := CommAlgCat.of F (InfiniteAdeleRing F))
    (T := CommAlgCat.of F v.Completion)
    (CommAlgCat.ofHom (Pi.evalAlgHom F (fun v : InfinitePlace F => v.Completion) v)) x

end GeneralLinearGroupPoints

end Langlands.Global
