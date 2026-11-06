import Langlands.GroupScheme.Lie.WeightLineGaloisCoordinates
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof

/-! # Galois coordinates on roots of a split maximal torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Each actual root weight of a maximal torus after it splits is a line.
The line dimension is a conclusion of the reductive-group theorem. -/
theorem finrank_splitRootWeight_eq_one
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus (T_L).toGrp)
    (β : roots (T := T_L) (G := G_L) j_L) :
    Module.finrank L (weightSpace j_L β.val) = 1 := by
  have : Smooth G.X.hom := hG.smooth
  have hGL : IsConnectedReductive G_L :=
    connectedReductiveFieldExtensionStatement k L G hG
  have hjL : IsMaximalTorus (T := T_L) j_L :=
    (maximalTorusBaseChange k L G T j hj.1 hj.2.1).mp hj
  obtain ⟨e⟩ := splitRootLieLine L G_L hGL T_L hT j_L hjL β.val β.property
  rw [← e.finrank_eq]
  exact Module.finrank_self L

variable [FiniteDimensional k L]

attribute [local instance] rootsGaloisAction

/-- Actual split maximal-torus roots have stabilizer-equivariant coordinates
without a supplied line-dimension or weight-space-action premise. -/
def splitRootWeightEquivariantLinearEquiv
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus (T_L).toGrp)
    (β : roots (T := T_L) (G := G_L) j_L) :
    L ≃ₗ[L] weightSpace j_L β.val :=
  rootWeightEquivariantLinearEquiv k L j β
    (finrank_splitRootWeight_eq_one k L j hG hj hT β)

/-- The chosen coordinate uses the canonical actual Lie coefficient map. -/
theorem splitRootWeightEquivariantLinearEquiv_galois
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus (T_L).toGrp)
    (β : roots (T := T_L) (G := G_L) j_L)
    (σ : MulAction.stabilizer (L ≃ₐ[k] L) β) (x : L) :
    Lie.baseChangeGaloisEquiv k L G σ.val
        (splitRootWeightEquivariantLinearEquiv k L j hG hj hT β x).val =
      (splitRootWeightEquivariantLinearEquiv k L j hG hj hT β (σ.val x)).val :=
  rootWeightEquivariantLinearEquiv_galois k L j β
    (finrank_splitRootWeight_eq_one k L j hG hj hT β) σ x

end Langlands.GroupScheme
