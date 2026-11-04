import Langlands.GroupScheme.Nilpotent.TorusWeights
import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.GeometricConnectedness

/-! # Tori are central in smooth connected nilpotent affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- The full all-test centralizer of any split torus mapping to a smooth
connected geometrically nilpotent affine group is the whole group. -/
theorem IsNilpotentGroupScheme.splitTorusCentralizer_eq_top
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) : torusCentralizer i = ⊤ := by
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have hInv : (AutomorphicAction.conjugation i).lieInvariants = ⊤ := by
    apply top_unique
    intro X _
    have hX : X ∈ weightSpace i 0 := by
      rw [hG.weightSpace_zero_eq_top T hT i]
      trivial
    intro A _ _ t
    rw [AutomorphicAction.differential_conjugation]
    simpa only [Lie.characterValue_zero, Units.val_one, one_smul] using hX A t
  classical
  obtain ⟨I, hfin, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let := Module.Finite.iff_addGroup_fg.mp (inferInstance : Module.Finite ℤ (I → ℤ))
  let d := e ≪≫
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  have h := AutomorphicAction.fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top
    (AutomorphicAction.conjugation i) d hInv
  rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer] at h

/-- Every homomorphism from a split torus into a smooth connected
geometrically nilpotent affine group is central on all test schemes. -/
theorem IsNilpotentGroupScheme.isCentral_of_isSplitTorus
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) : IsCentral i := by
  intro U t V a g
  have hg : g ∈ (torusCentralizer i).carrier V := by
    rw [hG.splitTorusCentralizer_eq_top T hT i]
    trivial
  exact (hg V (𝟙 V) (a ≫ t)).symm

/-- The representing inclusion of any split-torus centralizer is an
isomorphism onto a smooth connected geometrically nilpotent affine group. -/
def IsNilpotentGroupScheme.splitTorusCentralizerIso
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j) : C ≅ G :=
  (show (⊤ : SubgroupFunctor G).IsRepresentedBy j from
    (hG.splitTorusCentralizer_eq_top T hT i) ▸ hj).topIso

@[simp] theorem IsNilpotentGroupScheme.splitTorusCentralizerIso_hom
    (hG : IsNilpotentGroupScheme G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ G) (hj : (torusCentralizer i).IsRepresentedBy j) :
    (hG.splitTorusCentralizerIso T hT i j hj).hom = j :=
  SubgroupFunctor.IsRepresentedBy.topIso_hom _

end Langlands.GroupScheme
