import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Derived.SuppliedCocenterTorusReduction

/-! # Generic cocharacters and reductivity of arbitrary split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Generic

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A generic cocharacter of any split-torus homomorphism has the same
centralizer as the full torus on every test scheme. -/
theorem IsSplitTorus.dynamicCentralizer_eq_torusCentralizer
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i := by
  refine le_antisymm ?_ (torusCentralizer_le_dynamicCentralizer i _)
  refine le_torusCentralizer_of_le_dynamicCentralizer hT i fun c => ?_
  refine dynamicCentralizer_le_of_weightSpace_zero_le
    dynamicSmooth dynamicConnected dynamicLie lieSubgroupEquality _ _ ?_ ?_
  · exact (SubgroupFunctor.range_comp_le _ i).trans
      ((range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _))
  · rw [map_zero, weightSpace_zero_genericCocharacter hT i ν hν]
    simpa only [Limits.comp_zero] using weightSpace_le_comp c i 0

/-- Every homomorphism from a split torus admits a cocharacter with the same
centralizer as the whole torus. -/
theorem IsSplitTorus.exists_cocharacter_centralizer_eq
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) :
    ∃ ν : cocharacterLattice T,
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i := by
  obtain ⟨ν, hν⟩ := hT.exists_genericCocharacter i
  exact ⟨ν, hT.dynamicCentralizer_eq_torusCentralizer i ν hν⟩

end Generic

/-- Every representative of the centralizer of a split-torus homomorphism
in a connected reductive field group is connected reductive. -/
def SplitTorusCentralizerReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsSplitTorus T.toGrp →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer i).IsRepresentedBy j → IsConnectedReductive M

/-- Dynamic-centralizer reductivity implies reductivity of every supplied
split-torus centralizer representative; closedness of that representative
is not an additional premise. -/
theorem splitTorusCentralizerReductive_of_dynamic
    (hred : DynamicCentralizerReductiveStatement.{u}) :
    SplitTorusCentralizerReductiveStatement.{u} := by
  intro k _ G hG T i hT M j hj
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨ν, hν⟩ := hT.exists_cocharacter_centralizer_eq i
  let χ := CommGroupScheme.groupHom ν ≫ i
  have hjχ : (Dynamic.centralizer χ).IsRepresentedBy j := by
    change (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j
    rwa [hν]
  exact hjχ.isConnectedReductive
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)
    (hred k G hG χ (Dynamic.Affine.centralizerScheme χ)
      (Dynamic.Affine.centralizerHom χ)
      (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ))

/-- Every supplied derived quotient of a split-torus centralizer has a
finite Galois splitting extension, conditionally on the two structural
statements for dynamic reductivity and cocenter existence. -/
theorem splitTorusCentralizerCocenter_finiteGaloisSplitting_of_inputs
    (hred : DynamicCentralizerReductiveStatement.{u})
    (hexists : CocenterQuotientExistenceStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp)
    (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G)
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M)
    (hd : IsDerivedSubgroup d)
    (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E),
      FiniteDimensional k E ∧ IsGalois k E ∧
      IsSplitTorus (GaloisPointComparison.baseChanged k E Q.toGrp) :=
  suppliedCocenter_finiteGaloisSplitting_of_existence hexists k M D d
    (splitTorusCentralizerReductive_of_dynamic hred k G hG T i hT M j hj) hd Q q hq

end Langlands.GroupScheme
