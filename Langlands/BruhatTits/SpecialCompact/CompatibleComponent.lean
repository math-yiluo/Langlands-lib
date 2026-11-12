import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup

/-! # Actual compatible split components for the simultaneous-basis target -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- The split component can be chosen in the prescribed maximal split torus,
independently of any compact-open basis member. -/
theorem exists_compatibleStandardSplitComponent
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of F))) (q : A.toGrp ⟶ S.toGrp),
      IsCompatibleStandardSplitComponent i ν J A q := by
  obtain ⟨hM, A, a, q, ha, hcomp⟩ :=
    standardLeviSplitComponentStatement F G hG S i hi ν hν J hJ
  have hq : IsSplitSubtorus q :=
    IsSplitSubtorus.of_comp hi.isSplitSubtorus.2
      (hcomp.symm ▸ ha.isCentralSplitTorus.isSplitSubtorus.comp
        (Standard.isClosedSubgroup_leviHom i ν J))
  exact ⟨A, q, hq, Standard.leviScheme i ν J, Standard.leviHom i ν J,
    a, Standard.isRepresentedBy_leviHom i ν J,
    Standard.isClosedSubgroup_leviHom i ν J, hM, ha, hcomp.symm⟩

end Langlands.BruhatTits.SpecialCompact
