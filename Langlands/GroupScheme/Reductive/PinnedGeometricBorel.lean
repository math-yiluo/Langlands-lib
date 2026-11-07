import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # The actual geometric Borel of a supplied split pinning -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The reverse of the chosen positive cocharacter is regular. -/
theorem isRegularCocharacter_neg_positiveCocharacter :
    IsRegularCocharacter p.inclusion (-p.positiveCocharacter) := by
  intro α hα
  simpa only [map_neg, neg_ne_zero] using
    p.isGenericCocharacter_positiveCocharacter α hα

/-- The negative dynamic parabolic remains Borel after every field extension. -/
theorem isBorelSubgroup_baseChange_negativeBorelHom
    (K : Type u) [Field K] [Algebra k K] :
    IsBorelSubgroup
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map p.negativeBorelHom) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let F := GroupScheme.baseChange b
  let T := (CommGroupScheme.baseChange b).obj p.torus
  let ν := cocharacterLattice.baseChange b p.torus (-p.positiveCocharacter)
  have hG : IsConnectedReductive (F.obj G) :=
    connectedReductiveFieldExtensionStatement k K G p.isConnectedReductive
  have := p.isConnectedReductive.smooth
  have := hG.isAffineHom
  have hT : IsSplitTorus T.toGrp := p.isSplitTorus.baseChange b
  have hi : IsMaximalTorus (T := T) (F.map p.inclusion) :=
    (maximalTorusBaseChange k K G p.torus p.inclusion p.isSplitTorus.isTorus
      p.isMaximalTorus.2.1).mp p.isMaximalTorus
  have hν : IsRegularCocharacter (T := T) (F.map p.inclusion) ν := by
    intro α hα
    obtain ⟨β, rfl⟩ := (characterLattice.baseChangeEquiv b p.torus p.isSplitTorus).surjective α
    have hβ := (mem_roots_baseChange_iff (K := K) G p.torus p.isSplitTorus p.inclusion β).mp hα
    rw [characterLattice.baseChangeEquiv_apply, latticePairing_baseChange]
    exact p.isRegularCocharacter_neg_positiveCocharacter β hβ
  have heq : Dynamic.baseChangeCocharacter b
        (Dynamic.oppositeCocharacter p.positiveGm) =
      CommGroupScheme.groupHom ν ≫ F.map p.inclusion := by
    change Dynamic.baseChangeCocharacter b
        (Dynamic.oppositeCocharacter
          (CommGroupScheme.groupHom p.positiveCocharacter ≫ p.inclusion)) = _
    rw [← groupHom_neg_comp_eq_oppositeCocharacter,
      Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic]
  have hrep := p.isRepresentedBy_negativeBorelHom.baseChange b
  rw [← Dynamic.parabolic_baseChange, heq] at hrep
  exact (regularCocharacterBorel K (F.obj G) hG T (F.map p.inclusion) hT hi).1
    ν hν (F.obj p.negativeBorel) (F.map p.negativeBorelHom)
    ((Dynamic.Affine.isClosedSubgroup_parabolicHom _).baseChange b) hrep

/-- The negative dynamic parabolic is an actual field-defined geometric Borel. -/
theorem isGeometricBorelSubgroup_negativeBorelHom :
    IsGeometricBorelSubgroup p.negativeBorelHom :=
  isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
    (p.isBorelSubgroup_baseChange_negativeBorelHom (AlgebraicClosure k))
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)

/-- The actual geometric Borel, including its inclusion and geometric property. -/
def negativeGeometricBorel :
    Σ B : GroupScheme (Spec (CommRingCat.of k)), {i : B ⟶ G // IsGeometricBorelSubgroup i} :=
  ⟨p.negativeBorel, p.negativeBorelHom, p.isGeometricBorelSubgroup_negativeBorelHom⟩

/-- The supplied torus and the constructed negative Borel form a Borel pair. -/
theorem isBorelPair_negativeBorelHom : IsBorelPair p.negativeBorelHom p.inclusion :=
  ⟨p.isGeometricBorelSubgroup_negativeBorelHom.1, p.isMaximalTorus,
    p.torusToNegativeBorel, p.torusToNegativeBorel_comp⟩

include p in
/-- A supplied complete split pinning supplies quasi-splitness of the actual group. -/
theorem isQuasiSplit : IsQuasiSplit G :=
  ⟨p.isConnectedReductive, p.negativeBorel, p.negativeBorelHom,
    p.isGeometricBorelSubgroup_negativeBorelHom⟩

end Langlands.GroupScheme.SplitPinning
