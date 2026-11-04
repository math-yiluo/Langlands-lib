import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.ActionWeightFunctoriality
import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Contraction and positive weights when the dynamic centralizer is a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Dynamic

variable {k : Type u} [Field k]
    {G H P Z U : GroupScheme (Spec (CommRingCat.of k))}
    [IsSeparated G.X.hom]
    {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
    {p : P ⟶ G} {z : Z ⟶ G} {u : U ⟶ G}
    (hP : (parabolic χ).IsRepresentedBy p)
    (hZ : (centralizer χ).IsRepresentedBy z)
    (hZT : IsSplitTorus Z) (hH : IsUnipotent H)
    (i : H ⟶ G) (hi : SubgroupFunctor.range i ≤ parabolic χ)

include hP hZ hZT hH hi in
/-- Every unipotent source contained in `P(χ)` contracts to the identity if
the represented centralizer `Z(χ)` is a split torus. -/
theorem range_le_unipotent_of_splitCentralizer :
    SubgroupFunctor.range i ≤ unipotent χ := by
  let f : H ⟶ P := hP.factorHom i hi
  have hf := hP.factorHom_comp i hi
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hz := hH.comp_eq_one_of_isSplitTorus hZT (f ≫ limitGroupHom hP hZ) V y
  change y ≫ (f.hom.hom ≫ (limitGroupHom hP hZ).hom.hom) = 1 at hz
  rw [← Category.assoc] at hz
  have hlim : limit χ (hP.pointsEquiv V (y ≫ f.hom.hom)) = 1 := by
    rw [← limitGroupHom_comp hP hZ, hz, MonObj.one_comp]
  have hu := (limit_eq_one_iff χ (hP.pointsEquiv V (y ≫ f.hom.hom))).mp hlim
  change (y ≫ f.hom.hom) ≫ p.hom.hom ∈ (unipotent χ).carrier V at hu
  rw [Category.assoc, ← Grp.comp_hom_hom, hf] at hu
  exact hu

/-- The actual homomorphism to a supplied representative of `U(χ)`, obtained
from unipotence, parabolic containment, and a split-torus centralizer. -/
def unipotentFactorOfSplitCentralizer
    (hU : (unipotent χ).IsRepresentedBy u) : H ⟶ U :=
  hU.factorHom i (range_le_unipotent_of_splitCentralizer hP hZ hZT hH i hi)

/-- The contraction factor preserves the original morphism into the ambient group. -/
theorem unipotentFactorOfSplitCentralizer_comp
    (hU : (unipotent χ).IsRepresentedBy u) :
    unipotentFactorOfSplitCentralizer hP hZ hZT hH i hi hU ≫ u = i :=
  hU.factorHom_comp i _

end Dynamic

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)

include hT in
/-- Whole-test containment in `U(ν)` forces strict positivity of every
occurring ambient tangent weight, including exclusion of weight zero. -/
theorem actionWeightSupport_subset_positive_of_le_unipotent
    {F : SubgroupFunctor G}
    (hF : F ≤ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ j)) :
    actionWeightSupport (AutomorphicAction.conjugation j) F ⊆
      positiveSemigroup ν := by
  apply actionWeightSupport_subset_of_tangentSubmodule_le
    (AutomorphicAction.conjugation j) hT (positiveSemigroup ν) F
  rw [← tangentSubmodule_unipotent_eq_semigroupWeightSpan hT j ν]
  intro X hX
  exact hF _ hX

end RelativeRoot

namespace AutomorphicAction.IsEquivariant

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    {a : AutomorphicAction T.toGrp H} {i : H ⟶ G} [Mono i.hom.hom]
    (ha : a.IsEquivariant (AutomorphicAction.conjugation j) i)

include hT ha in
/-- An equivariant subgroup inside the dynamic identity-limit subgroup has
strictly positive intrinsic actual Lie weights. -/
theorem latticePairing_pos_of_range_le_unipotent
    (hi : SubgroupFunctor.range i ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ j))
    (χ : characterLattice T) (hχ : a.lieWeightSpace (𝟙 T.toGrp) χ ≠ ⊥) :
    0 < latticePairing T χ ν := by
  have hs : χ ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
      (SubgroupFunctor.range i) := by
    apply (RelativeRoot.mem_actionWeightSupport_range_iff
      (AutomorphicAction.conjugation j) a i (fun _ s x => ha s x) χ).mpr
    rwa [RelativeRoot.actionWeightSpace_eq_lieWeightSpace]
  exact RelativeRoot.actionWeightSupport_subset_positive_of_le_unipotent hT j ν hi hs

end AutomorphicAction.IsEquivariant

end Langlands.GroupScheme
