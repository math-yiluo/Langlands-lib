import Langlands.GroupScheme.Reductive.IsogenyRootImage
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Actual root factors of split reductive isogenies -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.LinearAlgebra.RationalSpan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

namespace IsRootDatumOf

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]
    {J J' : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')

include hP

/-- Reducedness excludes every higher positive multiple of an actual root. -/
theorem noHigherRoots (hT : IsSplitTorus T.toGrp) (r : J) :
    RelativeRoot.HasNoHigherRoots i (P.root r) := by
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice T) :=
    IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice T) :=
    hT.character_toRat_injective.isAddTorsionFree toRat
  intro n hn
  let : n.AtLeastTwo := ⟨hn⟩
  rw [relativeRoots_eq_roots, ← hP.2.1]
  exact P.nsmul_notMem_range_root

include hP'

/-- Every actual source root has a target root whose pullback is a
characteristic-power multiple of that source root. -/
theorem exists_isogenyRootFactor
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (hi : IsMaximalTorus i)
    (φ : G ⟶ G') [IsFinite φ.hom.hom.left] (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') (r : J) :
    ∃ (s : J') (n : ℕ), t ≫ P'.root s = (ringExpChar k ^ n) • P.root r := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom T.toGrp.X.hom := hi.2.1.isAffineHom
  have hr : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  have hhigh := hP.noHigherRoots hT r
  obtain ⟨U, j, hj, hjclosed, _, _⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hT i (P.root r) hr.1
  let : IsClosedImmersion j.hom.hom.left := hjclosed
  let : IsAffineHom U.X.hom := hjclosed.isAffineHom
  let : CommGroup (lieKernel U k) := lieKernelCommGroup U
  let : Module k (Additive (lieKernel U k)) := lieKernelModule U
  obtain ⟨n, e, he⟩ :=
    RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots hT i hr.1 hhigh hj
  have hn : n = 1 := by
    let E := RelativeRoot.vectorLieCoordinates e he.1 (CommAlgCat.of k k)
    let L := RelativeRoot.representedRootLieEquiv hT i hr.1 hhigh hj
    obtain ⟨l⟩ := splitRootLieLine k G hG T hT i hi (P.root r) hr
    calc
      n = Module.finrank k (Fin n → k) := by simp
      _ = Module.finrank k (Additive (lieKernel U k)) := E.finrank_eq.symm
      _ = Module.finrank k (weightSpace i (P.root r)) := L.finrank_eq
      _ = 1 := by rw [← l.finrank_eq, Module.finrank_self]
  subst n
  let x : U ⟶ G' := j ≫ φ
  let : IsFinite x.hom.hom.left := by
    change IsFinite (j.hom.hom.left ≫ φ.hom.hom.left)
    infer_instance
  have hx : ∀ (Z : Over (Spec (CommRingCat.of k))) (s : Z ⟶ T.X) (v : Z ⟶ U.X),
      (RelativeRoot.subgroupAction i (P.root r) j hj).act s v ≫ x.hom.hom =
        (AutomorphicAction.conjugation (CommGroupScheme.groupHom t ≫ i')).act
          s (v ≫ x.hom.hom) := by
    intro Z s v
    have hs := congrArg (fun f : T.toGrp ⟶ G' => s ≫ f.hom.hom) ht
    simp only [Grp.comp_hom_hom] at hs
    simp only [x, Grp.comp_hom_hom]
    rw [← Category.assoc, RelativeRoot.subgroupAction_act_comp,
      MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    simp only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom, Category.assoc, hs]
  obtain ⟨β, hβ, m, hm⟩ := HomImage.exists_root_expChar_factor hT hT' t i'
    (RelativeRoot.subgroupAction i (P.root r) j hj) e he x hx hr.1
  obtain ⟨s, hs⟩ := hP'.2.1 ▸ hβ
  exact ⟨s, m, hs ▸ hm⟩

/-- A chosen target-root index and characteristic-power exponent for each
actual source root, together with the exact integral pullback equation. -/
def isogenyRootFactor
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (hi : IsMaximalTorus i)
    (φ : G ⟶ G') [IsFinite φ.hom.hom.left] (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') (r : J) :
    Σ s : J', {n : ℕ // t ≫ P'.root s = (ringExpChar k ^ n) • P.root r} :=
  Classical.choice (by
    obtain ⟨s, n, h⟩ := hP.exists_isogenyRootFactor hP' hG hT hT' hi φ t ht r
    exact ⟨⟨s, n, h⟩⟩)

end IsRootDatumOf
end Langlands.GroupScheme
