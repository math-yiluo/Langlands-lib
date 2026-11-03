import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.Characters

/-! # Nonidentity actual root points from realization and vector structure -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace RelativeRoot

variable {k : Type u} [Field k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}

/-- A positive-dimensional vector group has a nonidentity point over its base
field, as seen in any system of vector coordinates. -/
theorem IsVectorGroupOfDimension.exists_rationalPoint_ne_one {n : ℕ}
    (hU : IsVectorGroupOfDimension U n) (hn : 0 < n) :
    ∃ x : rationalPoints U, x ≠ 1 := by
  obtain ⟨e, _⟩ := hU
  let v : Multiplicative (Fin n → Γ(Spec (CommRingCat.of k), ⊤)) :=
    Multiplicative.ofAdd (fun _ => 1)
  refine ⟨(e (Over.mk (𝟙 _))).symm v, ?_⟩
  intro hx
  have hv : v = 1 := by
    simpa only [MulEquiv.apply_symm_apply, map_one] using
      congrArg (e (Over.mk (𝟙 _))) hx
  have h10 : (1 : Γ(Spec (CommRingCat.of k), ⊤)) = 0 :=
    congrArg (fun w => w.toAdd ⟨0, hn⟩) hv
  have h10k := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom h10
  apply (one_ne_zero : (1 : k) ≠ 0)
  simpa only [map_one, map_zero] using h10k

variable [IsAffineHom G.X.hom]

/-- A represented vector group with a nonzero exact Lie image has positive
dimension. Dimension zero would make every point on every test the identity. -/
theorem IsVectorGroupOfDimension.pos_of_hasLieImage {F : SubgroupFunctor G}
    {j : U ⟶ G} (hj : F.IsRepresentedBy j)
    {W : Submodule k (Additive (lieKernel G k))}
    (hW : W ≠ ⊥) (hLie : HasLieImage F W)
    {n : ℕ} (hU : IsVectorGroupOfDimension U n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  obtain ⟨e, _⟩ := hU
  apply hW
  apply le_antisymm _ bot_le
  intro X hX
  change X = 0
  have hpoint := (hLie X).mpr hX
  rw [← hj.2] at hpoint
  obtain ⟨y, hy⟩ := hpoint
  change y ≫ j.hom.hom = X.toMul.val at hy
  have hy1 : y = 1 := by
    apply (e _).injective
    apply Multiplicative.toAdd.injective
    funext q
    exact Fin.elim0 q
  apply Additive.toMul.injective
  apply Subtype.ext
  change X.toMul.val = 1
  simpa only [hy1, MonObj.one_comp] using hy.symm

/-- A nonzero exact Lie image in a represented vector group yields an actual
nonidentity ambient rational point in the represented subgroup. -/
theorem exists_rationalPoint_ne_one_of_vector_lieImage {F : SubgroupFunctor G}
    {j : U ⟶ G} (hj : F.IsRepresentedBy j)
    {W : Submodule k (Additive (lieKernel G k))}
    (hW : W ≠ ⊥) (hLie : HasLieImage F W) (hU : IsVectorGroup U) :
    ∃ x : rationalPoints G, x ∈ F.carrier (Over.mk (𝟙 _)) ∧ x ≠ 1 := by
  obtain ⟨n, hn⟩ := hU
  obtain ⟨x, hx⟩ := hn.exists_rationalPoint_ne_one
    (hn.pos_of_hasLieImage hj hW hLie)
  have : Mono j.hom.hom := hj.1
  refine ⟨x ≫ j.hom.hom, ?_, ?_⟩
  · rw [← hj.2]
    exact ⟨x, rfl⟩
  · intro h
    apply hx
    apply (cancel_mono j.hom.hom).mp
    simpa only [MonObj.one_comp] using h

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G)

/-- The first weight space is contained in the positive integral weight span. -/
theorem weightSpace_le_positiveWeightSpan (a : characterLattice S) :
    weightSpace i a ≤ positiveWeightSpan i a := by
  simpa only [positiveWeightSpan, one_smul] using
    (le_iSup (fun n : {n : ℕ // 0 < n} => weightSpace i (n.val • a)) ⟨1, by decide⟩)

/-- An actual root has nonzero positive integral weight span. -/
theorem positiveWeightSpan_ne_bot {a : characterLattice S}
    (ha : a ∈ relativeRoots i) : positiveWeightSpan i a ≠ ⊥ := by
  intro h
  apply ha.2
  apply le_antisymm _ bot_le
  exact (weightSpace_le_positiveWeightSpan i a).trans (le_of_eq h)

/-- Conditional point existence for a nonmultipliable actual root. Geometric
realization and vector structure remain explicit inputs. -/
theorem exists_rootPoint_of_not_two_mem
    (hReal : RootSubgroupRealizationStatement.{u})
    (hVec : RootSubgroupVectorStatement.{u}) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) (h2 : 2 • a ∉ relativeRoots i) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧ x ≠ 1 := by
  obtain ⟨U, j, hj, _, _, _, _, _, _, hLie⟩ := hReal k G hG S i hi a ha
  have hU := (hVec k G hG S i hi a ha).1 h2 U j hj
  exact exists_rationalPoint_ne_one_of_vector_lieImage hj
    (positiveWeightSpan_ne_bot i ha) hLie hU

variable [Mono i.hom.hom.left]

/-- Conditional point existence for every actual root, including multipliable
roots. For a multipliable root, use its nonmultipliable doubled root. -/
theorem exists_rootPoint_of_statements
    (hReal : RootSubgroupRealizationStatement.{u})
    (hVec : RootSubgroupVectorStatement.{u}) (hR : HasRelativeRootSystem i)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    ∃ x : rationalPoints G,
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧ x ≠ 1 := by
  by_cases h2 : 2 • a ∈ relativeRoots i
  · have h4 : 2 • (2 • a) ∉ relativeRoots i := by
      simpa only [smul_smul, show (2 : ℕ) * 2 = 4 from rfl] using
        hR.nsmul_not_mem_of_three_le ha (n := 4) (by decide)
    obtain ⟨x, hx, hx1⟩ :=
      exists_rootPoint_of_not_two_mem i hReal hVec hG hi h2 h4
    exact ⟨x, (hVec k G hG S i hi a ha).2 h2 |>.1 _ hx, hx1⟩
  · exact exists_rootPoint_of_not_two_mem i hReal hVec hG hi ha h2

end RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

/-- Choose actual nonidentity simple-root points from the structural targets.
The prerequisites remain explicit and the full Tits theorem is not asserted. -/
def RelativeSimpleRootPointData.of_rootSubgroup_statements
    (hReal : RelativeRoot.RootSubgroupRealizationStatement.{u})
    (hVec : RelativeRoot.RootSubgroupVectorStatement.{u})
    (hR : HasRelativeRootSystem i) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    RelativeSimpleRootPointData i ν where
  point a := Classical.choose
    (RelativeRoot.exists_rootPoint_of_statements i hReal hVec hR hG hi a.property.1.1)
  mem a := (Classical.choose_spec
    (RelativeRoot.exists_rootPoint_of_statements i hReal hVec hR hG hi a.property.1.1)).1
  ne_one a := (Classical.choose_spec
    (RelativeRoot.exists_rootPoint_of_statements i hReal hVec hR hG hi a.property.1.1)).2

end Langlands.GroupScheme
