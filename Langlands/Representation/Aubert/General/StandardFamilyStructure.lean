import Langlands.Representation.Aubert.General.StandardFamily
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof

/-!
# Structural properties of the actual standard family of rational points

Closedness, normalization and the top endpoint for the published standard
family `RationalPointFamily.parabolic/levi/unipotent i ν`, and the product
decompositions that follow from the published structural statements.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Unconditional

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

theorem mem_levi_iff (I : Finset (SimpleRoot i ν)) (g : RationalPoint k G.X) :
    g ∈ levi i ν I ↔ ∀ zeta, IsStandardCocharacter i ν (rootSet i ν I) zeta →
      g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
  mem_standardLevi i ν

theorem mem_unipotent_iff (I : Finset (SimpleRoot i ν)) (g : RationalPoint k G.X) :
    g ∈ unipotent i ν I ↔ ∀ zeta, IsStandardCocharacter i ν (rootSet i ν I) zeta →
      g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
  mem_standardUnipotent i ν

theorem coe_levi (I : Finset (SimpleRoot i ν)) :
    (levi i ν I : Set (RationalPoint k G.X)) =
      ⋂ (zeta : cocharacterLattice T) (_ : IsStandardCocharacter i ν (rootSet i ν I) zeta),
        ((Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :
          Set (RationalPoint k G.X)) := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_iInter]
  exact mem_levi_iff i ν I g

theorem coe_unipotent (I : Finset (SimpleRoot i ν)) :
    (unipotent i ν I : Set (RationalPoint k G.X)) =
      ⋂ (zeta : cocharacterLattice T) (_ : IsStandardCocharacter i ν (rootSet i ν I) zeta),
        ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :
          Set (RationalPoint k G.X)) := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_iInter]
  exact mem_unipotent_iff i ν I g

/-- Every standard Levi normalizes the standard unipotent subgroup of the same index. -/
theorem levi_le_normalizer (I : Finset (SimpleRoot i ν)) :
    levi i ν I ≤ Subgroup.normalizer (unipotent i ν I : Set (RationalPoint k G.X)) := by
  intro m hm
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  simp only [SetLike.mem_coe]
  rw [mem_unipotent_iff, mem_unipotent_iff]
  refine forall_congr' fun zeta => forall_congr' fun hzeta => ?_
  have hp := Dynamic.centralizer_le_parabolic (CommGroupScheme.groupHom zeta ≫ i) _
    ((mem_levi_iff i ν I m).1 hm zeta hzeta)
  exact Subgroup.mem_set_normalizer_iff.mp
    (dynamic_parabolic_le_normalizer (CommGroupScheme.groupHom zeta ≫ i) _ hp) u

/-- An index containing every simple root has trivial standard unipotent subgroup. -/
theorem unipotent_eq_bot_of_forall_mem {I : Finset (SimpleRoot i ν)} (hI : ∀ a, a ∈ I) :
    unipotent i ν I = ⊥ := by
  let : Fintype (SimpleRoot i ν) := ⟨I, hI⟩
  exact unipotent_univ_eq_bot i ν

/-- The wall subgroup of the standard Levi `M_I` at a simple root `α`: the
points of `N_{I \ {α}}` lying in `M_I`. For `α ∈ I` it models the unipotent
radical of the maximal standard parabolic `P_{I \ {α}} ∩ M_I` of `M_I`; that
identification is not proved here. -/
def wallUnipotent [DecidableEq (SimpleRoot i ν)] (I : Finset (SimpleRoot i ν))
    (α : SimpleRoot i ν) : Subgroup (RationalPoint k G.X) :=
  unipotent i ν (I.erase α) ⊓ levi i ν I

theorem wallUnipotent_le_levi [DecidableEq (SimpleRoot i ν)] (I : Finset (SimpleRoot i ν))
    (α : SimpleRoot i ν) : wallUnipotent i ν I α ≤ levi i ν I :=
  inf_le_right

section Topology

variable [TopologicalSpace k] [T2Space k] [IsAffine G.X.left]

/-- Every standard Levi subgroup is closed in the pinned point topology. -/
theorem isClosed_levi (I : Finset (SimpleRoot i ν)) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    IsClosed (levi i ν I : Set (RationalPoint k G.X)) := by
  let : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  rw [coe_levi]
  exact isClosed_iInter fun zeta => isClosed_iInter fun _ =>
    isClosed_rationalPoint_subgroup k _ (Dynamic.Affine.centralizerHom _)
      (Dynamic.Affine.isRepresentedBy_centralizerHom _)
      (Dynamic.Affine.isClosedSubgroup_centralizerHom _)

/-- Every standard unipotent subgroup is closed in the pinned point topology. -/
theorem isClosed_unipotent (I : Finset (SimpleRoot i ν)) :
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    IsClosed (unipotent i ν I : Set (RationalPoint k G.X)) := by
  let : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
  rw [coe_unipotent]
  exact isClosed_iInter fun zeta => isClosed_iInter fun _ =>
    isClosed_rationalPoint_subgroup k _ (Dynamic.Affine.unipotentHom _)
      (Dynamic.Affine.isRepresentedBy_unipotentHom _)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom _)

end Topology

end Unconditional

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Over a nonarchimedean local field every standard Levi subgroup is closed in
the pinned point topology. -/
theorem isClosed_levi_of_isNonarchimedeanLocalField (I : Finset (SimpleRoot i ν)) :
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    IsClosed (levi i ν I : Set (RationalPoint F G.X)) :=
  haveI := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
  isClosed_levi i ν I

/-- Over a nonarchimedean local field every standard unipotent subgroup is
closed in the pinned point topology. -/
theorem isClosed_unipotent_of_isNonarchimedeanLocalField (I : Finset (SimpleRoot i ν)) :
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    IsClosed (unipotent i ν I : Set (RationalPoint F G.X)) :=
  haveI := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F
  isClosed_unipotent i ν I

end LocalField

/-- For a maximal split torus of a connected reductive group there are only
finitely many simple roots. -/
theorem finite_simpleRoot (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    Finite (SimpleRoot i ν) := by
  have := hG.smooth
  let := simpleRelativeRootFintypeOfIsSplitTorus i hi.isSplitSubtorus.1 ν
  infer_instance

/-- For a maximal split torus of a connected reductive group some index, the set
of all simple roots, has trivial standard unipotent subgroup. -/
theorem exists_unipotent_eq_bot (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    ∃ I : Finset (SimpleRoot i ν), (∀ a, a ∈ I) ∧ unipotent i ν I = ⊥ := by
  have := finite_simpleRoot hG hi ν
  let := Fintype.ofFinite (SimpleRoot i ν)
  exact ⟨Finset.univ, Finset.mem_univ, unipotent_univ_eq_bot i ν⟩

/-- A connected reductive group has an actual maximal split torus with a
generic cocharacter. -/
theorem exists_maximalSplitTorus_genericCocharacter (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T), IsMaximalSplitTorus i ∧ IsGenericCocharacter i ν := by
  have := hG.isAffineHom
  have := hG.smooth
  obtain ⟨T, i, -, hi, -⟩ := cocharacterMaximalSplitTorus k G (Dynamic.trivialCocharacter G)
  obtain ⟨ν, hν⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter i
  exact ⟨T, i, ν, hi, hν⟩

section Conditional

variable (hG : IsConnectedReductive G) [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
  (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)

include hG hi hν

/-- From the published order statement: parabolics increase with the index. -/
theorem parabolic_mono (hord : StandardParabolicOrderStatement.{u})
    {J I : Finset (SimpleRoot i ν)} (hJI : J ⊆ I) :
    parabolic i ν J ≤ parabolic i ν I := by
  have h := ((hord k G hG T i hi ν hν).1 (rootSet i ν J) (rootSet i ν I)
    (rootSet_subset i ν J) (rootSet_subset i ν I)).1.1
    ((rootSet_subset_iff i ν J I).2 hJI)
  exact h _

/-- From the published order statement: standard Levi subgroups increase with
the index. -/
theorem levi_mono (hord : StandardParabolicOrderStatement.{u})
    {J I : Finset (SimpleRoot i ν)} (hJI : J ⊆ I) :
    levi i ν J ≤ levi i ν I := by
  have h := (((hord k G hG T i hi ν hν).1 (rootSet i ν J) (rootSet i ν I)
    (rootSet_subset i ν J) (rootSet_subset i ν I)).2
    ((rootSet_subset_iff i ν J I).2 hJI)).1
  exact h _

/-- From the published order statement: standard unipotent subgroups decrease
with the index. -/
theorem unipotent_anti (hord : StandardParabolicOrderStatement.{u})
    {J I : Finset (SimpleRoot i ν)} (hJI : J ⊆ I) :
    unipotent i ν I ≤ unipotent i ν J := by
  have h := (((hord k G hG T i hi ν hν).1 (rootSet i ν J) (rootSet i ν I)
    (rootSet_subset i ν J) (rootSet_subset i ν I)).2
    ((rootSet_subset_iff i ν J I).2 hJI)).2
  exact h _

/-- From the published standard-cocharacter statement: every point of the
standard parabolic is a Levi point times a unipotent point. -/
theorem exists_mul_of_mem_parabolic (hstd : StandardCocharacterStatement.{u})
    (I : Finset (SimpleRoot i ν)) {p : RationalPoint k G.X} (hp : p ∈ parabolic i ν I) :
    ∃ m ∈ levi i ν I, ∃ n ∈ unipotent i ν I, p = m * n := by
  have hd := isSemidirectDecomposition hstd hG i hi ν hν I
  obtain ⟨⟨⟨m, hm⟩, ⟨n, hn⟩⟩, hmn, -⟩ :=
    hd.isComplement'.existsUnique (⟨p, hp⟩ : parabolic i ν I)
  refine ⟨m, hm, n, hn, ?_⟩
  have := congrArg Subtype.val hmn
  simpa using this.symm

/-- From the two published structural statements: for `J ⊆ I`, every point of
`N_J` is a point of `N_J ∩ M_I` times a point of `N_I`. -/
theorem exists_mul_of_mem_unipotent (hstd : StandardCocharacterStatement.{u})
    (hord : StandardParabolicOrderStatement.{u})
    {J I : Finset (SimpleRoot i ν)} (hJI : J ⊆ I) {n : RationalPoint k G.X}
    (hn : n ∈ unipotent i ν J) :
    ∃ u ∈ unipotent i ν J ⊓ levi i ν I, ∃ n' ∈ unipotent i ν I, n = u * n' := by
  have hp : n ∈ parabolic i ν I :=
    parabolic_mono hG hi hν hord hJI (unipotent_le_parabolic i ν J hn)
  obtain ⟨m, hm, n', hn', rfl⟩ := exists_mul_of_mem_parabolic hG hi hν hstd I hp
  refine ⟨m, ⟨?_, hm⟩, n', hn', rfl⟩
  have hn'J : n' ∈ unipotent i ν J := unipotent_anti hG hi hν hord hJI hn'
  have := mul_mem hn (inv_mem hn'J)
  simpa using this

/-- Descent through a wall: every point of `N_{I \ {α}}` is a point of the wall
subgroup of `M_I` at `α` times a point of `N_I`. -/
theorem exists_mul_of_mem_unipotent_erase [DecidableEq (SimpleRoot i ν)]
    (hstd : StandardCocharacterStatement.{u}) (hord : StandardParabolicOrderStatement.{u})
    (I : Finset (SimpleRoot i ν)) (α : SimpleRoot i ν) {n : RationalPoint k G.X}
    (hn : n ∈ unipotent i ν (I.erase α)) :
    ∃ u ∈ wallUnipotent i ν I α, ∃ n' ∈ unipotent i ν I, n = u * n' :=
  exists_mul_of_mem_unipotent hG hi hν hstd hord (I.erase_subset α) hn

end Conditional

end Langlands.Aubert.General.RationalPointFamily
