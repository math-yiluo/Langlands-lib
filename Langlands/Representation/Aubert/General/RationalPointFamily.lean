import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.Group.RelativeWeyl

/-!
# Actual simple-root subsets and rational-point families

The indices are the published simple relative roots themselves. The subgroup
families evaluate the published standard subgroup functors at the identity test
object. No finiteness or structural realization theorem is assumed as data.
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

/-- The actual image of the torus map on identity-test rational points. -/
def torusPoints (i : T.toGrp ⟶ G) : Subgroup (RationalPoint k G.X) :=
  (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))

theorem mem_torusPoints (i : T.toGrp ⟶ G) (g : RationalPoint k G.X) :
    g ∈ torusPoints i ↔
      ∃ t : RationalPoint k T.X, t ≫ i.hom.hom = g :=
  Iff.rfl

/-- Torus-image points centralize the torus on every test scheme. -/
theorem torusPoints_le_centralizerPoints (i : T.toGrp ⟶ G) :
    torusPoints i ≤ centralizerPoints i := by
  intro g hg
  rw [← torusCentralizer_carrier_base]
  rcases (mem_torusPoints i g).mp hg with ⟨t, rfl⟩
  rw [mem_torusCentralizer]
  intro V a s
  rw [← Category.assoc]
  exact ((show Commute (a ≫ t) s from mul_comm _ _).map
    ((yonedaGrp.map i).app (Opposite.op V)).hom)

/-- Scheme centralization implies centralization of the actual point image.
The converse is a separate rational-point comparison. -/
theorem centralizerPoints_le_pointCentralizer (i : T.toGrp ⟶ G) :
    centralizerPoints i ≤ Group.RelativeWeyl.centralizer (torusPoints i) := by
  intro g hg
  rw [← torusCentralizer_carrier_base] at hg
  intro x hx
  rcases (mem_torusPoints i x).mp hx with ⟨t, rfl⟩
  have hc := hg _ (𝟙 _) t
  rw [Category.id_comp] at hc
  exact hc.symm.eq

/-- The normalizer/full-centralizer quotient of the actual torus image.
It is not identified here with the scheme-normalizer point quotient. -/
abbrev Weyl (i : T.toGrp ⟶ G) :=
  Group.RelativeWeyl.Weyl (torusPoints i)

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A label is literally a simple relative root with its membership proof. -/
abbrev SimpleRoot :=
  {α : characterLattice T // α ∈ simpleRelativeRoots i ν}

/-- The character subset associated to a finite set of actual simple roots. -/
def rootSet (I : Finset (SimpleRoot i ν)) : Set (characterLattice T) :=
  Subtype.val '' (I : Set (SimpleRoot i ν))

theorem mem_rootSet (I : Finset (SimpleRoot i ν)) (α : characterLattice T) :
    α ∈ rootSet i ν I ↔
      ∃ a : SimpleRoot i ν, a ∈ I ∧ (a : characterLattice T) = α :=
  Iff.rfl

@[simp] theorem val_mem_rootSet (I : Finset (SimpleRoot i ν)) (a : SimpleRoot i ν) :
    (a : characterLattice T) ∈ rootSet i ν I ↔ a ∈ I := by
  constructor
  · rintro ⟨b, hb, hba⟩
    exact Subtype.val_injective hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem rootSet_subset (I : Finset (SimpleRoot i ν)) :
    rootSet i ν I ⊆ simpleRelativeRoots i ν := by
  rintro α ⟨a, _, rfl⟩
  exact a.property

theorem rootSet_finite (I : Finset (SimpleRoot i ν)) :
    (rootSet i ν I).Finite :=
  I.finite_toSet.image Subtype.val

theorem rootSet_subset_iff (I J : Finset (SimpleRoot i ν)) :
    rootSet i ν I ⊆ rootSet i ν J ↔ I ⊆ J := by
  constructor
  · intro h a ha
    exact (val_mem_rootSet i ν J a).mp (h ((val_mem_rootSet i ν I a).mpr ha))
  · intro h
    exact Set.image_mono h

theorem rootSet_injective : Function.Injective (rootSet i ν) := by
  intro I J h
  apply Finset.Subset.antisymm
  · exact (rootSet_subset_iff i ν I J).mp h.le
  · exact (rootSet_subset_iff i ν J I).mp h.symm.le

@[simp] theorem rootSet_empty : rootSet i ν ∅ = ∅ := by
  simp [rootSet]

@[simp] theorem rootSet_univ [Fintype (SimpleRoot i ν)] :
    rootSet i ν Finset.univ = simpleRelativeRoots i ν := by
  apply Set.Subset.antisymm (rootSet_subset i ν _)
  intro α hα
  exact ⟨⟨α, hα⟩, Finset.mem_univ _, rfl⟩

/-- The exact published standard parabolic, indexed by actual roots. -/
abbrev parabolic (I : Finset (SimpleRoot i ν)) : Subgroup (RationalPoint k G.X) :=
  standardParabolicPoints i ν (rootSet i ν I)

/-- The exact published standard Levi, indexed by actual roots. -/
abbrev levi (I : Finset (SimpleRoot i ν)) : Subgroup (RationalPoint k G.X) :=
  standardLeviPoints i ν (rootSet i ν I)

/-- The exact published standard unipotent subgroup, indexed by actual roots. -/
abbrev unipotent (I : Finset (SimpleRoot i ν)) : Subgroup (RationalPoint k G.X) :=
  standardUnipotentPoints i ν (rootSet i ν I)

theorem levi_le_parabolic (I : Finset (SimpleRoot i ν)) :
    levi i ν I ≤ parabolic i ν I :=
  standardLevi_le_standardParabolic i ν _ _

theorem unipotent_le_parabolic (I : Finset (SimpleRoot i ν)) :
    unipotent i ν I ≤ parabolic i ν I :=
  standardUnipotent_le_standardParabolic i ν _ _

theorem centralizerPoints_le_levi (I : Finset (SimpleRoot i ν)) :
    centralizerPoints i ≤ levi i ν I := by
  rw [← torusCentralizer_carrier_base]
  exact torusCentralizer_le_standardLevi i ν _ _

theorem torusPoints_le_levi (I : Finset (SimpleRoot i ν)) :
    torusPoints i ≤ levi i ν I :=
  (torusPoints_le_centralizerPoints i).trans (centralizerPoints_le_levi i ν I)

/-- The actual subgroup Weyl quotient for the indexed standard Levi. -/
abbrev LeviWeyl (I : Finset (SimpleRoot i ν)) :=
  Group.RelativeWeyl.WeylIn (torusPoints i) (levi i ν I)

/-- The existing scheme-point standard Weyl subgroup at the same root subset.
Comparison with `LeviWeyl` still requires the two point-subgroup comparisons. -/
abbrev schemeStandardWeyl (I : Finset (SimpleRoot i ν)) :
    Subgroup (relativeWeylGroup i) :=
  standardRelativeWeylGroup i ν (rootSet i ν I)

section Topology

variable [TopologicalSpace k]

/-- The canonical published evaluation topology on this exact ambient group.
This declaration installs no global topology instance. -/
@[instance_reducible]
def pointTopology : TopologicalSpace (RationalPoint k G.X) := by
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact rationalPointTopology k G.X

end Topology

end Langlands.Aubert.General.RationalPointFamily
