import Langlands.GroupScheme.SplitExistence.Assembly
import Langlands.GroupScheme.SplitExistence.ChevalleyLieExistence
import Langlands.GroupScheme.SplitExistence.ToChevalleyData
import Langlands.GroupScheme.SplitExistence.RootSubgroupRepresentation
import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

/-! # A Chevalley model of the actual based root datum of a split pinning -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme.SplitExistence
open Langlands.GroupScheme.SplitExistence.ChevalleyData

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (p : SplitPinning G)

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1

local instance : Module.Finite ℤ (characterLattice p.torus) :=
  (TorusSurjectionIsogenySection.characterLattice_free_finite p.isSplitTorus).2

local instance : Module.Free ℤ (characterLattice p.torus) :=
  (TorusSurjectionIsogenySection.characterLattice_free_finite p.isSplitTorus).1

local instance : p.rootDatum.IsReduced := p.isReduced

/-- Choose integral Chevalley Lie data on the actual lattices and base of the pinning. -/
def chevalleyLieData : ChevalleyLieData p.rootDatum p.base :=
  Classical.choice (nonempty_chevalleyLieData p.rootDatum p.base)

/-- Choose a represented Chevalley group over the field for these Lie data. -/
def chevalleyGroup : p.chevalleyLieData.toChevalleyData.ChevGroup k :=
  Classical.choice (p.chevalleyLieData.toChevalleyData.nonempty_chevGroup k)

variable {D : ChevalleyData p.rootDatum p.base} (M : D.ChevGroup k)

local instance : IsAffineHom M.H.X.hom := M.affine
local instance : IsAffine M.H.X.left := isAffine_of_isAffineHom M.H.X.hom
local instance : Smooth M.H.X.hom := M.smooth

private theorem chevalleyDatum_isReduced : (chevDatum k p.rootDatum).IsReduced where
  eq_or_eq_neg i j h := by
    let e := (chevDatumEquiv k p.rootDatum).weightEquiv
    have he : ![(chevDatum k p.rootDatum).root i, (chevDatum k p.rootDatum).root j] =
        e ∘ ![p.rootDatum.root i, p.rootDatum.root j] := by
      funext a
      fin_cases a <;> rfl
    rw [he] at h
    have hdep : ¬ LinearIndependent ℤ ![p.rootDatum.root i, p.rootDatum.root j] :=
      fun hi => h (hi.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective))
    change e (p.rootDatum.root i) = e (p.rootDatum.root j) ∨
      e (p.rootDatum.root i) = -e (p.rootDatum.root j)
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := p.rootDatum) i j hdep with hi | hi
    · exact Or.inl (congrArg e hi)
    · exact Or.inr ((congrArg e hi).trans (e.map_neg _))

/-- The Chevalley model has the transported base and the simple Lie trivializations
obtained by differentiating its given root maps in the standard epsilon coordinates. -/
abbrev chevalleyPinning : SplitPinning M.H where
  isConnectedReductive := M.isConnectedReductive
  torus := Tk (X := characterLattice p.torus) k
  inclusion := M.t
  isSplitTorus := isSplitTorus_Tk k p.rootDatum
  isMaximalTorus := M.isMaximalTorus
  rootIndex := p.rootIndex
  rootDatum := chevDatum k p.rootDatum
  isRootDatum := M.isRootDatumOf
  isReduced := p.chevalleyDatum_isReduced
  base := p.base.map (chevDatumEquiv k p.rootDatum)
  pinning.trivialization a :=
    (LocalSplitCell.gaLieEquiv k).trans
      (RelativeRoot.representedRootLieEquiv (isSplitTorus_Tk k p.rootDatum) M.t
        ((chevDatum k p.rootDatum).ne_zero a)
        (by rw [chevDatum_root]; exact M.hasNoHigherRoots_charOf a)
        (by rw [chevDatum_root]; exact M.represents_root a))

/-- The common root index is simple in the model exactly when it is simple in the
supplied base. -/
theorem chevalleyPinning_simple_iff (a : p.rootIndex) :
    a ∈ (p.chevalleyPinning M).base.support ↔ a ∈ p.base.support := by
  classical
  change a ∈ (p.base.map (chevDatumEquiv k p.rootDatum)).support ↔ _
  rw [RootPairing.Base.support_map_eq]
  change a ∈ p.base.support.image (Equiv.refl p.rootIndex) ↔ _
  simp

/-- The model pinning vector is the differential of the corresponding raw root map. -/
theorem chevalleyPinning_rootVector (a : (p.chevalleyPinning M).base.support) :
    (p.chevalleyPinning M).pinning.rootVector a =
      Lie.targetMapLinear (M.u a.val) (CommRingCat.of k) (VectorGroup.standardEpsilon k) := by
  change Lie.targetMapLinear (M.u a.val) k (LocalSplitCell.gaLieEquiv k 1) = _
  rw [LocalSplitCell.gaLieEquiv_one]

/-- The comparison of based data from the model's torus to the supplied torus. -/
def chevalleyPinningEquiv : RootPairing.Equiv (p.chevalleyPinning M).rootDatum p.rootDatum :=
  (chevDatumEquiv k p.rootDatum).symm

private theorem exists_chevalleyIso :
    ∃ f : (p.chevalleyPinning M).Iso p,
      (characterLattice.congr f.torusIso).toIntLinearEquiv =
        (p.chevalleyPinningEquiv M).weightEquiv ∧
      (cocharacterLattice.congr f.torusIso).toIntLinearEquiv =
        (p.chevalleyPinningEquiv M).coweightEquiv.symm ∧
      f.indexEquiv = Equiv.refl p.rootIndex := by
  have hs (a : p.rootIndex) : a ∈ (p.chevalleyPinning M).base.support ↔
      (p.chevalleyPinningEquiv M).indexEquiv a ∈ p.base.support :=
    p.chevalleyPinning_simple_iff M a
  exact (pinnedIsomorphism k M.H G (p.chevalleyPinning M) p
    (p.chevalleyPinningEquiv M) hs).exists

/-- The isomorphism of pinnings with the prescribed lattice identifications. The model
may be any fixed Chevalley group built from data on the supplied based root datum. -/
def chevalleyIso : (p.chevalleyPinning M).Iso p :=
  (p.exists_chevalleyIso M).choose

/-- The pinned comparison has the specified lattice maps and uses the very same root
indices on both sides. -/
theorem chevalleyIso_lattices :
    (characterLattice.congr (p.chevalleyIso M).torusIso).toIntLinearEquiv =
      (p.chevalleyPinningEquiv M).weightEquiv ∧
    (cocharacterLattice.congr (p.chevalleyIso M).torusIso).toIntLinearEquiv =
      (p.chevalleyPinningEquiv M).coweightEquiv.symm ∧
    (p.chevalleyIso M).indexEquiv = Equiv.refl p.rootIndex :=
  (p.exists_chevalleyIso M).choose_spec

@[simp]
theorem chevalleyIso_index (a : p.rootIndex) : (p.chevalleyIso M).indexEquiv a = a :=
  Equiv.congr_fun (p.chevalleyIso_lattices M).2.2 a

/-- The group comparison restricts to its specified isomorphism on the tori. -/
theorem chevalleyIso_square :
    M.t ≫ (p.chevalleyIso M).groupIso.hom =
      CommGroupScheme.groupHom (p.chevalleyIso M).torusIso.hom ≫ p.inclusion :=
  (p.chevalleyIso M).square

/-- The model character of an actual root is carried to the supplied root character. -/
theorem chevalleyIso_root (a : p.rootIndex) :
    characterLattice.congr (p.chevalleyIso M).torusIso (charOf k (p.rootDatum.root a)) =
      p.rootDatum.root a := by
  have h := (p.chevalleyIso M).root_eq a
  change characterLattice.congr (p.chevalleyIso M).torusIso ((chevDatum k p.rootDatum).root a) =
    p.rootDatum.root ((p.chevalleyIso M).indexEquiv a) at h
  rw [chevDatum_root, p.chevalleyIso_index M a] at h
  exact h

/-- The actual coroot into the ambient group is transported by the pinned isomorphism. -/
theorem chevalleyIso_corootHom (a : p.rootIndex) :
    (p.chevalleyPinning M).corootHom a ≫ (p.chevalleyIso M).groupIso.hom = p.corootHom a := by
  rw [corootHom, Category.assoc, chevalleyIso_square, ← Category.assoc]
  change CommGroupScheme.groupHom (cocharacterLattice.congr (p.chevalleyIso M).torusIso
    ((p.chevalleyPinning M).rootDatum.coroot a)) ≫ p.inclusion = _
  rw [(p.chevalleyIso M).coroot_eq, chevalleyIso_index, corootHom]

/-- Evaluating the actual coroot at any unit on a test scheme commutes with the
pinned comparison. -/
theorem chevalleyIso_coroot_apply (a : p.rootIndex) {Z : Over (Spec (CommRingCat.of k))}
    (z : Z ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    (z ≫ ((p.chevalleyPinning M).corootHom a).hom.hom) ≫
      (p.chevalleyIso M).groupIso.hom.hom.hom = z ≫ (p.corootHom a).hom.hom := by
  simpa only [Category.assoc, Grp.comp_hom_hom] using
    congrArg (fun f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G => z ≫ f.hom.hom)
      (p.chevalleyIso_corootHom M a)

end Langlands.GroupScheme.SplitPinning
