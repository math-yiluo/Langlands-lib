import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.LinearAlgebra.CartanD5ExcludesA5
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv

/-! # Maximal-torus rank and the exclusion of A5 in type D5 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2100000

section TorusDimensions

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffineHom H.X.hom]

/-- The absolute simple roots are at most the dimension of a split maximal torus. -/
theorem SplitPinning.card_base_le_torusDimension (p : SplitPinning H) :
    haveI := p.isSplitTorus.isAffineHom
    Nat.card p.base.support ≤ Lie.dimension p.torus.toGrp := by
  classical
  let : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
  let : Module.Finite ℤ (cocharacterLattice p.torus) := p.isSplitTorus.finite_cocharacterLattice
  have hl := p.base.linearIndepOn_coroot
  change Nat.card p.base.support ≤ Module.finrank k (Additive (lieKernel p.torus.toGrp k))
  rw [p.isSplitTorus.finrank_lieKernel_eq_cocharacter, Nat.card_eq_fintype_card]
  exact hl.fintype_card_le_finrank

omit [LocallyOfFiniteType G.X.hom] in
/-- In a split simply connected group the simple coroots give the dimension
of the actual split maximal torus. -/
theorem SplitPinning.torusDimension_eq_card_base_of_isSimplyConnected (q : SplitPinning G)
    (hsc : IsSimplyConnected G) :
    haveI := q.isSplitTorus.isAffineHom
    Lie.dimension q.torus.toGrp = Nat.card q.base.support := by
  classical
  let : IsAffineHom q.torus.toGrp.X.hom := q.isSplitTorus.isAffineHom
  let : Finite q.rootIndex := q.finiteRootIndex
  let : q.rootDatum.IsReduced := q.isReduced
  have hspan := splitSimplyConnectedCorootSpan k G hsc q.torus q.isSplitTorus q.inclusion
    q.isMaximalTorus q.rootIndex q.rootDatum q.isRootDatum q.isReduced
  change Module.finrank k (Additive (lieKernel q.torus.toGrp k)) = _
  rw [q.isSplitTorus.finrank_lieKernel_eq_cocharacter, Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (Langlands.RootDatumSimpleCorootEquiv.simpleCorootBasis q.base hspan)

/-- An actual closed subgroup has no larger maximal torus than the ambient
reductive group. Equality makes its maximal torus maximal in the ambient group. -/
theorem SplitPinning.torusDimension_le_of_closedSubgroup [IsAlgClosed k]
    (p : SplitPinning H) (q : SplitPinning G) (j : H ⟶ G) (hj : IsClosedSubgroup j) :
    haveI := p.isSplitTorus.isAffineHom
    haveI := q.isSplitTorus.isAffineHom
    Lie.dimension p.torus.toGrp ≤ Lie.dimension q.torus.toGrp ∧
      (Lie.dimension q.torus.toGrp ≤ Lie.dimension p.torus.toGrp →
        IsMaximalTorus (p.inclusion ≫ j)) := by
  let : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
  let : IsAffineHom q.torus.toGrp.X.hom := q.isSplitTorus.isAffineHom
  let : Smooth G.X.hom := q.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := q.isConnectedReductive.connectedSpace
  have hjT := p.isMaximalTorus.2.1.comp hj
  obtain ⟨M, m, hm, f, hf⟩ := exists_maximalTorus_extension_of_finiteType G (p.inclusion ≫ j)
    p.isSplitTorus.isTorus hjT
  obtain ⟨_, e, _⟩ := maximalTorusConjugacy k G M q.torus m q.inclusion hm q.isMaximalTorus
  let : IsAffineHom M.toGrp.X.hom := hm.2.1.isAffineHom
  let : Smooth M.toGrp.X.hom := hm.1.smooth
  let : ConnectedSpace M.toGrp.X.left := hm.1.connectedSpace
  let : Smooth p.torus.toGrp.X.hom := p.isSplitTorus.smooth
  have hdim : Lie.dimension M.toGrp = Lie.dimension q.torus.toGrp :=
    (Lie.targetEquiv (CommGroupScheme.groupIso e) k).finrank_eq
  have hfclosed : IsClosedSubgroup f := IsClosedSubgroup.of_comp hm.2.1 (hf.symm ▸ hjT)
  let : IsClosedImmersion f.hom.hom.left := hfclosed
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  have hfi := Lie.targetMapLinear_injective f k
  have hle : Lie.dimension p.torus.toGrp ≤ Lie.dimension M.toGrp :=
    LinearMap.finrank_le_finrank_of_injective hfi
  refine ⟨hle.trans hdim.le, fun hge => ?_⟩
  have heq : Lie.dimension p.torus.toGrp = Lie.dimension M.toGrp :=
    le_antisymm hle (hdim.le.trans hge)
  have hfs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hfi
  let : IsIso f := Lie.isIso_of_surjective_targetMapLinear f hfclosed hfs
  exact hf ▸ hm.iso_comp (asIso f)

end TorusDimensions

section D5

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom D.X.hom]
  [LocallyOfFiniteType D.X.hom] [IsAffineHom H.X.hom]

/-- A closed reductive subgroup with A5 Cartan matrix cannot embed into split
simply connected D5. Its maximal torus would have full rank, so the root
and coroot pairings would be inherited on that same torus. -/
theorem SplitPinning.not_isClosedSubgroup_of_typeA5_typeD5
    (p : SplitPinning H) (q : SplitPinning D) (e : p.base.support ≃ Fin 5)
    (f : q.base.support ≃ Fin 5) (hsc : IsSimplyConnected D)
    (hA : ∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.A 5 (e a) (e b))
    (hD : ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (f a) (f b))
    (j : H ⟶ D) : ¬ IsClosedSubgroup j := by
  intro hj
  let : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom
  let : IsAffineHom q.torus.toGrp.X.hom := q.isSplitTorus.isAffineHom
  have hq : Lie.dimension q.torus.toGrp = 5 := by
    rw [q.torusDimension_eq_card_base_of_isSimplyConnected hsc, Nat.card_congr f, Nat.card_fin]
  have hp : 5 ≤ Lie.dimension p.torus.toGrp := by
    rw [← Nat.card_fin 5, ← Nat.card_congr e]
    exact p.card_base_le_torusDimension
  let i := p.inclusion ≫ j
  have hi : IsMaximalTorus i := (p.torusDimension_le_of_closedSubgroup q j hj).2 (hq ▸ hp)
  obtain ⟨J, _, P, hP, _⟩ := rootDatumExistence k D q.isConnectedReductive p.torus p.isSplitTorus i hi
  obtain ⟨w⟩ := nonempty_rootDatumEquiv_of_iso q.isConnectedReductive q.isConnectedReductive
    p.isSplitTorus q.isSplitTorus hi q.isMaximalTorus (Iso.refl D) hP q.isRootDatum
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Finite (weylImage i) := splitTorusWeylImageFinite k D p.torus p.isSplitTorus i hi.2.1
  let a := hP.sameTorusSubgroupEmbedding i p.inclusion j rfl p.isRootDatum (roots_subset_comp j _)
  let r : Fin 5 → q.rootIndex := fun x => w.indexEquiv (a.index (e.symm x).val)
  apply Langlands.LinearAlgebra.cartanD5ExcludesA5 q.rootIndex _ _ q.rootDatum q.base f
    (fun x y => by simpa using hD (f.symm x) (f.symm y)) r
  intro x y
  have heq : q.rootDatum.pairing (r x) (r y) = P.pairing (a.index (e.symm x).val) (a.index (e.symm y).val) :=
    w.toHom.pairing
  rw [heq]
  change P.toLinearMap (P.root (a.index (e.symm x).val)) (P.coroot (a.index (e.symm y).val)) = _
  rw [a.root_eq, a.coroot_eq, hP.1, ← p.isRootDatum.1]
  simpa using hA (e.symm x) (e.symm y)

end D5

/-- A reductive group with a split A5 pinning over an algebraically closed
field admits no closed embedding into split simply connected D5. -/
def TypeD5ExcludesClosedTypeA5Statement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (H D : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom H.X.hom] [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
      (p : SplitPinning H) (q : SplitPinning D) (e : p.base.support ≃ Fin 5)
      (f : q.base.support ≃ Fin 5), IsSimplyConnected D →
      (∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.A 5 (e a) (e b)) →
      (∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.D 5 (f a) (f b)) →
      ∀ j : H ⟶ D, ¬ IsClosedSubgroup j

theorem typeD5ExcludesClosedTypeA5 : TypeD5ExcludesClosedTypeA5Statement.{u} := by
  intro k _ _ H D _ _ _ p q e f hsc hA hD j
  exact p.not_isClosedSubgroup_of_typeA5_typeD5 q e f hsc hA hD j

end Langlands.GroupScheme
