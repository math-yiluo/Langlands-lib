import Langlands.GroupScheme.Reductive.StarActionIndependenceProof

/-! # Full star naturality for an embedded orthogonal root component -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An integral root embedding whose image is orthogonal to every outside root.
The root-index map is only injective; no full-root or lattice surjectivity is assumed. -/
structure RootComponentEmbedding
    {J K X Y V W : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup V] [AddCommGroup W]
    (P : RootDatum J X Y) (Q : RootDatum K V W) where
  index : J ↪ K
  weightMap : X →ₗ[ℤ] V
  root_eq : ∀ r, weightMap (P.root r) = Q.root (index r)
  pairing_eq : ∀ r s, Q.pairing (index r) (index s) = P.pairing r s
  orthogonal : ∀ r s, s ∉ Set.range index → Q.pairing (index r) s = 0

namespace RootComponentEmbedding

variable {J K X Y V W : Type*} [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup V] [AddCommGroup W]
  {P : RootDatum J X Y} {Q : RootDatum K V W}
  (f : RootComponentEmbedding P Q)

/-- Corresponding abstract root reflections have the exact embedded root-index action. -/
theorem reflection_index (r s : J) :
    f.index (P.reflectionPerm r s) = Q.reflectionPerm (f.index r) (f.index s) := by
  apply Q.root.injective
  rw [← f.root_eq, P.root_reflectionPerm, P.reflection_apply_root,
    map_sub, map_smul, f.root_eq, f.root_eq,
    Q.root_reflectionPerm, Q.reflection_apply_root, f.pairing_eq]

/-- Every ambient Weyl word restricts to one Weyl word on the embedded
orthogonal root component, simultaneously for all its roots. -/
theorem exists_weyl_lift {w : Q.Aut} (hw : w ∈ Q.weylGroup) :
    ∃ v : P.Aut, v ∈ P.weylGroup ∧
      ∀ r, f.index (v.indexEquiv r) = w.indexEquiv (f.index r) := by
  induction hw using RootPairing.weylGroup.induction with
  | mem s =>
    by_cases hs : s ∈ Set.range f.index
    · obtain ⟨r, rfl⟩ := hs
      exact ⟨RootPairing.Equiv.reflection P r, P.reflection_mem_weylGroup r,
        fun s => f.reflection_index r s⟩
    · refine ⟨1, one_mem _, fun r => ?_⟩
      change f.index r = Q.reflectionPerm s (f.index r)
      exact (Q.reflectionPerm_eq_of_pairing_eq_zero (f.orthogonal r s hs)).symm
  | one => exact ⟨1, one_mem _, fun _ => rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨x', hx', hix⟩ := ihx
    obtain ⟨y', hy', hiy⟩ := ihy
    refine ⟨x' * y', mul_mem hx' hy', fun r => ?_⟩
    change f.index (x'.indexEquiv (y'.indexEquiv r)) = x.indexEquiv (y.indexEquiv (f.index r))
    rw [hix, hiy]

/-- Ordinary weight intertwining suffices for exact root-index intertwining. -/
theorem index_intertwine (a : P.Aut) (b : Q.Aut)
    (h : ∀ x, f.weightMap (a.weightMap x) = b.weightMap (f.weightMap x)) (r : J) :
    f.index (a.indexEquiv r) = b.indexEquiv (f.index r) := by
  apply Q.root.injective
  rw [← f.root_eq, ← RootPairing.Hom.root_weightMap_apply P P r a.toHom,
    h, f.root_eq, RootPairing.Hom.root_weightMap_apply Q Q (f.index r) b.toHom]

end RootComponentEmbedding

namespace SplitPinning

variable {k k' : Type u} [Field k] [Field k']
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- A base-preserving embedding as a full orthogonal component of another
actual pinning's root datum. -/
structure BasedComponentEmbedding (p : SplitPinning G) (q : SplitPinning H) where
  rootEmbedding : RootComponentEmbedding p.rootDatum q.rootDatum
  base_iff : ∀ r, r ∈ p.base.support ↔ rootEmbedding.index r ∈ q.base.support

namespace BasedComponentEmbedding

variable {p : SplitPinning G} {q : SplitPinning H} (f : BasedComponentEmbedding p q)

/-- Weyl correction to both chosen bases respects the full root-component
embedding whenever the original root actions intertwine. -/
theorem basedProjection_index (a : p.rootDatum.Aut) (b : q.rootDatum.Aut)
    (h : ∀ r, f.rootEmbedding.index (a.indexEquiv r) = b.indexEquiv (f.rootEmbedding.index r))
    (r : p.rootIndex) :
    f.rootEmbedding.index ((p.basedRootDatumProjection a).val.indexEquiv r) =
      (q.basedRootDatumProjection b).val.indexEquiv (f.rootEmbedding.index r) := by
  obtain ⟨w, hw⟩ := q.exists_weyl_mul_eq_basedRootDatumProjection b
  obtain ⟨v, hv, hindex⟩ := f.rootEmbedding.exists_weyl_lift w.property
  let a' : p.rootDatum.Aut := v * a
  have ha' : ∀ s, f.rootEmbedding.index (a'.indexEquiv s) =
      (q.basedRootDatumProjection b).val.indexEquiv (f.rootEmbedding.index s) := by
    intro s
    rw [← hw]
    change f.rootEmbedding.index (v.indexEquiv (a.indexEquiv s)) =
      w.val.indexEquiv (b.indexEquiv (f.rootEmbedding.index s))
    rw [hindex, h]
  have hbase : a' ∈ p.basedRootDatumAut := by
    intro s
    rw [f.base_iff, f.base_iff, ha']
    exact (q.basedRootDatumProjection b).property (f.rootEmbedding.index s)
  have hweyl : a' * a⁻¹ ∈ p.rootDatum.weylGroup := by
    simpa only [a', mul_inv_cancel_right] using hv
  have heq : a' = (p.basedRootDatumProjection a).val :=
    congrArg Subtype.val (p.basedRootDatum_representative_unique a ⟨a', hbase⟩
      (p.basedRootDatumProjection a) hweyl (p.basedRootDatumProjection_correction a))
  rw [← heq]
  exact ha' r

end BasedComponentEmbedding
end SplitPinning

namespace GaloisPinningData

variable {k L k' L' : Type u} [Field k] [Field L] [Field k'] [Field L']
  [Algebra k L] [Algebra k' L']
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (p : GaloisPinningData k L G) (q : GaloisPinningData k' L' H)

/-- The full star actions intertwine on all roots of an embedded orthogonal
component whenever their ordinary Galois root actions intertwine. -/
theorem starAction_index_of_componentEmbedding
    (f : SplitPinning.BasedComponentEmbedding p.toSplitPinning q.toSplitPinning)
    (σ : L ≃ₐ[k] L) (τ : L' ≃ₐ[k'] L')
    (h : ∀ r, f.rootEmbedding.index ((p.galoisAction σ).indexEquiv r) =
      (q.galoisAction τ).indexEquiv (f.rootEmbedding.index r)) (r : p.rootIndex) :
    f.rootEmbedding.index ((p.starAction σ).val.indexEquiv r) =
      (q.starAction τ).val.indexEquiv (f.rootEmbedding.index r) :=
  f.basedProjection_index (p.galoisAction σ) (q.galoisAction τ) h r

/-- Actual ordinary character intertwining is a sufficient hypothesis for
full star compatibility on the entire embedded root component. -/
theorem starAction_index_of_componentWeightIntertwining
    (f : SplitPinning.BasedComponentEmbedding p.toSplitPinning q.toSplitPinning)
    (σ : L ≃ₐ[k] L) (τ : L' ≃ₐ[k'] L')
    (h : ∀ χ, f.rootEmbedding.weightMap
        (characterLattice.galoisRepresentation k L p.torus σ χ) =
      characterLattice.galoisRepresentation k' L' q.torus τ (f.rootEmbedding.weightMap χ))
    (r : p.rootIndex) :
    f.rootEmbedding.index ((p.starAction σ).val.indexEquiv r) =
      (q.starAction τ).val.indexEquiv (f.rootEmbedding.index r) := by
  apply p.starAction_index_of_componentEmbedding q f σ τ
    (fun s => f.rootEmbedding.index_intertwine (p.galoisAction σ) (q.galoisAction τ) ?_ s) r
  intro χ
  rw [StarActionIndependence.galoisAction_weightMap_apply,
    StarActionIndependence.galoisAction_weightMap_apply]
  exact h χ

end GaloisPinningData
end Langlands.GroupScheme
