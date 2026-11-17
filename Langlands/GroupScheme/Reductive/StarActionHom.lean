import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.LinearAlgebra.RootDatumHomBase

/-! # Star naturality for based morphisms of root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RootHomStar

variable {J J' M M' N N' : Type*}
  [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
  {P : RootDatum J M N} {Q : RootDatum J' M' N'}

/-- Root-datum morphisms intertwine the reflections in corresponding roots. -/
theorem reflection_intertwine (f : RootPairing.Hom P Q) (i : J) (x : M) :
    f.weightMap (P.reflection i x) = Q.reflection (f.indexEquiv i) (f.weightMap x) := by
  have hpair : Q.coroot' (f.indexEquiv i) (f.weightMap x) = P.coroot' i x := by
    have h := LinearMap.congr_fun
      (f.weight_coweight_transpose_apply P Q (Q.coroot (f.indexEquiv i))) x
    change Q.toLinearMap (f.weightMap x) (Q.coroot (f.indexEquiv i)) =
      P.toLinearMap x (f.coweightMap (Q.coroot (f.indexEquiv i))) at h
    change Q.toLinearMap (f.weightMap x) (Q.coroot (f.indexEquiv i)) =
      P.toLinearMap x (P.coroot i)
    simpa only [RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply] using h
  rw [RootPairing.reflection_apply, RootPairing.reflection_apply, map_sub, map_smul,
    RootPairing.Hom.root_weightMap_apply, hpair]

/-- Every Weyl word on the target has a Weyl word on the source intertwining
its action on the actual weight map; no lattice surjectivity is used. -/
theorem exists_weyl_lift (f : RootPairing.Hom P Q) {w : Q.Aut} (hw : w ∈ Q.weylGroup) :
    ∃ v : P.Aut, v ∈ P.weylGroup ∧
      ∀ x, f.weightMap (v.weightMap x) = w.weightMap (f.weightMap x) := by
  induction hw using RootPairing.weylGroup.induction with
  | mem i =>
    refine ⟨RootPairing.Equiv.reflection P (f.indexEquiv.symm i),
      P.reflection_mem_weylGroup _, fun x => ?_⟩
    change f.weightMap (P.reflection (f.indexEquiv.symm i) x) =
      Q.reflection i (f.weightMap x)
    simpa only [Equiv.apply_symm_apply] using
      reflection_intertwine f (f.indexEquiv.symm i) x
  | one => exact ⟨1, one_mem _, fun _ => rfl⟩
  | mul a b ha hb ia ib =>
    obtain ⟨a', ha', hia⟩ := ia
    obtain ⟨b', hb', hib⟩ := ib
    refine ⟨a' * b', mul_mem ha' hb', fun x => ?_⟩
    change f.weightMap (a'.weightMap (b'.weightMap x)) =
      a.weightMap (b.weightMap (f.weightMap x))
    rw [hia, hib]

/-- Intertwining the weight maps also intertwines every root index. -/
theorem index_intertwine (f : RootPairing.Hom P Q) (a : P.Aut) (b : Q.Aut)
    (h : ∀ x, f.weightMap (a.weightMap x) = b.weightMap (f.weightMap x)) (i : J) :
    f.indexEquiv (a.indexEquiv i) = b.indexEquiv (f.indexEquiv i) := by
  apply Q.root.injective
  rw [← RootPairing.Hom.root_weightMap_apply P Q _ f,
    ← RootPairing.Hom.root_weightMap_apply P P _ a.toHom, h,
    RootPairing.Hom.root_weightMap_apply P Q _ f,
    RootPairing.Hom.root_weightMap_apply Q Q _ b.toHom]

end RootHomStar

namespace SplitPinning

variable {k k' : Type u} [Field k] [Field k']
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- A morphism on the actual root lattices retaining both full simple supports.
Its lattice maps are not required to be surjective. -/
structure BasedRootHom (p : SplitPinning G) (q : SplitPinning H) where
  toHom : RootPairing.Hom p.rootDatum q.rootDatum
  base_iff : ∀ i, i ∈ p.base.support ↔ toHom.indexEquiv i ∈ q.base.support

namespace BasedRootHom

variable {p : SplitPinning G} {q : SplitPinning H} (f : BasedRootHom p q)

/-- Weyl correction to the chosen bases commutes with a based root morphism
whenever the original automorphisms intertwine its weight map. -/
theorem basedProjection_weight (a : p.rootDatum.Aut) (b : q.rootDatum.Aut)
    (h : ∀ x, f.toHom.weightMap (a.weightMap x) = b.weightMap (f.toHom.weightMap x))
    (x) :
    f.toHom.weightMap ((p.basedRootDatumProjection a).val.weightMap x) =
      (q.basedRootDatumProjection b).val.weightMap (f.toHom.weightMap x) := by
  obtain ⟨w, hw⟩ := q.exists_weyl_mul_eq_basedRootDatumProjection b
  obtain ⟨v, hv, hweight⟩ := RootHomStar.exists_weyl_lift f.toHom w.property
  let a' : p.rootDatum.Aut := v * a
  have ha' : ∀ y, f.toHom.weightMap (a'.weightMap y) =
      (q.basedRootDatumProjection b).val.weightMap (f.toHom.weightMap y) := by
    intro y
    rw [← hw]
    change f.toHom.weightMap (v.weightMap (a.weightMap y)) =
      w.val.weightMap (b.weightMap (f.toHom.weightMap y))
    rw [hweight, h]
  have hindex := RootHomStar.index_intertwine f.toHom a'
    (q.basedRootDatumProjection b).val ha'
  have hbase : a' ∈ p.basedRootDatumAut := by
    intro i
    rw [f.base_iff, f.base_iff, hindex]
    exact (q.basedRootDatumProjection b).property (f.toHom.indexEquiv i)
  have hweyl : a' * a⁻¹ ∈ p.rootDatum.weylGroup := by
    simpa only [a', mul_inv_cancel_right] using hv
  have heq : a' = (p.basedRootDatumProjection a).val :=
    congrArg Subtype.val (p.basedRootDatum_representative_unique a ⟨a', hbase⟩
      (p.basedRootDatumProjection a) hweyl (p.basedRootDatumProjection_correction a))
  rw [← heq]
  exact ha' x

/-- The same comparison on every root index. -/
theorem basedProjection_index (a : p.rootDatum.Aut) (b : q.rootDatum.Aut)
    (h : ∀ x, f.toHom.weightMap (a.weightMap x) = b.weightMap (f.toHom.weightMap x))
    (i : p.rootIndex) :
    f.toHom.indexEquiv ((p.basedRootDatumProjection a).val.indexEquiv i) =
      (q.basedRootDatumProjection b).val.indexEquiv (f.toHom.indexEquiv i) :=
  RootHomStar.index_intertwine f.toHom _ _ (f.basedProjection_weight a b h) i

end BasedRootHom
end SplitPinning

namespace GaloisPinningData

variable {k E k' E' : Type u} [Field k] [Field E] [Field k'] [Field E']
  [Algebra k E] [Algebra k' E']
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (p : GaloisPinningData k E G) (q : GaloisPinningData k' E' H)

/-- A based morphism intertwining actual ordinary Galois character actions
intertwines the full star action on every weight. The ground fields and
splitting fields may differ. -/
theorem starAction_weight_of_basedHom
    (f : SplitPinning.BasedRootHom p.toSplitPinning q.toSplitPinning)
    (σ : E ≃ₐ[k] E) (τ : E' ≃ₐ[k'] E')
    (h : ∀ χ, f.toHom.weightMap (characterLattice.galoisRepresentation k E p.torus σ χ) =
      characterLattice.galoisRepresentation k' E' q.torus τ (f.toHom.weightMap χ)) (χ) :
    f.toHom.weightMap ((p.starAction σ).val.weightMap χ) =
      (q.starAction τ).val.weightMap (f.toHom.weightMap χ) := by
  apply f.basedProjection_weight (p.galoisAction σ) (q.galoisAction τ)
  intro ψ
  rw [StarActionIndependence.galoisAction_weightMap_apply,
    StarActionIndependence.galoisAction_weightMap_apply]
  exact h ψ

/-- A single Galois element comparison holds simultaneously on all roots,
with the exact root-index map of the supplied morphism. -/
theorem starAction_index_of_basedHom
    (f : SplitPinning.BasedRootHom p.toSplitPinning q.toSplitPinning)
    (σ : E ≃ₐ[k] E) (τ : E' ≃ₐ[k'] E')
    (h : ∀ χ, f.toHom.weightMap (characterLattice.galoisRepresentation k E p.torus σ χ) =
      characterLattice.galoisRepresentation k' E' q.torus τ (f.toHom.weightMap χ))
    (i : p.rootIndex) :
    f.toHom.indexEquiv ((p.starAction σ).val.indexEquiv i) =
      (q.starAction τ).val.indexEquiv (f.toHom.indexEquiv i) :=
  RootHomStar.index_intertwine f.toHom _ _ (p.starAction_weight_of_basedHom q f σ τ h) i

end GaloisPinningData
end Langlands.GroupScheme
