import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Reductive.PinnedIsomorphismFunctoriality
import Langlands.GroupScheme.Rational.TangentImageBaseChange

/-! # Actual scalar transport of complete pinned isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SplitPinning

section ScalarExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {p : SplitPinning G} {q : SplitPinning H}

local notation "b" => algebraBaseMap k K

local instance (C : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom C.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj C).X.hom := by
  change IsAffineHom (pullback.snd C.X.hom b)
  infer_instance

namespace Iso

/-- Pull back every part of an actual complete pinned isomorphism. -/
def baseChange (f : SplitPinning.Iso p q) :
    SplitPinning.Iso (p.baseChange (F := K)) (q.baseChange (F := K)) where
  torusIso := (CommGroupScheme.baseChange b).mapIso f.torusIso
  groupIso := (GroupScheme.baseChange b).mapIso f.groupIso
  square := by
    change (GroupScheme.baseChange b).map p.inclusion ≫
        (GroupScheme.baseChange b).map f.groupIso.hom =
      (GroupScheme.baseChange b).map (CommGroupScheme.groupHom f.torusIso.hom) ≫
        (GroupScheme.baseChange b).map q.inclusion
    rw [← Functor.map_comp, ← Functor.map_comp, f.square]
  indexEquiv := f.indexEquiv
  root_eq := by
    intro a
    change (CommGroupScheme.baseChange b).map f.torusIso.inv ≫
        characterLattice.baseChange b p.torus (p.rootDatum.root a) =
      characterLattice.baseChange b q.torus (q.rootDatum.root (f.indexEquiv a))
    rw [← characterLattice.baseChange_precomp, ← f.root_eq]
    rfl
  coroot_eq := by
    intro a
    change cocharacterLattice.baseChange b p.torus (p.rootDatum.coroot a) ≫
        (CommGroupScheme.baseChange b).map f.torusIso.hom =
      cocharacterLattice.baseChange b q.torus (q.rootDatum.coroot (f.indexEquiv a))
    rw [← cocharacterLattice.baseChange_comp, ← f.coroot_eq]
    rfl
  simple_iff := by
    intro a
    change a ∈ p.baseChangeBase.support ↔ f.indexEquiv a ∈ q.baseChangeBase.support
    rw [baseChangeBase_support, baseChangeBase_support]
    exact f.simple_iff a
  rootVector_eq := by
    intro a
    have := p.isConnectedReductive.smooth
    have := q.isConnectedReductive.smooth
    let a₀ : p.base.support := (p.baseChangeSimpleEquiv (F := K)).symm a
    have hleft :
        (p.baseChange (F := K)).pinning.rootVector a =
          Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] p.pinning.rootVector a₀) := by
      simpa only [a₀, Equiv.apply_symm_apply] using
        p.baseChange_rootVector (F := K) a₀
    rw [hleft, Functor.mapIso_hom]
    rw [Lie.targetMapLinear_schemeScalarExtension_one_tmul, f.rootVector_eq]
    exact (q.baseChange_rootVector
      ⟨f.indexEquiv a₀, (f.simple_iff a₀).mp a₀.property⟩).symm

@[simp] theorem baseChange_torusIso (f : SplitPinning.Iso p q) :
    (f.baseChange (K := K)).torusIso =
      (CommGroupScheme.baseChange b).mapIso f.torusIso := rfl

@[simp] theorem baseChange_groupIso (f : SplitPinning.Iso p q) :
    (f.baseChange (K := K)).groupIso = (GroupScheme.baseChange b).mapIso f.groupIso := rfl

@[simp] theorem baseChange_indexEquiv (f : SplitPinning.Iso p q) :
    (f.baseChange (K := K)).indexEquiv = f.indexEquiv := rfl

/-- Scalar pullback preserves complete pinned identities. -/
@[simp] theorem baseChange_refl (p : SplitPinning G) :
    (Iso.refl p).baseChange (K := K) = Iso.refl (p.baseChange (F := K)) := by
  apply ext_torus_index
  · simp [baseChange, refl, SplitPinning.baseChange]
  · rfl

variable {C : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom C.X.hom]
    {r : SplitPinning C}

/-- Scalar pullback preserves complete pinned composition. -/
theorem baseChange_trans (f : SplitPinning.Iso p q) (g : SplitPinning.Iso q r) :
    (f.trans g).baseChange (K := K) =
      (f.baseChange (K := K)).trans (g.baseChange (K := K)) := by
  apply ext_torus_index
  · simp [baseChange, trans]
  · rfl

end Iso

end ScalarExtension

end Langlands.GroupScheme.SplitPinning
