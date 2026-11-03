import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-! # Transport of split root data along actual lattice base change -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitRootDatum

variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    {J : Type v} (P : RootDatum J (characterLattice T) (cocharacterLattice T))

/-- Transport of an integral root datum along the canonical actual lattice equivalences. -/
def baseChange :
    RootDatum J (characterLattice ((CommGroupScheme.baseChange b).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :=
  P.map (Equiv.refl J) (characterLattice.baseChangeEquiv b T hT).toIntLinearEquiv
    (cocharacterLattice.baseChangeEquiv b T hT).toIntLinearEquiv

@[simp] theorem baseChange_root (α : J) :
    (baseChange b T hT P).root α = characterLattice.baseChange b T (P.root α) := rfl

@[simp] theorem baseChange_coroot (α : J) :
    (baseChange b T hT P).coroot α = cocharacterLattice.baseChange b T (P.coroot α) := rfl

@[simp] theorem baseChange_pairing (χ : characterLattice T) (ν : cocharacterLattice T) :
    (baseChange b T hT P).toLinearMap
      (characterLattice.baseChange b T χ) (cocharacterLattice.baseChange b T ν) =
        P.toLinearMap χ ν := by
  change P.toLinearMap
    ((characterLattice.baseChangeEquiv b T hT).symm
      (characterLattice.baseChangeEquiv b T hT χ))
    ((cocharacterLattice.baseChangeEquiv b T hT).symm
      (cocharacterLattice.baseChangeEquiv b T hT ν)) = _
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- The transported pairing is the actual integer character/cocharacter pairing. -/
theorem baseChange_toLinearMap (hP : P.toLinearMap = latticePairing T) :
    (baseChange b T hT P).toLinearMap =
      latticePairing ((CommGroupScheme.baseChange b).obj T) := by
  apply LinearMap.ext
  intro χ'
  apply LinearMap.ext
  intro ν'
  obtain ⟨χ, rfl⟩ := (characterLattice.baseChangeEquiv b T hT).surjective χ'
  obtain ⟨ν, rfl⟩ := (cocharacterLattice.baseChangeEquiv b T hT).surjective ν'
  change (baseChange b T hT P).toLinearMap
    (characterLattice.baseChange b T χ) (cocharacterLattice.baseChange b T ν) = _
  rw [baseChange_pairing, hP]
  exact (latticePairing_baseChange b T χ ν).symm

/-- Integral reflections commute with the actual character pullback. -/
theorem baseChange_reflection (α : J) (χ : characterLattice T) :
    (baseChange b T hT P).reflection α (characterLattice.baseChange b T χ) =
      characterLattice.baseChange b T (P.reflection α χ) := by
  simp only [RootPairing.reflection_apply, RootPairing.coroot', LinearMap.flip_apply,
    baseChange_root, baseChange_coroot, baseChange_pairing, map_sub, map_zsmul]

/-- The integral coroot span is carried to the integral coroot span by actual pullback. -/
theorem map_corootSpan :
    (P.corootSpan ℤ).map
      (cocharacterLattice.baseChangeEquiv b T hT).toIntLinearEquiv.toLinearMap =
        (baseChange b T hT P).corootSpan ℤ := by
  rw [RootPairing.corootSpan, Submodule.map_span]
  change Submodule.span ℤ
    ((cocharacterLattice.baseChange b T) '' Set.range P.coroot) =
      Submodule.span ℤ (Set.range fun α => cocharacterLattice.baseChange b T (P.coroot α))
  exact congrArg (Submodule.span ℤ)
    (Set.range_comp' (cocharacterLattice.baseChange b T) P.coroot).symm

/-- Integral coroot generation is invariant under the canonical lattice transport. -/
theorem corootSpan_eq_top_iff :
    (baseChange b T hT P).corootSpan ℤ = ⊤ ↔ P.corootSpan ℤ = ⊤ := by
  rw [← map_corootSpan]
  exact Submodule.map_eq_top_iff

end SplitRootDatum

/-- Compatibility of the actual root datum of a split maximal torus with an arbitrary
extension of its ground field. The transported roots and coroots are the canonical
actual lattice pullbacks, rather than newly chosen lattice identifications. -/
def SplitRootDatumFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G), IsMaximalTorus i →
      haveI := hG.isAffineHom
      haveI : IsAffineHom
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom := by
        change IsAffineHom (pullback.snd G.X.hom _)
        infer_instance
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P →
          IsRootDatumOf
            ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)
            (SplitRootDatum.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) T hT P)

end Langlands.GroupScheme
