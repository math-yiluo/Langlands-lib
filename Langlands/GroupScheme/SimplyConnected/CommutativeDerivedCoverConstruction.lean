import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Derived.CommutativeTriviality
import Langlands.GroupScheme.Torus.ExistenceProof

/-! # Actual trivial derived covers of commutative connected reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Homomorphisms into the actual trivial group scheme are unique. -/
theorem hom_to_trivial_ext {S : Scheme.{u}} {H : GroupScheme S}
    (f g : H ⟶ Grp.trivial (Over S)) : f = g :=
  Grp.hom_ext f g (toUnit_unique _ _)

variable {k : Type u} [Field k]

/-- The actual trivial group scheme over a field is semisimple. -/
theorem isSemisimple_trivial : IsSemisimple (Grp.trivial (Over (Spec (CommRingCat.of k)))) := by
  let Q := Grp.trivial (Over (Spec (CommRingCat.of k)))
  have hred : IsConnectedReductive Q :=
    (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) PEmpty.{u + 1}).isConnectedReductive.of_iso
      TorusExistence.splitTorusEmptyIso.symm
  have hcenter : center Q = ⊤ := by
    apply SubgroupFunctor.ext
    intro U
    apply top_unique
    intro x _ V a y
    change (a ≫ x) * y = y * (a ≫ x)
    exact toUnit_unique _ _
  refine ⟨hred, Q, 𝟙 Q, ?_, ?_⟩
  · constructor
    · change IsClosedImmersion (𝟙 Q.X.left)
      infer_instance
    · rw [SubgroupFunctor.range_id, hcenter]
  · change IsFinite (𝟙 (Spec (CommRingCat.of k)))
    infer_instance

/-- Every incoming central isogeny from a semisimple group to the actual trivial
group is an isomorphism: its unit section is an inverse by finite-hom cancellation. -/
theorem isSimplyConnected_trivial :
    IsSimplyConnected (Grp.trivial (Over (Spec (CommRingCat.of k)))) := by
  refine ⟨isSemisimple_trivial, ?_⟩
  intro H q hH hq
  let s := kernelUnit H
  have hs : s ≫ q = 𝟙 _ := hom_to_trivial_ext _ _
  have hq' : q ≫ s = 𝟙 H := by
    apply hq.cancel_of_connectedReductive hH.isConnectedReductive
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  exact ⟨⟨s, hq', hs⟩⟩

/-- The identity of the actual trivial group is its universal simply connected cover. -/
theorem isSimplyConnectedCover_id_trivial :
    IsSimplyConnectedCover (𝟙 (Grp.trivial (Over (Spec (CommRingCat.of k))))) := by
  refine ⟨isSemisimple_trivial, isSimplyConnected_trivial, isCentralIsogeny_id _, ?_⟩
  intro H q hH hq
  have : IsIso q := isSimplyConnected_trivial.central_isogeny_isIso H q hH hq
  refine ⟨inv q, IsIso.inv_hom_id q, ?_⟩
  intro a ha
  apply (cancel_mono q).mp
  rw [ha, IsIso.inv_hom_id]

/-- The actual identity-subgroup inclusion and identity covering map exhibit a
simply connected derived cover of every commutative connected reductive field group. -/
def commutativeDerivedCoverData
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsCommMonObj G.X]
    (hG : IsConnectedReductive G) :
    {d : Grp.trivial (Over (Spec (CommRingCat.of k))) ⟶ G //
      IsSimplyConnectedDerivedCover d
        (𝟙 (Grp.trivial (Over (Spec (CommRingCat.of k)))))} := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsSeparated G.X.hom := inferInstance
  refine ⟨kernelUnit G, hG, ?_, isSimplyConnectedCover_id_trivial⟩
  refine ⟨kernelUnit_isClosedSubgroup G, ?_⟩
  rw [range_kernelUnit, derivedSubgroup_eq_bot_of_isCommMonObj G]

@[simp]
theorem commutativeDerivedCoverData_val
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsCommMonObj G.X]
    (hG : IsConnectedReductive G) :
    (commutativeDerivedCoverData G hG).val = kernelUnit G :=
  rfl

end Langlands.GroupScheme
