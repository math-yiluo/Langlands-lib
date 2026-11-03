import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.RelativeWeylRootPermutation
import Langlands.LinearAlgebra.RootPairingChambers

/-! # Relative Weyl generation from a trivial positive-root stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Every element of the actual relative Weyl quotient preserving the positive
roots selected by `ν` is trivial. This is a structural input, not a consequence
of the definitions. -/
def HasTrivialPositiveRootStabilizer (ν : cocharacterLattice T) : Prop :=
  ∀ w : relativeWeylGroup i,
    (∀ α ∈ relativeRoots i,
      0 < latticePairing T (relativeWeylCharacterAction i w α) ν ↔
        0 < latticePairing T α ν) → w = 1

namespace RelativeRootSystem

/-- The actual quotient action transports the root vectors by its root permutation. -/
theorem relativeWeylAction_rootVector (w : relativeWeylGroup i) (α : relativeRoots i) :
    relativeWeylAction i w (rootVector i α) =
      rootVector i (relativeWeylRootPermutation i w α) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  rfl

/-- Evaluation on the transported root is the original integral pairing,
rationalized. -/
theorem corootFunctional_relativeWeylAction_rootVector (ν : cocharacterLattice T)
    (w : relativeWeylGroup i) (α : relativeRoots i) :
    corootFunctional i ν (relativeWeylAction i w (rootVector i α)) =
      (latticePairing T (relativeWeylCharacterAction i w α.val) ν : ℚ) := by
  rw [relativeWeylAction_rootVector, corootFunctional_rootVector]
  rfl

end RelativeRootSystem

open RelativeRootSystem

variable {i}

/-- A trivial positive-root stabilizer already gives faithfulness on the root span. -/
theorem HasTrivialPositiveRootStabilizer.relativeWeylAction_injective
    {ν : cocharacterLattice T} (h : HasTrivialPositiveRootStabilizer i ν) :
    Function.Injective (relativeWeylAction i) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  apply h w
  intro α hα
  have he := congrArg (fun e : relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i =>
    corootFunctional i ν (e (rootVector i ⟨α, hα⟩))) hw
  change corootFunctional i ν (relativeWeylAction i w (rootVector i ⟨α, hα⟩)) =
    corootFunctional i ν (rootVector i ⟨α, hα⟩) at he
  rw [corootFunctional_relativeWeylAction_rootVector, corootFunctional_rootVector] at he
  have hez : latticePairing T (relativeWeylCharacterAction i w α) ν =
      latticePairing T α ν := by exact_mod_cast he
  rw [hez]

namespace RelativeRootReflectionData

variable (D : RelativeRootReflectionData i)

/-- If the actual quotient has trivial positive-root stabilizer at a generic
cocharacter, its normalizing reflection representatives generate it. -/
theorem closure_representatives_eq_top_of_positive_stabilizer
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν) :
    Subgroup.closure (Set.range fun α =>
      (QuotientGroup.mk (D.representative α) : relativeWeylGroup i)) = ⊤ := by
  let := hfinite.fintype
  let P := D.rootPairing hT hfinite
  have : P.IsRootSystem := D.rootPairing_isRootSystem hT hfinite
  let f := corootFunctional i ν
  have hf : Langlands.LinearAlgebra.RootPairingChambers.Regular P f := by
    intro α
    change corootFunctional i ν (rootVector i α) ≠ 0
    rw [corootFunctional_rootVector]
    exact_mod_cast hν α.val α.property
  let H := Subgroup.closure (Set.range fun α =>
    (QuotientGroup.mk (D.representative α) : relativeWeylGroup i))
  have hmap : P.weylGroup.map (RootPairing.Equiv.weightHom P) =
      H.map (relativeWeylAction i) := by
    rw [D.weylGroup_image]
    rw [MonoidHom.map_closure]
    congr 1
    exact Set.range_comp _ _
  apply top_unique
  intro q _
  let g : Module.Dual ℚ (relativeRootSpan i) :=
    f.comp (relativeWeylAction i q).toLinearMap
  have hg : Langlands.LinearAlgebra.RootPairingChambers.Regular P g := by
    intro α
    change corootFunctional i ν (relativeWeylAction i q (rootVector i α)) ≠ 0
    rw [corootFunctional_relativeWeylAction_rootVector]
    exact_mod_cast hν _ (relativeWeylRootPermutation i q α).property
  obtain ⟨w, hw⟩ :=
    Langlands.LinearAlgebra.RootPairingChambers.exists_weylGroup_sameChamber P hf hg
  have hwmap : RootPairing.Equiv.weightHom P w.val ∈ H.map (relativeWeylAction i) := by
    rw [← hmap]
    exact ⟨w.val, w.property, rfl⟩
  obtain ⟨r, hr, hwr⟩ := hwmap
  have hqr : q * r = 1 := by
    apply hstab (q * r)
    intro α hα
    have he := w.val.toLinearMap_weightEquiv (P.root ⟨α, hα⟩)
      g
    have hs := hw ⟨α, hα⟩
    change 0 < f (rootVector i ⟨α, hα⟩) ↔
      0 < w.val.coweightEquiv g (rootVector i ⟨α, hα⟩) at hs
    change g (w.val.weightEquiv (rootVector i ⟨α, hα⟩)) =
      w.val.coweightEquiv g (rootVector i ⟨α, hα⟩) at he
    rw [← he] at hs
    change 0 < f (rootVector i ⟨α, hα⟩) ↔
      0 < f (relativeWeylAction i q
        (RootPairing.Equiv.weightHom P w.val (rootVector i ⟨α, hα⟩))) at hs
    rw [← hwr, ← LinearEquiv.mul_apply, ← map_mul] at hs
    rw [corootFunctional_relativeWeylAction_rootVector,
      corootFunctional_rootVector] at hs
    exact_mod_cast hs.symm
  have hq : q = r⁻¹ := (eq_inv_iff_mul_eq_one).mpr hqr
  exact hq ▸ H.inv_mem hr

include D in
/-- Integral reflection data and a trivial positive-root stabilizer at one
generic cocharacter imply the full relative-root-system predicate. -/
theorem hasRelativeRootSystem_of_positive_stabilizer
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν) : HasRelativeRootSystem i := by
  exact D.hasRelativeRootSystem hT hfinite
    (D.closure_representatives_eq_top_of_positive_stabilizer hT hfinite hν hstab)
    hstab.relativeWeylAction_injective

end RelativeRootReflectionData

end Langlands.GroupScheme
