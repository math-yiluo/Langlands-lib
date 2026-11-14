import Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement
import Langlands.Geometry.Building.Kottwitz.CocenterCharacters
import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelStatement
import Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionStatement
import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement

/-! # Cocenter reduction for the character-kernel theorem -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- A homomorphism with torsion kernel reflects torsion. -/
theorem torsion_comap_eq_of_kernel_le {A B : Type*} [CommGroup A] [CommGroup B]
    (f : A →* B) (hk : f.ker ≤ CommGroup.torsion A) :
    (CommGroup.torsion B).comap f = CommGroup.torsion A := by
  apply le_antisymm
  · intro a ha
    obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
    have hpow : a ^ n ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact he
    exact (hk hpow).of_pow (Nat.ne_of_gt hn)
  · exact CommGroup.le_comap_torsion f

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)

/-- Inclusion of residual invariants into the inertia group is injective. -/
theorem reductiveInvariantInclusion_injective :
    Function.Injective (reductiveInvariantInclusion F G hG) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  apply Subtype.val_injective
  exact congrArg Multiplicative.toAdd hab

/-- Finite order in the residual fixed subgroup is finite order in the full
inertia group. -/
theorem mem_fundamentalInvariantTorsion_iff
    (a : Multiplicative (ReductiveInvariantTarget F G hG)) :
    a ∈ fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG ↔
      reductiveInvariantInclusion F G hG a ∈
        fundamentalInertiaTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG :=
  (reductiveInvariantInclusion_injective F G hG).isOfFinOrder_iff.symm

/-- The pointwise cocenter argument, assuming the exact torus kernel, torsion
kernel, cocenter square and rational restriction laws. -/
theorem characterKernel_of_cocenter (c : Cocenter F G)
    (ht : characterValuationKernel (ValuativeRel.valuation F) c.torus.toGrp =
      (CommGroup.torsion (Multiplicative (TorusTarget F F c.torus))).comap
        ((torusKottwitz F F c.torus c.isTorus).comp
          ((GaloisPoint.extend F (UnramifiedClosure F) c.torus.toGrp).comp
            (rationalCoeffEquiv F c.torus.toGrp).toMonoidHom)))
    (hk : (cocenterTargetMap F F G hG c).toAddMonoidHom.toMultiplicative.ker ≤
      fundamentalInertiaTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG)
    (hκ : CocenterKottwitzLawAt F F G hG c (reductiveKottwitz F F G hG))
    (hr : IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG)) :
    characterValuationKernel (ValuativeRel.valuation F) G =
      (fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG).comap
        (reductiveKottwitzRational F G hG) := by
  let f := (cocenterTargetMap F F G hG c).toAddMonoidHom.toMultiplicative
  have hf := torsion_comap_eq_of_kernel_le f hk
  rw [c.characterValuationKernel_eq_comap hG, ht]
  ext x
  have hsquare :
      f (reductiveInvariantInclusion F G hG (reductiveKottwitzRational F G hG x)) =
        torusKottwitz F F c.torus c.isTorus
          (GaloisPoint.extend F (UnramifiedClosure F) c.torus.toGrp
            (rationalCoeffEquiv F c.torus.toGrp (rationalPoints.map c.quotient x))) := by
    rw [hr x, rationalCoeffEquiv_map]
    have he := congrArg (fun m => m (rationalCoeffEquiv F G x))
      (affinePointsTarget_naturality G c.quotient
        (CommAlgCat.ofHom (Algebra.ofId F (UnramifiedClosure F))))
    change GaloisPoint.extend F (UnramifiedClosure F) c.torus.toGrp
        (G.affinePointsTarget c.quotient (CommAlgCat.of F F) (rationalCoeffEquiv F G x)) =
      G.affinePointsTarget c.quotient (CommAlgCat.of F (UnramifiedClosure F))
        (GaloisPoint.extend F (UnramifiedClosure F) G (rationalCoeffEquiv F G x)) at he
    rw [he]
    apply Multiplicative.toAdd.injective
    exact hκ _
  change torusKottwitz F F c.torus c.isTorus
      (GaloisPoint.extend F (UnramifiedClosure F) c.torus.toGrp
        (rationalCoeffEquiv F c.torus.toGrp (rationalPoints.map c.quotient x))) ∈
      CommGroup.torsion _ ↔ _
  rw [Subgroup.mem_comap, mem_fundamentalInvariantTorsion_iff, ← hsquare]
  exact SetLike.ext_iff.mp hf _

/-- The four separate mathematical inputs to the cocenter reduction. -/
def CharacterKernelInputs : Prop :=
  TorusCharacterKernelStatement.{u} ∧ CocenterTargetTorsionStatement.{u} ∧
    ReductiveKottwitzFunctorialityStatement.{u} ∧ ReductiveKottwitzDescentStatement.{u}

/-- The source's cocenter argument proves the exact Library target from the
four stated inputs. It does not assert that those inputs have been proved. -/
theorem CharacterKernelInputs.characterKernel (h : CharacterKernelInputs.{u}) :
    CharacterKernelStatement.{u} := by
  rcases h with ⟨ht, hk, hfun, hd⟩
  intro F _ _ _ _ G hG
  obtain ⟨c⟩ := nonempty_cocenter F G hG
  have hκ : CocenterKottwitzLawAt F F G hG c (reductiveKottwitz F F G hG) := by
    intro x
    change torusInertiaComparison F (UnramifiedClosure F) (SeparableClosure F)
      c.torus c.isTorus
      (fundamentalInertiaMap F (UnramifiedClosure F) (SeparableClosure F)
        c.torus.toGrp c.isTorus.isConnectedReductive_of_fieldSplitting G hG c.quotient
        (reductiveKottwitz F F G hG x).toAdd) = _
    rw [← (hfun F F).1 G c.torus.toGrp hG c.isTorus.isConnectedReductive_of_fieldSplitting
      c.quotient x]
    exact (hfun F F).2 c.torus c.isTorus _
  exact characterKernel_of_cocenter F G hG c (ht F c.torus c.isTorus)
    (hk F G hG c) hκ (hd.2 F G hG).2.2

end Langlands.Geometry.Building.Kottwitz
