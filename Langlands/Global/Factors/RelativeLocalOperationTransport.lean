import Langlands.Global.Factors.RelativeIsometryOperationStatement
import Langlands.VirtualRepresentation.Weil.ExactOperations
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupportDual
import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupportCharacterTwist
import Langlands.Correspondence.AssemblyTwist

/-! # Local restriction and support transport for relative witnessed operations -/

noncomputable section

universe uF uW uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every supplied unitary support transports by the target's actual field-character twist. -/
theorem isUnitaryLatticeSupport_characterTwist {n : ℕ}
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : UnitaryLattice.{uF, uV} F}
    (hx : IsUnitaryLatticeSupport F π x)
    (χ : Correspondence.QuasiCharacter F) (hu : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup n
    IsUnitaryLatticeSupport F
      (π.twist (χ.toMonoidHom.comp GeneralLinear.determinant)
        ((Correspondence.AssemblyTwist.isOpen_ker_quasiCharacter F χ).preimage
          (F.canonicalTopologicalData.generalLinearDeterminant n).continuous))
      (unitaryCharacterTwistLatticeEquiv F χ hu x) := by
  let := F.canonicalTopologicalData.topology
  let χs : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨χ.toMonoidHom, Correspondence.AssemblyTwist.isOpen_ker_quasiCharacter F χ⟩
  exact isUnitaryLatticeSupport_smoothCharacterTwist F hx χs hu

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The identity on actual dual vectors identifies restriction with the local dual. -/
def localComponentDualEquiv
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    FiniteRepresentation.Equiv (RelativeWeilGroup.localComponent S.dual ι)
      (RelativeWeilGroup.localComponent S ι).dual := by
  change Representation.Equiv (S.representation.dual.comp ι.toMonoidHom)
    (Representation.dual (S.representation.comp ι.toMonoidHom))
  refine { toLinearEquiv := LinearEquiv.refl ℂ _, isIntertwining' := ?_ }
  intro g
  ext f x
  change f (S.representation ((ι g)⁻¹) x) = f (S.representation (ι g⁻¹) x)
  rw [map_inv ι g]

/-- The full local exact class, rather than a semisimplification, commutes with duality. -/
theorem localExactClass_dual
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous) (hSd : S.dual.IsContinuous)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    localExactClass F E c v S.dual hSd ι =
      ExactGrothendieckGroup.continuousDual (localExactClass F E c v S hS ι) := by
  unfold localExactClass
  rw [ExactGrothendieckGroup.continuousDual_ofRepresentation]
  exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
    (localComponentDualEquiv F E c v S ι)

/-- Restriction of the actual scalar twist, when its local character is identified. -/
def localComponentTwistEquiv
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (χ : RelativeWeilGroup c F E →* ℂˣ)
    (η : Weil.Local.localWeilGroup (padicField v) →ₜ* ℂˣ)
    (hη : χ.comp ι.toMonoidHom = η.toMonoidHom) :
    FiniteRepresentation.Equiv
      (RelativeWeilGroup.localComponent (FiniteRepresentation.twist χ S) ι)
      (FiniteRepresentation.twist η.toMonoidHom (RelativeWeilGroup.localComponent S ι)) := by
  refine { toLinearEquiv := LinearEquiv.refl ℂ _, isIntertwining' := ?_ }
  intro g
  ext x
  change (χ (ι g) : ℂ) • S.representation (ι g) x =
    (η g : ℂ) • S.representation (ι g) x
  rw [show χ (ι g) = η g from DFunLike.congr_fun hη g]

/-- An identified continuous local character twists the actual full exact restriction. -/
theorem localExactClass_twist
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (χ : RelativeWeilGroup c F E →* ℂˣ)
    (hχS : (FiniteRepresentation.twist χ S).IsContinuous)
    (η : Weil.Local.localWeilGroup (padicField v) →ₜ* ℂˣ)
    (hη : χ.comp ι.toMonoidHom = η.toMonoidHom) :
    localExactClass F E c v (FiniteRepresentation.twist χ S) hχS ι =
      ExactGrothendieckGroup.continuousTwist η (localExactClass F E c v S hS ι) := by
  unfold localExactClass
  change ExactGrothendieckGroup.ofRepresentation _ _ =
    ExactGrothendieckGroup.twist _ _ _ _ (ExactGrothendieckGroup.ofRepresentation _ _)
  rw [ExactGrothendieckGroup.twist_ofRepresentation]
  exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
    (localComponentTwistEquiv F E c v S ι χ η hη)

/-- A supplied local unitary expansion transports to the actual restricted global dual. -/
theorem localExactExpansion_dual
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous) (hSd : S.dual.IsContinuous)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (x : LocalWeil.UnitaryLattice.{uF, uW} (padicField v))
    (hx : LocalWeil.ExactExpansion (padicField v) (localExactClass F E c v S hS ι)
      (LocalWeil.includeUnitary (padicField v) x)) :
    LocalWeil.ExactExpansion (padicField v)
      (localExactClass F E c v S.dual hSd ι)
      (LocalWeil.includeUnitary (padicField v)
        (LocalWeil.unitaryDualLatticeEquiv (padicField v) x)) := by
  rw [localExactClass_dual F E c v S hS hSd ι]
  exact Weil.ExactExpansion.unitaryDual hx

/-- A supplied unitary expansion transports to the actual restricted global scalar twist. -/
theorem localExactExpansion_twist
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hS : S.IsContinuous)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (χ : RelativeWeilGroup c F E →* ℂˣ)
    (hχS : (FiniteRepresentation.twist χ S).IsContinuous)
    (η : Weil.Local.localWeilGroup (padicField v) →ₜ* ℂˣ)
    (hη : χ.comp ι.toMonoidHom = η.toMonoidHom)
    (hu : ∀ g, ‖(η g : ℂ)‖ = 1)
    (x : LocalWeil.UnitaryLattice.{uF, uW} (padicField v))
    (hx : LocalWeil.ExactExpansion (padicField v) (localExactClass F E c v S hS ι)
      (LocalWeil.includeUnitary (padicField v) x)) :
    LocalWeil.ExactExpansion (padicField v)
      (localExactClass F E c v (FiniteRepresentation.twist χ S) hχS ι)
      (LocalWeil.includeUnitary (padicField v)
        (LocalWeil.unitaryTwistLatticeEquiv (padicField v) η hu x)) := by
  rw [localExactClass_twist F E c v S hS ι χ hχS η hη]
  exact Weil.ExactExpansion.unitaryTwist hx η hu

end Langlands.VirtualRepresentation.RelativeGlobal
