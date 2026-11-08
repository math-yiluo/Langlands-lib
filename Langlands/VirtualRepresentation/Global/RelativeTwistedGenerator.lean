import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Global.Factors.RelativeLocalOperationTransport
import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.ClassField.Global.LocalRelativeWeilTransferStatement
import Langlands.Global.FiniteAdelicGL.Determinant

/-! # Actual relative witnessed generators under unitary Hecke twisting -/

noncomputable section

universe uF uW uP

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic

variable {F E : Type uF} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] {c : FundamentalClass.ClassFamily.{uF}}
  {v : FinitePlace F}

/-- The two inverse conventions cancel in the actual local character restriction. -/
theorem reciprocityCharacter_comp_localMap
    (Ω : HeckeCharacter F)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : HasLocalTransferReciprocity v ι)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e)
    (χ : Correspondence.QuasiCharacter (padicField v))
    (hΩv : ∀ a : (FiniteCompletion F v)ˣ, Ω.finiteComponent v a = χ a) :
    (reciprocityCharacter c F E Ω).comp ι.toMonoidHom =
      (LocalFactor.RankOne.weilCharacter (padicField v) e χ).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change (Ω (transfer c F E (ι g)))⁻¹ = _
  rw [hι e he g, map_inv, inv_inv]
  exact hΩv _

theorem norm_reciprocityCharacter_of_isUnitary
    (Ω : HeckeCharacter F) (hΩ : Ω.IsUnitary) (g : RelativeWeilGroup c F E) :
    ‖(reciprocityCharacter c F E Ω g : ℂ)‖ = 1 := by
  change ‖(((Ω (transfer c F E g))⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, hΩ _, inv_one]

end Langlands.ClassField.Global.RelativeWeilGroup

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Automorphic

variable {F E : Type uF} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  {c : FundamentalClass.ClassFamily.{uF}} {v : FinitePlace F}

local instance twistRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance twistContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance twistSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance twistFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance twistLocalSpaceAddCommGroup {n : ℕ} (S : LocalRealization F n v) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace WitnessedGenerator

variable (d : WitnessedGenerator.{uF, uW, uP} F E c v)
  (Ω : HeckeCharacter F)
  (χ : Correspondence.QuasiCharacter (padicField v))
  (hΩv : ∀ a : (FiniteCompletion F v)ˣ, Ω.finiteComponent v a = χ a)
  (T : CuspidalOperatorRealization F d.rankIndex)
  (P : CuspidalSpectralPresentation.{uF, uP} T)
  (hP : d.presentation.IsDeterminantMultiple Ω P)

set_option maxHeartbeats 800000 in
/-- The prescribed local component gives exactly the target's determinant twist. -/
def determinantMultipleLocalEquiv :
    letI := (padicField v).canonicalTopologicalData.topology
    (Langlands.twist
      (χ.toMonoidHom.comp GeneralLinear.determinant)
      (d.presentation.localComponent v).representation).Equiv
      (P.localComponent v).representation := by
  let ψ : FiniteLocalGL F (d.rankIndex + 1) v →* ℂˣ :=
    (Ω.finiteLocalDeterminant (d.rankIndex + 1) v).toMonoidHom
  let := (padicField v).canonicalTopologicalData.topology
  have hc : ψ = χ.toMonoidHom.comp GeneralLinear.determinant := by
    apply MonoidHom.ext
    intro g
    exact (HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det Ω _ v g).trans (hΩv _)
  change (Langlands.twist (χ.toMonoidHom.comp GeneralLinear.determinant) _).Equiv _
  rw [← hc]
  exact Classical.choice (hP.2.1 v)

include Ω χ hΩv hP

theorem determinantMultipleLocal_irreducible :
    (P.localComponent v).IsIrreducible :=
  (Langlands.isIrreducible_iff_of_equiv
    (d.determinantMultipleLocalEquiv Ω χ hΩv T P hP)).mp
      ((Langlands.isIrreducible_twist_iff _ _).mpr d.local_irreducible)

theorem determinantMultipleLocal_admissible :
    (P.localComponent v).IsAdmissible := by
  let K := padicField v
  let := K.canonicalTopologicalData.topology
  let := K.canonicalGeneralLinearTopology (d.rankIndex + 1)
  let := K.canonicalTopologicalData.generalLinearTopologicalGroup (d.rankIndex + 1)
  have hker :=
    Correspondence.isOpen_ker_determinantQuasiCharacter K d.rankIndex.succPNat χ
  apply (P.localComponent v).isAdmissible_canonical_iff.mp
  exact Langlands.isAdmissible_of_equiv
    (d.determinantMultipleLocalEquiv Ω χ hΩv T P hP)
    ((Langlands.isAdmissible_twist_iff
      (Correspondence.determinantQuasiCharacter K d.rankIndex.succPNat χ) _ hker).mpr
      ((d.presentation.localComponent v).isAdmissible_canonical_iff.mpr
        d.local_admissible))

theorem determinantMultipleLocal_support
    (hu : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v)
      ((P.localComponent v).padicObject
        (d.determinantMultipleLocal_irreducible Ω χ hΩv T P hP)
        (d.determinantMultipleLocal_admissible Ω χ hΩv T P hP)).obj
      (PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv
        (padicField v) χ hu d.automorphicElement) := by
  let K := padicField v
  let := K.canonicalTopologicalData.topology
  let := K.canonicalGeneralLinearTopology (d.rankIndex + 1)
  let := K.canonicalTopologicalData.generalLinearTopologicalGroup (d.rankIndex + 1)
  have hs := PadicSupercuspidal.isUnitaryLatticeSupport_characterTwist
    K d.automorphic_support χ hu
  exact hs.of_iso (SmoothRep.mkIso
    (d.determinantMultipleLocalEquiv Ω χ hΩv T P hP))

/-- A complete twisted generator, with the same characterized local map. -/
def heckeTwist
    (hΩ : Ω.IsUnitary)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e)
    (hu : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (hι : RelativeWeilGroup.HasLocalTransferReciprocity v d.localMap)
    (hassoc : RelativeWeilGroup.IsWeaklyAssociated
      (FiniteRepresentation.twist (RelativeWeilGroup.reciprocityCharacter c F E Ω) d.weil)
      P.spectralSystem) : WitnessedGenerator.{uF, uW, uP} F E c v where
  rankIndex := d.rankIndex
  weil := FiniteRepresentation.twist (RelativeWeilGroup.reciprocityCharacter c F E Ω) d.weil
  weil_irreducible :=
    (Langlands.isIrreducible_twist_iff _ _).mpr d.weil_irreducible
  weil_unitary :=
    (FiniteRepresentation.unitaryTwisting _ _ _
      (RelativeWeilGroup.norm_reciprocityCharacter_of_isUnitary Ω hΩ)).mpr d.weil_unitary
  cuspidal := T
  presentation := P
  associated := hassoc
  placeOver := d.placeOver
  reciprocity := d.reciprocity
  localMap := d.localMap
  localMap_spec := d.localMap_spec
  local_irreducible := d.determinantMultipleLocal_irreducible Ω χ hΩv T P hP
  local_admissible := d.determinantMultipleLocal_admissible Ω χ hΩv T P hP
  weilElement := LocalWeil.unitaryFieldCharacterTwistLatticeEquiv
    (padicField v) e χ hu d.weilElement
  weil_effective :=
    (Weil.effective_unitaryTwist_iff _ _ _).mpr d.weil_effective
  weil_expansion := localExactExpansion_twist F E c v d.weil d.associated.1
    d.localMap (RelativeWeilGroup.reciprocityCharacter c F E Ω) hassoc.1
    (LocalFactor.RankOne.weilCharacter (padicField v) e χ)
    (RelativeWeilGroup.reciprocityCharacter_comp_localMap Ω d.localMap hι e he χ hΩv)
    (LocalWeil.norm_weilCharacter_eq_one (padicField v) e χ hu)
    d.weilElement d.weil_expansion
  automorphicElement := PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv
    (padicField v) χ hu d.automorphicElement
  automorphic_support := d.determinantMultipleLocal_support Ω χ hΩv T P hP hu

end WitnessedGenerator

end Langlands.VirtualRepresentation.RelativeGlobal
