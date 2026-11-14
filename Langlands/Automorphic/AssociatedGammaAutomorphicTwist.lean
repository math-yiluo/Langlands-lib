import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.HeckeTwist.FiniteLocalTransport
import Langlands.Automorphic.HeckeTwist.Admissibility
import Langlands.Automorphic.HeckeTwist.ContragredientTwist
import Langlands.Automorphic.HeckeTwist.OperatorTwist
import Langlands.Automorphic.HeckeTwist.DifferentialMultiplier
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Global.Factors.RelativeWeilLocalHecke
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.ArchimedeanCharacterSmoothness
import Langlands.Representation.Classification.SupercuspidalContragredientAux

/-!
# Local and archimedean effect of a Hecke determinant twist on cuspidal pairs

For an actual cuspidal spectral presentation `P` and an arbitrary Hecke character `χ`:

* (A) the local class of the twisted presentation `P.heckeDeterminantTwist χ` at a finite
  place `v` is the character twist of the local class of `P` by the local component `χ_v`;
* (B) if `χ` is trivial on the archimedean ideles, the twist keeps every archimedean
  standard-module parameter;
* (C) twisting a contragredient pair by `χ⁻¹` and `χ` keeps the contragredient relation.
-/

noncomputable section

universe uF uP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F]

local instance automorphicTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance automorphicTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance automorphicTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance automorphicTwistFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance automorphicTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance automorphicTwistLocalGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

/-! ### (A) Local classes of the twisted presentation -/

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)]
variable {r : ℕ} {S : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{uF, uP} S) (χ : HeckeCharacter F)

/-- Twisting the presentation preserves and reflects local irreducibility. -/
theorem heckeDeterminantTwist_localComponent_isIrreducible_iff (v : FinitePlace F) :
    ((P.heckeDeterminantTwist χ).localComponent v).IsIrreducible ↔
      (P.localComponent v).IsIrreducible :=
  (Langlands.isIrreducible_iff_of_equiv
    (P.heckeDeterminantTwistLocalComponentEquiv χ v)).trans
      ((P.localComponent v).heckeDeterminantTwist_isIrreducible_iff χ)

/-- Twisting the presentation preserves and reflects local admissibility. -/
theorem heckeDeterminantTwist_localComponent_isAdmissible_iff (v : FinitePlace F) :
    ((P.heckeDeterminantTwist χ).localComponent v).IsAdmissible ↔
      (P.localComponent v).IsAdmissible :=
  (Langlands.isAdmissible_iff_of_equiv
    (P.heckeDeterminantTwistLocalComponentEquiv χ v)).trans
      ((P.localComponent v).heckeDeterminantTwist_isAdmissible_iff χ)

/-- Irreducible admissible components at every place are kept by the twist. -/
theorem heckeDeterminantTwist_hasIrreducibleAdmissibleComponents
    (h : CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents P) :
    CuspidalPairFunctionalEquation.HasIrreducibleAdmissibleComponents
      (P.heckeDeterminantTwist χ) := fun v =>
  ⟨(P.heckeDeterminantTwist_localComponent_isIrreducible_iff χ v).mpr (h v).1,
    (P.heckeDeterminantTwist_localComponent_isAdmissible_iff χ v).mpr (h v).2⟩

omit [CompactSpace (AdeleQuotient F)] in
/-- On `GL_(r+1)(F_v)`, `χ_v ∘ det` is the local determinant character of `χ`. -/
theorem determinantQuasiCharacter_quasicharacterBase (v : FinitePlace F) :
    Correspondence.determinantQuasiCharacter (CompletionPadic.padicField v) r.succPNat
        (CompletionPadic.quasicharacterBase v (χ.finiteComponent v)) =
      (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom := by
  ext g
  change ((χ.finiteComponent v) (Matrix.GeneralLinearGroup.det g) : ℂ) =
    ((χ.finiteLocalDeterminant (r + 1) v g : ℂˣ) : ℂ)
  rw [HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det]
  rfl

/-- **(A)** The local class of the twisted presentation is the character twist of the
local class of `P` by the local component of `χ`. -/
theorem isCharacterTwist_heckeDeterminantTwist_padicClass (v : FinitePlace F)
    (hI : (P.localComponent v).IsIrreducible) (hA : (P.localComponent v).IsAdmissible)
    (hIχ : ((P.heckeDeterminantTwist χ).localComponent v).IsIrreducible)
    (hAχ : ((P.heckeDeterminantTwist χ).localComponent v).IsAdmissible) :
    Correspondence.IsCharacterTwist (CompletionPadic.padicField v)
      (CompletionPadic.quasicharacterBase v (χ.finiteComponent v))
      ((P.localComponent v).padicClass hI hA)
      (((P.heckeDeterminantTwist χ).localComponent v).padicClass hIχ hAχ) := by
  refine ⟨(P.localComponent v).padicObject hI hA,
    ((P.heckeDeterminantTwist χ).localComponent v).padicObject hIχ hAχ, rfl, rfl, ?_⟩
  change Nonempty ((Langlands.twist
    (Correspondence.determinantQuasiCharacter (CompletionPadic.padicField v) r.succPNat
      (CompletionPadic.quasicharacterBase v (χ.finiteComponent v)))
    (P.localComponent v).representation).Equiv
      ((P.heckeDeterminantTwist χ).localComponent v).representation)
  rw [determinantQuasiCharacter_quasicharacterBase]
  exact ⟨((P.localComponent v).heckeDeterminantTwistRepresentationEquiv χ).trans
    (P.heckeDeterminantTwistLocalComponentEquiv χ v).symm⟩

end CuspidalSpectralPresentation

/-! ### (B) Archimedean parameters under a twist trivial at infinity -/

section Archimedean

variable {n : ℕ}

/-- A Hecke character trivial on the archimedean ideles has trivial archimedean
determinant character. -/
theorem HeckeCharacter.infiniteDeterminantCharacter_eq_one {χ : HeckeCharacter F}
    (hχ : χ.HasPrescribedInfinityComponent 1) (a : InfiniteAdelicGL F n) :
    χ.infiniteDeterminantCharacter n a = 1 := by
  rw [HeckeCharacter.infiniteDeterminantCharacter_apply]
  change χ.onIdeles (AdelicGL.determinant F n (AdelicGL.ofInfinite F n a)) = 1
  rw [AdelicGL.determinant_ofInfinite]
  change χ.atInfinity (Matrix.GeneralLinearGroup.det a) = 1
  rw [hχ]
  rfl

/-- The derivative of a trivial smooth character vanishes. -/
theorem ArchimedeanGL.characterDifferential_eq_zero_of_eq_one
    (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) →* ℂˣ)
    (hc : (fun g => (c g : ℂ)) ∈ ArchimedeanGL.smoothFunctions F n)
    (h1 : ∀ g, c g = 1) (X : ArchimedeanGL.RealLieAlgebra F n) :
    ArchimedeanGL.characterDifferential c hc X = 0 := by
  change (ArchimedeanGL.smoothDifferential F n X
    (ArchimedeanGL.characterFunction c hc)).val 1 = 0
  rw [ArchimedeanGL.smoothDifferential_apply]
  have hconst : ArchimedeanGL.coordinateExtension F n (ArchimedeanGL.characterFunction c hc) =
      fun _ => (1 : ℂ) := by
    funext a
    change ((c _ : ℂˣ) : ℂ) = 1
    rw [h1, Units.val_one]
  rw [hconst]
  simp

/-- The enveloping shift of a Hecke character trivial at infinity is the identity. -/
theorem heckeEnvelopingShift_eq_id {χ : HeckeCharacter F}
    (hχ : χ.HasPrescribedInfinityComponent 1) (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    heckeEnvelopingShift n χ a = a := by
  have hzero : ∀ U : ArchimedeanGL.ComplexLieAlgebra F n,
      ArchimedeanGL.complexCharacterDifferential (χ.infiniteDeterminantCharacter n)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions n) U = 0 := by
    intro U
    induction U using TensorProduct.inductionOn with
    | tmul z X =>
      rw [ArchimedeanGL.complexCharacterDifferential_tmul,
        ArchimedeanGL.characterDifferential_eq_zero_of_eq_one _ _
          (HeckeCharacter.infiniteDeterminantCharacter_eq_one hχ), mul_zero]
    | add U V hU hV => rw [map_add, hU, hV, add_zero]
  have hgen : ∀ U : ArchimedeanGL.ComplexLieAlgebra F n,
      heckeEnvelopingShift n χ (ArchimedeanGL.envelopingGenerator F n U) =
        ArchimedeanGL.envelopingGenerator F n U := by
    intro U
    change ArchimedeanGL.envelopingShift _ _ (ArchimedeanGL.envelopingGenerator F n U) = _
    rw [ArchimedeanGL.envelopingShift_generator, hzero, map_zero, add_zero]
  have hext : heckeEnvelopingShift n χ = AlgHom.id ℂ (ArchimedeanGL.EnvelopingAlgebra F n) :=
    UniversalEnvelopingAlgebra.hom_ext ℂ (LieHom.ext fun U => hgen U)
  rw [hext, AlgHom.id_apply]

namespace OperatorRealization

variable (S : OperatorRealization F n) {χ : HeckeCharacter F}
  (hχ : χ.HasPrescribedInfinityComponent 1)

include hχ in
theorem heckeDeterminantTwistEquiv_compact_of_trivial (k : standardInfiniteCompact F n)
    (f : S.Space) :
    (S.heckeDeterminantTwist χ).compactRepresentation k (S.heckeDeterminantTwistEquiv χ f) =
      S.heckeDeterminantTwistEquiv χ (S.compactRepresentation k f) := by
  have h : ((χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂˣ) : ℂ) = 1 := by
    have h₀ := HeckeCharacter.infiniteDeterminantCharacter_eq_one (n := n) hχ k.val
    rw [HeckeCharacter.infiniteDeterminantCharacter_apply] at h₀
    rw [h₀, Units.val_one]
  refine (S.heckeDeterminantTwistEquiv_compact χ k f).trans ?_
  exact (congrArg (· • S.heckeDeterminantTwistEquiv χ (S.compactRepresentation k f)) h).trans
    (one_smul ℂ _)

include hχ in
theorem heckeDeterminantTwistEquiv_enveloping_of_trivial
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    (S.heckeDeterminantTwist χ).envelopingAction a (S.heckeDeterminantTwistEquiv χ f) =
      S.heckeDeterminantTwistEquiv χ (S.envelopingAction a f) :=
  (S.heckeDeterminantTwistEquiv_differential χ a f).trans
    (congrArg (fun b => S.heckeDeterminantTwistEquiv χ (S.envelopingAction b f))
      (heckeEnvelopingShift_eq_id hχ a))

include hχ in
theorem heckeDeterminantTwist_realPlaceCompact
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    (k : Matrix.unitaryGroup (Fin n) ℝ) (x : S.Space) :
    S.heckeDeterminantTwistEquiv χ (S.realPlaceCompactRepresentation v k x) =
      (S.heckeDeterminantTwist χ).realPlaceCompactRepresentation v k
        (S.heckeDeterminantTwistEquiv χ x) :=
  (S.heckeDeterminantTwistEquiv_compact_of_trivial hχ _ x).symm

include hχ in
theorem heckeDeterminantTwist_complexPlaceCompact
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v})
    (k : Matrix.unitaryGroup (Fin n) ℂ) (x : S.Space) :
    S.heckeDeterminantTwistEquiv χ (S.complexPlaceCompactRepresentation v k x) =
      (S.heckeDeterminantTwist χ).complexPlaceCompactRepresentation v k
        (S.heckeDeterminantTwistEquiv χ x) :=
  (S.heckeDeterminantTwistEquiv_compact_of_trivial hχ _ x).symm

include hχ in
theorem heckeDeterminantTwist_realPlaceLie
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v})
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (x : S.Space) :
    S.heckeDeterminantTwistEquiv χ (S.realPlaceLieAction v X x) =
      (S.heckeDeterminantTwist χ).realPlaceLieAction v X (S.heckeDeterminantTwistEquiv χ x) :=
  (S.heckeDeterminantTwistEquiv_enveloping_of_trivial hχ _ x).symm

include hχ in
theorem heckeDeterminantTwist_complexPlaceLie
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v})
    (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (x : S.Space) :
    S.heckeDeterminantTwistEquiv χ (S.complexPlaceLieAction v X x) =
      (S.heckeDeterminantTwist χ).complexPlaceLieAction v X (S.heckeDeterminantTwistEquiv χ x) :=
  (S.heckeDeterminantTwistEquiv_enveloping_of_trivial hχ _ x).symm

include hχ in
/-- **(B)** A real-place standard-module parameter is kept by a twist trivial at
infinity. -/
theorem HasRealPlaceParameter.heckeDeterminantTwist
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}}
    {ds : List LocalFactor.Archimedean.RealBlock}
    (h : S.HasRealPlaceParameter v ds) :
    (S.heckeDeterminantTwist χ).HasRealPlaceParameter v ds := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  exact ⟨hr, (S.heckeDeterminantTwistEquiv χ).toLinearEquiv.toLinearMap ∘ₗ A,
    (S.heckeDeterminantTwistEquiv χ).injective.comp hA,
    fun k f => ⟨(hK k f).1,
      (congrArg (S.heckeDeterminantTwistEquiv χ) (hK k f).2).trans
        (S.heckeDeterminantTwist_realPlaceCompact hχ v _ _)⟩,
    fun X f => ⟨(hL X f).1,
      (congrArg (S.heckeDeterminantTwistEquiv χ) (hL X f).2).trans
        (S.heckeDeterminantTwist_realPlaceLie hχ v _ _)⟩⟩

include hχ in
/-- **(B)** A complex-place standard-module parameter is kept by a twist trivial at
infinity. -/
theorem HasComplexPlaceParameter.heckeDeterminantTwist
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}}
    {ds : List LocalFactor.Archimedean.ComplexCharacterData}
    (h : S.HasComplexPlaceParameter v ds) :
    (S.heckeDeterminantTwist χ).HasComplexPlaceParameter v ds := by
  obtain ⟨hr, A, hA, hK, hL⟩ := h
  exact ⟨hr, (S.heckeDeterminantTwistEquiv χ).toLinearEquiv.toLinearMap ∘ₗ A,
    (S.heckeDeterminantTwistEquiv χ).injective.comp hA,
    fun k f => ⟨(hK k f).1,
      (congrArg (S.heckeDeterminantTwistEquiv χ) (hK k f).2).trans
        (S.heckeDeterminantTwist_complexPlaceCompact hχ v _ _)⟩,
    fun X f => ⟨(hL X f).1,
      (congrArg (S.heckeDeterminantTwistEquiv χ) (hL X f).2).trans
        (S.heckeDeterminantTwist_complexPlaceLie hχ v _ _)⟩⟩

end OperatorRealization

end Archimedean

/-! ### (C) Contragredients of twisted pairs -/

namespace OperatorRealization

variable {n : ℕ}

/-- Twisting by `χ` and then by `χ⁻¹` returns the original realization. -/
theorem heckeDeterminantTwist_heckeDeterminantTwist_inv (S : OperatorRealization F n)
    (χ : HeckeCharacter F) :
    (S.heckeDeterminantTwist χ).heckeDeterminantTwist χ⁻¹ = S := by
  have hM : ∀ f : StableAutomorphicFunctions F n,
      StableAutomorphicFunctions.heckeDeterminantMultiplier n χ⁻¹
        (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ f) = f := by
    intro f
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousRationalFunctions.toContinuousMap_injective F n
    ext g
    have h1 : ((χ⁻¹.adelicDeterminant n g : ℂˣ) : ℂ) * ((χ.adelicDeterminant n g : ℂˣ) : ℂ) =
        1 := by
      rw [HeckeCharacter.adelicDeterminant_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    change ((χ⁻¹.adelicDeterminant n g : ℂˣ) : ℂ) * (((χ.adelicDeterminant n g : ℂˣ) : ℂ) *
        ContinuousRationalFunctions.evaluate F n f.val.val g) =
      ContinuousRationalFunctions.evaluate F n f.val.val g
    rw [← mul_assoc, h1, one_mul]
  have hsub : ((S.heckeDeterminantTwist χ).heckeDeterminantTwist χ⁻¹).toSubmodule =
      S.toSubmodule := by
    change (S.toSubmodule.map
      (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ).toLinearMap).map
        (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ⁻¹).toLinearMap = _
    rw [← Submodule.map_comp]
    have hid : (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ⁻¹).toLinearMap ∘ₗ
        (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ).toLinearMap =
          LinearMap.id := LinearMap.ext hM
    rw [hid, Submodule.map_id]
  cases S
  cases hS : (OperatorRealization.heckeDeterminantTwist _ χ).heckeDeterminantTwist χ⁻¹
  simp_all

/-- **(C)** If `Td` is a contragredient of `T`, then `Td ⊗ χ⁻¹` is a contragredient of
`T ⊗ χ`. -/
theorem IsContragredientOf.heckeDeterminantTwist_inv {S Sd : OperatorRealization F n}
    (h : Sd.IsContragredientOf S) (χ : HeckeCharacter F) :
    (Sd.heckeDeterminantTwist χ⁻¹).IsContragredientOf (S.heckeDeterminantTwist χ) := by
  apply IsContragredientOf.of_heckeDeterminantTwist
  rw [heckeDeterminantTwist_heckeDeterminantTwist_inv]
  exact h

end OperatorRealization

end Langlands.Automorphic
