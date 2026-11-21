import Langlands.Automorphic.IndexedHilbertPlaceFixedLevel
import Langlands.Automorphic.HilbertPlaceMixedWhittaker
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerPlaces

/-! # Indexed archimedean Whittaker restriction comparison -/

noncomputable section
open NumberField
open scoped Classical CategoryTheory.MonObj ContDiff Manifold Matrix.Norms.Operator TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
set_option Elab.async false

namespace Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion

open Langlands.Global ArchimedeanGL RankinSelbergGlobal OperatorDeterminantSlice
open RankinSelbergGlobal.ArchimedeanWhittakerRegularity
open Langlands.Archimedean MixedSmooth InfinitePlaceFamily SmoothInvariantSubspace
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean Langlands.HarishChandraSchwartz
open Langlands.Global.CuspidalPairFunctionalEquation
universe u uV uX uE uZ
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] regSchemeAffine regSchemeSmooth

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

private theorem compare_on_component
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
    (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
    (hcomm : ∀ g l x, π g (σ l x) = σ l (π g x))
    (U : OpenSubgroup (FiniteAdelicGL F (r + 1))) (hU : IsCompact (U : Set (FiniteAdelicGL F (r + 1))))
    (j : V →ₗ[ℂ] E) (W : Submodule ℂ V)
    {𝕜 : Type} [RCLike 𝕜] (hUnique : UnitaryWhittakerMultiplicityOneOver.{uE} 𝕜)
    (i : Langlands.GeneralLinear (r + 1) 𝕜 →* ArchimedeanGL F (r + 1))
    (k : Representation ℂ (Matrix.unitaryGroup (Fin (r + 1)) 𝕜) V)
    (d : (ℂ ⊗[ℝ] Matrix (Fin (r + 1)) (Fin (r + 1)) 𝕜) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hR : HasPlaceFixedSmoothRealization (𝔞 := ArchimedeanMatrix F (r + 1)) π σ
      i j Unitary.toUnits k d hcomm U.toSubgroup W)
    (j₀ : V →ₗ[ℂ] Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm)
    (hj₀ : ∀ v, (j₀ v).val.val = j v)
    (ψ : AddChar (Adeles F) ℂ) (ψv : UnitaryAdditiveCharacter 𝕜)
    (ℓ₀ ℓ₁ : Vectors (A := ArchimedeanMatrix F (r + 1)) σ π hcomm →ₗ[ℂ] ℂ)
    (h₀ : IsMixedWhittakerFunctional (r := r) ψ σ π hcomm ℓ₀)
    (h₁ : IsMixedWhittakerFunctional (r := r) ψ σ π hcomm ℓ₁)
    (hc₀ : ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) 𝕜, ∀ w,
      ℓ₀ (archimedeanRepresentation σ π hcomm (i u.val) w) =
        (Langlands.Whittaker.standardCharacter ψv r u : ℂ) * ℓ₀ w)
    (hc₁ : ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) 𝕜, ∀ w,
      ℓ₁ (archimedeanRepresentation σ π hcomm (i u.val) w) =
        (Langlands.Whittaker.standardCharacter ψv r u : ℂ) * ℓ₁ w)
    (hn : ℓ₀.comp (j₀.comp W.subtype) ≠ 0) :
    ∃ c : ℂ, ℓ₁.comp (j₀.comp W.subtype) = c • ℓ₀.comp (j₀.comp W.subtype) := by
  let J : CompactOpenSubgroup (FiniteAdelicGL F (r + 1)) := ⟨U, hU⟩
  obtain ⟨f₀, hf₀, he₀⟩ := h₀.1 J
  obtain ⟨f₁, hf₁, he₁⟩ := h₁.1 J
  exact proportional_mixedRestrictions_of_placeFixedSmoothRealization σ π hcomm U j W r
    hUnique i k d hR j₀ hj₀ ψv ℓ₀ ℓ₁ f₀ f₁ hf₀ hf₁ he₀ he₁ hc₀ hc₁ hn

variable {X : Type uX}
  {ρ : Representation ℂ (FiniteAdelicGL F (r + 1)) V}
  {κ : Representation ℂ (standardInfiniteCompact F (r + 1)) V} {D : X → Module.End ℂ V}
  {b : OperatorUnitaryFormCore ρ κ D} (B : AdelicCompletion b)
  (d : ∀ i : Index F, Lie (r + 1) i →ₗ⁅ℂ⁆ Module.End ℂ V)

local notation "R∞" => B.action.comp (infiniteCoordinateInclusion F (r + 1))
local notation "Rf" => B.action.comp (ContinuousMonoidHom.toMonoidHom (AdelicGL.ofFinite F (r + 1)))
local notation "cm" => coordinateActions_commute B.action
local notation "Y" => Vectors (A := ArchimedeanMatrix F (r + 1)) Rf R∞ cm

/-- Local unitary uniqueness compares two mixed Whittaker functionals on an indexed
component with its fixed-level Hilbert realization. -/
theorem proportional_mixedRestrictions_of_indexedPlace
    (hUnique : UnitaryWhittakerMultiplicityOneStatement.{uV}) (i : Index F)
    (U : OpenSubgroup (FiniteAdelicGL F (r + 1))) (hU : IsCompact (U : Set (FiniteAdelicGL F (r + 1))))
    (W : Submodule ℂ V) (hR : B.HasIndexedPlaceFixedSmoothRealization d i U.toSubgroup W)
    (j : V →ₗ[ℂ] Y) (hj : ∀ v, (j v).val.val = b.toHilbert v)
    (ψ : UnitaryAdditiveCharacter (Adeles F)) (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ℓ₀ ℓ₁ : Y →ₗ[ℂ] ℂ)
    (h₀ : IsMixedWhittakerFunctional (r := r) ψ.complex Rf R∞ cm ℓ₀)
    (h₁ : IsMixedWhittakerFunctional (r := r) ψ.complex Rf R∞ cm ℓ₁)
    (hn : ℓ₀.comp (j.comp W.subtype) ≠ 0) :
    ∃ c : ℂ, ℓ₁.comp (j.comp W.subtype) = c • ℓ₀.comp (j.comp W.subtype) := by
  cases i with
  | inl w =>
    let c : ℝˣ := Classical.choose (exists_isRealAdditiveComponent ψ hψ w)
    have hc := Classical.choose_spec (exists_isRealAdditiveComponent ψ hψ w)
    exact compare_on_component (F := F) (r := r) (E := b.HilbertCompletion) (𝕜 := ℝ)
      Rf R∞ cm U hU b.toHilbert W hUnique.1 (realPlaceGL F (r + 1) w)
      (κ.comp (compactInclusion _ (.inl w)).toMonoidHom) (d (.inl w)) hR j hj
      ψ.complex (realScaledCharacter c) ℓ₀ ℓ₁ h₀ h₁
      (mixedWhittaker_realPlace Rf R∞ cm ψ ℓ₀ h₀ w c hc)
      (mixedWhittaker_realPlace Rf R∞ cm ψ ℓ₁ h₁ w c hc) hn
  | inr w =>
    let c : ℂˣ := Classical.choose (exists_isComplexAdditiveComponent ψ hψ w)
    have hc := Classical.choose_spec (exists_isComplexAdditiveComponent ψ hψ w)
    exact compare_on_component (F := F) (r := r) (E := b.HilbertCompletion) (𝕜 := ℂ)
      Rf R∞ cm U hU b.toHilbert W hUnique.2 (complexPlaceGL F (r + 1) w)
      (κ.comp (compactInclusion _ (.inr w)).toMonoidHom) (d (.inr w)) hR j hj
      ψ.complex (complexScaledCharacter c) ℓ₀ ℓ₁ h₀ h₁
      (mixedWhittaker_complexPlace Rf R∞ cm ψ ℓ₀ h₀ w c hc)
      (mixedWhittaker_complexPlace Rf R∞ cm ψ ℓ₁ h₁ w c hc) hn

/-- A comparison on the image of a supplied slice gives proportionality in its
original variable. -/
theorem proportional_mixedRestrictions_of_indexedSlice
    (hUnique : UnitaryWhittakerMultiplicityOneStatement.{uV}) (i : Index F)
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z] (L : Z →ₗ[ℂ] V)
    (hR : ∃ U : OpenSubgroup (FiniteAdelicGL F (r + 1)),
      IsCompact (U : Set (FiniteAdelicGL F (r + 1))) ∧
      B.HasIndexedPlaceFixedSmoothRealization d i U.toSubgroup (LinearMap.range L))
    (j : V →ₗ[ℂ] Y) (hj : ∀ v, (j v).val.val = b.toHilbert v)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (ℓ₀ ℓ₁ : Y →ₗ[ℂ] ℂ)
    (h₀ : IsMixedWhittakerFunctional (r := r) ψ Rf R∞ cm ℓ₀)
    (h₁ : IsMixedWhittakerFunctional (r := r) ψ Rf R∞ cm ℓ₁)
    (hn : ℓ₀.comp (j.comp L) ≠ 0) :
    ∃ c : ℂ, ℓ₁.comp (j.comp L) = c • ℓ₀.comp (j.comp L) := by
  let a : Z →ₗ[ℂ] LinearMap.range L := L.codRestrict _ (LinearMap.mem_range_self L)
  have hn' : ℓ₀.comp (j.comp (LinearMap.range L).subtype) ≠ 0 := by
    intro h
    apply hn
    exact LinearMap.ext fun x => LinearMap.congr_fun h (a x)
  let U := Classical.choose hR
  have h := Classical.choose_spec hR
  let ψ₀ := UnitaryAdditiveCharacter.ofComplex ψ hψ.1 hψ.2.1 hψ.2.2.2
  have hdiag (x : F) : ψ₀ (diagonal F x) = 1 := Subtype.ext (hψ.2.2.1 x)
  have hcompare := B.proportional_mixedRestrictions_of_indexedPlace d hUnique i U h.1
    (LinearMap.range L) h.2 j hj ψ₀ hdiag ℓ₀ ℓ₁ h₀ h₁ hn'
  exact ⟨Classical.choose hcompare,
    LinearMap.ext fun x => LinearMap.congr_fun (Classical.choose_spec hcompare) (a x)⟩

/-- A specified algebraic slice has the corresponding comparison of mixed
Whittaker functionals for every standard adelic additive character. -/
def HasIndexedWhittakerSliceComparison {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
    (L : Z →ₗ[ℂ] V) : Prop :=
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (j : V →ₗ[ℂ] Y), (∀ v, (j v).val.val = b.toHilbert v) →
    ∀ (ℓ₀ ℓ₁ : Y →ₗ[ℂ] ℂ),
      IsMixedWhittakerFunctional (r := r) ψ Rf R∞ cm ℓ₀ →
      IsMixedWhittakerFunctional (r := r) ψ Rf R∞ cm ℓ₁ →
      ℓ₀.comp (j.comp L) ≠ 0 → ∃ c : ℂ, ℓ₁.comp (j.comp L) = c • ℓ₀.comp (j.comp L)

/-- A fixed-level realization for each nonzero slice restriction suffices
for the mixed Whittaker comparison on that slice. -/
theorem hasIndexedWhittakerSliceComparison_of_fixedLevel
    (hUnique : UnitaryWhittakerMultiplicityOneStatement.{uV}) (i : Index F)
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z] (L : Z →ₗ[ℂ] V)
    (hR : (∃ f : V →ₗ[ℂ] ℂ, f.comp L ≠ 0) →
      ∃ U : OpenSubgroup (FiniteAdelicGL F (r + 1)),
        IsCompact (U : Set (FiniteAdelicGL F (r + 1))) ∧
        B.HasIndexedPlaceFixedSmoothRealization d i U.toSubgroup (LinearMap.range L)) :
    B.HasIndexedWhittakerSliceComparison L := by
  intro ψ hψ j hj ℓ₀ ℓ₁ h₀ h₁ hn
  have hs : ∃ f : V →ₗ[ℂ] ℂ, f.comp L ≠ 0 := ⟨ℓ₀.comp j, hn⟩
  exact B.proportional_mixedRestrictions_of_indexedSlice d hUnique i L (hR hs)
    j hj ψ hψ ℓ₀ ℓ₁ h₀ h₁ hn

end Langlands.Automorphic.OperatorUnitaryFormCore.AdelicCompletion
