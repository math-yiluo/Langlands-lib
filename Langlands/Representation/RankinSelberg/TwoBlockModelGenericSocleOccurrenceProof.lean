import Langlands.Representation.RankinSelberg.TwoBlockModelGenericSocleOccurrenceStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.Representation.Whittaker.FunctionalExactness
import Langlands.Representation.Whittaker.CoefficientMapNonvanishing
import Langlands.Representation.Whittaker.MirabolicFunctionalTransfer
import Langlands.Representation.Induction.Equivalences
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Generic model socle occurrence in normalized upper induction

Induce the block coefficient quotients, and inject induction of the block
socles into that quotient. Extend a nonzero Whittaker functional from this
injected representation. Its coefficient map has nonzero image in the
specified original coefficient model, hence contains the specified least
socle. Restriction to its inverse image gives the actual subquotient.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uG uX uY uZ

namespace ModelSocleOccurrence

/-- Tensoring submodule inclusions over a field is injective: tensor the
linear retractions to obtain a left inverse. -/
theorem tensor_subtype_injective {ι : Type*} {X : ι → Type uX}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (W : ∀ i, Submodule ℂ (X i)) :
    Function.Injective (PiTensorProduct.map (fun i => (W i).subtype)) := by
  refine Function.LeftInverse.injective
    (g := PiTensorProduct.map (fun i => (W i).subtype.leftInverse)) ?_
  intro x
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have h : (fun i => (W i).subtype.leftInverse ∘ₗ (W i).subtype) =
      fun i => LinearMap.id := by
    funext i
    exact LinearMap.leftInverse_comp_of_inj (W i).ker_subtype
  rw [h, PiTensorProduct.map_id, LinearMap.id_apply]

/-- An actual invariant subspace contained in an intertwiner's range is a
quotient of the invariant inverse image. -/
theorem subquotient_of_le_range {G : Type uG} [Group G]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {τ : Representation ℂ G Y}
    (f : ρ.IntertwiningMap τ) (S : Subrepresentation τ) (hS : S ≤ f.range) :
    ∃ A : Subrepresentation ρ,
      ∃ q : A.toRepresentation.IntertwiningMap S.toRepresentation,
        Function.Surjective q := by
  let A : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule.comap f.toLinearMap
      apply_mem_toSubmodule := by
        intro g x hx
        change f (ρ g x) ∈ S.toSubmodule
        rw [f.isIntertwining]
        exact S.apply_mem_toSubmodule g hx }
  let q : A.toRepresentation.IntertwiningMap S.toRepresentation :=
    { toLinearMap := (f.toLinearMap.comp A.toSubmodule.subtype).codRestrict
        S.toSubmodule (fun x => x.property)
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change f (ρ g x.val) = τ g (f x.val)
        exact LinearMap.congr_fun (f.isIntertwining' g) x.val }
  refine ⟨A, q, ?_⟩
  intro s
  obtain ⟨x, hx⟩ := hS s.property
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change f x ∈ S.toSubmodule
  change f x = s.val at hx
  rw [hx]
  exact s.property

/-- A common smooth quotient and a nonzero generic source put the least
coefficient-model subrepresentation in an actual subquotient of the source. -/
theorem subquotient_of_common_quotient
    {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) X}
    {μ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) Y}
    {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) Z}
    {θ : upperUnipotent (n + 1) F →* ℂˣ}
    (hU : Jacquet.Localization.IsLimitOfCompactSubgroups (upperUnipotent (n + 1) F))
    (hθ : IsLocallyConstant (fun u : upperUnipotent (n + 1) F => (θ u : ℂ)))
    (hρ : IsOfWhittakerType n θ ρ) (hμ : IsOfWhittakerType n θ μ)
    (hτ : IsSmooth τ)
    (ell : functionals (upperUnipotent (n + 1) F) θ ρ) (hell : ell.val ≠ 0)
    (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (j : μ.IntertwiningMap τ) (hj : Function.Injective j)
    (S : Subrepresentation (modelRepresentation ρ ell))
    (hS : ∀ R : Subrepresentation (modelRepresentation ρ ell), R ≠ ⊥ → S ≤ R) :
    ∃ A : Subrepresentation μ,
      ∃ r : A.toRepresentation.IntertwiningMap S.toRepresentation,
        Function.Surjective r := by
  obtain ⟨eμ⟩ := hμ.2.2
  let lamμ : functionals (upperUnipotent (n + 1) F) θ μ := eμ.symm 1
  have hlamμ : lamμ.val ≠ 0 := by
    intro hz
    have hz' : lamμ = 0 := Subtype.ext hz
    have hone : (1 : ℂ) = 0 := by
      simpa only [lamμ, LinearEquiv.apply_symm_apply, map_zero] using congrArg eμ hz'
    exact one_ne_zero hone
  obtain ⟨lamτ, hlamτ⟩ := functionalsComap_surjective_of_smooth
    (upperUnipotent (n + 1) F) hU θ hθ j hj hτ lamμ
  have hlamτne : lamτ.val ≠ 0 := by
    intro hz
    apply hlamμ
    have hzero : lamτ = 0 := Subtype.ext hz
    have hzeroμ : lamμ = 0 := by rw [← hlamτ, hzero, map_zero]
    exact congrArg Subtype.val hzeroμ
  have hmodel : coefficientModel ρ ell = coefficientModel τ lamτ :=
    coefficientModel_eq_of_surjective_of_whittakerType hρ q hq ell lamτ hell hlamτne
  have hrestrict : (functionalsComap j lamτ).val ≠ 0 := by
    rw [hlamτ]
    exact hlamμ
  let f : μ.IntertwiningMap (modelRepresentation ρ ell) :=
    coefficientMapCompToSubrepresentation j lamτ (coefficientModel ρ ell)
      (le_of_eq hmodel.symm)
  have hf : f.range ≠ ⊥ :=
    coefficientMapCompToSubrepresentation_range_ne_bot j lamτ
      (coefficientModel ρ ell) (le_of_eq hmodel.symm) hrestrict
  apply subquotient_of_le_range (G := Langlands.GeneralLinear (n + 1) F)
    (X := Y) (Y := (coefficientModel ρ ell).toSubmodule)
    (ρ := μ) (τ := modelRepresentation ρ ell) f S
  exact hS f.range hf

end ModelSocleOccurrence

/-- The specified least generic model socle is an actual subquotient of
normalized induction of the specified block model socles. -/
theorem twoBlockModelGenericSocleOccurrence :
    TwoBlockModelGenericSocleOccurrenceStatement.{uF,uV} := by
  intro p hp F
  let T := F.canonicalTopologicalData
  let := T.topology
  intro ψ t m h V _ _ σ hσ ℓ _
  let : ∀ i, AddCommGroup (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
  intro I ℓI hℓI
  let : AddCommGroup (glCoefficientModel ψ t I ℓI).toSubmodule :=
    (glCoefficientModel ψ t I ℓI).toSubmodule.addCommGroup
  intro Si S hSi hS J
  let := T.generalLinearTopologicalGroup (t + 1)
  let B := succBlockShape m h
  let W : Fin 2 → Type uF :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule
  let τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i) :=
    fun i => glModelRepresentation ψ (m i) (σ i) (ℓ i)
  let K := F.canonicalNormalizedProductInduced B τ
  let q : I.IntertwiningMap K := T.normalizedProductModelMap B σ ℓ
  have hq : Function.Surjective q :=
    T.normalizedProductModelMap_surjective B σ (fun i => (hσ i).1.1) ℓ
  let incl : ∀ i, (Si i).toRepresentation.IntertwiningMap (τ i) :=
    fun i => { toLinearMap := (Si i).toSubmodule.subtype
               isIntertwining' := fun _ => rfl }
  let j : J.IntertwiningMap K := T.normalizedProductInducedMap B incl
  have htensor : Function.Injective (FiniteTensor.externalMap incl) := by
    change Function.Injective (PiTensorProduct.map (fun i => (Si i).toSubmodule.subtype))
    exact ModelSocleOccurrence.tensor_subtype_injective (X := W)
      (fun i => (Si i).toSubmodule)
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply htensor
    exact congrArg (fun z => z.1.1 g) hxy
  have hI : IsOfWhittakerType t (standardCharacter ψ t) I :=
    normalizedProductWhittakerType p F ψ t 2 m h (W := V) σ hσ
  have hJ : IsOfWhittakerType t (standardCharacter ψ t) J :=
    normalizedProductWhittakerType p F ψ t 2 m h
      (W := fun i => (Si i).toSubmodule) (fun i => (Si i).toRepresentation)
      (fun i => (hSi i).2.2.2)
  have hθ : IsLocallyConstant
      (fun u : upperUnipotent (t + 1) F.Carrier => (standardCharacter ψ t u : ℂ)) :=
    character_isLocallyConstant_of_hasFunctional _ _ _ hI.1.1 ⟨ℓI, hℓI⟩
  have hK : IsSmooth K := T.isSmooth_normalizedProductInduced B τ
  exact ModelSocleOccurrence.subquotient_of_common_quotient
    (upperUnipotent_isLimitOfCompactSubgroups F T (t + 1)) hθ hI hJ hK
    ℓI hℓI q hq j hj S hS.2.2.1

end Langlands.RankinSelberg
