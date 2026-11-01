import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Whittaker.SurjectiveCoefficientTransport
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters

/-! # Actual induced quotients onto block coefficient models -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Whittaker

universe uR uG uV uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  {W : Type uW} [AddCommGroup W] [Module R W]
  {N : Subgroup G} {θ : N →* Rˣ}
  {ρ : Representation R G V} {σ : Representation R G W}

/-- A surjective intertwiner identifies the actual coefficient images of a
functional and its pullback. -/
theorem coefficientModel_functionalsComap (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) (ℓ : functionals N θ σ) :
    coefficientModel ρ (functionalsComap f ℓ) = coefficientModel σ ℓ := by
  apply Subrepresentation.toSubmodule_injective
  ext a
  change (∃ v, coefficientMap ρ (functionalsComap f ℓ) v = a) ↔
    ∃ w, coefficientMap σ ℓ w = a
  have hcoeff (v : V) :
      coefficientMap ρ (functionalsComap f ℓ) v = coefficientMap σ ℓ (f v) := by
    apply Subtype.ext
    funext g
    exact coefficient_functionalsComap f ℓ v g
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨f v, (hcoeff v).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨v, hcoeff v⟩

end Langlands.Whittaker

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- The actual normalized parabolic map is surjective for smooth endpoints
in independent carrier universes. -/
theorem normalizedParabolicInducedMap_surjective {n : ℕ} (B : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (τ : Representation ℂ (B.Levi F.Carrier) W)
    (hσ : letI := T.topology; IsSmooth σ)
    (hτ : letI := T.topology; IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    letI := T.topology
    Function.Surjective (T.normalizedParabolicInducedMap B f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearT2Space n
  let χ := B.inflateCharacter (T.leviHalfCharacter B)
  apply Induction.smoothInductionSurjectivity (GeneralLinear n F.Carrier)
  · intro K
    let L := T.generalLinearCompactOpen n K (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L.1, L.2.1, L.2.2⟩
  · exact B.isClosed_parabolic F.Carrier
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous hσ)
  · exact (isSmooth_twist_iff χ.toMonoidHom _ χ.isOpen_ker).mpr
      (isSmooth_comp (B.leviProjection F.Carrier)
        (B.leviProjectionContinuous F.Carrier).continuous hτ)
  · exact hf

/-- Factorwise surjective smooth block maps give a surjective actual
normalized product map, with independent source and target universes. -/
theorem normalizedProductInducedMap_surjective {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hσ : letI := T.topology; ∀ i, IsSmooth (σ i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i))
    (f : ∀ i, (σ i).IntertwiningMap (τ i)) (hf : ∀ i, Function.Surjective (f i)) :
    letI := T.topology
    Function.Surjective (T.normalizedProductInducedMap B f) := by
  let := T.topology
  exact T.normalizedParabolicInducedMap_surjective B
    (B.blockTensor σ) (B.blockTensor τ)
    (FiniteTensor.isSmooth_external σ hσ) (FiniteTensor.isSmooth_external τ hτ)
    (FiniteTensor.externalMap f)
    (FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _ f hf)

/-- The actual normalized product map from a block family to its specified
coefficient-image family. -/
def normalizedProductModelMap {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    {N : ∀ i, Subgroup (GeneralLinear (B.size i) F.Carrier)}
    {θ : ∀ i, N i →* ℂˣ}
    (ℓ : ∀ i, Whittaker.functionals (N i) (θ i) (σ i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).IntertwiningMap
      (T.normalizedProductInduced B
        (V := fun i => (Whittaker.coefficientModel (σ i) (ℓ i)).toSubmodule)
        (fun i => Whittaker.modelRepresentation (σ i) (ℓ i))) := by
  let := T.topology
  let W : Fin B.length → Type uF :=
    fun i => (Whittaker.coefficientModel (σ i) (ℓ i)).toSubmodule
  let : ∀ i, AddCommGroup (W i) := fun i => inferInstance
  let : ∀ i, Module ℂ (W i) := fun i => inferInstance
  let τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i) :=
    fun i => Whittaker.modelRepresentation (σ i) (ℓ i)
  let f : ∀ i, (σ i).IntertwiningMap (τ i) :=
    fun i => Whittaker.modelMap (σ i) (ℓ i)
  exact T.normalizedProductInducedMap B (V := V) (W := W) (σ := σ) (τ := τ) f

/-- Normalized induction of the actual block coefficient quotient maps is a
surjection; neither the originals nor their coefficient maps need be injective. -/
theorem normalizedProductModelMap_surjective {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (hσ : letI := T.topology; ∀ i, IsSmooth (σ i))
    {N : ∀ i, Subgroup (GeneralLinear (B.size i) F.Carrier)}
    {θ : ∀ i, N i →* ℂˣ}
    (ℓ : ∀ i, Whittaker.functionals (N i) (θ i) (σ i)) :
    letI := T.topology
    Function.Surjective (T.normalizedProductModelMap B σ ℓ) := by
  let := T.topology
  let W : Fin B.length → Type uF :=
    fun i => (Whittaker.coefficientModel (σ i) (ℓ i)).toSubmodule
  let : ∀ i, AddCommGroup (W i) := fun i => inferInstance
  let : ∀ i, Module ℂ (W i) := fun i => inferInstance
  let τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i) :=
    fun i => Whittaker.modelRepresentation (σ i) (ℓ i)
  let f : ∀ i, (σ i).IntertwiningMap (τ i) :=
    fun i => Whittaker.modelMap (σ i) (ℓ i)
  have hτ : ∀ i, IsSmooth (τ i) := by
    intro i
    exact Whittaker.model_isSmooth (σ i) (hσ i) (ℓ i)
  have hf : ∀ i, Function.Surjective (f i) := by
    intro i
    exact Whittaker.modelMap_surjective (σ i) (ℓ i)
  exact T.normalizedParabolicInducedMap_surjective B
    (B.blockTensor σ) (B.blockTensor τ)
    (FiniteTensor.isSmooth_external σ hσ) (FiniteTensor.isSmooth_external τ hτ)
    (FiniteTensor.externalMap f)
    (FiniteTensor.externalMapSurjectivity ℂ _ _ _ _ _ _ f hf)

end Langlands.PadicField.TopologicalData

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

/-- Full Whittaker type on the source identifies the model of every nonzero
source functional with that of a specified nonzero quotient functional. -/
theorem coefficientModel_eq_of_surjective_of_whittakerType
    (hρ : IsOfWhittakerType n θ ρ)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ ρ)
    (ℓ' : functionals (upperUnipotent (n + 1) F) θ σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) :
    coefficientModel ρ ℓ = coefficientModel σ ℓ' :=
  (coefficientModel_eq_of_whittakerType hρ hℓ
    (functionalsComap_ne_zero f hf ℓ' hℓ')).trans
      (coefficientModel_functionalsComap f hf ℓ')

end Langlands.RankinSelberg
