import Langlands.BaseChange.Norm
import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Twisted characters, σ-lifts and Shintani lifts for `GL_n` over a cyclic algebra

After Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
caractéristique non nulle* (2011), Chapter II, §II.1.3 and §§II.2.7–II.2.9.

* Generic part, imported from `Langlands.BaseChange.TwistedCharacter.Basic`: for a locally
  profinite group `G` and an admissible representation `ρ`, the twisted character
  `φ ↦ trace(ρ(φ) ∘ A)` of an endomorphism `A` (`twistedDistribution`), its local values
  (`HasTwistedCharacterValue`) and their elementary lemmas.
* `GL_n` part, for a topological field `F`, a commutative topological `F`-algebra `E` and
  `σ : E ≃ₐ[F] E`: isomorphisms `A` of a representation `τ` of `GL_n(E)` onto
  `τ^σ = τ ∘ entrywiseAut σ n` (`SigmaIntertwiner`), σ-stability (`IsSigmaStable`), the identity
  "à la Shintani" between twisted and ordinary character values (`IsShintaniLift`) and the
  σ-lift relation through concordant test functions (`IsSigmaLift`).
* The topological properties of `GL_n(E)` for a finite algebra `E` over a nonarchimedean
  local field with its module topology (lemma 9), as explicit theorems, not instances.

Every Haar measure is an explicit, universally quantified argument; none is chosen here.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Langlands.JacquetLanglands

universe uF uE uV uW

/-! ## Topology of `GL_n(E)` for a finite algebra over a nonarchimedean local field -/

section Topology

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : Type uE) [CommRing E] [Algebra F E] [Module.Finite F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E]

include F

/-- The coordinate isomorphism of `Module.finBasis F E` is a homeomorphism for the module
topology. -/
def finiteCoordinateHomeomorph : E ≃ₜ (Fin (Module.finrank F E) → F) :=
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  let e := (Module.finBasis F E).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

omit [IsTopologicalRing E] in
/-- `E` is Hausdorff. -/
theorem finiteAlgebra_t2Space : T2Space E := by
  have := LocalFieldTopology.t2Space F
  exact (finiteCoordinateHomeomorph F E).isEmbedding.t2Space

omit [IsTopologicalRing E] in
/-- `E` is locally compact. -/
theorem finiteAlgebra_locallyCompactSpace : LocallyCompactSpace E :=
  (finiteCoordinateHomeomorph F E).isClosedEmbedding.locallyCompactSpace

omit [IsTopologicalRing E] in
/-- `E` is totally disconnected. -/
theorem finiteAlgebra_totallyDisconnectedSpace : TotallyDisconnectedSpace E := by
  have := LocalFieldTopology.totallyDisconnectedSpace F
  exact (finiteCoordinateHomeomorph F E).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

variable (n : ℕ)

omit [IsTopologicalRing E] in
/-- `GL_n(E)` is Hausdorff (lemma 9). -/
theorem generalLinear_t2Space_of_finite : T2Space (GeneralLinear n E) := by
  have := finiteAlgebra_t2Space F E
  infer_instance

/-- `GL_n(E)` is locally compact (lemma 9). -/
theorem generalLinear_locallyCompactSpace_of_finite :
    LocallyCompactSpace (GeneralLinear n E) := by
  have := finiteAlgebra_t2Space F E
  have := finiteAlgebra_locallyCompactSpace F E
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  infer_instance

omit [IsTopologicalRing E] in
/-- `GL_n(E)` is totally disconnected (lemma 9). -/
theorem generalLinear_totallyDisconnectedSpace_of_finite :
    TotallyDisconnectedSpace (GeneralLinear n E) := by
  have := finiteAlgebra_totallyDisconnectedSpace F E
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → E))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end Topology

/-! ## σ-stable representations of `GL_n(E)` -/

section SigmaStable

variable {F : Type uF} [CommRing F] {E : Type uE} [CommRing E] [Algebra F E]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The isomorphisms `A` of `τ` onto `τ^σ : g ↦ τ(g^σ)`: linear automorphisms `A` of `W` with
`A ∘ τ(g) = τ(g^σ) ∘ A` for every `g` (Henniart–Lemaire II.1.3, printed p. 56; II.2.7, printed
p. 67). -/
abbrev SigmaIntertwiner (σ : E ≃ₐ[F] E) (n : ℕ) (τ : Representation ℂ (GeneralLinear n E) W) :=
  Representation.Equiv τ (τ.comp (entrywiseAut σ n).toMonoidHom)

/-- The representation `τ` is σ-stable: `τ ≅ τ^σ` (Henniart–Lemaire II.1.3, II.2.7). -/
def IsSigmaStable (σ : E ≃ₐ[F] E) (n : ℕ) (τ : Representation ℂ (GeneralLinear n E) W) : Prop :=
  Nonempty (SigmaIntertwiner σ n τ)

/-- The defining relation `A ∘ τ(g) = τ(g^σ) ∘ A` of a σ-intertwiner. -/
theorem SigmaIntertwiner.comp_apply_eq {σ : E ≃ₐ[F] E} {n : ℕ}
    {τ : Representation ℂ (GeneralLinear n E) W} (A : SigmaIntertwiner σ n τ)
    (g : GeneralLinear n E) :
    A.toLinearMap ∘ₗ τ g = τ (entrywiseAut σ n g) ∘ₗ A.toLinearMap :=
  A.isIntertwining' g

end SigmaStable

/-! ## Shintani lifts and σ-lifts -/

section Lift

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type uE} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ}
  [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [TotallyDisconnectedSpace (GeneralLinear n F)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The identity "à la Shintani" `Θ^A_τ(δ) = c Θ_π(γ)` (Henniart–Lemaire II.2.9, printed p. 69;
II.1.3, printed p. 57): `c ≠ 0`, and for every `δ ∈ GL_n(E)` associated with a regular semisimple
`γ ∈ GL_n(F)`, the character of `π` has a value `a` at `γ` and the twisted character of `τ` and
`A` has the value `c * a` at `δ`. -/
def IsShintaniLift (σ : E ≃ₐ[F] E) (l : ℕ) (π : Representation ℂ (GeneralLinear n F) V)
    (hπ : IsAdmissible π) (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ)
    (A : SigmaIntertwiner σ n τ) (c : ℂ) : Prop :=
  c ≠ 0 ∧ ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F),
    IsNormAssociated σ l δ γ → IsRegularSemisimple γ →
      ∃ a : ℂ, HasCharacterValue π hπ γ a ∧ HasTwistedCharacterValue τ hτ A.toLinearMap δ (c * a)

/-- `τ` is a σ-lift ("σ-relèvement") of `π` with constant `c` (Henniart–Lemaire II.2.7,
Définition, printed p. 67): `c ≠ 0`, and for all Haar measures `μF` on `GL_n(F)` and `μE` on
`GL_n(E)` and all concordant test functions `φ` and `f`, `Θ^A_τ(φ) = c Θ_π(f)`. -/
def IsSigmaLift (σ : E ≃ₐ[F] E) (l : ℕ) (π : Representation ℂ (GeneralLinear n F) V)
    (hπ : IsAdmissible π) (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ)
    (A : SigmaIntertwiner σ n τ) (c : ℂ) : Prop :=
  c ≠ 0 ∧
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
      AreConcordant σ l μF μE φ f →
        twistedDistribution μE τ hτ A.toLinearMap φ = c * Character.distribution μF π hπ f

variable (n) in
/-- The trivial representations of `GL_n(F)` and `GL_n(E)` on `ℂ`, with the identity as
σ-intertwiner, satisfy the Shintani identity with constant `1`. -/
theorem isShintaniLift_trivial (σ : E ≃ₐ[F] E) (l : ℕ) :
    ∃ A : SigmaIntertwiner σ n (Representation.trivial ℂ (GeneralLinear n E) ℂ),
      A.toLinearMap = LinearMap.id ∧
      ∀ (hπ : IsAdmissible (Representation.trivial ℂ (GeneralLinear n F) ℂ))
        (hτ : IsAdmissible (Representation.trivial ℂ (GeneralLinear n E) ℂ)),
        IsShintaniLift σ l (Representation.trivial ℂ (GeneralLinear n F) ℂ) hπ
          (Representation.trivial ℂ (GeneralLinear n E) ℂ) hτ A 1 := by
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ ℂ) (fun g => ?_), rfl,
    fun hπ hτ => ⟨one_ne_zero, fun δ γ _ _ => ?_⟩⟩
  · ext
    simp
  · refine ⟨LinearMap.trace ℂ ℂ (Representation.trivial ℂ (GeneralLinear n F) ℂ γ),
      hasCharacterValue_trace _ hπ γ, ?_⟩
    have h := hasTwistedCharacterValue_trace (Representation.trivial ℂ (GeneralLinear n E) ℂ) hτ
      LinearMap.id δ
    have e1 : Representation.trivial ℂ (GeneralLinear n F) ℂ γ = LinearMap.id := rfl
    have e2 : Representation.trivial ℂ (GeneralLinear n E) ℂ δ ∘ₗ LinearMap.id =
        (LinearMap.id : Module.End ℂ ℂ) := rfl
    rw [one_mul, e1]
    rw [e2] at h
    exact h

end Lift

end Langlands.BaseChange
