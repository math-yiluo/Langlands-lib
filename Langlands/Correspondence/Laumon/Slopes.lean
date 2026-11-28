import Langlands.Correspondence.HenniartLadicClasses
import Langlands.LocalFactor.Ramification.Herbrand.GeneralAbsolute
import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RepresentationTheory.Coinvariants

/-!
# ℓ-adic slopes and the Swan conductor `s(V)`

Laumon 1987, (2.1.2.2)–(2.1.2.5), p. 152: for a continuous ℓ-adic representation `V` of the
wild inertia group `P` of a local field (and hence of the inertia or the whole Galois group),
`P` acts through a finite quotient, `V` splits canonically as `⊕_λ V_λ` according to the slopes
of its simple constituents, and the Swan conductor is `s(V) = Σ_λ λ · dim V_λ`.

This module defines the slope summands from the Library's absolute upper ramification groups
`G^u = localAbsoluteUpperRamificationGroup K Ω u`: `V_0 = V^P` with `P = localWildInertia K Ω`,
and for `λ > 0`, `V_λ` is the intersection of the vectors fixed by `G^{λ+}` (the closure of the
union of the `G^v`, `v > λ`) with the span of the vectors `g v - v`, `g ∈ G^λ`. It states that
wild inertia acts through a finite quotient (`WildImageFiniteStatement`) and that these
summands form a decomposition with the properties of Laumon's (`SlopesExactStatement`).

The representations are those of a topological group `H` embedded in `Ω ≃ₐ[K] Ω` by `f` with
image containing wild inertia: the whole Galois group (`f` the identity) and the inertia
subgroup (`f` its inclusion) are the cases used.
-/

noncomputable section

universe uK uΩ uH uV

open ValuativeRel
open Langlands.Ramification.Local (localAbsoluteUpperRamificationGroup localWildInertia
  localUpperRamificationGroup absoluteFiniteRestriction)
open Langlands.Henniart.LocalNumerical (IsLadicContinuous IsLadicDefinedOverFiniteExtension)

namespace Langlands.Henniart.Laumon

section Definitions

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The group `G^{u+}`: the closure of the union of the absolute upper ramification groups
`G^v` for `v > u` (Laumon (2.1.1), p. 151). At `u = 0` this is the Library's wild inertia. -/
def upperPlusRamificationGroup (u : ℝ) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (⨆ (v : ℝ) (_ : u < v), localAbsoluteUpperRamificationGroup K Ω v).topologicalClosure

/-- The elements of wild inertia whose restriction to the finite Galois subextension `L` lies
in the finite upper ramification group `Gal(L/K)^v`. -/
def finiteLevelUpperGroup (L : FiniteGaloisIntermediateField K Ω) (v : ℝ) :
    Subgroup (Ω ≃ₐ[K] Ω) :=
  localWildInertia K Ω ⊓
    (localUpperRamificationGroup K L v).comap (absoluteFiniteRestriction K Ω L).toMonoidHom

variable {K Ω} {H : Type uH} [Group H] (f : H →* (Ω ≃ₐ[K] Ω)) {ℓ : ℕ} [Fact ℓ.Prime]

/-- The slope-`μ` summand `V_μ` of Laumon (2.1.2.4): `V^P` at `μ = 0`; for `μ > 0`, the vectors
fixed by `G^{μ+}` that lie in the span of the `g v - v` with `g ∈ G^μ`; zero for `μ < 0`. The
groups act on `V` through `f`. -/
def slopeSummand (A : FiniteRepresentation.{0, uH, uV} (PadicAlgCl ℓ) H) (μ : ℝ) :
    Submodule (PadicAlgCl ℓ) A :=
  if μ = 0 then fixedVectors A.representation ((localWildInertia K Ω).comap f)
  else if 0 < μ then
    fixedVectors A.representation ((upperPlusRamificationGroup K Ω μ).comap f) ⊓
      Representation.Coinvariants.ker
        (A.representation.comp ((localAbsoluteUpperRamificationGroup K Ω μ).comap f).subtype)
  else ⊥

/-- The slope summand computed at the finite level `L`, with the finite upper groups
`Gal(L/K)^v` in place of the absolute ones. -/
def finiteSlopeSummand (L : FiniteGaloisIntermediateField K Ω)
    (A : FiniteRepresentation.{0, uH, uV} (PadicAlgCl ℓ) H) (μ : ℝ) :
    Submodule (PadicAlgCl ℓ) A :=
  if μ = 0 then fixedVectors A.representation ((localWildInertia K Ω).comap f)
  else if 0 < μ then
    fixedVectors A.representation ((⨆ (v : ℝ) (_ : μ < v), finiteLevelUpperGroup K Ω L v).comap f) ⊓
      Representation.Coinvariants.ker
        (A.representation.comp ((finiteLevelUpperGroup K Ω L μ).comap f).subtype)
  else ⊥

/-- The slopes `Λ(V)`: the real numbers `μ` with `V_μ ≠ 0`. -/
def slopeSupport (A : FiniteRepresentation.{0, uH, uV} (PadicAlgCl ℓ) H) : Set ℝ :=
  {μ | slopeSummand f A μ ≠ ⊥}

/-- Laumon's Swan conductor `s(V) = Σ_λ λ · dim V_λ` ((2.1.2.5)), as a finite sum over the
slopes; the sum is `0` by convention if the set of slopes were infinite. -/
def ladicSwan (A : FiniteRepresentation.{0, uH, uV} (PadicAlgCl ℓ) H) : ℝ :=
  ∑ᶠ μ : ℝ, μ * (Module.finrank (PadicAlgCl ℓ) (slopeSummand f A μ) : ℝ)

end Definitions

/-- Laumon (2.1.2.2): for `ℓ` different from the residue characteristic, wild inertia acts on a
continuous ℓ-adic representation with a finite model through a finite quotient
`P / (P ∩ Gal(Ω/L))`, so with finite image, and `G^u` acts trivially for some `u > 0`. -/
def WildImageFiniteStatement.{u₁, u₂, u₃, u₄} : Prop :=
  ∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (H : Type u₃) [Group H] [TopologicalSpace H] (f : H →* (Ω ≃ₐ[K] Ω)),
      Topology.IsEmbedding f → localWildInertia K Ω ≤ f.range →
      ∀ A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H,
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
          (∃ L : FiniteGaloisIntermediateField K Ω, ∀ h : H, f h ∈ localWildInertia K Ω →
              absoluteFiniteRestriction K Ω L (f h) = 1 → A.representation h = 1) ∧
          (A.representation '' ((localWildInertia K Ω).comap f : Set H)).Finite ∧
          ∃ u : ℝ, 0 < u ∧ ∀ h : H, f h ∈ localAbsoluteUpperRamificationGroup K Ω u →
            A.representation h = 1

/-- Laumon (2.1.2.3)–(2.1.2.5) and the following paragraph, p. 152–153, for `ℓ` different from
the residue characteristic and continuous ℓ-adic representations with a finite model of a group
`H` embedded in the Galois group with image containing wild inertia:

* the set of slopes is finite and `V = ⊕_λ V_λ` (internal direct sum);
* every `V_λ` is stable under `H`, and `V_λ^{G^λ} = 0` for `λ > 0` (so `V_λ` is purely of
  slope `λ`);
* the summands can be computed at every finite Galois level `L` through which the action of
  wild inertia factors, with the finite upper groups `Gal(L/K)^v`;
* `V` is tame (wild inertia acts trivially) exactly when its slopes lie in `{0}`;
* intertwiners preserve the summands, and in a short exact sequence `0 → A → B → C → 0` the
  sequences of slope summands are exact, so their dimensions and `s` are additive. -/
def SlopesExactStatement.{u₁, u₂, u₃, u₄} : Prop :=
  ∀ (K : Type u₁) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type u₂) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime], ((ℓ : ℕ) : 𝓀[K]) ≠ 0 →
    ∀ (H : Type u₃) [Group H] [TopologicalSpace H] (f : H →* (Ω ≃ₐ[K] Ω)),
      Topology.IsEmbedding f → localWildInertia K Ω ≤ f.range →
      (∀ A : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H,
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
          (slopeSupport f A).Finite ∧
          DirectSum.IsInternal (slopeSummand f A) ∧
          (∀ (μ : ℝ) (h : H), ∀ v ∈ slopeSummand f A μ,
            A.representation h v ∈ slopeSummand f A μ) ∧
          (∀ μ : ℝ, 0 < μ → slopeSummand f A μ ⊓
            fixedVectors A.representation ((localAbsoluteUpperRamificationGroup K Ω μ).comap f) =
              ⊥) ∧
          (∀ L : FiniteGaloisIntermediateField K Ω,
            (∀ h : H, f h ∈ localWildInertia K Ω →
              absoluteFiniteRestriction K Ω L (f h) = 1 → A.representation h = 1) →
            ∀ μ : ℝ, finiteSlopeSummand f L A μ = slopeSummand f A μ) ∧
          ((∀ h : H, f h ∈ localWildInertia K Ω → A.representation h = 1) ↔
            slopeSupport f A ⊆ {0})) ∧
      (∀ (A B : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H)
        (φ : A.representation.IntertwiningMap B.representation),
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
        IsLadicContinuous ℓ B → IsLadicDefinedOverFiniteExtension ℓ B →
          ∀ μ : ℝ, (slopeSummand f A μ).map φ.toLinearMap ≤ slopeSummand f B μ) ∧
      (∀ (A B C : FiniteRepresentation.{0, u₃, u₄} (PadicAlgCl ℓ) H)
        (i : A.representation.IntertwiningMap B.representation)
        (q : B.representation.IntertwiningMap C.representation),
        IsLadicContinuous ℓ A → IsLadicDefinedOverFiniteExtension ℓ A →
        IsLadicContinuous ℓ B → IsLadicDefinedOverFiniteExtension ℓ B →
        IsLadicContinuous ℓ C → IsLadicDefinedOverFiniteExtension ℓ C →
        Function.Injective i → Function.Surjective q →
        LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
          (∀ μ : ℝ, (slopeSummand f A μ).map i.toLinearMap =
              slopeSummand f B μ ⊓ LinearMap.range i.toLinearMap ∧
            (slopeSummand f B μ).map q.toLinearMap = slopeSummand f C μ ∧
            Module.finrank (PadicAlgCl ℓ) (slopeSummand f B μ) =
              Module.finrank (PadicAlgCl ℓ) (slopeSummand f A μ) +
                Module.finrank (PadicAlgCl ℓ) (slopeSummand f C μ)) ∧
          ladicSwan f B = ladicSwan f A + ladicSwan f C)

end Langlands.Henniart.Laumon
