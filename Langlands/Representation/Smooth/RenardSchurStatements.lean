import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Category.Basic
import Langlands.Representation.Hecke.IntegratedConvolution
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.MeasureTheory.Group.Measure

/-! # Schur's lemma and its consequences for t.d. groups (Renard III.1.7–III.1.11)

For a t.d. group: admissibility is reflexivity for the smooth contragredient (III.1.7); for a
t.d. group countable at infinity, Schur's lemma holds for irreducible smooth representations
(III.1.8), invariant pairings with the contragredient are multiples of the canonical one
(III.1.9), irreducible representations have central characters on which the centre of the
category acts by scalars, and distinct central characters exclude intertwiners (III.1.10), and
irreducible representations separate the points of the Hecke algebra (III.1.11).
-/

noncomputable section

universe u v w

open CategoryTheory MeasureTheory

namespace Langlands.Renard.Smooth

/-- Renard III.1.7, Proposition: for a Hausdorff, locally compact, totally disconnected group,
a smooth complex representation `π` is admissible if and only if the canonical map
`V → Ṽ̃` (the published `smoothBidual`) is bijective, if and only if `π` is equivalent to its
double smooth contragredient. -/
def AdmissibleBidualStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π),
    (IsAdmissible π ↔ Function.Bijective (smoothBidual hπ)) ∧
      (IsAdmissible π ↔
        Nonempty (π.Equiv (smoothContragredient (smoothContragredient π))))

/-- Renard III.1.8, Proposition: let `G` be a Hausdorff, locally compact, totally disconnected
group, countable at infinity, and `π` an irreducible smooth complex representation. Every
`G`-endomorphism of `π` is a scalar, and there is no nonzero intertwiner from `π` to an
irreducible smooth representation not equivalent to `π`. -/
def SigmaCompactSchurStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → π.IsIrreducible →
    (∀ f : π.IntertwiningMap π, ∃ c : ℂ, f = c • Representation.IntertwiningMap.id π) ∧
      ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
        IsSmooth τ → τ.IsIrreducible → IsEmpty (π.Equiv τ) →
          ∀ f : π.IntertwiningMap τ, f = 0

/-- Renard III.1.9, Proposition: let `G` be a Hausdorff, locally compact, totally disconnected
group, countable at infinity, and `π` an irreducible admissible representation. Every
`G`-invariant bilinear form `B` on `V × Ṽ` is a multiple `c λ(v)` of the canonical pairing; in
particular a nonzero such form is nondegenerate in both variables. -/
def InvariantContragredientPairingStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsAdmissible π → π.IsIrreducible →
    ∀ B : V →ₗ[ℂ] SmoothDual π →ₗ[ℂ] ℂ,
      (∀ (g : G) (x : V) (ℓ : SmoothDual π),
        B (π g x) (smoothContragredient π g ℓ) = B x ℓ) →
      (∃ c : ℂ, ∀ (x : V) (ℓ : SmoothDual π), B x ℓ = c * (ℓ : Module.Dual ℂ V) x) ∧
        (B ≠ 0 → (∀ x : V, (∀ ℓ, B x ℓ = 0) → x = 0) ∧
          ∀ ℓ : SmoothDual π, (∀ x, B x ℓ = 0) → ℓ = 0)

/-- Renard III.1.10, central characters and the Lemma, with the Remark: let `G` be a
Hausdorff, locally compact, totally disconnected group, countable at infinity, and `Z` a
subgroup of the centre of `G`.

* Every irreducible smooth representation `π` has a central character on `Z`: a character
  `χ : Z → ℂˣ` with `π(z) = χ(z) Id`.
* If smooth representations `π₁` and `π₂` admit central characters `χ₁ ≠ χ₂` on `Z`, every
  intertwiner from `π₁` to `π₂` vanishes.
* Every element `z` of the centre `CatCenter` of the category of smooth representations acts
  on an irreducible smooth representation by a scalar. -/
def CentralCharacterStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    (Z : Subgroup G), Z ≤ Subgroup.center G →
    (∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
      IsSmooth π → π.IsIrreducible →
        ∃ χ : Z →* ℂˣ, ∀ (z : Z) (x : V), π z x = (χ z : ℂ) • x) ∧
    (∀ (V : Type v) [AddCommGroup V] [Module ℂ V] (π₁ : Representation ℂ G V)
      (W : Type w) [AddCommGroup W] [Module ℂ W] (π₂ : Representation ℂ G W)
      (χ₁ χ₂ : Z →* ℂˣ), χ₁ ≠ χ₂ →
        (∀ (z : Z) (x : V), π₁ z x = (χ₁ z : ℂ) • x) →
        (∀ (z : Z) (y : W), π₂ z y = (χ₂ z : ℂ) • y) →
        ∀ f : π₁.IntertwiningMap π₂, f = 0) ∧
    ∀ (z : CatCenter (SmoothRep.{0, u, v} ℂ G)) (V : SmoothRep.{0, u, v} ℂ G),
      V.IsIrreducible → ∃ c : ℂ, ∀ x : V, SmoothRep.hom (z.app V) x = c • x

/-- Renard III.1.11, Theorem: let `G` be a Hausdorff, locally compact, totally disconnected
group, countable at infinity, with a left Haar measure `μ`. For every nonzero element `T` of
the Hecke algebra there is an irreducible smooth representation `π` with `π(T) ≠ 0`. -/
def HeckeCompletenessStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (T : Hecke.HeckeAlgebra μ), T ≠ 0 →
      ∃ π : SmoothRep.{0, u, v} ℂ G, π.IsIrreducible ∧
        Hecke.heckeAction μ π.representation π.isSmooth T ≠ 0

/-- The five statements above. -/
def RenardSchurStatements.{u', v', w'} : Prop :=
  AdmissibleBidualStatement.{u', v'} ∧ SigmaCompactSchurStatement.{u', v', w'} ∧
    InvariantContragredientPairingStatement.{u', v'} ∧ CentralCharacterStatement.{u', v', w'} ∧
    HeckeCompletenessStatement.{u', v'}

end Langlands.Renard.Smooth
