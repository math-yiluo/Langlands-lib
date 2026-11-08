import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.HarmonicAnalysis.GroupAction
import Mathlib.RepresentationTheory.Basic

/-! # Regular representations, tensor products and smooth Hom (Renard III.1.2, III.1.3, III.1.15)

The left and right regular representations of a t.d. group on uniformly locally constant
functions and on test functions are smooth (III.1.2); the left regular action of the Hecke
algebra on test functions is convolution (III.1.3, Example); the smooth part of `Hom` is right
adjoint to the tensor product, smooth linear maps out of a smooth representation take smooth
values, and the functors `• ⊗ V`, `Hom(•, V)₀` and `Hom(V, •)₀` are exact and preserve
projectives, send projectives to injectives, and preserve injectives respectively (III.1.15).
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory TensorProduct

namespace Langlands.Renard.Smooth

/-- Renard III.1.2, Proposition: let `G` be a Hausdorff, locally compact, totally disconnected
group. Call `f : G → ℂ` uniformly locally constant if it is bi-invariant under some compact
open subgroup (`f ∈ 𝒞^∞(G, K)`). Left and right translates of uniformly locally constant
functions are uniformly locally constant, each such function is fixed by an open subgroup
under both translations, and the left and right regular representations on test functions
`𝒟(G)` are smooth. -/
def RegularRepresentationSmoothStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    let IsUniform : (G → ℂ) → Prop := fun f =>
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
        ∀ k ∈ K, ∀ k' ∈ K, ∀ x : G, f (k * x * k') = f x
    (∀ (g : G) (f : G → ℂ), IsUniform f →
      IsUniform (fun x => f (g⁻¹ * x)) ∧ IsUniform (fun x => f (x * g))) ∧
    (∀ f : G → ℂ, IsUniform f → ∃ K : OpenSubgroup G,
      ∀ k ∈ K, (fun x => f (k⁻¹ * x)) = f ∧ (fun x => f (x * k)) = f) ∧
    IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)) ∧
      IsSmooth (HarmonicAnalysis.GroupAction.rightTests (G := G))

/-- Renard III.1.3, Example: for a left Haar measure `μ` and the left regular representation
`l` on test functions, `l(T) f = T ∗ f` for every `T` in the Hecke algebra and every test
function `f`. -/
def LeftRegularHeckeActionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)))
    (T : Hecke.HeckeAlgebra μ) (f : Hecke.HeckeAlgebra μ),
    Hecke.heckeAction μ (HarmonicAnalysis.GroupAction.leftTests (G := G)) hl T
        (Hecke.HeckeAlgebra.toTestFunction μ f) =
      Hecke.HeckeAlgebra.toTestFunction μ (T * f)

/-- Renard III.1.15, Lemma, Proposition and Corollary: let `G` be a Hausdorff, locally compact,
totally disconnected group.

* (Lemma) If `π₁` is smooth, every smooth vector `φ` of `Hom(V₁, V₂)` (for the action
  `(g φ)(v) = π₂(g) φ(π₁(g⁻¹) v)`) takes values in the smooth vectors of `π₂`.
* (Proposition) For smooth `π₁, π₂, π₃`, currying `φ ↦ Φ`, `Φ(v₁)(v₂) = φ(v₁ ⊗ v₂)`, is an
  equivalence of representations `Hom(V₁ ⊗ V₂, V₃)₀ ≃ Hom(V₁, Hom(V₂, V₃)₀)₀`.
* (Corollary) It induces a linear equivalence
  `Hom_G(V₁ ⊗ V₂, V₃) ≃ Hom_G(V₁, Hom(V₂, V₃)₀)` given by the same formula. -/
def TensorHomAdjunctionStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V₁ V₂ V₃ : Type v) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃]
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂) (π₃ : Representation ℂ G V₃),
    (IsSmooth π₁ → ∀ φ ∈ smoothVectors (Representation.linHom π₁ π₂), ∀ x : V₁,
      φ x ∈ smoothVectors π₂) ∧
    (IsSmooth π₁ → IsSmooth π₂ → IsSmooth π₃ →
      (∃ e : (smoothPart (Representation.linHom (Representation.tprod π₁ π₂) π₃)).Equiv
          (smoothPart (Representation.linHom π₁ (smoothPart (Representation.linHom π₂ π₃)))),
        ∀ φ x₁ x₂, (((e φ : V₁ →ₗ[ℂ] smoothVectors (Representation.linHom π₂ π₃)) x₁ :
          V₂ →ₗ[ℂ] V₃) x₂) = (φ : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₃) (x₁ ⊗ₜ x₂)) ∧
      ∃ e : (Representation.tprod π₁ π₂).IntertwiningMap π₃ ≃ₗ[ℂ]
          π₁.IntertwiningMap (smoothPart (Representation.linHom π₂ π₃)),
        ∀ φ x₁ x₂, ((e φ x₁ : V₂ →ₗ[ℂ] V₃) x₂) = φ (x₁ ⊗ₜ x₂))

/-- Renard III.1.15, Theorem, with lifting properties in the category of smooth
representations on carriers in `Type v`: let `G` be a Hausdorff, locally compact, totally
disconnected group and `π` a smooth representation on `V`.

* (i) `• ⊗ V` preserves projective objects.
* (ii) `Hom(•, V)₀` is exact: for an injective intertwiner `i : W₁ → W₂` of smooth
  representations, every smooth linear map `W₁ → V` extends along `i` to a smooth linear map
  `W₂ → V`. It sends projective objects to injective objects.
* (iii) `Hom(V, •)₀` is exact: for a surjective intertwiner `q : W₂ → W₃`, every smooth
  linear map `V → W₃` lifts through `q` to a smooth linear map `V → W₂`. It preserves
  injective objects.

A smooth representation `P` is projective if every intertwiner `P → Z` lifts through every
surjective intertwiner `Y → Z` of smooth representations, and injective if every intertwiner
`X → P` extends along every injective intertwiner `X → Y` of smooth representations. -/
def TensorHomExactnessStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (V : Type v) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
    let IsProj : ∀ {P : Type v} [AddCommGroup P] [Module ℂ P], Representation ℂ G P → Prop :=
      fun {_} _ _ ρ => ∀ (Y Z : Type v) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z]
        [Module ℂ Z] (σ : Representation ℂ G Y) (τ : Representation ℂ G Z),
        IsSmooth σ → IsSmooth τ → ∀ q : σ.IntertwiningMap τ, Function.Surjective q →
          ∀ f : ρ.IntertwiningMap τ, ∃ g : ρ.IntertwiningMap σ, q.comp g = f
    let IsInj : ∀ {P : Type v} [AddCommGroup P] [Module ℂ P], Representation ℂ G P → Prop :=
      fun {_} _ _ ρ => ∀ (X Y : Type v) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
        [Module ℂ Y] (σ : Representation ℂ G X) (τ : Representation ℂ G Y),
        IsSmooth σ → IsSmooth τ → ∀ j : σ.IntertwiningMap τ, Function.Injective j →
          ∀ f : σ.IntertwiningMap ρ, ∃ g : τ.IntertwiningMap ρ, g.comp j = f
    (∀ (P : Type v) [AddCommGroup P] [Module ℂ P] (ρ : Representation ℂ G P), IsSmooth ρ →
      IsProj ρ → IsProj (Representation.tprod ρ π)) ∧
    (∀ (W₁ W₂ : Type v) [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
      (σ₁ : Representation ℂ G W₁) (σ₂ : Representation ℂ G W₂),
      IsSmooth σ₁ → IsSmooth σ₂ → ∀ i : σ₁.IntertwiningMap σ₂, Function.Injective i →
        ∀ f ∈ smoothVectors (Representation.linHom σ₁ π),
          ∃ f' ∈ smoothVectors (Representation.linHom σ₂ π), f'.comp i.toLinearMap = f) ∧
    (∀ (P : Type v) [AddCommGroup P] [Module ℂ P] (ρ : Representation ℂ G P), IsSmooth ρ →
      IsProj ρ → IsInj (smoothPart (Representation.linHom ρ π))) ∧
    (∀ (W₂ W₃ : Type v) [AddCommGroup W₂] [Module ℂ W₂] [AddCommGroup W₃] [Module ℂ W₃]
      (σ₂ : Representation ℂ G W₂) (σ₃ : Representation ℂ G W₃),
      IsSmooth σ₂ → IsSmooth σ₃ → ∀ q : σ₂.IntertwiningMap σ₃, Function.Surjective q →
        ∀ f ∈ smoothVectors (Representation.linHom π σ₃),
          ∃ f' ∈ smoothVectors (Representation.linHom π σ₂), q.toLinearMap.comp f' = f) ∧
    ∀ (I : Type v) [AddCommGroup I] [Module ℂ I] (ρ : Representation ℂ G I), IsSmooth ρ →
      IsInj ρ → IsInj (smoothPart (Representation.linHom π ρ))

/-- The four statements above. -/
def RenardTensorHomStatements.{u', v'} : Prop :=
  RegularRepresentationSmoothStatement.{u'} ∧ LeftRegularHeckeActionStatement.{u'} ∧
    TensorHomAdjunctionStatement.{u', v'} ∧ TensorHomExactnessStatement.{u', v'}

end Langlands.Renard.Smooth
