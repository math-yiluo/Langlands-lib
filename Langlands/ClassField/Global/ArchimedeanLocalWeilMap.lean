import Langlands.ClassField.Global.AbsoluteLocalWeilMap
import Langlands.Weil.Archimedean

/-! # Archimedean local Weil groups mapped into relative and absolute global Weil groups

Properties of continuous homomorphisms `W_ℂ → W_{E/F}` and `W_ℝ → W_{E/F}` from the concrete
archimedean Weil groups, at the infinite places determined by a complex embedding of `E`
(Tate 1979, (1.4.3) and (1.6.1)), and of the corresponding maps into the projective limit of a
supplied system of Weil maps. No such map is constructed and none is asserted to exist.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField NumberField.InfinitePlace
open scoped NumberField
open Langlands.Weil.Archimedean

universe u

namespace RelativeWeilGroup

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- `ψw` is the continuous extension of the embedding `ψ : E → ℂ` to the completion of `E` at
the infinite place of `ψ`. -/
def IsCompletionExtension (ψ : E →+* ℂ) (ψw : (InfinitePlace.mk ψ).Completion →+* ℂ) :
    Prop :=
  Continuous ψw ∧ ∀ a : E, ψw (a : (InfinitePlace.mk ψ).Completion) = ψ a

/-- `ι : W_ℂ → W_{E/F}` is the local-to-relative Weil map at the complex place of `F` below
the embedding `ψ : E → ℂ`, with `F_v` and `E_w` identified with `ℂ` through `ψ`: the place of
`F` below `ψ` is complex; the image of `ι g` in `Gal(E/F)` fixes `ψ`; and `ι` is the inverse of
the identification `E_wˣ ≅ ℂˣ` followed by `E_wˣ → C_E`, then inverted. -/
def IsComplexLocalRelativeWeilMap (ψ : E →+* ℂ)
    (ι : ComplexWeil →ₜ* RelativeWeilGroup c F E) : Prop :=
  ¬ ComplexEmbedding.IsReal (ψ.comp (algebraMap F E)) ∧
    (∀ (g : ComplexWeil) (x : E), ψ (projection c F E (ι g) x) = ψ x) ∧
    ∃ ψw : (InfinitePlace.mk ψ).Completion →+* ℂ, IsCompletionExtension ψ ψw ∧
      ∀ x : ((InfinitePlace.mk ψ).Completion)ˣ,
        ι (Units.map ψw.toMonoidHom x) =
          (inclusion c F E (IdeleClassGroup.ofCompletion (𝓞 E) E (InfinitePlace.mk ψ) x))⁻¹

/-- `ι : W_ℝ → W_{E/F}` is the local-to-relative Weil map at the real place of `F` below the
embedding `ψ : E → ℂ`, with `\bar{F_v} = ℂ` and `E_w ⊆ ℂ` through `ψ`: the place of `F` below
`ψ` is real; the image of `ι g` in `Gal(E/F)` acts through `ψ` as the Galois image of `g`; and
on `W_{E_w}` the map `ι` is the inverse of Tate's reciprocity `r_{E_w}` followed by
`E_wˣ → C_E`, then inverted. For real `ψ`, `W_{E_w}` is all of `W_ℝ` and `r_ℝ⁻¹` is
`RealWeil.abelianCoordinate`; for nonreal `ψ`, `W_{E_w}` is `W_ℂ` and `r_ℂ` is the identity. -/
def IsRealLocalRelativeWeilMap (ψ : E →+* ℂ) (ι : RealWeil →ₜ* RelativeWeilGroup c F E) :
    Prop :=
  ComplexEmbedding.IsReal (ψ.comp (algebraMap F E)) ∧
    (∀ (g : RealWeil) (x : E),
      ψ (projection c F E (ι g) x) = RealWeil.toGalois g (ψ x)) ∧
    ∃ ψw : (InfinitePlace.mk ψ).Completion →+* ℂ, IsCompletionExtension ψ ψw ∧
      ∀ x : ((InfinitePlace.mk ψ).Completion)ˣ,
        (ComplexEmbedding.IsReal ψ → ∀ g : RealWeil,
          ((RealWeil.abelianCoordinate g : ℝ) : ℂ) = ψw x →
            ι g = (inclusion c F E
              (IdeleClassGroup.ofCompletion (𝓞 E) E (InfinitePlace.mk ψ) x))⁻¹) ∧
        (¬ ComplexEmbedding.IsReal ψ →
          ι (RealWeil.ofComplex (Units.map ψw.toMonoidHom x)) =
            (inclusion c F E (IdeleClassGroup.ofCompletion (𝓞 E) E (InfinitePlace.mk ψ) x))⁻¹)

end RelativeWeilGroup

namespace WeilMapSystem

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h)

/-- `θ : W_ℂ → W_F` is a local-to-global Weil map at the complex embedding `φ : F → ℂ`: for every
finite Galois layer `K` there are an embedding `ψ : K → ℂ` extending `φ` and `x ∈ W_{K/F}` such
that `W_ℂ → W_F → W_{K/F}` followed by conjugation by `x` is a local-to-relative Weil map
at `ψ`. -/
def IsComplexLocalWeilMap (φ : F →+* ℂ) (θ : ComplexWeil →ₜ* S.WeilGroup) : Prop :=
  ∀ K : FiniteGaloisIntermediateField F Ω,
    ∃ (ψ : K →+* ℂ) (_ : ψ.comp (algebraMap F K) = φ) (x : RelativeWeilGroup c F K),
      RelativeWeilGroup.IsComplexLocalRelativeWeilMap ψ (S.conjLevelMap K x θ)

/-- `θ : W_ℝ → W_F` is a local-to-global Weil map at the real embedding `φ : F → ℂ`: for every
finite Galois layer `K` there are an embedding `ψ : K → ℂ` extending `φ` and `x ∈ W_{K/F}` such
that `W_ℝ → W_F → W_{K/F}` followed by conjugation by `x` is a local-to-relative Weil map
at `ψ`. -/
def IsRealLocalWeilMap (φ : F →+* ℂ) (θ : RealWeil →ₜ* S.WeilGroup) : Prop :=
  ∀ K : FiniteGaloisIntermediateField F Ω,
    ∃ (ψ : K →+* ℂ) (_ : ψ.comp (algebraMap F K) = φ) (x : RelativeWeilGroup c F K),
      RelativeWeilGroup.IsRealLocalRelativeWeilMap ψ (S.conjLevelMap K x θ)

variable {S}

/-- The complex property is invariant under conjugation by elements of the global Weil
group. -/
theorem IsComplexLocalWeilMap.conjMap {φ : F →+* ℂ} {θ : ComplexWeil →ₜ* S.WeilGroup}
    (hθ : S.IsComplexLocalWeilMap φ θ) (y : S.WeilGroup) :
    S.IsComplexLocalWeilMap φ (S.conjMap y θ) := by
  intro K
  obtain ⟨ψ, hψ, x, hx⟩ := hθ K
  refine ⟨ψ, hψ, x * (S.toLevel K y)⁻¹, ?_⟩
  rw [conjLevelMap_conjMap, inv_mul_cancel_right]
  exact hx

/-- The real property is invariant under conjugation by elements of the global Weil group. -/
theorem IsRealLocalWeilMap.conjMap {φ : F →+* ℂ} {θ : RealWeil →ₜ* S.WeilGroup}
    (hθ : S.IsRealLocalWeilMap φ θ) (y : S.WeilGroup) :
    S.IsRealLocalWeilMap φ (S.conjMap y θ) := by
  intro K
  obtain ⟨ψ, hψ, x, hx⟩ := hθ K
  refine ⟨ψ, hψ, x * (S.toLevel K y)⁻¹, ?_⟩
  rw [conjLevelMap_conjMap, inv_mul_cancel_right]
  exact hx

/-- At each layer, a complex local-to-global Weil map is conjugate to a local-to-relative
Weil map. -/
theorem IsComplexLocalWeilMap.exists_level {φ : F →+* ℂ} {θ : ComplexWeil →ₜ* S.WeilGroup}
    (hθ : S.IsComplexLocalWeilMap φ θ) (K : FiniteGaloisIntermediateField F Ω) :
    ∃ (ψ : K →+* ℂ) (_ : ψ.comp (algebraMap F K) = φ) (x : RelativeWeilGroup c F K)
      (ι : ComplexWeil →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsComplexLocalRelativeWeilMap ψ ι ∧
        ∀ g, S.toLevel K (θ g) = x⁻¹ * ι g * x := by
  obtain ⟨ψ, hψ, x, hx⟩ := hθ K
  refine ⟨ψ, hψ, x, _, hx, fun g => ?_⟩
  rw [conjLevelMap_apply]
  group

/-- At each layer, a real local-to-global Weil map is conjugate to a local-to-relative Weil
map. -/
theorem IsRealLocalWeilMap.exists_level {φ : F →+* ℂ} {θ : RealWeil →ₜ* S.WeilGroup}
    (hθ : S.IsRealLocalWeilMap φ θ) (K : FiniteGaloisIntermediateField F Ω) :
    ∃ (ψ : K →+* ℂ) (_ : ψ.comp (algebraMap F K) = φ) (x : RelativeWeilGroup c F K)
      (ι : RealWeil →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsRealLocalRelativeWeilMap ψ ι ∧
        ∀ g, S.toLevel K (θ g) = x⁻¹ * ι g * x := by
  obtain ⟨ψ, hψ, x, hx⟩ := hθ K
  refine ⟨ψ, hψ, x, _, hx, fun g => ?_⟩
  rw [conjLevelMap_apply]
  group

end WeilMapSystem

end Langlands.ClassField.Global
