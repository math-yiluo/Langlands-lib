import Langlands.Global.LocalWavePacketMainTermLimitStatement
import Langlands.Global.GMFamilyFieldDescent
import Langlands.Geometry.Building.RealTorusAction
import Langlands.LinearAlgebra.GMFamilyOrthogonalSetLimitStatement

/-! # The chambers of `𝔞_P` and the Weyl sets `Ω(P, S)`

Arthur 1982, §§1–2, pp.1292–1298; Lapid 2011, §7, (15) (p.326) and §8, p.328. For a standard
parabolic subgroup `P = P_J` with Levi `M`, the parabolic subgroups `Q ∈ 𝓟(M)` (the chambers of
`𝔞_M`) correspond to the pairs `(S, s)` of a standard parabolic subgroup `S` and an element
`s ∈ Ω(P, S) = W(𝔞_P, 𝔞_S)`: the chamber of `(S, s)` is `s⁻¹(𝔞_S^+)`, its simple roots are
`s⁻¹(Δ_S)`, the chambers adjacent along a wall are related by the elementary symmetry, which
fixes that wall, and for `T` in the closed positive chamber the points `Y_Q = s⁻¹(T_S)` form a
positive `(G, M)`-orthogonal set. The points use the unshifted exponential in
`WavePacketMainTermLimitStatement`. Arthur's height comparison gives the projection of
`s⁻¹(T − T₀) + T₀`.

The statement uses the Euclidean model of `Langlands.LinearAlgebra.GMFamilies`: a linear
isomorphism `eV : 𝔞_0 = V T ≃ E` onto a Euclidean space whose inner product is invariant under the
relative Weyl group, the roots `R` as Riesz vectors (`Langlands.GMFamily.rootVectorIn`), and
`𝔞_S = {H : α(H) = 0, α ∈ Δ_0^S}` (`rootAnnihilator`) inside `E`.

* `standardChamberSpace`, `IsParameterTranspose`, `IsStandardChamberPoint`,
  `IsSimpleRootTranspose`: the subspaces `𝔞_S ⊆ E`, the transpose of a parameter map, the
  points of the chamber `s⁻¹(𝔞_S^+)`, and the vectors `s⁻¹(α_S)`.
* `StandardChamberParametrizationStatement`: the correspondence and its properties. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct RealInnerProductSpace Classical

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  ArthurTruncation ArthurParabolicSpaces Langlands.GMFamily

section Chambers

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (eV : V T ≃ₗ[ℝ] E)

/-- `𝔞_S = {H ∈ 𝔞_0 : α(H) = 0 for α ∈ S}` as a subspace of the Euclidean model `E`. -/
def standardChamberSpace (S : Set (characterLattice T)) : Submodule ℝ E :=
  (rootAnnihilator T S).map eV.toLinearMap

/-- `h ∈ 𝔞_J` is the transpose image of `hS ∈ 𝔞_S` under a parameter map
`σ : 𝔞_J^* → 𝔞_S^*`: `⟨σμ, hS⟩ = ⟨μ, h⟩` for every `μ ∈ 𝔞_J^*`, the pairings being those of
`X^*(T) ⊗ ℝ` with `𝔞_0` after restriction of characters to `T`. -/
def IsParameterTranspose (J S : Set (characterLattice T))
    (σ : RealCharacterParameter F (Standard.parabolicScheme i ν J) →ₗ[ℝ]
      RealCharacterParameter F (Standard.parabolicScheme i ν S)) (h hS : E) : Prop :=
  ∀ y, pair T (restrictToTorus F i ν S (σ y)) (eV.symm hS) =
    pair T (restrictToTorus F i ν J y) (eV.symm h)

/-- `h` lies in the chamber `σ⁻¹(𝔞_S^+)` of `𝔞_J`: `h ∈ 𝔞_J` is the transpose image of a point
`hS ∈ 𝔞_S` on which every simple root `α ∉ S` is positive. -/
def IsStandardChamberPoint (Δ : Set (characterLattice T)) (J S : Set (characterLattice T))
    (σ : RealCharacterParameter F (Standard.parabolicScheme i ν J) →ₗ[ℝ]
      RealCharacterParameter F (Standard.parabolicScheme i ν S)) (h : E) : Prop :=
  h ∈ standardChamberSpace eV J ∧ ∃ hS ∈ standardChamberSpace eV S,
    (∀ α ∈ Δ, α ∉ S → 0 < eval T α (eV.symm hS)) ∧ IsParameterTranspose i ν eV J S σ h hS

/-- `v ∈ 𝔞_J` is the transpose image of the restriction `α_S ∈ 𝔞_S` of the root `α` (the
orthogonal projection of its Riesz vector): in the chamber `σ⁻¹(𝔞_S^+)` this is the simple root
`σ⁻¹(α_S)`. -/
def IsSimpleRootTranspose
    (J S : Set (characterLattice T))
    (σ : RealCharacterParameter F (Standard.parabolicScheme i ν J) →ₗ[ℝ]
      RealCharacterParameter F (Standard.parabolicScheme i ν S))
    (α : characterLattice T) (v : E) : Prop :=
  v ∈ standardChamberSpace eV J ∧
    IsParameterTranspose i ν eV J S σ v
      ((restrictedRoot (standardChamberSpace eV S) (rootVectorIn eV α) :
        standardChamberSpace eV S) : E)

end Chambers

/-- **The chambers of `𝔞_P` and the Weyl sets `Ω(P, S)`** (Arthur 1982, §§1–2,
pp.1292–1298; Lapid 2011, §7, (15) (p.326), and §8, p.328). Let `G` be connected reductive over a
number field `F`, `i : T → G` a maximal split torus, `ν` a generic cocharacter with simple roots
`Δ_0`, `D` reflection data, `π S` Levi projections of the standard parabolic subgroups, and
`eV : 𝔞_0 ≃ E` Euclidean coordinates in which the relative Weyl group acts by isometries; let `R`
be the Riesz vectors of the relative roots. Let `Ω(P_J, P_S)` be the set of real parameter maps
`realWeylParameter` of the Weyl conjugations from `P_J` to `P_S`. Then `R` is a root set (`IsRootSet`), the coroot of `α` is `α^∨ = 2α/⟪α, α⟫`, and for every
standard `J`, `𝔞_J` is a Levi space (`IsLeviSpace`) and:

1. every `σ ∈ Ω(P_J, P_S)` is the restriction of an element `w` of the relative Weyl group:
   `σμ = wμ` in `𝔞_0^*`;
2. every point of the chamber `σ⁻¹(𝔞_S^+)` of `𝔞_J` is regular, all of them have the same
   positive roots, the chamber is not empty, every regular point of `𝔞_J` lies in some chamber
   `σ⁻¹(𝔞_S^+)`, and two pairs `(S, σ)` with a common chamber are equal: this is the bijection
   `𝓟(M_J) ≅ ⊔_S Ω(P_J, P_S)`;
3. the simple roots `Δ_Q` of the chamber `Q` of `(S, σ)` (`simpleRoots`) are the vectors
   `σ⁻¹(α_S)`, `α ∈ Δ_0 ∖ S`, and distinct `α` give distinct vectors;
4. if the chambers of `(S, σ)` and `(S₂, σ₂)` are adjacent along the simple root `σ⁻¹(α_S)` of
   the first, then `σ₂ σ⁻¹` fixes the wall `⟨·, α^∨⟩ = 0` of `𝔞_S^*` pointwise;
5. for `T` in the closed positive chamber of `𝔞_0` the points `Y_Q = σ⁻¹(T_S)` (the transpose
   images of the projections `T_S` of `T` to `𝔞_S`, characterized by
   `⟨μ, Y_Q⟩ = ⟨σμ, T⟩`) form a positive `(G, M_J)`-orthogonal set with `α(T) ≤ ⟨σ⁻¹(α_S), Y_Q⟩`
   for `α ∈ Δ_0 ∖ S` (Lapid's (15)) and `‖Y_Q‖ ≤ ‖T‖`. -/
def StandardChamberParametrizationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν →
  ∀ (D : RelativeRootReflectionData i)
    (π : ∀ S : StandardIndex hG hi ν,
      Standard.parabolicScheme i ν S.roots ⟶ Standard.leviScheme i ν S.roots),
    (∀ S : StandardIndex hG hi ν,
      Standard.leviToParabolic i ν S.roots ≫ π S = 𝟙 (Standard.leviScheme i ν S.roots)) →
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (eV : V T ≃ₗ[ℝ] E),
    (∀ (w : relativeWeylGroup i) (x y : V T),
      ⟪eV (relativeWeylRealAction i w x), eV (relativeWeylRealAction i w y)⟫ = ⟪eV x, eV y⟫) →
  ∀ (R : Finset E), (R : Set E) = rootVectorIn eV '' relativeRoots i →
  let Δ : Set (characterLattice T) := simpleRelativeRoots i ν
  let Ωr (J S : StandardIndex hG hi ν) :
      Set (RealCharacterParameter F (Standard.parabolicScheme i ν J.roots) →ₗ[ℝ]
        RealCharacterParameter F (Standard.parabolicScheme i ν S.roots)) :=
    {σ | ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
      (c : Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J.roots),
      IsWeylConjugation (Standard.parabolicHom i ν J.roots) (Standard.leviToParabolic i ν J.roots)
        (Standard.parabolicHom i ν S.roots) (Standard.leviToParabolic i ν S.roots) w c ∧
      realWeylParameter (Standard.leviToParabolic i ν J.roots) c (π S) = σ}
  -- 0. the Euclidean model
  IsRootSet R ∧
  (∀ α ∈ relativeRoots i,
    eV (corootVector D α) = (2 / ‖rootVectorIn eV α‖ ^ 2) • rootVectorIn eV α) ∧
  ∀ J : StandardIndex hG hi ν,
    IsLeviSpace R (standardChamberSpace eV J.roots) ∧
    -- 1. Weyl realization
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∃ w : relativeWeylGroup i, ∀ y,
      restrictToTorus F i ν S.roots (σ y) =
        relativeWeylRealCharacterAction i w (restrictToTorus F i ν J.roots y)) ∧
    -- 2. chambers
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ h : E,
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
        IsRegular R (standardChamberSpace eV J.roots) h) ∧
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ h h' : E,
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h' → posSet R h = posSet R h') ∧
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∃ h : E,
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h) ∧
    (∀ h : E, IsRegular R (standardChamberSpace eV J.roots) h →
      ∃ (S : StandardIndex hG hi ν), ∃ σ ∈ Ωr J S,
        IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h) ∧
    (∀ (S S' : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ σ' ∈ Ωr J S', ∀ h h' : E,
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
      IsStandardChamberPoint i ν eV Δ J.roots S'.roots σ' h' → posSet R h = posSet R h' →
        S = S') ∧
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ σ' ∈ Ωr J S, ∀ h h' : E,
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ' h' → posSet R h = posSet R h' →
        σ = σ') ∧
    -- 3. simple roots
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ h : E,
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
      ∀ v : standardChamberSpace eV J.roots,
        v ∈ simpleRoots (standardChamberSpace eV J.roots) (posSet R h) ↔
          ∃ α ∈ simpleFinset ν hG hi \ S.1,
            IsSimpleRootTranspose i ν eV J.roots S.roots σ α v) ∧
    (∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ α ∈ simpleFinset ν hG hi \ S.1,
      ∀ β ∈ simpleFinset ν hG hi \ S.1, ∀ v : E,
        IsSimpleRootTranspose i ν eV J.roots S.roots σ α v →
        IsSimpleRootTranspose i ν eV J.roots S.roots σ β v → α = β) ∧
    -- 4. walls
    (∀ (S S₂ : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ σ₂ ∈ Ωr J S₂, ∀ (h h₂ : E)
      (v : standardChamberSpace eV J.roots),
      IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
      IsStandardChamberPoint i ν eV Δ J.roots S₂.roots σ₂ h₂ →
      IsAdjacentAlong R (standardChamberSpace eV J.roots) (posSet R h) (posSet R h₂) v →
      ∀ α ∈ simpleFinset ν hG hi \ S.1,
        IsSimpleRootTranspose i ν eV J.roots S.roots σ α v →
      ∀ y, pair T (restrictToTorus F i ν S.roots (σ y)) (corootVector D α) = 0 →
        restrictToTorus F i ν S₂.roots (σ₂ y) = restrictToTorus F i ν S.roots (σ y)) ∧
    -- 5. the orthogonal set of `T`
    (∀ H : V T, (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ eval T α H) →
      ∃ Y : Finset E → standardChamberSpace eV J.roots,
        IsPositiveOrthogonalSet R (standardChamberSpace eV J.roots) Y ∧
        (∀ Q ∈ parabolics R (standardChamberSpace eV J.roots), ‖(Y Q : E)‖ ≤ ‖eV H‖) ∧
        ∀ (S : StandardIndex hG hi ν), ∀ σ ∈ Ωr J S, ∀ h : E,
          IsStandardChamberPoint i ν eV Δ J.roots S.roots σ h →
            (∀ y, pair T (restrictToTorus F i ν J.roots y) (eV.symm (Y (posSet R h))) =
              pair T (restrictToTorus F i ν S.roots (σ y)) H) ∧
            ∀ α ∈ simpleFinset ν hG hi \ S.1, ∀ v : E,
              IsSimpleRootTranspose i ν eV J.roots S.roots σ α v →
                eval T α H ≤ ⟪v, (Y (posSet R h) : E)⟫)

end Langlands.Global
