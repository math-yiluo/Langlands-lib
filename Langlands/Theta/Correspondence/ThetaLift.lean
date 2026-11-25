import Langlands.Representation.Smooth.IsotypicQuotient
import Langlands.Theta.Metaplectic.Defs
import Mathlib.RepresentationTheory.Irreducible

/-!
# The big theta lift and the statement of Howe duality

GKT §13.3 (Definition 13.15, Proposition 13.16, p. 399; Definition 13.17, Proposition 13.18,
p. 400; Theorem 13.19, Definition 13.20, Theorem 13.21, p. 401), on the general isotypic
quotients of `Langlands.Representation.Smooth.IsotypicQuotient` (GKT §13.2.2).

* `MetaplecticGroup.Splitting.bigTheta s π`: for a splitting `s` of a dual pair `G × H`, the big
  theta lift `Θ_{ψ,s}(π) = (ω_{ψ,s} ⊗ π^∨)_G` (Definition 13.17), a representation of `H`.
* `ThetaMultiplicityOne ω`, `ThetaInjective ω`, `HoweDuality ω`: Howe duality (Theorem 13.21)
  for a representation `ω` of `G × H`, in the form free of `θ`: (1) a smooth irreducible `π` of `G`
  that is a quotient of `ω` has a unique smooth irreducible `σ` of `H` with
  `Hom_{G×H}(ω, π ⊠ σ) ≠ 0`, and that space has dimension one; (2) `σ` determines `π`.
* `finrank_hom_eq_finrank_bigTheta`: the bridge to the book's form through Corollary 13.8:
  `dim Hom_{G×H}(ω, π ⊠ σ) = dim Hom_H(Θ_ω(π), σ)`.
* `swapRep`, `homSwapEquiv`: `ω` with the roles of `G` and `H` exchanged, and
  `Hom_{H×G}(ω ∘ swap, σ ⊠ π) ≅ Hom_{G×H}(ω, π ⊠ σ)`.
-/

noncomputable section

open TensorProduct

namespace Langlands.Theta

open Langlands.LinearMap.BilinForm (isometryGroup)

universe uG uH uS

variable {G : Type uG} {H : Type uH} [Group G] [Group H] {S : Type uS} [AddCommGroup S]
  [Module ℂ S]

section Statement

variable [TopologicalSpace G] [TopologicalSpace H]

/-- **Howe duality, part (1)** (GKT Theorem 13.21 (1), p. 401, without `Θ` and `θ`): every
smooth irreducible representation `π` of `G` that is a quotient of `ω|_G` has a smooth irreducible
`σ` of `H`, unique up to isomorphism among the smooth irreducible `σ'` with a non-zero
`G × H`-map `ω → π ⊠ σ'`, such that `Hom_{G×H}(ω, π ⊠ σ)` has dimension one. -/
def ThetaMultiplicityOne (ω : Representation ℂ (G × H) S) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → π.IsIrreducible →
    (∃ f : (restrictLeft ω).IntertwiningMap π, f ≠ 0) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ H W),
      IsSmooth σ ∧ σ.IsIrreducible ∧
      Module.finrank ℂ (ω.IntertwiningMap (outerTensor π σ)) = 1 ∧
      ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'),
        IsSmooth σ' → σ'.IsIrreducible →
        (∃ f : ω.IntertwiningMap (outerTensor π σ'), f ≠ 0) → Nonempty (σ'.Equiv σ)

/-- **Howe duality, part (2)** (GKT Theorem 13.21 (2), p. 401): if `π ⊠ σ` and `π' ⊠ σ` are both
quotients of `ω`, with `π, π', σ` smooth irreducible, then `π ≅ π'`. -/
def ThetaInjective (ω : Representation ℂ (G × H) S) : Prop :=
  ∀ (V V' W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G V')
    (σ : Representation ℂ H W), IsSmooth π → π.IsIrreducible → IsSmooth π' → π'.IsIrreducible →
    IsSmooth σ → σ.IsIrreducible →
    (∃ f : ω.IntertwiningMap (outerTensor π σ), f ≠ 0) →
    (∃ f : ω.IntertwiningMap (outerTensor π' σ), f ≠ 0) → Nonempty (π.Equiv π')

/-- **Howe duality** for a representation `ω` of `G × H` (GKT Theorem 13.21, p. 401, in the form
free of `θ`; equivalent to `dim Hom_H(θ(π), θ(π')) ≤ δ_{π,π'}` once `Θ(π)` has finite length,
Theorem 13.19, through Corollary 13.8). -/
def HoweDuality (ω : Representation ℂ (G × H) S) : Prop :=
  ThetaMultiplicityOne ω ∧ ThetaInjective ω

end Statement

section Swap

/-- `ω ∘ swap`: the representation `ω` of `G × H` as a representation of `H × G`. -/
abbrev swapRep (ω : Representation ℂ (G × H) S) : Representation ℂ (H × G) S :=
  ω.comp (MulEquiv.prodComm : H × G ≃* G × H).toMonoidHom

theorem restrictLeft_swapRep (ω : Representation ℂ (G × H) S) :
    restrictLeft (swapRep ω) = restrictRight ω := rfl

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- `Hom_{H×G}(ω ∘ swap, σ ⊠ π) = Hom_{G×H}(ω, π ⊠ σ)` by `σ ⊗ π ≅ π ⊗ σ`. -/
def homSwapEquiv (ω : Representation ℂ (G × H) S) (π : Representation ℂ G V)
    (σ : Representation ℂ H W) :
    (swapRep ω).IntertwiningMap (outerTensor σ π) ≃ₗ[ℂ] ω.IntertwiningMap (outerTensor π σ) where
  toFun F :=
    { toLinearMap := (TensorProduct.comm ℂ W V).toLinearMap ∘ₗ F.toLinearMap
      isIntertwining' := fun p => LinearMap.ext fun s => by
        have h := Representation.IntertwiningMap.isIntertwining _ _ F (p.2, p.1) s
        change TensorProduct.comm ℂ W V (F (ω (p.1, p.2) s)) =
          TensorProduct.map (π p.1) (σ p.2) (TensorProduct.comm ℂ W V (F s))
        change F (ω (p.1, p.2) s) = TensorProduct.map (σ p.2) (π p.1) (F s) at h
        rw [h]
        induction F s using TensorProduct.inductionOn with
        | tmul w v => rfl
        | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add] }
  map_add' F F' := Representation.IntertwiningMap.ext (LinearMap.ext fun s =>
    LinearEquiv.map_add (TensorProduct.comm ℂ W V) (F s) (F' s))
  map_smul' c F := Representation.IntertwiningMap.ext (LinearMap.ext fun s =>
    LinearEquiv.map_smul (TensorProduct.comm ℂ W V) c (F s))
  invFun F :=
    { toLinearMap := (TensorProduct.comm ℂ V W).toLinearMap ∘ₗ F.toLinearMap
      isIntertwining' := fun p => LinearMap.ext fun s => by
        have h := Representation.IntertwiningMap.isIntertwining _ _ F (p.2, p.1) s
        change TensorProduct.comm ℂ V W (F (ω (p.2, p.1) s)) =
          TensorProduct.map (σ p.1) (π p.2) (TensorProduct.comm ℂ V W (F s))
        change F (ω (p.2, p.1) s) = TensorProduct.map (π p.2) (σ p.1) (F s) at h
        rw [h]
        induction F s using TensorProduct.inductionOn with
        | tmul v w => rfl
        | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add] }
  left_inv F := Representation.IntertwiningMap.ext (LinearMap.ext fun s =>
    TensorProduct.comm_comm ℂ V W (F s))
  right_inv F := Representation.IntertwiningMap.ext (LinearMap.ext fun s =>
    TensorProduct.comm_comm ℂ W V (F s))

end Swap

section Bridge

variable [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- **The bridge to the book's form of Howe duality** (GKT Corollary 13.8): for `π` admissible,
`dim Hom_{G×H}(ω, π ⊠ σ) = dim Hom_H(Θ_ω(π), σ)`. -/
theorem finrank_hom_eq_finrank_bigTheta {ω : Representation ℂ (G × H) S}
    {π : Representation ℂ G V} (σ : Representation ℂ H W)
    (hG : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hπ : IsAdmissible π) (hω : IsSmooth (restrictLeft ω)) :
    Module.finrank ℂ (ω.IntertwiningMap (outerTensor π σ)) =
      Module.finrank ℂ ((bigTheta ω π).IntertwiningMap σ) :=
  (homEquivThetaHom hG hπ hω).finrank_eq

end Bridge

section Splitting

variable {R : Type*} [CommRing R] [Invertible (2 : R)] {X : Type*} [AddCommGroup X] [Module R X]
  {B : LinearMap.BilinForm R X} {ρ : Representation ℂ (HeisenbergGroup B) S}
  {ι : G × H →* isometryGroup B}

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The big theta lift for a splitting of a dual pair** (GKT Definition 13.17, p. 400):
`Θ_{ψ,s}(π) = (ω_{ψ,s} ⊗ π^∨)_G`, `ω_{ψ,s} = ω_ψ ∘ s` (Definition 13.15). -/
abbrev MetaplecticGroup.Splitting.bigTheta (s : MetaplecticGroup.Splitting ρ ι) {V : Type*}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) :
    Representation ℂ H (BigThetaSpace s.weil π) :=
  Langlands.bigTheta s.weil π

end Splitting

end Langlands.Theta
