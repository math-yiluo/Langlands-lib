import Langlands.Geometry.Building.TorusFiltration.MoyPrasad
import Langlands.Geometry.Building.TorusFiltration.GaloisStatements
import Langlands.GroupScheme.Lie.WeightSupportGalois

/-! # Statements on the Lie filtration and the Moy–Prasad isomorphism of tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Geometry.Building

/- The tower instance of the generic Lie algebra is tried first: the search through the
intermediate-field instances of `inertiaFixedField F` does not terminate in time. -/
attribute [local instance high] GenericLie.instIsScalarTower

/-- The Lie filtration `t(K)_r` of a `K`-torus is antitone in `r`, consists of lattices, and
satisfies the Lie congruence `t(K)_{r+1} = 𝔪 • t(K)_r` for every `r ≥ 0` (KP Propositions
B.10.15–B.10.16, Lemma A.5.13(4)). -/
def MinimalCongruentLieFiltrationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp),
    Antitone (minimalCongruentLie F T hT) ∧
      (∀ r : ℝ≥0, Submodule.IsLattice (inertiaFixedField F) (minimalCongruentLie F T hT r)) ∧
      ∀ r : ℝ≥0, IsLocalRing.maximalIdeal (fixedFieldIntegers F) • minimalCongruentLie F T hT r =
        minimalCongruentLie F T hT (r + 1)

/-- KP Proposition B.10.16, bijectivity: for `1 ≤ r ≤ s ≤ r + ⌊r⌋` the homomorphism
`T(K)_r / T(K)_s → t(K)_r / t(K)_s` built from the congruence–Lie homomorphism of the model
`𝒯_{r - ⌊r⌋}` is bijective. -/
def MinimalCongruentMoyPrasadBijectiveStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp)
    (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
    (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u})
    (r s : ℝ≥0) (hr : 1 ≤ r) (hrs : r ≤ s) (hs : s ≤ r + ⌊r⌋₊),
    Function.Bijective (minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs)

/-- KP Proposition B.10.16, functoriality: for a homomorphism of `K`-tori `f : T ⟶ U` the
differential of `f` carries `t(K)_r` into `u(K)_r`, and the homomorphisms of Proposition B.10.16
for `T` and `U` commute with the maps induced by `f` on `T(K)_r / T(K)_s` and by its
differential on `t(K)_r / t(K)_s`. -/
def MinimalCongruentMoyPrasadFunctorialStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (T U : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffine T.X.left] [IsAffine U.X.left] (hT : IsTorus T.toGrp) (hU : IsTorus U.toGrp)
    (f : T ⟶ U),
    (∀ r : ℝ≥0, (minimalCongruentLie F T hT r).map
        (GenericLie.map (fixedFieldIntegers F) (CommGroupScheme.groupHom f)) ≤
      minimalCongruentLie F U hU r) ∧
    ∀ (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
      (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u})
      (r s : ℝ≥0) (hr : 1 ≤ r) (hrs : r ≤ s) (hs : s ≤ r + ⌊r⌋₊),
      (minimalCongruentMoyPrasad F U hU h𝔩 hF r s hr hrs hs).comp
          (minimalCongruentQuotientMap F hT hU f r s) =
        (minimalCongruentLieQuotientMap F hT hU f r s).toAddMonoidHom.toMultiplicative.comp
          (minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs)

/-- Corrected KP Proposition B.10.17: for `0 < r < s ≤ r + 1` with `s ≤ 2r` there is an
isomorphism of abelian groups `T(K)_r / T(K)_s ≅ t(K)_r / t(K)_s`, possibly not functorial.
KP state it for all `0 < r < s ≤ r + 1`; the condition `s ≤ 2r`, automatic for `r ≥ 1`, is
needed for `r < 1`. -/
def MinimalCongruentQuotientIsoStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffine T.X.left]
    (hT : IsTorus T.toGrp) (r s : ℝ≥0),
    0 < r → r < s → s ≤ r + 1 → s ≤ 2 * r →
      Nonempty (minimalCongruentQuotient F T hT r s ≃*
        Multiplicative (minimalCongruentLieQuotient F T hT r s))

/-- Galois compatibility (KP Propositions B.10.16 and B.10.17, compatibility with unramified
extensions). Let `S` be an `F`-torus and `T = S_K` its base change to `K`, on whose points and
Lie algebra `Gal(K/F)` acts through the coefficients (`rationalConjugate`,
`Lie.baseChangeGaloisEquiv`).
1. The homomorphism of Proposition B.10.16 commutes with `σ ∈ Gal(K/F)`: if it sends the class
   of `g ∈ T(K)_r` to the class of `X ∈ t(K)_r`, then `σ g ∈ T(K)_r`, `σ X ∈ t(K)_r`, and it
   sends the class of `σ g` to the class of `σ X`.
2. In the range of the corrected Proposition B.10.17 there is an isomorphism
   `T(K)_r / T(K)_s ≅ t(K)_r / t(K)_s` commuting with `Gal(K/F)` in the same sense. -/
def MinimalCongruentMoyPrasadGaloisStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine S.X.left]
    [IsAffine (torusUnramifiedBaseChange F S).X.left] (hS : IsTorus S.toGrp),
    let T := torusUnramifiedBaseChange F S
    let hT : IsTorus T.toGrp := IsTorus.baseChange hS
    let σL : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
        GenericLie (fixedFieldIntegers F) T.toGrp → GenericLie (fixedFieldIntegers F) T.toGrp :=
      fun σ X => (GenericLie.equiv (fixedFieldIntegers F) T.toGrp).symm
        (Lie.baseChangeGaloisEquiv F (inertiaFixedField F) S.toGrp σ
          (GenericLie.equiv (fixedFieldIntegers F) T.toGrp X))
    (∀ (h𝔩 : IntegralModel.CongruenceModelLieLatticeStatement.{u})
      (hF : IntegralModel.CongruenceLieFunctorialityStatement.{u})
      (r s : ℝ≥0) (hr : 1 ≤ r) (hrs : r ≤ s) (hs : s ≤ r + ⌊r⌋₊)
      (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : minimalCongruentPoints F T hT r) (X : minimalCongruentLie F T hT r),
      minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs (QuotientGroup.mk g) =
          Multiplicative.ofAdd (Submodule.Quotient.mk X) →
        ∃ (hg : rationalConjugate F (inertiaFixedField F) S.toGrp σ g.val ∈
            minimalCongruentPoints F T hT r)
          (hX : σL σ X.val ∈ minimalCongruentLie F T hT r),
          minimalCongruentMoyPrasad F T hT h𝔩 hF r s hr hrs hs (QuotientGroup.mk ⟨_, hg⟩) =
            Multiplicative.ofAdd (Submodule.Quotient.mk ⟨_, hX⟩)) ∧
    ∀ r s : ℝ≥0, 0 < r → r < s → s ≤ r + 1 → s ≤ 2 * r →
      ∃ e : minimalCongruentQuotient F T hT r s ≃*
          Multiplicative (minimalCongruentLieQuotient F T hT r s),
        ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
          (g : minimalCongruentPoints F T hT r) (X : minimalCongruentLie F T hT r),
          e (QuotientGroup.mk g) = Multiplicative.ofAdd (Submodule.Quotient.mk X) →
            ∃ (hg : rationalConjugate F (inertiaFixedField F) S.toGrp σ g.val ∈
                minimalCongruentPoints F T hT r)
              (hX : σL σ X.val ∈ minimalCongruentLie F T hT r),
              e (QuotientGroup.mk ⟨_, hg⟩) = Multiplicative.ofAdd (Submodule.Quotient.mk ⟨_, hX⟩)

/-- The statements of this module together: the Lie filtration, bijectivity and functoriality
of the Moy–Prasad homomorphism (KP Proposition B.10.16), the corrected Proposition B.10.17, and
Galois compatibility. -/
def MinimalCongruentMoyPrasadStatements : Prop :=
  MinimalCongruentLieFiltrationStatement.{u} ∧ MinimalCongruentMoyPrasadBijectiveStatement.{u} ∧
    MinimalCongruentMoyPrasadFunctorialStatement.{u} ∧ MinimalCongruentQuotientIsoStatement.{u} ∧
    MinimalCongruentMoyPrasadGaloisStatement.{u}

end Langlands.Geometry.Building
