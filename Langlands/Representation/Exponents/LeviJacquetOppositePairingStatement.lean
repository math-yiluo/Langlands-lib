import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.Contragredient
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Reductive.Basic

/-! # The pairing between opposite Jacquet modules

Renard 2026, VI.9.6, Proposition (printed p.202/PDF p.208): for a parabolic `P = MN` of
`G` with split component `A` and opposite parabolic `P̄ = M N̄`, and a smooth
representation `(π, V)` of `G`, there is an `M`-equivariant duality
`⟨·,·⟩_P : r_P^G(V) × r_{P̄}^G(Ṽ) → ℂ` inducing an isomorphism `r_{P̄}^G(Ṽ) ≅ r_P^G(V)~`,
such that `⟨r_P^G(π)(t^m) j_N(v), j_{N̄}(λ)⟩_P = δ_P^{1/2}(t^m) λ(π(t^m) v)` for
`t ∈ C_A^{++}` and all large `m` (VI.9.6.4), and such that the same identity holds for all
`t ∈ C_A^+(ε)` for some `ε > 0` depending on `v` and `λ` (VI.9.6.5).
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.9.6, Proposition: for actual rational parabolics `P = MN` and `P̄ = M N̄`
with the same Levi and `P(F) ∩ P̄(F) = M(F)`, and every smooth representation `π` of `G(F)`,
there is an isomorphism `E : r_{P̄}^G(π̃) ≅ (r_P^G π)~` of smooth representations of `M(F)`
whose pairing `⟨x, y⟩_P = E(y)(x)` satisfies, for every split component `a : A → M` with a
compatible root presentation of `P` and the restricted simple roots `Δ(P)` it defines:

* (VI.9.6.4) for all `v`, `λ` and `t ∈ C_A^{++}`, for all sufficiently large `j`,
  `⟨r_P^G(π)(t^j) j_N(v), j_{N̄}(λ)⟩_P = δ_P^{1/2}(t^j) λ(π(t^j) v)`;
* (VI.9.6.5) for all `v`, `λ` there is `ε > 0` such that for all `t ∈ C_A^+(ε)`,
  `⟨r_P^G(π)(t) j_N(v), j_{N̄}(λ)⟩_P = δ_P^{1/2}(t) λ(π(t) v)`.

Here `δ_P^{1/2}` is the normalizing character of `r_P^G` in (VI.1.2.2), so that
`r_P^G(π)(x) j_N(v) = δ_P^{1/2}(x) j_N(π(x) v)`. -/
def LeviJacquetOppositePairingStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
      (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
        haveI := hm.isConnectedReductive.isAffineHom
        letI : TopologicalSpace (rationalPoints M) := leviPointTopology m hm
        haveI : LocallyCompactSpace (rationalPoints M) :=
          leviPoints_locallyCompactSpace p m hp hm
        haveI : NonarchimedeanGroup (rationalPoints M) :=
          leviPoints_nonarchimedeanGroup p m hp hm
        ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G),
          ∃ E : (leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar).obj
                π.contragredient ≅
              ((leviJacquetFunctor.{u, v} p m n hp hn hm hmul).obj π).contragredient,
            ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
              (pres : ParabolicRootPresentation p m a),
              let Δ : Set (characterLattice A) :=
                (fun α => pres.data.f ≫ α) ''
                  (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
              let rP := (leviJacquetFunctor.{u, v} p m n hp hn hm hmul).obj π
              let pairing : rP →
                  (leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar).obj
                    π.contragredient → ℂ :=
                fun x y => smoothDualPairing rP.representation (SmoothRep.hom E.hom y) x
              let jN : π → rP := fun x =>
                Jacquet.Localization.mk π.representation (pointImage (n ≫ p)) 1 x
              let jNbar : π.contragredient →
                  (leviJacquetFunctor.{u, v} pbar mbar nbar hpbar hnbar hmbar hmulbar).obj
                    π.contragredient := fun ℓ =>
                Jacquet.Localization.mk π.contragredient.representation
                  (pointImage (nbar ≫ pbar)) 1 ℓ
              let δ : rationalPoints M → ℂ := fun x =>
                ((HaarModulus.closedInverseHalfCharacter (pointImage (n ≫ p))
                    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup)
                    (pointImage (m ≫ p)) (pointImage_le_normalizer p m n hn)
                    (leviPointsEquiv p m hp hm x) : ℂˣ) : ℂ)
              let incM : rationalPoints A.toGrp → rationalPoints M := rationalPoints.map a
              let incG : rationalPoints A.toGrp → rationalPoints G := fun t =>
                (leviPointsEquiv p m hp hm (incM t) : rationalPoints G)
              (∀ (x : π) (ℓ : π.contragredient),
                ∀ t ∈ CocharacterUniformizer.CAstrict k A Δ,
                  ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
                    pairing (rP.representation (incM (t ^ j)) (jN x)) (jNbar ℓ) =
                      δ (incM (t ^ j)) *
                        smoothDualPairing π.representation ℓ
                          (π.representation (incG (t ^ j)) x)) ∧
              ∀ (x : π) (ℓ : π.contragredient), ∃ ε : ℝ, 0 < ε ∧
                ∀ t ∈ CocharacterUniformizer.CAepsilon k A Δ ε,
                  pairing (rP.representation (incM t) (jN x)) (jNbar ℓ) =
                    δ (incM t) * smoothDualPairing π.representation ℓ (π.representation (incG t) x)

end Langlands.Aubert.General.RepresentedParabolic
