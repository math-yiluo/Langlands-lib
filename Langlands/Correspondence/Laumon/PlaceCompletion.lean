import Langlands.LocalField.LaurentSeries
import Langlands.Weil.Local.Assembly

/-!
# Completion of the decomposition field of a place of a Dedekind domain

Let `R` be a Dedekind domain with fraction field `K`, `Ω` a separable closure of `K`, `p` a
nonzero maximal ideal of `R` with finite residue field and `K` of positive characteristic, and
`Q` a maximal ideal above `p` of the integral closure `B` of `R` in `Ω`. This module states that
the decomposition field `K_Q` (the fixed field of the stabilizer of `Q`) has a dense embedding
into a Laurent series field `κ((t))` over a finite field, which extends to the separable
closures so that restriction of automorphisms is a topological isomorphism from the absolute
Galois group of `κ((t))` onto `Gal(Ω/K_Q)`, matching the valuation, the inertia group and the
action on the residue field of `Q` with the Library's `closureValuation`, `absoluteInertia` and
`absoluteResidueHom` of `κ((t))`.

The comparison uses Serre, *Local Fields* (`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`), I §7,
Propositions 19–20 (pp. 20–21), II §2, Proposition 3, Corollaries 2–3 and Exercises 1–2
(pp. 28–30), II §3, Theorem 1, Corollaries 1, 3–4 and Proposition 4 (pp. 30–32),
and II §4, Theorem 2 and Proposition 8 (pp. 33–36).
-/

noncomputable section

universe u

open scoped Pointwise

namespace Langlands.Henniart.Laumon

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

attribute [local instance] Ideal.Quotient.field in
open Langlands.LocalGalois Langlands.LocalGalois.SepClosed Langlands.Weil.Local.SepClosed in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Completion of the decomposition field at a place.** For a Dedekind domain `R` with
fraction field `K` of positive characteristic, a separable closure `Ω` of `K`, a nonzero maximal
ideal `p` of `R` with finite residue field and a maximal ideal `Q` above `p` of the integral
closure `B` of `R` in `Ω`, let `K_Q` be the decomposition field. There are a finite field `κ`,
a dense ring map `ι₀ : K_Q → κ((t))`, an extension `ι : Ω → κ((t))^sep` and a topological group
isomorphism `φ` from the absolute Galois group of `κ((t))` onto `Gal(Ω/K_Q)` with
`ι ∘ φ σ = σ ∘ ι`. The map `ι` sends `B` into the valuation ring of the Library's
`closureValuation`, and `Q` is the preimage of its maximal ideal. The map `φ` carries the
Library's `absoluteInertia` onto the elements whose image in `Gal(Ω/K)` lies in the inertia
group of `Q`. Reduction of `ι` followed by `residueClosureEquiv` gives a ring isomorphism `ψ`
from `B/Q` onto the algebraic closure of the residue field of `κ((t))`. This isomorphism
transports the action of `φ σ` on `B/Q` to the Library's `absoluteResidueHom σ`. -/
def PlaceCompletionStatement : Prop :=
  ∀ (R K Ω : Type u) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [IsSepClosure K Ω] (p : Ideal R) [p.IsMaximal], p ≠ ⊥ → Finite (R ⧸ p) →
    ringChar K ≠ 0 →
  ∀ (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal],
    Q.comap (algebraMap R (integralClosure R Ω)) = p →
      ∃ (κ : Type u) (_ : Field κ) (_ : Finite κ)
        (ι₀ : IntermediateField.fixedField (MulAction.stabilizer Gal(Ω/K) Q) →+*
          LaurentSeries κ)
        (ι : Ω →+* SeparableClosure (LaurentSeries κ))
        (φ : Gal(SeparableClosure (LaurentSeries κ)/LaurentSeries κ) ≃ₜ*
          Gal(Ω/IntermediateField.fixedField (MulAction.stabilizer Gal(Ω/K) Q))),
        DenseRange ι₀ ∧
        (∀ a : IntermediateField.fixedField (MulAction.stabilizer Gal(Ω/K) Q),
          ι a = algebraMap (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) (ι₀ a)) ∧
        (∀ σ a, ι (φ σ a) = σ (ι a)) ∧
        (∀ b : integralClosure R Ω,
          closureValuation (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) (ι b) ≤ 1 ∧
            (b ∈ Q ↔
              closureValuation (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) (ι b) < 1)) ∧
        (∀ σ, σ ∈ absoluteInertia (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) ↔
          AlgEquiv.restrictScalarsHom K (φ σ) ∈ Q.inertia Gal(Ω/K)) ∧
        letI := localNormedField (LaurentSeries κ)
        letI := localNormedField_ultrametric (LaurentSeries κ)
        letI := localNormedField_complete (LaurentSeries κ)
        ∃ ψ : (integralClosure R Ω ⧸ Q) ≃+*
            AlgebraicClosure (localResidueField (LaurentSeries κ)),
          (∀ (b : integralClosure R Ω)
              (c : closureIntegers (LaurentSeries κ) (SeparableClosure (LaurentSeries κ))),
            (c : SeparableClosure (LaurentSeries κ)) = ι b →
              ψ (Ideal.Quotient.mk Q b) =
                residueClosureEquiv (LaurentSeries κ) (SeparableClosure (LaurentSeries κ))
                  (IsLocalRing.residue _ c)) ∧
          ∀ σ (b b' : integralClosure R Ω),
            (b' : Ω) = φ σ b →
              ψ (Ideal.Quotient.mk Q b') =
                AlgEquiv.toAlgHom
                  (absoluteResidueHom (LaurentSeries κ) (SeparableClosure (LaurentSeries κ)) σ)
                  (ψ (Ideal.Quotient.mk Q b))

end Langlands.Henniart.Laumon
