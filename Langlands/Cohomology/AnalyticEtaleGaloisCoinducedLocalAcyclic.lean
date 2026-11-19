import Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclicCorrected

/-! # Coinduced Galois fixed sections and ordinary higher direct images -/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Data

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] {ρ : G →* Aut X}

/-- The twisted endomorphism, with trivial twist, given by an automorphism of an
étale object that commutes with its structure arrow to `X`. -/
def deckEndomorphism (V : TwistedOver (etale (K := K)) ρ) (e : V.obj.left ≅ V.obj.left)
    (he : e.hom ≫ V.hom = V.hom) : V ⟶ V :=
  homMk 1 e.hom (by rw [he, rho_one_hom, Category.comp_id])

variable [TopologicalSpace G] {R : Type w} [CommRing R]

/-- The sections of an étale `G`-sheaf over `V` fixed by every element of a subgroup
`Kₒ` of the subgroup of a lift `l`, for the local action `liftAction l`: the element
`k` acts by the twisted endomorphism with twist `k⁻¹` and arrow `l.action k⁻¹`. -/
def liftFixedSubmodule (S : EtaleGSheaf ρ (ModuleCat.{w} R))
    (V : TwistedOver (etale (K := K)) ρ) (l : ActionLift ρ V.hom) (Kₒ : Subgroup G)
    (hK : Kₒ ≤ l.subgroup) : Submodule R (S.obj.obj.obj (op V)) :=
  ⨅ (k : G) (hk : k ∈ Kₒ),
    LinearMap.ker ((S.obj.obj.map (liftAction l ⟨k, hK hk⟩).unop.op).hom - LinearMap.id)

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]

/-- Coinduced fixed sections on equivariant finite Galois data. Let `V` be a
distinguished étale object over `X` with a finite group `Γ` of automorphisms over
`X` acting freely on the `L`-valued points of `V`, and with a lift `l` of the
action whose automorphisms commute with those of `Γ`. Then, for every open
subgroup `Kₒ` of the lift subgroup, the module of `Kₒ`-fixed sections of `S` over
`V` is coinduced from the trivial subgroup of `Γ`: some linear map `π` to a
module `A` makes `s ↦ (γ ↦ π (γ s))` a bijection onto all functions `Γ → A`,
where `γ s` is restriction along the deck endomorphism of `γ`. -/
def HasCoinducedGaloisFixedSections (S : EtaleGSheaf ρ (ModuleCat.{w} R)) :
    Prop :=
  ∀ (V : TwistedOver (etale (K := K)) ρ), IsDistinguishedEtale V.hom →
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (deck : Γ →* Aut V.obj.left)
      (hdeck : ∀ γ : Γ, (deck γ).hom ≫ V.hom = V.hom),
      (∀ (γ : Γ) (p : (localizedFieldPointFunctor L).obj V.obj.left),
        (localizedFieldPointFunctor L).map (deck γ).hom p = p → γ = 1) →
      ∀ l : ActionLift ρ V.hom,
        (∀ (γ : Γ) (k : l.subgroup),
          (l.action k).hom ≫ (deck γ).hom = (deck γ).hom ≫ (l.action k).hom) →
        ∀ Kₒ : Subgroup G, IsOpen (Kₒ : Set G) → ∀ hK : Kₒ ≤ l.subgroup,
          ∃ (A : ModuleCat.{w} R) (π : S.obj.obj.obj (op V) →ₗ[R] A),
            Function.Bijective fun s : liftFixedSubmodule S V l Kₒ hK => fun γ : Γ =>
              π ((S.obj.obj.map (deckEndomorphism V (deck γ) (hdeck γ)).op).hom s.1)

end Data

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

/-- Local analytic input: for a Hausdorff analytic space with a continuous action,
an étale `G`-sheaf whose fixed sections on equivariant finite Galois data are
coinduced has vanishing positive ordinary higher direct images after restriction to
the ordinary étale site. This statement is unproved. -/
def AnalyticEtaleGaloisCoinducedLocalAcyclicStatement
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → IsContinuousAction ρ →
    ∀ S : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R),
      HasCoinducedGaloisFixedSections L S → ∀ q : ℕ,
        IsZero ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj
          ((TwistedOver.restriction ρ (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)).obj
            (((distinguishedLiftSystem ρ).smoothSheafInclusion
              (ModuleCat.{max u (v + 1) uL} R) (twistedEtaleTopology ρ)).obj S)))

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
