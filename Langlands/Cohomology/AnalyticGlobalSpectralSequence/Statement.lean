import Langlands.Cohomology.AnalyticGlobalComposite.Statement
import Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement

/-!
# Berkovich's ordinary equivariant cohomology spectral sequences

Statement of Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
§1.2, pp. 4–5, on the étale and quasi-étale analytic sites. The second page is
`H^p(G, H^q(X{G}, F))` and the abutment is `H^{p+q}(X(G), F)`. The spectral
sequence used here is the covariant hyperext spectral sequence of the trivial
smooth representation and `RΓ(X{G}, F)`. Convergence is expressed using the
finite truncation filtration on the abutment, not an assumed spectral sequence.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite CategoryTheory.Triangulated Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticGlobalSpectralSequence

open HyperextSpectralSequence AnalyticGlobalComposite

universe w vC uC uH u v uL z

section Derived

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The covariant hyperext spectral sequence from `A` in degree `0` to `D`.
This is the existing hyperext spectral sequence in the opposite of `D(C)`. -/
abbrev spectralSequence (D : DerivedCategory C) (A : C) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w} :=
  hyperextSpectralSequence (opTStructure DerivedCategory.TStructure.t) (op D)
    (op ((DerivedCategory.singleFunctor C 0).obj A))

/-- First-quadrant convergence of the specified spectral sequence to `H`.
The decreasing abutment filtration is the truncation filtration in the opposite
category. In degree `n` it starts at the whole group in step `0` and ends at
zero in step `n + 1`. In bidegree `(p,q)` both differentials at that position
vanish and the page is the graded piece of the filtration as soon as
`r ≥ 2`, `r ≥ p + 1` and `r ≥ q + 2`. -/
def FirstQuadrantAbutmentStatement (D : DerivedCategory C) (A : C)
    (H : ℕ → AddCommGrpCat.{uH}) : Prop :=
  let t := opTStructure (DerivedCategory.TStructure.t : TStructure (DerivedCategory C))
  let D' := op D
  let A' := op ((DerivedCategory.singleFunctor C 0).obj A)
  (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero (((spectralSequence D A).page 2).X (p, q))) ∧
  (∀ n : ℕ, Nonempty (ShiftedHom D' A' (n : ℤ) ≃+ H n) ∧
    HyperextAbutment.filtration t D' A' (n : ℤ) 0 = ⊤ ∧
    HyperextAbutment.filtration t D' A' (n : ℤ) ((n : ℤ) + 1) = ⊥) ∧
  ∀ (p q r : ℤ) (hr : 2 ≤ r), p + 1 ≤ r → q + 2 ≤ r →
    (∀ pq : ℤ × ℤ,
      ((spectralSequence D A).page r hr).d (p, q) pq = 0 ∧
      ((spectralSequence D A).page r hr).d pq (p, q) = 0) ∧
    Nonempty (((spectralSequence D A).page r hr).X (p, q) ≅
      AddCommGrpCat.of (HyperextAbutment.graded t D' A' (p + q) p))

end Derived

/-- Berkovich §1.2, étale case: the covariant hyperext spectral sequence of the
trivial `R`-representation and `RΓ(X{G}, F)` for an étale `G`-sheaf `F` is
first-quadrant, with second page `Ext^p(R, H^q(X{G}, F))` in smooth
representations and abutment `H^{p+q}(X(G), F)`. -/
def AnalyticEtaleGlobalSpectralSequenceStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)),
    letI : HasExt.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
      hasExt_of_hasDerivedCategory _
    let D := DerivedCategory.Plus.ι.obj ((etaleGSheafComplex.{u, v, uL} ρ R).obj F)
    let A := trivialSmoothRep R G
    (∀ p q : ℕ, Nonempty (((spectralSequence D A).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      Abelian.Ext.{w} A ((etaleGSheafCohomology.{u, v, uL} ρ R q).obj F) p)) ∧
    FirstQuadrantAbutmentStatement D A
      (fun n => AddCommGrpCat.of ((etaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F))

/-- Berkovich §1.2, quasi-étale case: the covariant hyperext spectral sequence of
the trivial `R`-representation and `RΓ(X{G}, F)` for a quasi-étale `G`-sheaf
`F` is first-quadrant, with second page `Ext^p(R, H^q(X{G}, F))` in smooth
representations and abutment `H^{p+q}(X(G), F)`. -/
def AnalyticQuasiEtaleGlobalSpectralSequenceStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)),
    letI : HasExt.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
      hasExt_of_hasDerivedCategory _
    let D := DerivedCategory.Plus.ι.obj ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).obj F)
    let A := trivialSmoothRep R G
    (∀ p q : ℕ, Nonempty (((spectralSequence D A).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      Abelian.Ext.{w} A ((quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F) p)) ∧
    FirstQuadrantAbutmentStatement D A
      (fun n => AddCommGrpCat.of ((quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F))

end Langlands.Cohomology.AnalyticGlobalSpectralSequence
