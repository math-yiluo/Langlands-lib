import Langlands.Geometry.Building.KPMoyPrasadLieLattices
import Langlands.Geometry.Building.KPLieFiltrationDual

/-! # Statements on the constructed lattices `𝔤_{x,r} = Lie(𝒢_{x,r})`

For the lattices `moyPrasadLie` and the `LieFiltrationData` `lieFiltrationData` constructed in
`KPMoyPrasadLieLattices` from chosen models, this module states

* independence of the chosen model `𝒢_{x,r}` (KP Corollary 2.10.11), for models over `𝒪[F]`
  with the same integral points over the integers of the maximal unramified extension;
* the description of KP 13.3.3: `𝔤_{x,r}` is the `𝒪[F]`-span of `𝔷_r = Lie(𝒵_r)` and of the
  `𝔲_ψ = Lie(𝒰_ψ)` with `ψ(x) ≥ r`;
* the periodicity of KP 13.3.1: `𝔤_{x,r+1} = 𝔪 𝔤_{x,r}`, and `IsPeriodic` for the
  constructed `LieFiltrationData`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **KP Corollary 2.10.11 for the lattices `𝔤_{x,r}`.** Every smooth model `M` of `G` over
`𝒪[F]` whose integral points over the integers of the maximal unramified extension are those
of the chosen model `𝒢_{x,r}` (namely `G(K)_{x,r}`) has Lie lattice `𝔤_{x,r}`. The hypothesis
cannot be weakened to equality of the integral points over `𝒪[F]`. -/
def MoyPrasadLieIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (h : P.MinimalCongruentCentralizerOrder)
    (x : P.Apartment) (r : ℝ≥0) (M : IntegralModel ↥𝒪[F] F G),
    M.IsSmooth →
    M.baseChangeUnramified.integralPoints =
      (P.moyPrasadModel hG hP h x r).baseChangeUnramified.integralPoints →
    M.lieLattice = P.moyPrasadLie hG hP h x r

/-- **KP 13.3.3.** The lattice `𝔤_{x,r} = Lie(𝒢_{x,r})` is the `lieFiltration x r` of the
constructed `LieFiltrationData`: the `𝒪[F]`-span of the image of `𝔷_r = Lie(𝒵_r)` in `Lie(G)`
and of the lattices `𝔲_ψ = Lie(𝒰_ψ)` of the affine roots `ψ` with `ψ(x) ≥ r`. -/
def MoyPrasadLieSpanStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hZ : CentralizerModelStatement.{u}) (hU : AffineRootGroupModelStatement.{u})
    (hOrder : MinimalCongruentOrderStatement.{u}) (hP : P.SatisfiesApartmentAxioms)
    (h : P.MinimalCongruentCentralizerOrder) (x : P.Apartment) (r : ℝ≥0),
    P.moyPrasadLie hG hP h x r = (P.lieFiltrationData hZ hU hOrder hP).lieFiltration x r

/-- **KP 13.3.1 (Proposition 8.5.16 with Lemma A.5.13).** The lattices `𝔤_{x,r}` satisfy
`𝔤_{x,r+1} = 𝔪 𝔤_{x,r}`, where `𝔪` is the maximal ideal of `𝒪[F]`, and the constructed
`LieFiltrationData` is periodic in the sense of `IsPeriodic`. -/
def MoyPrasadLiePeriodicStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (hG : MoyPrasadModelStatement.{u})
    (hZ : CentralizerModelStatement.{u}) (hU : AffineRootGroupModelStatement.{u})
    (hOrder : MinimalCongruentOrderStatement.{u}) (hP : P.SatisfiesApartmentAxioms)
    (h : P.MinimalCongruentCentralizerOrder),
    (∀ (x : P.Apartment) (r : ℝ≥0),
      P.moyPrasadLie hG hP h x (r + 1) = 𝓂[F] • P.moyPrasadLie hG hP h x r) ∧
    (P.lieFiltrationData hZ hU hOrder hP).IsPeriodic

end Langlands.Geometry.Building
