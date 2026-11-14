import Langlands.Automorphic.AssociatedGammaLocalMatch
import Langlands.Automorphic.OperatorScalarCentralCharacter
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.LocalFactor.BrauerKernel.PlaceRamification
import Langlands.Automorphic.StableTwistGammaMatchStatement

/-!
# Local inputs of the stable comparison at ramified places

The hypotheses of `StableTwistPairGammaMatchStatement` at a finite place, for the local
classes of a cuspidal pair and the local restrictions of weakly associated relative Weil
representations: the twisted arithmetic class as a `twistClass`, the conductor of a deep
local twist, the central character of a local component, and the determinant of a local
restriction.
-/

noncomputable section

set_option autoImplicit false

universe u uQ uV uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- The twisted arithmetic class is the class twist by the local character of `χ_z`. -/
theorem localPairClass_twist_eq_twistClass
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) {z : FinitePlace F}
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (χ : HeckeCharacter F) :
    localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι =
      WeilDeligneRepresentation.twistClass
        (Correspondence.weilCharacter (padicField z)
          (Correspondence.baseReciprocityCandidate _ eC)
          (quasicharacterBase z (χ.finiteComponent z)))
        (localPairClass S ι) := by
  rw [localPairClass_twist_eq S ι _ (localTwistCharacter eC χ).toMonoidHom
    (reciprocityCharacter_apply_localMap hι eC heC χ)]
  rfl

/-- A local character nontrivial on the principal units of level `r` has conductor larger
than `r`. -/
theorem lt_multiplicativeConductor_quasicharacterBase {z : FinitePlace F}
    (η : (FiniteCompletion F z)ˣ →ₜ* ℂˣ) (r : ℕ) (hη : NontrivialOnPrincipalUnits z η r) :
    r < (padicField z).canonicalTopologicalData.multiplicativeConductor
      (quasicharacterBase z η) :=
  LocalFactor.NonabelianBrauer.lt_multiplicativeConductor_of_nontrivialOnPrincipalUnits z η r
    hη rfl

/-- The determinant of a local restriction of `S` with `det S = ω ∘ τ_F` is the local Weil
character of `ω_z`. -/
theorem determinantCharacter_localComponent
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)) {z : FinitePlace F}
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (ω : HeckeCharacter F)
    (hdet : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω) :
    FiniteRepresentation.determinantCharacter (localComponent S ι) =
      Correspondence.weilCharacter (padicField z)
        (Correspondence.baseReciprocityCandidate _ eC)
        (quasicharacterBase z (ω.finiteComponent z)) := by
  ext g
  change LinearMap.det (S.representation (ι g)) = _
  rw [← FiniteRepresentation.determinantCharacter_apply, hdet,
    reciprocityCharacter_apply_localMap hι eC heC ω g]
  rfl

set_option maxHeartbeats 1000000 in
/-- In a local component of a presentation of a realization with central character `ω`, the
scalar `a` at `z` acts by `ω_z(a)`. -/
theorem localComponent_scalar_of_hasCentralCharacter [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {T : Automorphic.CuspidalOperatorRealization F r}
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T) (ω : HeckeCharacter F)
    (hω : T.realization.HasCentralCharacter ω) (z : FinitePlace F)
    (a : (FiniteCompletion F z)ˣ) (f : (P.localComponent z).Space) :
    (P.localComponent z).representation (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a) f =
      ((ω.finiteComponent z a : ℂˣ) : ℂ) • f := by
  have hmem := Automorphic.CuspidalSpectralPresentation.localComponent_le_full P z f.2
  set g := AdelicGL.scalar F (r + 1) (finiteIdeleInclusion F z a) with hg
  have hscal : AdelicGL.ofFinite F (r + 1) (FiniteAdelicGL.localInclusion F (r + 1) z
      (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a)) = g :=
    (AdelicGL.scalar_finiteIdeleInclusion F (r + 1) z a).symm
  have hcomm : ∀ y : AdelicGL F (r + 1), y * g = g * y := fun y =>
    (Matrix.GeneralLinearGroup.scalar_commute (finiteIdeleInclusion F z a) y).symm
  apply (P.localComponent z).toContinuous_injective
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h1 : Automorphic.ContinuousRationalFunctions.evaluate F (r + 1)
      ((P.localComponent z).toContinuous ((P.localComponent z).representation
        (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) a) f)) x =
      Automorphic.ContinuousRationalFunctions.evaluate F (r + 1)
        ((P.localComponent z).toContinuous f) (g * x) := by
    rw [Automorphic.LocalRealization.evaluate_representation, hscal, hcomm]
  have h2 := hω hmem (finiteIdeleInclusion F z a) x
  exact h1.trans h2

set_option maxHeartbeats 1000000 in
/-- The local class at `z` of a presentation of a realization with central character `ω` has
central character `ω_z`. -/
theorem centralActsBy_localClass [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {T : Automorphic.CuspidalOperatorRealization F r}
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (h : HasIrreducibleAdmissibleComponents P) (ω : HeckeCharacter F)
    (hω : T.realization.HasCentralCharacter ω) (z : FinitePlace F)
    (a : (padicField z).Carrierˣ) :
    Correspondence.CentralActsBy (padicField z) (localClass P h z) a
      (quasicharacterBase z (ω.finiteComponent z) a) :=
  ⟨(P.localComponent z).padicObject (h z).1 (h z).2, rfl, fun f =>
    localComponent_scalar_of_hasCentralCharacter P ω hω z a f⟩

end Langlands.ClassField.Global.RelativeWeilGroup
