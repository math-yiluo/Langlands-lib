import Langlands.Global.RankinSelberg.CuspidalMixedWhittakerFunctionalStatement
import Langlands.Representation.Archimedean.MixedSmoothIntertwiner

/-! # Whittaker comparison along mixed smooth intertwiners -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 55000

open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Automorphic NumberField Langlands.Archimedean Langlands.Archimedean.MixedSmooth

universe u v v'

attribute [local instance] regSchemeAffine regSchemeSmooth regRationalAddCommGroup
  regContinuousAddCommGroup regSmoothAddCommGroup regFormsAddCommGroup regStableAddCommGroup
  regRealizationAddCommGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (ψ : AddChar (Adeles F) ℂ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {E' : Type v'} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))]
  (σ : FiniteAdelicGL F (r + 1) →* (E →L[ℂ] E))
  (π : ArchimedeanGL F (r + 1) →* (E →L[ℂ] E))
  (c : ∀ g d x, π g (σ d x) = σ d (π g x))
  (σ' : FiniteAdelicGL F (r + 1) →* (E' →L[ℂ] E'))
  (π' : ArchimedeanGL F (r + 1) →* (E' →L[ℂ] E'))
  (c' : ∀ g d x, π' g (σ' d x) = σ' d (π' g x))
  (M : E →L[ℂ] E') (hf : ∀ d x, M (σ d x) = σ' d (M x))
  (ha : ∀ g x, M (π g x) = π' g (M x))

local notation "modelSpace" => ArchimedeanMatrix F (r + 1)
local notation "W" => Vectors (A := modelSpace) σ π c
local notation "W'" => Vectors (A := modelSpace) σ' π' c'
local notation "f" => MixedSmooth.map (A := modelSpace) σ π c σ' π' c' M hf ha
local notation "τ" => MixedSmooth.finiteRepresentation (A := modelSpace) σ π c
local notation "τ'" => MixedSmooth.finiteRepresentation (A := modelSpace) σ' π' c'
local notation "ι" => MixedSmooth.archimedeanRepresentation (A := modelSpace) σ π c
local notation "ι'" => MixedSmooth.archimedeanRepresentation (A := modelSpace) σ' π' c'

omit [CompactSpace (AdeleQuotient F)] [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))] in
/-- Pullback along a bounded intertwiner preserves both derivative
continuity at each level and the full adelic Whittaker character. -/
theorem isMixedWhittakerFunctional_comp
    (ℓ : W' →ₗ[ℂ] ℂ) (hℓ : IsMixedWhittakerFunctional (r := r) ψ σ' π' c' ℓ) :
    IsMixedWhittakerFunctional (r := r) ψ σ π c (ℓ.comp (f).toLinearMap) := by
  refine ⟨isContinuousAtEachLevel_comp σ π c σ' π' c' M hf ha ℓ hℓ.1, ?_⟩
  intro z w
  let a := archPart F (r + 1) z.val
  let d := finPart F (r + 1) z.val
  have he : f (τ d (ι a w)) = τ' d (ι' a (f w)) :=
    (Representation.IntertwiningMap.isIntertwining τ τ' f d (ι a w)).trans
      (congrArg (τ' d) (map_archimedeanRepresentation σ π c σ' π' c' M hf ha a w))
  exact (congrArg ℓ he).trans (hℓ.2 z (f w))

omit [NonarchimedeanGroup (FiniteAdelicGL F (r + 1))] in
/-- One scalar relating the two mixed identity functionals relates all
original actual cusp Whittaker functions. -/
theorem cuspWhittaker_eq_of_mixed_functional
    (T T' : CuspidalOperatorRealization F r)
    (e : T.Space →ₗ[ℂ] T'.Space)
    (j : T.Space →ₗ[ℂ] W) (j' : T'.Space →ₗ[ℂ] W')
    (he : ∀ w, f (j w) = j' (e w))
    (ℓ : W →ₗ[ℂ] ℂ) (ℓ' : W' →ₗ[ℂ] ℂ)
    (hval : ∀ w a d, ℓ (τ d (ι a (j w))) =
      cuspWhittaker F T ψ w (adelicPoint F (r + 1) a d))
    (hval' : ∀ w a d, ℓ' (τ' d (ι' a (j' w))) =
      cuspWhittaker F T' ψ w (adelicPoint F (r + 1) a d))
    (s : ℂ) (hs : ℓ'.comp (f).toLinearMap = s • ℓ) :
    ∀ (w : T.Space) (g : Points F (r + 1)),
      cuspWhittaker F T' ψ (e w) g = s * cuspWhittaker F T ψ w g := by
  intro w g
  let a := archPart F (r + 1) g
  let d := finPart F (r + 1) g
  let x := τ d (ι a (j w))
  have hg : adelicPoint F (r + 1) a d = g :=
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
      ((adelicEquiv_adelicPoint F (r + 1) a d).trans (adelicEquiv_eq_pair F (r + 1) g).symm)
  have hx : f x = τ' d (ι' a (j' (e w))) :=
    (Representation.IntertwiningMap.isIntertwining τ τ' f d (ι a (j w))).trans (congrArg (τ' d)
      ((map_archimedeanRepresentation σ π c σ' π' c' M hf ha a (j w)).trans
        (congrArg (ι' a) (he w))))
  have hx' : ℓ' (f x) = s * ℓ x := LinearMap.congr_fun hs x
  calc
    cuspWhittaker F T' ψ (e w) g =
        cuspWhittaker F T' ψ (e w) (adelicPoint F (r + 1) a d) :=
      congrArg (cuspWhittaker F T' ψ (e w)) hg.symm
    _ = ℓ' (f x) := (hval' (e w) a d).symm.trans (congrArg ℓ' hx.symm)
    _ = s * ℓ x := hx'
    _ = s * cuspWhittaker F T ψ w g :=
      congrArg (fun y : ℂ => s * y)
        ((hval w a d).trans (congrArg (cuspWhittaker F T ψ w) hg))

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
