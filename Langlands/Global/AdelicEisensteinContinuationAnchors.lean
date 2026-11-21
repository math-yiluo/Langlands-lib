import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinConvergentOperators
import Langlands.Global.AdelicIntertwiningCocycleReduction
import Langlands.Global.EisensteinConvergenceAnchors

/-! # Convergence anchors from meromorphic continuation of constant sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace Langlands.Global.EisensteinJet

open AdelicGroupPoints Langlands.GroupScheme Langlands.Analysis.Meromorphic
open Langlands.Automorphic.GroupSchemeFunctions UniformGrowthFrechetSpace

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) {m : ℕ}
  (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)

local notation "Region" => fun R : ℝ =>
  ((fun t : Fin m → ℂ => ParabolicRootPresentation.IsRegularParameter r hA hT R (e t)) :
    Set (Fin m → ℂ))

private theorem antitone_regularRegion : Antitone Region :=
  fun _ _ h _ ht α hα => h.trans_lt (ht α hα)

/-- The filter of sufficiently regular parameters after removing arbitrary
closed sets with empty interior. -/
def eisensteinConvergenceAnchorFilter : Filter (Fin m → ℂ) :=
  convergenceAnchorFilter Region (antitone_regularRegion r hA hT e)

/-- Each eventual property on the Eisenstein convergence filter holds on a
nonempty open subset of the complex parameter coordinates. -/
theorem exists_open_of_eventually_eisensteinConvergenceAnchorFilter
    (hG : IsConnectedReductive G) {Q : (Fin m → ℂ) → Prop}
    (hQ : ∀ᶠ t in eisensteinConvergenceAnchorFilter r hA hT e, Q t) :
    ∃ U : Set (Fin m → ℂ), IsOpen U ∧ U.Nonempty ∧ ∀ t ∈ U, Q t := by
  have : Smooth G.X.hom := hG.smooth
  refine exists_open_of_eventually_convergenceAnchorFilter Region
    (antitone_regularRegion r hA hT e) (fun R => isOpen_setOf_isRegularParameter r hA hT hG R e)
    ?_ hQ
  intro R
  obtain ⟨lam, hlam⟩ := r.exists_regularParameter hA hT R
  refine ⟨e.symm lam, ?_⟩
  change r.IsRegularParameter hA hT R (e (e.symm lam))
  rw [e.apply_symm_apply]
  exact hlam

variable [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] {U : GroupScheme (Spec (CommRingCat.of F))}
  {iU : U ⟶ P} {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "Adeles" => AdelicGroupPoints F G
local notation "Growth[" R "," L "]" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value[" R "," L "]" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L

/-- A continuation witness for a fixed automorphic input supplies eventual
agreement with the series and eventual membership in the domain of compact
majorants and smooth rational outputs. -/
theorem exists_continuedSection_on_convergenceAnchorFilter
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hmax : IsMaximalCompactSubgroup F G K) (φ : Adeles → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ f : (Fin m → ℂ) → Adeles → ℂ,
      (∀ᶠ t in eisensteinConvergenceAnchorFilter r hA hT e, f t = hK.eisensteinSeries φ (e t)) ∧
      (∀ᶠ t in eisensteinConvergenceAnchorFilter r hA hT e,
        φ ∈ smoothConvergenceSections F G hK (e t)) ∧
      ∀ z : Fin m → ℂ, ∃ W : TopologicalSpace.Opens (Fin m → ℂ), z ∈ W ∧
        ∃ (S : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
          IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
          ∃ (g : W → Growth[S, L]) (D : Set W), IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) g D ∧
            ∀ t ∈ D, value[S, L] (g t) = f t.val ∧
              IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
                (K.comap (ofInfinite F G).toMonoidHom) rho (f t.val) := by
  obtain ⟨f, ⟨S, hS⟩, hlocal⟩ :=
    hcont F G P M U A p iU l a r hA hT hG hU K hK rho hN hrho hsmooth hcalc φ hmax hφ
  obtain ⟨R, hR⟩ := eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT
    hG hU K hK rho hsmooth hcalc φ hmax hrho hφ
  have hEq : ∀ᶠ t in eisensteinConvergenceAnchorFilter r hA hT e,
      f (e t) = hK.eisensteinSeries φ (e t) :=
    (eventually_convergenceAnchorFilter_iff Region (antitone_regularRegion r hA hT e)).mpr
      ⟨S, univ, isOpen_univ, dense_univ, fun t ht => hS (e t) ht.1⟩
  refine ⟨fun t => f (e t), hEq, ?_, hlocal m e⟩
  have hLocalRange (z : Fin m → ℂ) :
      ∃ W : TopologicalSpace.Opens (Fin m → ℂ), z ∈ W ∧
        ∃ D : Set W, IsOpen D ∧ Dense D ∧
          ∀ t ∈ D, f (e t.val) ∈ LinearMap.range (finitePlotSmoothEvaluation F G) := by
    obtain ⟨W, hz, S₁, L, _, g, D, hg, hvalues⟩ := hlocal m e z
    refine ⟨W, hz, D, hg.1, hg.2.1, fun t ht => ?_⟩
    have hform := (hvalues t ht).2
    exact ⟨ofRationalSmoothFunction F G _ hform.1 hform.2.1, rfl⟩
  obtain ⟨D, hDo, hDd, hD⟩ := exists_open_dense_of_local
    (P := fun t : Fin m → ℂ => f (e t) ∈ LinearMap.range (finitePlotSmoothEvaluation F G)) hLocalRange
  have hMajor : ∀ᶠ t in eisensteinConvergenceAnchorFilter r hA hT e, φ ∈ hK.compactMajorantSections (e t) := by
    apply (eventually_convergenceAnchorFilter_iff Region (antitone_regularRegion r hA hT e)).mpr
    refine ⟨R, univ, isOpen_univ, dense_univ, fun t ht C hC => ?_⟩
    obtain ⟨b, hb, hbound⟩ := hR C hC m e {t} isCompact_singleton
      (fun s hs => (mem_singleton_iff.mp hs).symm ▸ ht.1)
    exact ⟨b, hb, fun c x hx => hbound c x hx t (mem_singleton t)⟩
  have hRange : ∀ᶠ t in eisensteinConvergenceAnchorFilter r hA hT e,
      f (e t) ∈ LinearMap.range (finitePlotSmoothEvaluation F G) :=
    (eventually_convergenceAnchorFilter_iff Region (antitone_regularRegion r hA hT e)).mpr
      ⟨R, D, hDo, hDd, fun t ht => hD t ht.2⟩
  filter_upwards [hEq, hMajor, hRange] with t heq hm hRange
  exact (mem_smoothConvergenceSections F G hK (e t) φ).mpr ⟨hm, heq ▸ hRange⟩

end Langlands.Global.EisensteinJet
