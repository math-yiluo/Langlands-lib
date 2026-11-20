import Langlands.Automorphic.LocalSphericalHecke
import Langlands.Global.FiniteAdelicGL.SphericalArithmeticTransport

/-! # Arithmetic compatibility of actual spherical Hecke actions -/

noncomputable section

universe uK uL uG uH uV uW

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global AdelicFunctoriality AdelicGLTransport FiniteAdelicGL Unramified
open MeasureTheory MeasureTheory.Measure
open HarmonicAnalysis (SchwartzBruhat)
open HarmonicAnalysis.AlgebraicIntegral

private theorem integratedAction_changeVariables
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H]
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    {ν : Measure H} [IsFiniteMeasureOnCompacts ν]
    {f : G → H} (hf : MeasurePreserving f μ ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (φ : SchwartzBruhat G) (ψ : SchwartzBruhat H)
    (hφψ : ∀ g, φ g = ψ (f g)) (T : V →ₗ[ℂ] W) (x : V)
    (hT : ∀ g, T (ρ g x) = σ (f g) (T x)) :
    T (Hecke.integratedAction μ ρ hρ φ x) = Hecke.integratedAction ν σ hσ ψ (T x) := by
  simp only [Hecke.integratedAction_apply]
  rw [← integral_linearMap _ (Hecke.actionIntegrand_finMeasSupp μ ρ hρ φ x) T,
    ← integral_comp_measurePreserving (Hecke.actionIntegrand σ hσ ψ (T x)) f hf]
  congr 1
  ext g
  simp only [SimpleFunc.map_apply, SimpleFunc.coe_comp, Function.comp_apply, Hecke.actionIntegrand_apply,
    map_smul, hφψ g, hT g]

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [Field L] [NumberField L]

local instance arithmeticSphericalRationalGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSphericalContinuousGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSphericalSmoothGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance arithmeticSphericalFormsGroup {F : Type*} [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance arithmeticSphericalSpaceGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} (S : LocalRealization F n v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace LocalRealization

variable (a : L ≃+* K) {v : FinitePlace K} {r : ℕ}
variable {S : LocalRealization L (r + 1) (finitePlaceEquiv a v)} {T : LocalRealization K (r + 1) v}
variable (B : S.Space ≃ₗ[ℂ] T.Space)
variable (hB : ∀ (g : FiniteLocalGL L (r + 1) (finitePlaceEquiv a v)) (x : S.Space),
  B (S.representation g x) = T.representation (localEquiv (r + 1) a v g) (B x))

/-- Restrict the equivalence of transported representations to spherical fixed vectors. -/
def sphericalVectorsArithmeticEquiv : S.SphericalVectors ≃ₗ[ℂ] T.SphericalVectors := by
  refine B.ofSubmodules S.SphericalVectors T.SphericalVectors (le_antisymm ?_ ?_)
  · rintro y ⟨x, hx, rfl⟩ g
    let f := localEquiv (r + 1) a v
    let k := f.symm (g : FiniteLocalGL K (r + 1) v)
    have hk : f k = (g : FiniteLocalGL K (r + 1) v) := f.apply_symm_apply g
    have hg : f k ∈ Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r :=
      hk.symm ▸ g.property
    have hmem := (localEquiv_mem_sphericalSubgroup_iff a v r k).mp hg
    calc
      T.representation (g : FiniteLocalGL K (r + 1) v) (B x) =
          T.representation (f k) (B x) :=
        congrArg (fun t : FiniteLocalGL K (r + 1) v => T.representation t (B x)) hk.symm
      _ = B (S.representation k x) := (hB k x).symm
      _ = B x := congrArg B (hx ⟨k, hmem⟩)
  · intro y hy
    refine ⟨B.symm y, ?_, B.apply_symm_apply y⟩
    intro g
    let k := localEquiv (r + 1) a v (g : FiniteLocalGL L (r + 1) (finitePlaceEquiv a v))
    have hk := (localEquiv_mem_sphericalSubgroup_iff a v r g).mpr g.property
    apply B.injective
    calc
      B (S.representation (g : FiniteLocalGL L (r + 1) (finitePlaceEquiv a v)) (B.symm y)) =
          T.representation k (B (B.symm y)) := hB g (B.symm y)
      _ = T.representation k y := congrArg (T.representation k) (B.apply_symm_apply y)
      _ = y := hy ⟨k, hk⟩
      _ = B (B.symm y) := (B.apply_symm_apply y).symm

@[simp] theorem sphericalVectorsArithmeticEquiv_apply (x : S.SphericalVectors) :
    (sphericalVectorsArithmeticEquiv a B hB x : T.Space) = B (x : S.Space) := rfl

section CanonicalHecke

local instance arithmeticSphericalTopology {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} : TopologicalSpace (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology n
local instance arithmeticSphericalTopologicalGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} : IsTopologicalGroup (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup n
local instance arithmeticSphericalT2 {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} : T2Space (FiniteLocalGL F n v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space n
local instance arithmeticSphericalMeasurable {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} : MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance arithmeticSphericalBorel {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : FinitePlace F} : BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

local instance arithmeticSphericalHaar {F : Type*} [Field F] [NumberField F]
    {v : FinitePlace F} {r : ℕ} : (sphericalHaar (CompletionPadic.padicField v) r).IsHaarMeasure :=
  sphericalHaar_isHaar (CompletionPadic.padicField v) r

private theorem standardHeckeOperator_arithmetic
    (i : Fin (r + 2)) (x : S.SphericalVectors) :
    sphericalVectorsArithmeticEquiv a B hB (S.standardHeckeOperator i x) =
      T.standardHeckeOperator i (sphericalVectorsArithmeticEquiv a B hB x) := by
  apply Subtype.ext
  simp only [sphericalVectorsArithmeticEquiv_apply, standardHeckeOperator, sphericalHeckeAction]
  refine integratedAction_changeVariables (measurePreserving_localEquiv_sphericalHaar a v r)
    _ _ _ _ _ _ ?_ B.toLinearMap (x : S.Space) ?_
  · intro g
    change standardHeckeElement (CompletionPadic.padicField (finitePlaceEquiv a v)) r i g =
      standardHeckeElement (CompletionPadic.padicField v) r i (localEquiv (r + 1) a v g)
    refine (standardHeckeElement_apply (CompletionPadic.padicField (finitePlaceEquiv a v)) r i g).trans
      (Eq.trans ?_ (standardHeckeElement_apply (CompletionPadic.padicField v) r i
        (localEquiv (r + 1) a v g)).symm)
    simp only [Hecke.TestFunction.doubleCosetSet, ← OpenSubgroup.coe_toSubgroup,
      sphericalOpenSubgroup_toSubgroup]
    have hc := localEquiv_mem_standardDoubleCoset_iff a v r i g
    by_cases hg : g ∈ DoubleCoset.doubleCoset
        (standardDiagonal (CompletionPadic.padicField (finitePlaceEquiv a v)) r i)
        (Correspondence.sphericalSubgroup (CompletionPadic.padicField (finitePlaceEquiv a v)) r)
        (Correspondence.sphericalSubgroup (CompletionPadic.padicField (finitePlaceEquiv a v)) r)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hc.mpr hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hc.mp h))]
  · exact fun g => hB g x

include hB in
/-- The spherical spectrum passes across the arithmetic equivalence. -/
theorem hasSphericalHeckeSpectrum_arithmetic
    (s : Eigenvalues (r + 1)) (hs : S.HasSphericalHeckeSpectrum s) :
    T.HasSphericalHeckeSpectrum s := by
  let U := sphericalVectorsArithmeticEquiv a B hB
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := S.SphericalVectors.ne_bot_iff.mp hs.1
    refine T.SphericalVectors.ne_bot_iff.mpr ⟨_, (U ⟨x, hx⟩).property, ?_⟩
    intro hz
    have h0 : U ⟨x, hx⟩ = 0 := Subtype.ext hz
    exact hx0 (congrArg Subtype.val (U.injective (h0.trans U.map_zero.symm)))
  · intro i y
    let x : S.SphericalVectors := U.symm y
    have hx : U x = y := U.apply_symm_apply y
    let sourceScalar := standardHeckeScalar (CompletionPadic.padicField (finitePlaceEquiv a v)) s i
    let targetScalar := standardHeckeScalar (CompletionPadic.padicField v) s i
    have hscalar : sourceScalar = targetScalar := by
      simp only [sourceScalar, targetScalar, standardHeckeScalar, residueCardinality_finitePlaceEquiv a v]
    calc
      T.standardHeckeOperator i y = T.standardHeckeOperator i (U x) :=
        congrArg (T.standardHeckeOperator i) hx.symm
      _ = U (S.standardHeckeOperator i x) := (standardHeckeOperator_arithmetic a B hB i x).symm
      _ = U (sourceScalar • x) := congrArg U (hs.2 i x)
      _ = sourceScalar • U x := U.map_smul sourceScalar x
      _ = targetScalar • y := congrArg₂ (fun (c : ℂ) (z : T.SphericalVectors) => c • z) hscalar hx

end CanonicalHecke
end LocalRealization
end Langlands.Automorphic
