import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence
import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof
import Langlands.Cohomology.RightDerivedSequence

/-! # The divisor sequence of a relative effective Cartier divisor and its twists -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules (unitToPushforwardUnit tensorObj tensorFunctor tensorComm)

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreSequence

open StructureKernelModule RelativeEffectiveDivisorBaseChangeProof
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

section Sequence

variable {X E : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i]

/-- The divisor sequence `K ⟶ 𝒪_X ⟶ i_* 𝒪_E` of a closed immersion. -/
def divisorSequence : ShortComplex X.Modules :=
  ShortComplex.mk (kernelModuleι i) (unitToPushforwardUnit i) (kernelModule_condition i)

/-- After a pullback keeping the ideal inclusion a monomorphism, the divisor sequence is short
exact: the pulled-back inclusion is a kernel (right exactness of pullback) and the pulled-back
structure map is an epimorphism. -/
lemma shortExact_divisorSequence_map {X' : Scheme.{u}} (b : X' ⟶ X)
    [Mono ((Scheme.Modules.pullback b).map (kernelModuleι i))] :
    ((divisorSequence i).map (Scheme.Modules.pullback b)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (pullbackKernelIsKernel b i)
  mono_f := (inferInstance : Mono ((Scheme.Modules.pullback b).map (kernelModuleι i)))
  epi_g := by
    have := epi_unitToPushforwardUnit i
    exact (Scheme.Modules.pullback b).map_epi (unitToPushforwardUnit i)

/-- The ideal inclusion of a relative effective Cartier divisor stays a monomorphism after
pullback along the first projection of any base change. -/
lemma mono_pullback_fst_kernelModuleι {S : Scheme.{u}} (f : X ⟶ S) [Flat (i ≫ f)]
    {T : Scheme.{u}} (h : T ⟶ S) (hK : Scheme.Modules.IsInvertibleFLT (kernelModule i)) :
    Mono ((Scheme.Modules.pullback (pullback.fst f h)).map (kernelModuleι i)) := by
  have := mono_pullback_snd_kernelModuleι f h i hK
  have : PreservesFiniteLimits (Scheme.Modules.pullback (pullbackSymmetry f h).hom) :=
    Langlands.AlgebraicGeometry.Modules.flatPullbackExact _ _ _ inferInstance
  have : Mono ((Scheme.Modules.pullback (pullback.snd h f) ⋙
      Scheme.Modules.pullback (pullbackSymmetry f h).hom).map (kernelModuleι i)) :=
    (Scheme.Modules.pullback (pullbackSymmetry f h).hom).map_mono _
  exact mono_map_of_iso (Scheme.Modules.pullbackCongr (pullbackSymmetry_hom_comp_snd f h).symm ≪≫
    (Scheme.Modules.pullbackComp _ _).symm) (kernelModuleι i)

end Sequence

section Twist

variable {X : Scheme.{u}} (L : X.Modules) (hL : IsLocallyFreeRankOne L)

/-- The twist `M ⊗ L^{⊗ n}` with the explicit sheaf tensor, associated to the right. -/
def twistObj (M : X.Modules) : ℕ → X.Modules
  | 0 => M
  | n + 1 => tensorObj (twistObj M n) L

/-- Twisting is functorial in isomorphisms of the coefficient module. -/
def twistObjMapIso {M M' : X.Modules} (e : M ≅ M') : (n : ℕ) → twistObj L M n ≅ twistObj L M' n
  | 0 => e
  | n + 1 => (tensorFunctor X).mapIso ((twistObjMapIso e n).prod (Iso.refl L))

/-- A short complex twisted `n` times by the line bundle `L`. -/
def twistSeq (S : ShortComplex X.Modules) : ℕ → ShortComplex X.Modules
  | 0 => S
  | n + 1 =>
    letI := tensorBy_isEquivalence L hL
    (twistSeq S n).map (tensorBy L)

/-- Twisting by a line bundle preserves short exactness. -/
lemma shortExact_twistSeq {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    ∀ n, (twistSeq L hL S n).ShortExact
  | 0 => hS
  | n + 1 => shortExact_tensorBy _ (shortExact_twistSeq hS n) L hL

lemma twistSeq_X₁ (S : ShortComplex X.Modules) : ∀ n, (twistSeq L hL S n).X₁ = twistObj L S.X₁ n
  | 0 => rfl
  | n + 1 => by
    change tensorObj (twistSeq L hL S n).X₁ L = tensorObj (twistObj L S.X₁ n) L
    rw [twistSeq_X₁ S n]

lemma twistSeq_X₂ (S : ShortComplex X.Modules) : ∀ n, (twistSeq L hL S n).X₂ = twistObj L S.X₂ n
  | 0 => rfl
  | n + 1 => by
    change tensorObj (twistSeq L hL S n).X₂ L = tensorObj (twistObj L S.X₂ n) L
    rw [twistSeq_X₂ S n]

lemma twistSeq_X₃ (S : ShortComplex X.Modules) : ∀ n, (twistSeq L hL S n).X₃ = twistObj L S.X₃ n
  | 0 => rfl
  | n + 1 => by
    change tensorObj (twistSeq L hL S n).X₃ L = tensorObj (twistObj L S.X₃ n) L
    rw [twistSeq_X₃ S n]

variable {E : Scheme.{u}} (j : E ⟶ X)

/-- One step of the projection formula: `j_* G ⊗ L ≅ j_* (G ⊗ j^* L)`. -/
def projectionStep (G : E.Modules) :
    tensorObj ((Scheme.Modules.pushforward j).obj G) L ≅
      (Scheme.Modules.pushforward j).obj (tensorObj G ((Scheme.Modules.pullback j).obj L)) :=
  tensorComm _ _ ≪≫ lineBundleProjectionIso j ⟨L, hL⟩ G ≪≫
    (Scheme.Modules.pushforward j).mapIso (tensorComm _ _)

/-- The iterated projection formula `(j_* G)(n) ≅ j_* (G(n))`. -/
def twistPushforwardIso (G : E.Modules) : (n : ℕ) →
    twistObj L ((Scheme.Modules.pushforward j).obj G) n ≅
      (Scheme.Modules.pushforward j).obj (twistObj ((Scheme.Modules.pullback j).obj L) G n)
  | 0 => Iso.refl _
  | n + 1 => (tensorFunctor X).mapIso ((twistPushforwardIso G n).prod (Iso.refl L)) ≪≫
      projectionStep L hL j _

end Twist

section H0

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [Field R] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))

/-- On a short exact sequence whose first term has vanishing `H¹`, global sections are exact,
so `h⁰` is additive. -/
lemma finrank_relativeGlobalSections_X₃ {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    (h₁ : IsZero ((relativeCohomology g 1).obj S.X₁))
    [Module.Finite R ((relativeGlobalSections g).obj S.X₂)] :
    (Module.finrank R ((relativeGlobalSections g).obj S.X₃) : ℤ) =
      Module.finrank R ((relativeGlobalSections g).obj S.X₂) -
        Module.finrank R ((relativeGlobalSections g).obj S.X₁) := by
  let : (relativeGlobalSections g).Additive :=
    (inferInstance : ∀ {R : CommRingCat.{u}} (g : Y ⟶ Spec R),
      (relativeGlobalSections g).Additive) g
  let : PreservesFiniteLimits (relativeGlobalSections g) :=
    (inferInstance : ∀ {R : CommRingCat.{u}} (g : Y ⟶ Spec R),
      PreservesFiniteLimits (relativeGlobalSections g)) g
  have hSE := Langlands.Cohomology.DerivedPlus.shortExact_map_of_isZero_rightDerived_one
    (relativeGlobalSections g) hS h₁
  have hinj : Function.Injective ((relativeGlobalSections g).map S.f) :=
    (ModuleCat.mono_iff_injective _).1 hSE.mono_f
  have hsurj : Function.Surjective ((relativeGlobalSections g).map S.g) :=
    (ModuleCat.epi_iff_surjective _).1 hSE.epi_g
  have hex : LinearMap.range ((relativeGlobalSections g).map S.f).hom =
      LinearMap.ker ((relativeGlobalSections g).map S.g).hom :=
    hSE.exact.moduleCat_range_eq_ker
  have h1 := LinearMap.finrank_range_add_finrank_ker ((relativeGlobalSections g).map S.g).hom
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h1
  rw [← hex, LinearMap.finrank_range_of_inj hinj] at h1
  change (Module.finrank (CommRingCat.of R) ((relativeGlobalSections g).obj S.X₃) : ℤ) =
    Module.finrank (CommRingCat.of R) ((relativeGlobalSections g).obj S.X₂) -
      Module.finrank (CommRingCat.of R) ((relativeGlobalSections g).obj S.X₁)
  omega

end H0

end Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreSequence
