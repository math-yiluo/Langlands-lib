import Langlands.AlgebraicGeometry.Modules.MonoidalTensorComparison
import Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreSequence
import Langlands.AlgebraicGeometry.Modules.GeometricFibreSectionsDim
import Langlands.AlgebraicGeometry.Modules.ProjectiveRelativeDivisorFibreHilbertStatement
import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyStatement
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2

/-! # Hilbert functions of relative effective divisors on fibres: the core computation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Langlands.Scheme.Modules (tensorFunctor)

attribute [-instance] Langlands.Scheme.Modules.tensorMonoidalCategory
  Langlands.Scheme.Modules.tensorSymmetricCategory

set_option backward.isDefEq.respectTransparency false

/-- The FLT twist of the projective-fibre statements. -/
local notation "twistF" => Langlands.AlgebraicGeometry.Modules.twist

namespace Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreHilbert

open StructureKernelModule StructureKernelFlatBaseChange RelativeEffectiveDivisorBaseChangeProof
open RelativeDivisorFibreSequence
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

section FLTTwist

variable {X : Scheme.{u}}

/-- The FLT tensor and the explicit sheafified tensor agree. -/
def fltTensorIso (A B : X.Modules) :
    Scheme.Modules.tensor A B ≅ Langlands.Scheme.Modules.tensorObj A B :=
  Langlands.AlgebraicGeometry.Modules.monoidalTensorIso A B

/-- The FLT twist `M ⊗ L^{⊗ n}` agrees with the explicit-tensor twist. -/
def twistIsoTwistObj (L M : X.Modules) : (n : ℕ) → twistF L M n ≅ twistObj L M n
  | 0 => Iso.refl _
  | n + 1 => fltTensorIso (twistF L M n) L ≪≫
      (tensorFunctor X).mapIso ((twistIsoTwistObj L M n).prod (Iso.refl L))

/-- FLT twists are functorial in isomorphisms of both arguments. -/
def twistCongr {L L' M M' : X.Modules} (eL : L ≅ L') (eM : M ≅ M') :
    (n : ℕ) → twistF L M n ≅ twistF L' M' n
  | 0 => eM
  | n + 1 => tensorIso (twistCongr eL eM n) eL

/-- Pullback commutes with FLT twists. -/
def pullbackTwistIso {Y : Scheme.{u}} (φ : Y ⟶ X) (L M : X.Modules) :
    (n : ℕ) → (Scheme.Modules.pullback φ).obj (twistF L M n) ≅
      twistF ((Scheme.Modules.pullback φ).obj L) ((Scheme.Modules.pullback φ).obj M) n
  | 0 => Iso.refl _
  | n + 1 => Scheme.Modules.pullbackTensorObjIso φ _ _ ≪≫
      tensorIso (pullbackTwistIso φ L M n) (Iso.refl _)

/-- Twists of invertible modules by an invertible module are invertible. -/
lemma isInvertible_twist {L M : X.Modules} (hL : Scheme.Modules.IsInvertibleFLT L)
    (hM : Scheme.Modules.IsInvertibleFLT M) : ∀ n, Scheme.Modules.IsInvertibleFLT (twistF L M n)
  | 0 => hM
  | n + 1 => Scheme.Modules.IsInvertible.tensor_monoidalV2 (isInvertible_twist hL hM n) hL

/-- FLT-invertible modules are locally free of rank one. -/
lemma isLocallyFreeRankOne_of_isInvertible {M : X.Modules}
    (hM : Scheme.Modules.IsInvertibleFLT M) : IsLocallyFreeRankOne M := fun x => by
  obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
  exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩⟩

end FLTTwist

/-- If all higher fibre cohomology vanishes, the fibre Euler characteristic is `h⁰`. -/
lemma fibreEulerCharacteristic_eq_of_vanishing {Y T : Scheme.{u}} (g : Y ⟶ T) (t : T)
    (F : Y.Modules) (h : ∀ p, 0 < p → IsZero (fibreCohomology g t F p)) :
    fibreEulerCharacteristic g t F = fibreCohomologyDim g t F 0 := by
  rw [fibreEulerCharacteristic, finsum_eq_single _ 0]
  · simp
  · intro p hp
    have : Subsingleton (fibreCohomology g t F p) :=
      ModuleCat.subsingleton_of_isZero (h p (Nat.pos_of_ne_zero hp))
    simp [fibreCohomologyDim, Module.finrank_zero_of_subsingleton]

section Core

variable {B : Type u} [CommRing B] [IsNoetherianRing B] {XB : Scheme.{u}}
  (fB : XB ⟶ Spec (CommRingCat.of B)) [IsProper fB] [Flat fB]
  (L : XB.Modules) (hL : Scheme.Modules.IsInvertibleFLT L)
  (I : XB.IdealSheafData) (hI : IsRelativeEffectiveCartierIdeal fB I)
  (LE : I.subscheme.Modules) (hLE : Scheme.Modules.IsInvertibleFLT LE)
  (eLE : (Scheme.Modules.pullback I.subschemeι).obj L ≅ LE)
  (k : Type u) [Field k] (sk : B →+* k)

include hL hI hLE eLE in
/-- **The fibre computation.** If the twists `K(n)` and `𝒪(n)` have no higher cohomology on the
fibre over `t`, then the geometric `h⁰` of `𝒪_E(n)` is `χ(𝒪(n)_t) - χ(K(n)_t)`. -/
theorem geomFibreH0Finrank_twist_eq (n : ℕ)
    (hvanK : ∀ p, 0 < p → IsZero (fibreCohomology fB
      ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
      (twistF L (kernelModule I.subschemeι) n) p))
    (hvan1 : ∀ p, 0 < p → IsZero (fibreCohomology fB
      ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
      (twistF L (𝟙_ XB.Modules) n) p)) :
    (Scheme.Modules.geomFibreH0Finrank (I.subschemeι ≫ fB)
        (twistF LE (𝟙_ I.subscheme.Modules) n) k sk : ℤ) =
      fibreEulerCharacteristic fB ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
          (twistF L (𝟙_ XB.Modules) n) -
        fibreEulerCharacteristic fB
          ((Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k))
          (twistF L (kernelModule I.subschemeι) n) := by
  set t := (Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k) with ht
  have hK : Scheme.Modules.IsInvertibleFLT (kernelModule I.subschemeι) :=
    isInvertible_of_isLocallyFreeRankOne hI.1
  have : Flat (I.subschemeι ≫ fB) := hI.2
  -- the fibre square
  let i := I.subschemeι
  let ιt := (Spec (CommRingCat.of B)).fromSpecResidueField t
  let b := pullback.fst fB ιt
  let g := pullback.snd fB ιt
  let p := pullback.fst (i ≫ fB) ιt
  let gE := pullback.snd (i ≫ fB) ιt
  let it : pullback (i ≫ fB) ιt ⟶ pullback fB ιt :=
    pullback.lift (p ≫ i) gE (by rw [Category.assoc]; exact pullback.condition)
  have hit : it ≫ g = gE := pullback.lift_snd _ _ _
  have hitb : it ≫ b = p ≫ i := pullback.lift_fst _ _ _
  have hsq : IsPullback p it i b :=
    IsPullback.of_bot (by rw [hit]; exact IsPullback.of_hasPullback (i ≫ fB) ιt) hitb.symm
      (IsPullback.of_hasPullback fB ιt)
  -- the short exact divisor sequence on the fibre, twisted
  have hm := mono_pullback_fst_kernelModuleι i fB ιt hK
  let St := (divisorSequence i).map (Scheme.Modules.pullback b)
  have hSt : St.ShortExact := shortExact_divisorSequence_map i b
  let Lt := (Scheme.Modules.pullback b).obj L
  have hLt : IsLocallyFreeRankOne Lt := isLocallyFreeRankOne_of_isInvertible (Scheme.Modules.IsInvertible.pullbackFLT (hL := hL) b)
  let Sn := twistSeq Lt hLt St n
  have hSn : Sn.ShortExact := shortExact_twistSeq Lt hLt hSt n
  -- identifications of the three terms
  let e₁ : Sn.X₁ ≅ fibreModule fB t (twistF L (kernelModule i) n) :=
    eqToIso (twistSeq_X₁ Lt hLt St n) ≪≫ (twistIsoTwistObj Lt _ n).symm ≪≫
      (pullbackTwistIso b L _ n).symm
  let e₂ : Sn.X₂ ≅ fibreModule fB t (twistF L (𝟙_ XB.Modules) n) :=
    eqToIso (twistSeq_X₂ Lt hLt St n) ≪≫ (twistIsoTwistObj Lt _ n).symm ≪≫
      (pullbackTwistIso b L _ n).symm
  let e₃ : Sn.X₃ ≅ (Scheme.Modules.pushforward it).obj
      (twistObj ((Scheme.Modules.pullback it).obj Lt)
        (SheafOfModules.unit (pullback (i ≫ fB) ιt).ringCatSheaf) n) :=
    eqToIso (twistSeq_X₃ Lt hLt St n) ≪≫
      twistObjMapIso Lt (structurePushforwardBaseChangeIso b i it p hsq) n ≪≫
      twistPushforwardIso Lt hLt it _ n
  let eL : (Scheme.Modules.pullback it).obj Lt ≅ (Scheme.Modules.pullback p).obj LE :=
    (Scheme.Modules.pullbackComp it b).app L ≪≫ (Scheme.Modules.pullbackCongr hitb).app L ≪≫
      ((Scheme.Modules.pullbackComp p i).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso eLE
  let e₄ : twistObj ((Scheme.Modules.pullback it).obj Lt)
      (SheafOfModules.unit (pullback (i ≫ fB) ιt).ringCatSheaf) n ≅
        fibreModule (i ≫ fB) t (twistF LE (𝟙_ I.subscheme.Modules) n) :=
    (twistIsoTwistObj _ _ n).symm ≪≫
      twistCongr eL (Scheme.Modules.pullbackTensorUnitObjIso p).symm n ≪≫
      (pullbackTwistIso p LE _ n).symm
  -- `H¹` of the first term vanishes
  have h₁ : IsZero ((relativeCohomology g 1).obj Sn.X₁) :=
    (hvanK 1 Nat.one_pos).of_iso ((relativeCohomology g 1).mapIso e₁)
  -- `H⁰` of the middle term is finite dimensional
  have hfin : Module.Finite ((Spec (CommRingCat.of B)).residueField t)
      ((relativeGlobalSections g).obj Sn.X₂) := by
    have hf0 : Module.Finite ((Spec (CommRingCat.of B)).residueField t)
        ((relativeCohomology g 0).obj (fibreModule fB t (twistF L (𝟙_ XB.Modules) n))) :=
      (properFlatFibreCohomologySemicontinuity (Spec (CommRingCat.of B)) XB fB
        inferInstance inferInstance _
        (isInvertible_twist hL (Scheme.Modules.isInvertible_unit XB) n)).1 t 0
    exact Module.Finite.equiv ((relativeCohomologyZeroIso g).app _ ≪≫
      (relativeGlobalSections g).mapIso e₂.symm).toLinearEquiv
  have hfin' : Module.Finite (IsLocalRing.ResidueField ((Spec (CommRingCat.of B)).presheaf.stalk t))
      ((relativeGlobalSections g).obj Sn.X₂) := hfin
  have hX₃ := finrank_relativeGlobalSections_X₃ g hSn h₁
  -- `h⁰` of the outer terms are the fibre Euler characteristics
  have hχK : fibreEulerCharacteristic fB t (twistF L (kernelModule I.subschemeι) n) =
      Module.finrank ((Spec (CommRingCat.of B)).residueField t)
        ((relativeGlobalSections g).obj Sn.X₁) := by
    rw [fibreEulerCharacteristic_eq_of_vanishing _ _ _ hvanK, fibreCohomologyDim,
      ((relativeCohomologyZeroIso g).app _ ≪≫
        (relativeGlobalSections g).mapIso e₁.symm).toLinearEquiv.finrank_eq]
  have hχ1 : fibreEulerCharacteristic fB t (twistF L (𝟙_ XB.Modules) n) =
      Module.finrank ((Spec (CommRingCat.of B)).residueField t)
        ((relativeGlobalSections g).obj Sn.X₂) := by
    rw [fibreEulerCharacteristic_eq_of_vanishing _ _ _ hvan1, fibreCohomologyDim,
      ((relativeCohomologyZeroIso g).app _ ≪≫
        (relativeGlobalSections g).mapIso e₂.symm).toLinearEquiv.finrank_eq]
  -- `h⁰` of the third term is `h⁰` of the divisor fibre
  have hE : (Module.finrank ((Spec (CommRingCat.of B)).residueField t)
      ((relativeGlobalSections g).obj Sn.X₃) : ℤ) =
        fibreCohomologyDim (I.subschemeι ≫ fB) t (twistF LE (𝟙_ I.subscheme.Modules) n) 0 := by
    let e₅ : (relativeGlobalSections g).obj Sn.X₃ ≅ (relativeCohomology gE 0).obj
        (fibreModule (i ≫ fB) t (twistF LE (𝟙_ I.subscheme.Modules) n)) :=
      (relativeGlobalSections g).mapIso e₃ ≪≫
        moduleSpecΓFunctor.mapIso ((Scheme.Modules.pushforwardComp it g).app _) ≪≫
        eqToIso (congrArg (fun φ => moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward φ).obj
          (twistObj ((Scheme.Modules.pullback it).obj Lt)
            (SheafOfModules.unit (pullback (i ≫ fB) ιt).ringCatSheaf) n))) hit) ≪≫
        (relativeGlobalSections gE).mapIso e₄ ≪≫ ((relativeCohomologyZeroIso gE).app _).symm
    rw [fibreCohomologyDim, e₅.toLinearEquiv.finrank_eq]
  rw [GeometricFibreSectionsDim.geomFibreH0Finrank_eq (I.subschemeι ≫ fB)
    (twistF LE (𝟙_ I.subscheme.Modules) n)
    (isInvertible_twist hLE (Scheme.Modules.isInvertible_unit _) n) k sk, ← hE, hχK, hχ1]
  exact hX₃

end Core

/-- **Reduction of the divisor Hilbert-function statement to uniform fibre vanishing.** The
first clause of `ProjectiveFibreTwistCohomologyStatement` (uniform vanishing of higher fibre
cohomology of large twists) implies `ProjectiveRelativeDivisorFibreHilbertStatement`. -/
theorem projectiveRelativeDivisorFibreHilbert_of_twistCohomology
    (hPT : ProjectiveFibreTwistCohomologyStatement.{u}) :
    ProjectiveRelativeDivisorFibreHilbertStatement.{u} := by
  intro A _ _ X f 𝓛X N 𝔓 hf hflat h𝓛 hcl B _ _ s I hI k _ _ sk
  have : IsProper f := hf
  have : Flat f := hflat
  have hK : Scheme.Modules.IsInvertibleFLT (kernelModule I.subschemeι) :=
    isInvertible_of_isLocallyFreeRankOne hI.1
  set t := (Spec.map (CommRingCat.ofHom sk)) (IsLocalRing.closedPoint k)
  obtain ⟨V₁, hV₁, n₁, hn₁⟩ := (hPT A f 𝓛X N 𝔓 hf hflat h𝓛 hcl (Spec (CommRingCat.of B)) s
    (kernelModule I.subschemeι) hK).1 t
  obtain ⟨V₂, hV₂, n₂, hn₂⟩ := (hPT A f 𝓛X N 𝔓 hf hflat h𝓛 hcl (Spec (CommRingCat.of B)) s
    (𝟙_ _) (Scheme.Modules.isInvertible_unit _)).1 t
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  exact geomFibreH0Finrank_twist_eq (pullback.snd f s)
    ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) (Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) _) I hI
    ((Scheme.Modules.pullback (I.subschemeι ≫ pullback.fst f s)).obj 𝓛X) (Scheme.Modules.IsInvertible.pullbackFLT (hL := h𝓛) _)
    ((Scheme.Modules.pullbackComp _ _).app 𝓛X) k sk n
    (fun p hp => hn₁ t hV₁ n p (le_of_max_le_left hn) hp)
    (fun p hp => hn₂ t hV₂ n p (le_of_max_le_right hn) hp)

end Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreHilbert
