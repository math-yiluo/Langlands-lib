import Langlands.Global.AdelicBlockSliceTensorSource
import Langlands.Global.AdelicBlockSmoothScalarSections

/-! # Nonzero infinite coefficients from compact seed slices -/

noncomputable section

open scoped Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 650000
set_option maxRecDepth 4000

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open PrimitiveAdelicHeight ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
variable {A V U : Type v}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
variable (ef : FiniteAdelicGL F n → A →ₗ[ℂ] V)
variable (c : standardInfiniteCompact F n → U)
variable (e : V ⊗[ℂ] U →ₗ[ℂ] coefficientValues F B S)

local notation "G" => FiniteAdelicGL F n
local notation "GI" => InfiniteAdelicGL F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "W" => smoothCompactFiniteSections F B S
local notation "H" => SmoothFunctions F n
local notation "C" => coefficientValues F B S
local notation "μi" => B.leviProjection (InfiniteAdeles F)
local notation "μf" => B.leviProjection (FiniteAdeles F)

local instance seedFiniteGroup : AddCommGroup (FiniteSmoothRealizedSections F B S) :=
  Submodule.addCommGroup _
local instance seedSmoothGroup : AddCommGroup W := Submodule.addCommGroup _
local instance seedInfiniteGroup : AddCommGroup H := Submodule.addCommGroup _

private def infiniteIwasawa (b : GI) : {x : Infinite F B × KI // b = x.1.val * x.2.val} := by
  have hb : ∃ p : Infinite F B, ∃ k : KI, b = p.val * k.val := by
    obtain ⟨a, k, h, ha, hk⟩ := exists_infinite_iwasawa F n b
    exact ⟨⟨a, B.mem_parabolic_of_isUpperTriangular a ha⟩, ⟨k, hk⟩, h⟩
  exact ⟨(hb.choose, hb.choose_spec.choose), hb.choose_spec.choose_spec⟩

private def coefficientAt (u : U) (m : FullLevi F B) : V →ₗ[ℂ] ℂ :=
  (LinearMap.proj m).comp ((C).subtype.comp
    (e.comp ((TensorProduct.mk ℂ V U).flip u)))

/-- Extend the common infinite seed coefficient to every infinite adelic point:
choose an infinite parabolic–compact factorization `b = p k`, multiply by the
archimedean half-character extension at `p`, and evaluate the seed coefficient at `c k` on
the infinite Levi argument of `p`. -/
def infiniteCoefficientFunctions : V →ₗ[ℂ] (GI → ℂ) :=
  LinearMap.pi fun b =>
    let x := (infiniteIwasawa F B b).val
    archimedeanHalfExtension F B (archimedeanGLCoordinates F n x.1.val).val •
      coefficientAt F B S e (c x.2) (leviPair F B (μi x.1) 1)

variable (f : A → smoothCompactFiniteSections F B S)
variable (hf : ∀ (a : A) (k : standardInfiniteCompact F n) (l : FiniteAdelicGL.standardIntegral F n)
    (m : FullLevi F B),
  normalizedSlice F B (f a).val.val.val (compactPair F k l) m = (e (ef l.val a ⊗ₜ[ℂ] c k)).val m)
variable (hleft : ∀ (p : AdelicBlockParabolic.Finite F B) (g : FiniteAdelicGL F n) (a : A) (w : U)
    (m : FullLevi F B),
  (e (ef (p.val * g) a ⊗ₜ[ℂ] w)).val m = (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
    (e (ef g a ⊗ₜ[ℂ] w)).val (m * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p)))

private theorem leviPair_mul_components (p : InfiniteLevi F B) (q : FiniteLevi F B) :
    leviPair F B p 1 * leviPair F B 1 q = leviPair F B p q := by
  funext i
  change AdelicGL.pair F (B.size i) (p i) 1 * AdelicGL.pair F (B.size i) 1 (q i) = _
  rw [AdelicGL.pair_mul, mul_one, one_mul]
  rfl

include f hf hleft in
private theorem infiniteCoefficientFunctions_eval (a : A) (g : G) :
    infiniteCoefficientFunctions F B S c e (ef g a) = (smoothScalarSlice F B S g (f a)).val := by
  funext b
  obtain ⟨p', l', hg, hp, hl⟩ := exists_finite_iwasawa F n g
  let p : AdelicBlockParabolic.Finite F B := ⟨p', B.mem_parabolic_of_isUpperTriangular p' hp⟩
  let l : KF := ⟨l', hl⟩
  let x := (infiniteIwasawa F B b).val
  let m := leviPair F B (μi x.1) 1
  let τ := archimedeanHalfExtension F B (archimedeanGLCoordinates F n x.1.val).val
  let δ : ℂ := parabolicHalfCharacter F B (ofFinite F B p)
  have hb : b = x.1.val * x.2.val := (infiniteIwasawa F B b).property
  have hg' : g = p.val * l.val := hg
  have he : (e (ef g a ⊗ₜ[ℂ] c x.2)).val m =
      δ * (e (ef l.val a ⊗ₜ[ℂ] c x.2)).val (leviPair F B (μi x.1) (μf p)) :=
    calc
      (e (ef g a ⊗ₜ[ℂ] c x.2)).val m = (e (ef (p.val * l.val) a ⊗ₜ[ℂ] c x.2)).val m :=
        congrArg (fun q : G => (e (ef q a ⊗ₜ[ℂ] c x.2)).val m) hg'
      _ = δ * (e (ef l.val a ⊗ₜ[ℂ] c x.2)).val (m * leviPair F B 1 (μf p)) :=
        hleft p l.val a (c x.2) m
      _ = _ := congrArg (fun q => δ * (e (ef l.val a ⊗ₜ[ℂ] c x.2)).val q)
        (leviPair_mul_components F B (μi x.1) (μf p))
  change τ * (e (ef g a ⊗ₜ[ℂ] c x.2)).val m = (f a).val.val.val (AdelicGL.pair F n b g)
  calc
    τ * (e (ef g a ⊗ₜ[ℂ] c x.2)).val m =
        (δ * τ) * (e (ef l.val a ⊗ₜ[ℂ] c x.2)).val (leviPair F B (μi x.1) (μf p)) := by
      rw [he, ← mul_assoc, mul_comm τ δ]
    _ = (f a).val.val.val (AdelicGL.pair F n (x.1.val * x.2.val) (p.val * l.val)) := by
      rw [scalarSection_pair_mul F B S (f a).val.val, hf]
    _ = _ := congrArg₂ (fun z d => (f a).val.val.val (AdelicGL.pair F n z d)) hb.symm hg'.symm

include f hf hleft in
private theorem mem_smoothFunctions_infiniteCoefficientFunctions
    (hspan : Submodule.span ℂ (Set.range fun q : G × A => ef q.1 q.2) = ⊤) (v : V) :
    infiniteCoefficientFunctions F B S c e v ∈ smoothFunctions F n := by
  have hv : v ∈ Submodule.span ℂ (Set.range fun q : G × A => ef q.1 q.2) :=
    hspan.symm ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨g, a⟩, rfl⟩ := hv
    rw [infiniteCoefficientFunctions_eval F B S ef c e f hf hleft]
    exact (smoothScalarSlice F B S g (f a)).property
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul z v _ hv => rw [map_smul]; exact Submodule.smul_mem _ z hv

include f hf hleft in
/-- A nonzero compact seed family supplies a nonzero vector of the stable
infinite coefficient space, once the finite inducing evaluations span. -/
theorem nontrivial_sliceTensorCoefficients_of_seed
    (hspan : Submodule.span ℂ (Set.range fun q : G × A => ef q.1 q.2) = ⊤)
    (hne : ∃ a : A, f a ≠ 0) : Nontrivial (sliceTensorCoefficients F B S ef) := by
  let φ : V →ₗ[ℂ] H := (infiniteCoefficientFunctions F B S c e).codRestrict (smoothFunctions F n)
    (mem_smoothFunctions_infiniteCoefficientFunctions F B S ef c e f hf hleft hspan)
  have hφ : ∀ a g, smoothScalarSlice F B S g (f a) = φ (ef g a) := by
    intro a g
    apply Subtype.ext
    exact (infiniteCoefficientFunctions_eval F B S ef c e f hf hleft a g).symm
  let z : sliceTensorCoefficients F B S ef :=
    ⟨φ, (mem_sliceTensorCoefficients_iff F B S ef φ).mpr fun a => ⟨f a, hφ a⟩⟩
  obtain ⟨a, ha⟩ := hne
  refine ⟨⟨z, 0, fun hz => ha ?_⟩⟩
  have hz' : φ = 0 := congrArg Subtype.val hz
  apply smoothScalarSlice_injective F B S
  funext g
  change smoothScalarSlice F B S g (f a) = smoothScalarSlice F B S g 0
  rw [hφ, hz', LinearMap.zero_apply, map_zero]

end Langlands.Global.AdelicBlockScalarSections
