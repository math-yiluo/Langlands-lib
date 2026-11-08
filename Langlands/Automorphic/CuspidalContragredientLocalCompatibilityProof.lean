import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Automorphic.CuspidalContragredientStatement
import Langlands.Automorphic.PadicLocalCategory
import Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
import Langlands.Representation.Category.Contragredient

/-! # Local smooth duality for every pair of cuspidal contragredient presentations

A full-operator contragredient pairing restricted to two embedded local components
need not be nonzero. Composing with an actual operator that commutes with the local
group at `v` makes it nonzero, by full-operator irreducibility. Irreducibility of the
two local components then makes it nondegenerate, and the published invariant-pairing
duality identifies one component with the smooth dual of the other.
-/

noncomputable section

universe uF uP uQ

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Global.CompletionPadic

section Group

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

/-- An adelic matrix with identity component at `v` commutes with the local group at `v`. -/
theorem localInclusion_commute_of_localProjection_eq_one (v : FinitePlace F)
    {d : FiniteAdelicGL F n} (hd : localProjection F n v d = 1) (g : FiniteLocalGL F n v) :
    Commute (localInclusion F n v g) d := by
  change localInclusion F n v g * d = d * localInclusion F n v g
  apply ext_localProjection F n
  intro t
  rw [map_mul, map_mul]
  by_cases ht : t = v
  · subst ht
    rw [hd, localProjection_localInclusion, mul_one, one_mul]
  · rw [localProjection_localInclusion_of_ne F n v t ht, one_mul, mul_one]

/-- Removing the `v`-component leaves an adelic matrix with identity component at `v`. -/
theorem localProjection_awayPart (v : FinitePlace F) (d : FiniteAdelicGL F n) :
    localProjection F n v ((localInclusion F n v (localProjection F n v d))⁻¹ * d) = 1 := by
  rw [map_mul, map_inv, localProjection_localInclusion, inv_mul_cancel]

/-- Every finite adelic matrix is a local matrix at `v` times one with identity
`v`-component. -/
theorem exists_localSplit (v : FinitePlace F) (d : FiniteAdelicGL F n) :
    ∃ (g : FiniteLocalGL F n v) (d' : FiniteAdelicGL F n),
      localProjection F n v d' = 1 ∧ d = localInclusion F n v g * d' :=
  ⟨_, _, localProjection_awayPart F n v d, (mul_inv_cancel_left _ _).symm⟩

end Group

section Pairing

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- A nonzero invariant pairing has zero left kernel when the left side is irreducible. -/
theorem invariantPairing_left_nondegenerate (hσ : σ.IsIrreducible)
    (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hinv : ∀ (g : G) (w : W) (x : V), b (σ g w) (ρ g x) = b w x)
    (hb : b ≠ 0) : ∀ w : W, (∀ x : V, b w x = 0) → w = 0 := by
  have := hσ
  let K : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker b
      apply_mem_toSubmodule := by
        intro g w hw
        rw [LinearMap.mem_ker] at hw ⊢
        apply LinearMap.ext
        intro x
        rw [← ρ.self_inv_apply g x, hinv g w (ρ g⁻¹ x), hw, LinearMap.zero_apply,
          LinearMap.zero_apply] }
  rcases eq_bot_or_eq_top K with h | h
  · intro w hw
    have hm : w ∈ K := LinearMap.mem_ker.mpr (LinearMap.ext hw)
    rw [h] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  · exfalso
    apply hb
    apply LinearMap.ext
    intro w
    have hm : w ∈ K := by
      rw [h]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp hm

/-- A nonzero invariant pairing has zero right kernel when the right side is irreducible. -/
theorem invariantPairing_right_nondegenerate (hρ : ρ.IsIrreducible)
    (b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hinv : ∀ (g : G) (w : W) (x : V), b (σ g w) (ρ g x) = b w x)
    (hb : b ≠ 0) : ∀ x : V, (∀ w : W, b w x = 0) → x = 0 := by
  have hb' : b.flip ≠ 0 := by
    intro h
    apply hb
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (LinearMap.congr_fun h x) w
  exact invariantPairing_left_nondegenerate (σ := ρ) (ρ := σ) hρ b.flip
    (fun g x w => hinv g w x) hb'

end Pairing

section Operators

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance localDualityRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localDualityContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localDualitySmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localDualityFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localDualityStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance localDualityOperatorSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance localDualityLocalSpaceAddCommGroup {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _
local instance localDualityFiniteSpaceAddCommGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable (n) in
/-- Ambient operators commuting with every actual local translation at `v`. -/
def localCentralizer (v : FinitePlace F) : Subalgebra ℂ (FiniteSmoothEnd F n) :=
  Subalgebra.centralizer ℂ
    (Set.range fun g : FiniteLocalGL F n v =>
      finiteSmoothFiniteRightAction F n (localInclusion F n v g))

theorem mem_localCentralizer {v : FinitePlace F} {a : FiniteSmoothEnd F n} :
    a ∈ localCentralizer n v ↔ ∀ g : FiniteLocalGL F n v,
      finiteSmoothFiniteRightAction F n (localInclusion F n v g) * a =
        a * finiteSmoothFiniteRightAction F n (localInclusion F n v g) := by
  rw [localCentralizer, Subalgebra.mem_centralizer_iff, Set.forall_mem_range]

theorem finite_mem_localCentralizer {v : FinitePlace F} {d : FiniteAdelicGL F n}
    (hd : localProjection F n v d = 1) :
    finiteSmoothFiniteRightAction F n d ∈ localCentralizer n v := by
  rw [mem_localCentralizer]
  intro g
  rw [← map_mul, ← map_mul, (localInclusion_commute_of_localProjection_eq_one F n v hd g).eq]

theorem compact_mem_localCentralizer (v : FinitePlace F) (k : standardInfiniteCompact F n) :
    finiteSmoothCompactRightAction F n k ∈ localCentralizer n v := by
  rw [mem_localCentralizer]
  intro g
  change finiteSmoothRightAction F n (AdelicGL.ofFinite F n (localInclusion F n v g)) *
      finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) =
    finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) *
      finiteSmoothRightAction F n (AdelicGL.ofFinite F n (localInclusion F n v g))
  rw [← map_mul, ← map_mul, (AdelicGL.ofFinite_commute_ofInfinite F n _ k.val).eq]

theorem enveloping_mem_localCentralizer (v : FinitePlace F)
    (u : ArchimedeanGL.EnvelopingAlgebra F n) :
    finiteSmoothEnvelopingAction F n u ∈ localCentralizer n v := by
  rw [mem_localCentralizer]
  intro g
  apply LinearMap.ext
  intro f
  exact finiteSmoothFiniteRightAction_envelopingAction F n _ u f

/-- Local translation of an embedded local vector is finite translation of its ambient
function by the local inclusion. -/
theorem LocalRealization.ambient_representation {v : FinitePlace F}
    (W : LocalRealization F n v) (g : FiniteLocalGL F n v) (x : W.Space) :
    ((W.representation g x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n) =
      finiteSmoothFiniteRightAction F n (localInclusion F n v g)
        ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n) := rfl

theorem LocalRealization.exists_ne_zero_of_ne_bot {v : FinitePlace F}
    {W : LocalRealization F n v} (h : W ≠ ⊥) : ∃ x : W.Space, x ≠ 0 := by
  by_contra! hx
  apply h
  apply le_antisymm ?_ bot_le
  intro f hf
  exact congrArg Subtype.val (hx ⟨f, hf⟩)

namespace OperatorRealization

variable (S : OperatorRealization F n)

theorem ext_ambient {y z : S.Space} (h : S.ambient y = S.ambient z) : y = z :=
  Subtype.ext (Subtype.ext h)

/-- An operator in the local centralizer commutes with the local translations of `S`. -/
theorem representation_commute {v : FinitePlace F} {a : automorphicOperatorAlgebra F n}
    (ha : a.val ∈ localCentralizer n v) (g : FiniteLocalGL F n v) (y : S.Space) :
    S.representation a (S.representation (finiteOperator F n (localInclusion F n v g)) y) =
      S.representation (finiteOperator F n (localInclusion F n v g)) (S.representation a y) := by
  apply S.ext_ambient
  change a.val (finiteSmoothFiniteRightAction F n (localInclusion F n v g) (S.ambient y)) =
    finiteSmoothFiniteRightAction F n (localInclusion F n v g) (a.val (S.ambient y))
  exact (LinearMap.congr_fun ((mem_localCentralizer.mp ha) g) (S.ambient y)).symm

variable {v : FinitePlace F} (W : LocalRealization F n v)
  (hW : W.toSubmodule ≤ S.toFiniteRealization.toSubmodule)

/-- A local subspace of the finite image, read back as vectors of the full realization. -/
def localLift : W.Space →ₗ[ℂ] S.Space :=
  S.finiteEquiv.symm.toLinearMap ∘ₗ Submodule.inclusion hW

theorem formInclusion_localLift (x : W.Space) :
    S.formInclusion (S.localLift W hW x) = x.val := by
  rw [← S.finiteEquiv_inclusion (S.localLift W hW x)]
  change S.toFiniteRealization.inclusion
      (S.finiteEquiv (S.finiteEquiv.symm (Submodule.inclusion hW x))) = x.val
  rw [Representation.Equiv.apply_symm_apply]
  rfl

theorem ambient_localLift (x : W.Space) :
    S.ambient (S.localLift W hW x) =
      ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n) :=
  congrArg Subtype.val (S.formInclusion_localLift W hW x)

theorem localLift_injective : Function.Injective (S.localLift W hW) := by
  intro x y h
  apply Subtype.ext
  rw [← S.formInclusion_localLift W hW x, ← S.formInclusion_localLift W hW y, h]

/-- The lift intertwines the local action with the restricted finite action. -/
theorem localLift_representation (g : FiniteLocalGL F n v) (x : W.Space) :
    S.localLift W hW (W.representation g x) =
      S.representation (finiteOperator F n (localInclusion F n v g)) (S.localLift W hW x) := by
  apply S.ext_ambient
  change S.ambient (S.localLift W hW (W.representation g x)) =
    finiteSmoothFiniteRightAction F n (localInclusion F n v g) (S.ambient (S.localLift W hW x))
  exact (S.ambient_localLift W hW (W.representation g x)).trans
    ((W.ambient_representation g x).trans
      (congrArg (finiteSmoothFiniteRightAction F n (localInclusion F n v g))
        (S.ambient_localLift W hW x).symm))

/-- The span of the lifted local vectors moved by operators in the local centralizer. -/
def twistedLocalSpan : Submodule ℂ S.Space :=
  Submodule.span ℂ {y | ∃ a : automorphicOperatorAlgebra F n, a.val ∈ localCentralizer n v ∧
    ∃ x : W.Space, S.representation a (S.localLift W hW x) = y}

theorem twisted_mem {a : automorphicOperatorAlgebra F n} (ha : a.val ∈ localCentralizer n v)
    (x : W.Space) :
    S.representation a (S.localLift W hW x) ∈ S.twistedLocalSpan W hW :=
  Submodule.subset_span ⟨a, ha, x, rfl⟩

theorem mul_twisted_mem {b a : automorphicOperatorAlgebra F n}
    (hb : b.val ∈ localCentralizer n v) (ha : a.val ∈ localCentralizer n v) (x : W.Space) :
    S.representation b (S.representation a (S.localLift W hW x)) ∈ S.twistedLocalSpan W hW := by
  have h := S.twisted_mem W hW (a := b * a) (Subalgebra.mul_mem _ hb ha) x
  rwa [map_mul S.representation b a, Module.End.mul_apply] at h

/-- A finite generator moves a twisted vector to a twisted vector, after splitting off its
`v`-component. -/
theorem finite_twisted_mem (d : FiniteAdelicGL F n) {a : automorphicOperatorAlgebra F n}
    (ha : a.val ∈ localCentralizer n v) (x : W.Space) :
    S.representation (finiteOperator F n d) (S.representation a (S.localLift W hW x)) ∈
      S.twistedLocalSpan W hW := by
  have hs := exists_localSplit F n v d
  rcases hs with ⟨g, d', hd', hd⟩
  subst hd
  have hc := LinearMap.congr_fun ((mem_localCentralizer.mp ha) g)
    ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n)
  have key : S.representation (finiteOperator F n (localInclusion F n v g * d'))
        (S.representation a (S.localLift W hW x)) =
      S.representation (finiteOperator F n d' * a)
        (S.localLift W hW (W.representation g x)) := by
    apply S.ext_ambient
    change finiteSmoothFiniteRightAction F n (localInclusion F n v g * d')
        (a.val (S.ambient (S.localLift W hW x))) =
      finiteSmoothFiniteRightAction F n d'
        (a.val (S.ambient (S.localLift W hW (W.representation g x))))
    calc finiteSmoothFiniteRightAction F n (localInclusion F n v g * d')
          (a.val (S.ambient (S.localLift W hW x)))
        = finiteSmoothFiniteRightAction F n (localInclusion F n v g * d')
          (a.val ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n)) :=
          congrArg (fun w => finiteSmoothFiniteRightAction F n (localInclusion F n v g * d')
            (a.val w)) (S.ambient_localLift W hW x)
      _ = finiteSmoothFiniteRightAction F n (d' * localInclusion F n v g)
          (a.val ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n)) :=
          congrArg (fun e => finiteSmoothFiniteRightAction F n e
            (a.val ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n)))
            (localInclusion_commute_of_localProjection_eq_one F n v hd' g).eq
      _ = finiteSmoothFiniteRightAction F n d'
          (finiteSmoothFiniteRightAction F n (localInclusion F n v g)
            (a.val ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n))) :=
          LinearMap.congr_fun (map_mul (finiteSmoothFiniteRightAction F n) d'
            (localInclusion F n v g)) _
      _ = finiteSmoothFiniteRightAction F n d'
          (a.val (finiteSmoothFiniteRightAction F n (localInclusion F n v g)
            ((x : AutomorphicForms F n) : FiniteSmoothRationalFunctions F n))) :=
          congrArg (finiteSmoothFiniteRightAction F n d') hc
      _ = finiteSmoothFiniteRightAction F n d'
          (a.val (S.ambient (S.localLift W hW (W.representation g x)))) :=
          congrArg (fun w => finiteSmoothFiniteRightAction F n d' (a.val w))
            ((S.ambient_localLift W hW (W.representation g x)).trans
              (W.ambient_representation g x)).symm
  rw [key]
  exact S.twisted_mem W hW (Subalgebra.mul_mem _ (finite_mem_localCentralizer hd') ha) _

/-- Every operator of the concrete algebra preserves the twisted span. -/
theorem representation_mem_twistedLocalSpan {c : FiniteSmoothEnd F n}
    (hc : c ∈ Algebra.adjoin ℂ (automorphicOperatorGenerators F n)) :
    ∀ y ∈ S.twistedLocalSpan W hW,
      S.representation ⟨c, hc⟩ y ∈ S.twistedLocalSpan W hW := by
  induction hc using Algebra.adjoin_induction with
  | mem c hc =>
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨a, ha, x, rfl⟩ := hz
          rcases hc with (⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩
          · exact S.finite_twisted_mem W hW d ha x
          · exact S.mul_twisted_mem W hW (b := compactOperator F n k)
              (compact_mem_localCentralizer v k) ha x
          · exact S.mul_twisted_mem W hW (b := differentialOperator F n u)
              (enveloping_mem_localCentralizer v u) ha x
      | zero =>
          rw [LinearMap.map_zero]
          exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
          rw [LinearMap.map_add]
          exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
          rw [LinearMap.map_smul]
          exact Submodule.smul_mem _ r hy
  | algebraMap r =>
      intro y hy
      have h : S.representation ⟨algebraMap ℂ (FiniteSmoothEnd F n) r,
          Subalgebra.algebraMap_mem _ r⟩ y = r • y := by
        apply S.ext_ambient
        change algebraMap ℂ (FiniteSmoothEnd F n) r (S.ambient y) = r • S.ambient y
        exact Module.algebraMap_end_apply ℂ ℂ (FiniteSmoothRationalFunctions F n) r _
      rw [h]
      exact Submodule.smul_mem _ r hy
  | add c₁ c₂ hc₁ hc₂ ih₁ ih₂ =>
      intro y hy
      have h : S.representation ⟨c₁ + c₂, add_mem hc₁ hc₂⟩ y =
          S.representation ⟨c₁, hc₁⟩ y + S.representation ⟨c₂, hc₂⟩ y := by
        apply S.ext_ambient
        change (c₁ + c₂) (S.ambient y) =
          S.ambient (S.representation ⟨c₁, hc₁⟩ y) + S.ambient (S.representation ⟨c₂, hc₂⟩ y)
        exact LinearMap.add_apply c₁ c₂ (S.ambient y)
      rw [h]
      exact Submodule.add_mem _ (ih₁ y hy) (ih₂ y hy)
  | mul c₁ c₂ hc₁ hc₂ ih₁ ih₂ =>
      intro y hy
      have h : S.representation ⟨c₁ * c₂, mul_mem hc₁ hc₂⟩ y =
          S.representation ⟨c₁, hc₁⟩ (S.representation ⟨c₂, hc₂⟩ y) := by
        apply S.ext_ambient
        change (c₁ * c₂) (S.ambient y) = c₁ (c₂ (S.ambient y))
        exact Module.End.mul_apply c₁ c₂ (S.ambient y)
      rw [h]
      exact ih₁ _ (ih₂ y hy)

/-- The twisted span is invariant under the whole concrete operator algebra. -/
theorem twistedLocalSpan_stable (b : automorphicOperatorAlgebra F n) {y : S.Space}
    (hy : y ∈ S.twistedLocalSpan W hW) :
    S.representation b y ∈ S.twistedLocalSpan W hW :=
  S.representation_mem_twistedLocalSpan W hW b.property y hy

/-- By full-operator irreducibility, the twisted span of a nonzero local subspace is all
of `S`. -/
theorem twistedLocalSpan_eq_top (hS : S.IsIrreducible) (hW0 : W ≠ ⊥) :
    S.twistedLocalSpan W hW = ⊤ := by
  have : IsSimpleOrder (Subrepresentation S.representation) := hS
  let Y : Subrepresentation S.representation :=
    { toSubmodule := S.twistedLocalSpan W hW
      apply_mem_toSubmodule := fun b _ hy => S.twistedLocalSpan_stable W hW b hy }
  rcases eq_bot_or_eq_top Y with h | h
  · exfalso
    have hx0 := LocalRealization.exists_ne_zero_of_ne_bot hW0
    rcases hx0 with ⟨x, hx⟩
    have hm : S.localLift W hW x ∈ Y := by
      have h1 := S.twisted_mem W hW (a := 1) (Subalgebra.one_mem _) x
      rwa [map_one, Module.End.one_apply] at h1
    rw [h] at hm
    have h0 : S.localLift W hW x = S.localLift W hW 0 :=
      ((Submodule.mem_bot ℂ).mp hm).trans (LinearMap.map_zero _).symm
    exact hx (S.localLift_injective W hW h0)
  · exact congrArg Subrepresentation.toSubmodule h

/-- A nonzero functional on `S` is nonzero on some twisted lifted local vector. -/
theorem exists_twist_ne_zero (hS : S.IsIrreducible) (hW0 : W ≠ ⊥)
    (l : S.Space →ₗ[ℂ] ℂ) (hl : l ≠ 0) :
    ∃ a : automorphicOperatorAlgebra F n, a.val ∈ localCentralizer n v ∧
      ∃ x : W.Space, l (S.representation a (S.localLift W hW x)) ≠ 0 := by
  by_contra! h
  have hall : ∀ y ∈ S.twistedLocalSpan W hW, l y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, ha, x, rfl⟩ := hz
        exact h a ha x
    | zero => exact LinearMap.map_zero l
    | add y z _ _ hy hz => rw [LinearMap.map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smul, hy, smul_zero]
  apply hl
  apply LinearMap.ext
  intro y
  have hy : y ∈ S.twistedLocalSpan W hW := by
    rw [S.twistedLocalSpan_eq_top W hW hS hW0]
    exact Submodule.mem_top
  rw [hall y hy, LinearMap.zero_apply]

end OperatorRealization

/-- Two embedded local subspaces of contragredient full realizations carry a nonzero
invariant pairing, obtained by twisting the full pairing by a commuting operator. -/
theorem exists_localInvariantPairing {S S' : OperatorRealization F n} (hS : S.IsIrreducible)
    {B : S.Space →ₗ[ℂ] S'.Space →ₗ[ℂ] ℂ} (hB : S.IsContragredientPairing S' B)
    {v : FinitePlace F} (W W' : LocalRealization F n v)
    (hW : W.toSubmodule ≤ S.toFiniteRealization.toSubmodule)
    (hW' : W'.toSubmodule ≤ S'.toFiniteRealization.toSubmodule)
    (hW0 : W ≠ ⊥) (hW'0 : W' ≠ ⊥) :
    ∃ b : W'.Space →ₗ[ℂ] W.Space →ₗ[ℂ] ℂ,
      (∀ (g : FiniteLocalGL F n v) (x' : W'.Space) (x : W.Space),
        b (W'.representation g x') (W.representation g x) = b x' x) ∧ b ≠ 0 := by
  have hx'0 := LocalRealization.exists_ne_zero_of_ne_bot hW'0
  rcases hx'0 with ⟨x', hx'⟩
  have hl : B.flip (S'.localLift W' hW' x') ≠ 0 := by
    intro h
    apply hx'
    apply S'.localLift_injective W' hW'
    apply hB.2.2.1
    exact h.trans ((LinearMap.map_zero B.flip).symm.trans
      (congrArg B.flip (LinearMap.map_zero (S'.localLift W' hW')).symm))
  have htw := S.exists_twist_ne_zero W hW hS hW0 _ hl
  rcases htw with ⟨a, ha, x, hax⟩
  let f : W.Space →ₗ[ℂ] S.Space := S.representation a ∘ₗ S.localLift W hW
  let b : W'.Space →ₗ[ℂ] W.Space →ₗ[ℂ] ℂ := (B.compl₁₂ f (S'.localLift W' hW')).flip
  have hb : ∀ (y' : W'.Space) (y : W.Space),
      b y' y = B (S.representation a (S.localLift W hW y)) (S'.localLift W' hW' y') :=
    fun y' y => (LinearMap.flip_apply (B.compl₁₂ f (S'.localLift W' hW')) y y').trans
      ((LinearMap.compl₁₂_apply B f (S'.localLift W' hW') y y').trans
        (congrArg (fun z => B z (S'.localLift W' hW' y'))
          (LinearMap.comp_apply (S.representation a) (S.localLift W hW) y)))
  refine ⟨b, ?_, ?_⟩
  · intro g y' y
    have h1 : S.representation a (S.localLift W hW (W.representation g y)) =
        S.representation (finiteOperator F n (localInclusion F n v g))
          (S.representation a (S.localLift W hW y)) :=
      (congrArg (S.representation a) (S.localLift_representation W hW g y)).trans
        (S.representation_commute ha g (S.localLift W hW y))
    have h2 := S'.localLift_representation W' hW' g y'
    exact (hb (W'.representation g y') (W.representation g y)).trans
      ((congrArg₂ (fun p q => B p q) h1 h2).trans
        ((hB.1.1 (localInclusion F n v g) (S.representation a (S.localLift W hW y))
          (S'.localLift W' hW' y')).trans (hb y' y).symm))
  · intro h
    apply hax
    refine (LinearMap.flip_apply B (S.representation a (S.localLift W hW x))
      (S'.localLift W' hW' x')).trans ((hb x' x).symm.trans ?_)
    exact (LinearMap.congr_fun (LinearMap.congr_fun h x') x).trans
      ((LinearMap.congr_fun (LinearMap.zero_apply x') x).trans (LinearMap.zero_apply x))

/-- Every pair of presentations of full-operator contragredient cusp objects has
contragredient original local actions at every finite place where both actual local
components are irreducible and admissible. -/
theorem cuspidalContragredientLocalCompatibility :
    CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uQ} := by
  intro F _ _ _ r T T' hTT' P P' v hI hA hI' hA'
  obtain ⟨B, hB⟩ := hTT'
  have hW : (P.localComponent v).toSubmodule ≤
      T.realization.toFiniteRealization.toSubmodule := fun f hf =>
    P.finiteSlice.le_image (P.presentation.localComponent_le P.finiteSlice.nonzero v hf)
  have hW' : (P'.localComponent v).toSubmodule ≤
      T'.realization.toFiniteRealization.toSubmodule := fun f hf =>
    P'.finiteSlice.le_image (P'.presentation.localComponent_le P'.finiteSlice.nonzero v hf)
  have hpair := exists_localInvariantPairing T.irreducible hB
    (P.localComponent v) (P'.localComponent v) hW hW'
    (P.localComponent_ne_bot v) (P'.localComponent_ne_bot v)
  rcases hpair with ⟨b, hinv, hb⟩
  have hleft := invariantPairing_left_nondegenerate hI' b hinv hb
  have hright := invariantPairing_right_nondegenerate hI b hinv hb
  let := (padicField v).canonicalTopologicalData.topology
  let _ : TopologicalSpace (Langlands.GeneralLinear (r.succPNat : ℕ)
      (padicField v).Carrier) := (padicField v).canonicalGeneralLinearTopology _
  let _ : IsTopologicalGroup (Langlands.GeneralLinear (r.succPNat : ℕ)
      (padicField v).Carrier) := (padicField v).canonicalGeneralLinearTopologicalGroup _
  have hE := smoothInvariantPairingDuality
    (GeneralLinear.compactOpen_cofinal (padicField v) (padicField v).canonicalTopologicalData
      (r.succPNat : ℕ))
    ((P.localComponent v).padicObject hI hA).obj.representation
    ((P'.localComponent v).padicObject hI' hA').obj.representation
    ((P.localComponent v).padicObject hI hA).property.2
    ((P'.localComponent v).padicObject hI' hA').obj.property
    b hinv hleft hright
  rcases hE with ⟨E, -⟩
  exact ⟨E⟩

end Operators

end Langlands.Automorphic
