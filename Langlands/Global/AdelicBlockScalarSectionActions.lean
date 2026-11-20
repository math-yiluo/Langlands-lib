import Langlands.Global.AdelicBlockScalarSections
import Langlands.Representation.Smooth.SmoothPart.BasicProof

/-!
# The finite adelic action on scalar block sections

Finite right translation uses the old compact slice translated on the right by
a finite Levi element and scaled by the positive parabolic half character.
The actual operator realizations supply the coefficient action.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local notation "K" => (standardCompact F n)
local notation "M" => FullLevi F B
local notation "P" => Full F B
local notation "μ" => B.leviProjection (Adeles F)

/-- On a compact slice, right translation is computed by right multiplication on
the Levi once the translated compact point has been factored. -/
theorem normalizedSlice_rightTranslate {W : Submodule ℂ (M → ℂ)}
    (f : ScalarSections F B W) (d : AdelicGL F n) (k l : K) (p : P)
    (h : k.val * d = p.val * l.val) (m : M) :
    normalizedSlice F B (fun g => f.val (g * d)) k m =
      (parabolicHalfCharacter F B p : ℂ) * normalizedSlice F B f.val l (m * μ p) := by
  have hfactor :
      (B.leviEmbedding (Adeles F) m * k.val) * d =
      ((B.leviInParabolic (Adeles F) m) * p).val * l.val := by
    rw [mul_assoc, h, ← mul_assoc, Subgroup.coe_mul, B.leviInParabolic_val]
  change (leviHalfCharacter F B m : ℂ)⁻¹ *
    f.val ((B.leviEmbedding (Adeles F) m * k.val) * d) = _
  rw [hfactor, scalarSection_apply_mul F B W]
  simp only [map_mul, parabolicHalfCharacter_section, B.leviProjection_section, Units.val_mul]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

private theorem exists_finiteParabolic_mul_compact (k : K) (d : FiniteAdelicGL F n) :
    ∃ (p : Finite F B) (l : K),
      k.val * AdelicGL.ofFinite F n d = (AdelicBlockParabolic.ofFinite F B p).val * l.val := by
  obtain ⟨β, κ, h, hβ, hκ⟩ :=
    exists_finite_iwasawa F n (AdelicGL.finite F n k.val * d)
  let p : Finite F B := ⟨β, B.mem_parabolic_of_isUpperTriangular β hβ⟩
  let kInf := AdelicGL.infinite F n k.val
  let l : K := ⟨AdelicGL.pair F n kInf κ, (mem_standardCompact_iff F n _).mpr
    ⟨by rw [AdelicGL.infinite_pair]; exact ((mem_standardCompact_iff F n k.val).mp k.property).1,
      by rw [AdelicGL.finite_pair]; exact hκ⟩⟩
  refine ⟨p, l, ?_⟩
  change k.val * AdelicGL.ofFinite F n d = AdelicGL.ofFinite F n β * AdelicGL.pair F n kInf κ
  calc
    k.val * AdelicGL.ofFinite F n d =
        AdelicGL.pair F n kInf (AdelicGL.finite F n k.val * d) := by
      conv_lhs => rw [← AdelicGL.pair_projections F n k.val, AdelicGL.ofFinite_eq_pair,
        AdelicGL.pair_mul, mul_one]
    _ = _ := by rw [h, AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, one_mul]

private theorem leviProjection_ofFinite (p : Finite F B) :
    μ (AdelicBlockParabolic.ofFinite F B p) =
      leviPair F B 1 (B.leviProjection (FiniteAdeles F) p) := by
  change μ (AdelicBlockParabolic.pair F B 1 p) = _
  rw [leviProjection_pair, map_one]

/-- Embed the infinite standard compact factor in the full adelic standard compact group. -/
def infiniteCompactInclusion : standardInfiniteCompact F n →* K where
  toFun k := ⟨AdelicGL.ofInfinite F n k.val, (mem_standardCompact_iff F n _).mpr
    ⟨by rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.infinite_pair]; exact k.property,
      by rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.finite_pair]; exact one_mem _⟩⟩
  map_one' := Subtype.ext ((AdelicGL.ofInfinite F n).map_one)
  map_mul' k l := Subtype.ext ((AdelicGL.ofInfinite F n).map_mul k.val l.val)

variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

/-- Finite right translation of a Levi coefficient stays in the realized coefficient space. -/
theorem coefficientValues_rightFinite {φ : M → ℂ} (hφ : φ ∈ coefficientValues F B S)
    (d : FiniteLevi F B) :
    (fun m : M => φ (m * leviPair F B 1 d)) ∈ coefficientValues F B S := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, rfl⟩ := h
    apply Submodule.subset_span
    refine ⟨fun i => (S i).finiteRepresentation (d i) (f i), ?_⟩
    funext m
    refine Finset.prod_congr rfl fun i _ => ?_
    exact OperatorRealization.evaluate_finiteRepresentation (S i) (d i) (f i) (m i)
  | zero => exact (coefficientValues F B S).zero_mem
  | add φ ψ _ _ hφ hψ => exact (coefficientValues F B S).add_mem hφ hψ
  | smul c φ _ hφ => exact (coefficientValues F B S).smul_mem c hφ

/-- Finite adelic right translation preserves scalar sections from the realized block
coefficients. -/
def RealizedSections.finiteSubrepresentation :
    Subrepresentation ((Whittaker.rightTranslation ℂ (AdelicGL F n)).comp
      (AdelicGL.ofFinite F n).toMonoidHom) where
  toSubmodule := RealizedSections F B S
  apply_mem_toSubmodule d f hf := by
    refine ⟨fun u g => ?_, fun k => ?_⟩
    · change f ((u.val.val * g) * AdelicGL.ofFinite F n d) =
        f (g * AdelicGL.ofFinite F n d)
      exact (congrArg f (mul_assoc _ _ _)).trans (hf.1 _ _)
    · obtain ⟨p, l, hp⟩ := exists_finiteParabolic_mul_compact F B k d
      let q := AdelicBlockParabolic.ofFinite F B p
      have hslice :
          normalizedSlice F B (fun g => f (g * AdelicGL.ofFinite F n d)) k =
          (parabolicHalfCharacter F B q : ℂ) •
            (fun m : M => normalizedSlice F B f l
              (m * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p))) := by
        funext m
        rw [normalizedSlice_rightTranslate F B (⟨f, hf⟩ : RealizedSections F B S) _ k l q hp m,
          leviProjection_ofFinite]
        rfl
      change normalizedSlice F B (fun g => f (g * AdelicGL.ofFinite F n d)) k ∈ _
      rw [hslice]
      exact (coefficientValues F B S).smul_mem _
        (coefficientValues_rightFinite F B S (hf.2 l) _)

/-- The action of the actual finite adelic factor on the full scalar carrier. -/
abbrev RealizedSections.finiteAction :
    Representation ℂ (FiniteAdelicGL F n) (RealizedSections F B S) :=
  (RealizedSections.finiteSubrepresentation F B S).toRepresentation

@[simp]
theorem RealizedSections.finiteAction_apply (d : FiniteAdelicGL F n)
    (f : RealizedSections F B S) (g : AdelicGL F n) :
    (RealizedSections.finiteAction F B S d f).val g = f.val (g * AdelicGL.ofFinite F n d) := rfl

/-- The infinite standard compact group acts by right translation on the scalar carrier. -/
abbrev RealizedSections.infiniteCompactAction :
    Representation ℂ (standardInfiniteCompact F n) (RealizedSections F B S) :=
  (ScalarSections.compactSubrepresentation F B (coefficientValues F B S)).toRepresentation.comp
    (infiniteCompactInclusion F)

@[simp]
theorem RealizedSections.infiniteCompactAction_apply (k : standardInfiniteCompact F n)
    (f : RealizedSections F B S) (g : AdelicGL F n) :
    (RealizedSections.infiniteCompactAction F B S k f).val g =
      f.val (g * AdelicGL.ofInfinite F n k.val) := rfl

/-- The finite and infinite compact actions commute on actual scalar sections. -/
theorem RealizedSections.finiteAction_infiniteCompactAction (d : FiniteAdelicGL F n)
    (k : standardInfiniteCompact F n) (f : RealizedSections F B S) :
    RealizedSections.finiteAction F B S d (RealizedSections.infiniteCompactAction F B S k f) =
      RealizedSections.infiniteCompactAction F B S k (RealizedSections.finiteAction F B S d f) := by
  apply Subtype.ext
  funext g
  rw [finiteAction_apply, infiniteCompactAction_apply, infiniteCompactAction_apply,
    finiteAction_apply, mul_assoc, mul_assoc,
    (AdelicGL.ofFinite_commute_ofInfinite F n d k.val).eq]

/-- The subspace with one common open stabilizer under finite right translations. -/
abbrev FiniteSmoothRealizedSections :=
  smoothVectors (RealizedSections.finiteAction F B S)

local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) :=
  Submodule.addCommGroup _

/-- A smooth representation of the actual finite adelic factor. -/
abbrev finiteSmoothAction :
    Representation ℂ (FiniteAdelicGL F n) (FiniteSmoothRealizedSections F B S) :=
  smoothPart (RealizedSections.finiteAction F B S)

theorem isSmooth_finiteSmoothAction : IsSmooth (finiteSmoothAction F B S) :=
  isSmooth_smoothPart _

/-- An open finite stabilizer is preserved by the commuting infinite compact action. -/
def finiteSmoothCompactSubrepresentation :
    Subrepresentation (RealizedSections.infiniteCompactAction F B S) where
  toSubmodule := FiniteSmoothRealizedSections F B S
  apply_mem_toSubmodule k f hf := by
    obtain ⟨L, hL⟩ := hf
    refine ⟨L, fun d => ?_⟩
    have hd : RealizedSections.finiteAction F B S d.val f = f := hL d
    change RealizedSections.finiteAction F B S d.val
        (RealizedSections.infiniteCompactAction F B S k f) =
      RealizedSections.infiniteCompactAction F B S k f
    rw [RealizedSections.finiteAction_infiniteCompactAction, hd]

/-- The infinite compact action on the finite-smooth carrier. -/
abbrev finiteSmoothCompactAction :
    Representation ℂ (standardInfiniteCompact F n) (FiniteSmoothRealizedSections F B S) :=
  (finiteSmoothCompactSubrepresentation F B S).toRepresentation

/-- Finite translations intertwine the infinite compact action on the finite-smooth carrier. -/
def finiteSmoothTranslateIntertwiner (d : FiniteAdelicGL F n) :
    (finiteSmoothCompactAction F B S).IntertwiningMap (finiteSmoothCompactAction F B S) where
  toLinearMap := finiteSmoothAction F B S d
  isIntertwining' k := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact RealizedSections.finiteAction_infiniteCompactAction F B S d k f.val

/-- The infinite compact finite vectors in the finite-smooth carrier. -/
def compactFiniteSubrepresentation :
    Subrepresentation (finiteSmoothCompactAction F B S) :=
  FiniteVectors.subrepresentation (finiteSmoothCompactAction F B S)

/-- The same compact-finite subspace is invariant under the finite adelic factor. -/
def compactFiniteFiniteSubrepresentation :
    Subrepresentation (finiteSmoothAction F B S) where
  toSubmodule := (compactFiniteSubrepresentation F B S).toSubmodule
  apply_mem_toSubmodule d f hf := by
    change FiniteVectors.IsFiniteVector (finiteSmoothCompactAction F B S) f at hf
    change FiniteVectors.IsFiniteVector (finiteSmoothCompactAction F B S)
      (finiteSmoothTranslateIntertwiner F B S d f)
    exact hf.map (finiteSmoothTranslateIntertwiner F B S d)

/-- The scalar carrier with one common open finite stabilizer and finite infinite compact span. -/
abbrev CompactFiniteRealizedSections := (compactFiniteSubrepresentation F B S).toSubmodule

end Langlands.Global.AdelicBlockScalarSections
