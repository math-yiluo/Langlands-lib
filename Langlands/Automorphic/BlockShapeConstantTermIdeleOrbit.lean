import Langlands.Automorphic.BlockShapeLeviIdeleOrbit
import Langlands.Automorphic.CompactAction
import Langlands.Global.FiniteBlockParabolicCosets
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The block idele centre orbit of an actual full constant term -/

noncomputable section

universe u

open NumberField
open scoped Classical BigOperators CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance fullOrbitRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance fullOrbitContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullOrbitFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance constantTermIdeleOrbitFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

local notation "G" => AdelicGL F n
local notation "V" => FiniteSmoothRationalFunctions F n
local notation "M" => AdelicBlockParabolic.FullLevi F B
local notation "Cen" => (Fin B.length → Ideles F)
local notation "K" => standardInfiniteCompact F n
local notation "Lemb" => B.leviEmbedding (Adeles F)
local notation "Pproj" => B.leviProjection (Adeles F)
local notation "finc" => AdelicGL.ofFinite F n
local notation "infc" => AdelicGL.ofInfinite F n

local notation "ρ" => blockConstantTermScalarAction F B
local notation "C" => blockShapeConstantTermLinear F B

private theorem blockConstantTermScalarAction_parabolic (f : V) (z : Cen)
    (p : AdelicBlockParabolic.Full F B) (g : G) :
    ρ z (C f) (p.val * g) = ρ z (C f) (Lemb (Pproj p) * g) := by
  let s := B.leviInParabolic (Adeles F) (blockLeviScalars F B z)
  change blockShapeConstantTerm B F f (s.val * (p.val * g)) =
    blockShapeConstantTerm B F f (Lemb (blockLeviScalars F B z) * (Lemb (Pproj p) * g))
  rw [← mul_assoc s.val p.val g, ← Subgroup.coe_mul, blockShapeConstantTerm_parabolic_mul,
    map_mul, B.leviProjection_section]
  simp only [blockShapeLeviSlice, map_mul, mul_assoc]

private theorem blockConstantTermOrbit_parabolic (f : V) (h : FiniteVectors.orbitSpan ρ (C f))
    (p : AdelicBlockParabolic.Full F B) (g : G) :
    h.val (p.val * g) = h.val (Lemb (Pproj p) * g) := by
  obtain ⟨h, hm⟩ := h
  change h (p.val * g) = h (Lemb (Pproj p) * g)
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨z, rfl⟩ := hv
    exact blockConstantTermScalarAction_parabolic F B f z p g
  | zero => rfl
  | add v w _ _ hv hw => exact congrArg₂ (· + ·) hv hw
  | smul c v _ hv => exact congrArg (c • ·) hv

private theorem blockConstantTermOrbit_finiteLevel (f : V) (h : FiniteVectors.orbitSpan ρ (C f))
    (g : G) (d : FiniteAdelicGL F n) (hd : finiteSmoothRightAction F n (finc d) f = f) :
    h.val (g * finc d) = h.val g := by
  obtain ⟨h, hm⟩ := h
  change h (g * finc d) = h g
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨z, rfl⟩ := hv
    change blockShapeConstantTerm B F f (Lemb (blockLeviScalars F B z) * (g * finc d)) =
      blockShapeConstantTerm B F f (Lemb (blockLeviScalars F B z) * g)
    rw [← mul_assoc, ← blockShapeConstantTerm_rightAction, hd]
  | zero => rfl
  | add v w _ _ hv hw => exact congrArg₂ (· + ·) hv hw
  | smul c v _ hv => exact congrArg (c • ·) hv

private theorem exists_fullOrbitEvaluation (f : AutomorphicForms F n)
    (h : FiniteVectors.orbitSpan ρ (C f.val)) :
    ∃ E : AutomorphicForms F n →ₗ[ℂ] (G → ℂ), ∀ (k : K) (g : G),
      h.val (g * infc k.val) = E (automorphicCompactRightAction F n k f) g := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h.property
  let j := (automorphicSubrepresentation F n).toSubmodule.subtype
  refine ⟨c.sum fun z a => a • ((ρ z).comp ((C).comp j)), fun k g => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  change blockShapeConstantTerm B F f.val (Lemb (blockLeviScalars F B z) * (g * infc k.val)) =
    blockShapeConstantTerm B F (finiteSmoothRightAction F n (infc k.val) f.val)
      (Lemb (blockLeviScalars F B z) * g)
  rw [blockShapeConstantTerm_rightAction, mul_assoc]

private theorem exists_parabolic_compact_finiteLevel (L : OpenSubgroup (FiniteAdelicGL F n)) (g : G) :
    ∃ (p : AdelicBlockParabolic.Full F B) (k : K)
      (d : finiteBlockParabolicDoubleCosetReps F B L) (l : L),
      g = p.val * (finc d.val * infc k.val) * finc l.val := by
  obtain ⟨b, k, hg, hb, hk⟩ := PrimitiveAdelicHeight.exists_infinite_iwasawa F n (AdelicGL.infinite F n g)
  obtain ⟨d, hd, q, l, hgf⟩ := finiteBlockParabolicDoubleCosetReps_cover F B L (AdelicGL.finite F n g)
  let p := AdelicBlockParabolic.pair F B ⟨b, B.mem_parabolic_of_isUpperTriangular b hb⟩ q
  refine ⟨p, ⟨k, hk⟩, ⟨d, hd⟩, l, ?_⟩
  change g = AdelicGL.pair F n b q.val * (finc d * infc k) * finc l.val
  simp only [AdelicGL.ofFinite_eq_pair, AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, one_mul, mul_one,
    ← hg, ← hgf, AdelicGL.pair_projections]

private theorem blockConstantTermOrbit_detected (f : AutomorphicForms F n)
    (L : OpenSubgroup (FiniteAdelicGL F n))
    (hL : ∀ l : L, finiteSmoothRightAction F n (finc l.val) f.val = f.val)
    {J : Type*} (k : J → K)
    (hk : Submodule.span ℂ (Set.range fun j => automorphicCompactRightAction F n (k j) f) =
      FiniteVectors.orbitSpan (automorphicCompactRightAction F n) f)
    (h : FiniteVectors.orbitSpan ρ (C f.val))
    (hzero : ∀ (j : J) (d : finiteBlockParabolicDoubleCosetReps F B L) (m : M),
      h.val (Lemb m * (finc d.val * infc (k j).val)) = 0) : h = 0 := by
  obtain ⟨E, hE⟩ := exists_fullOrbitEvaluation F B f h
  apply Subtype.ext
  funext x
  obtain ⟨p, u, d, l, hx⟩ := exists_parabolic_compact_finiteLevel F B L x
  rw [hx, blockConstantTermOrbit_finiteLevel F B f.val h _ _ (hL l),
    blockConstantTermOrbit_parabolic F B f.val h p, ← mul_assoc, hE]
  let y := Lemb (Pproj p) * finc d.val
  let e : AutomorphicForms F n →ₗ[ℂ] ℂ := (LinearMap.proj y).comp E
  change e (automorphicCompactRightAction F n u f) = 0
  apply LinearMap.mem_ker.mp
  have hm : automorphicCompactRightAction F n u f ∈
      FiniteVectors.orbitSpan (automorphicCompactRightAction F n) f :=
    FiniteVectors.action_mem_orbitSpan _ _ _
  rw [← hk] at hm
  refine (Submodule.span_le.mpr ?_) hm
  rintro _ ⟨j, rfl⟩
  apply LinearMap.mem_ker.mpr
  change E (automorphicCompactRightAction F n (k j) f) y = 0
  rw [← hE]
  dsimp only [y]
  rw [mul_assoc]
  exact hzero j d (Pproj p)

private def constantTermSample (k : K) (d : FiniteAdelicGL F n) :
    (G → ℂ) →ₗ[ℂ] (M → ℂ) where
  toFun h m := h (Lemb m * (finc d * infc k.val))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem constantTermSample_orbit (f : AutomorphicForms F n) (k : K) (d : FiniteAdelicGL F n)
    (z : Cen) :
    constantTermSample F B k d (ρ z (C f.val)) = blockLeviScalarAction F B z
      (blockLeviTermRestriction F B (automorphicFiniteRightAction F n d
        (automorphicCompactRightAction F n k f)).val) := by
  let a := finc d * infc k.val
  have hf : (automorphicFiniteRightAction F n d (automorphicCompactRightAction F n k f)).val =
      finiteSmoothRightAction F n a f.val := by
    change finiteSmoothRightAction F n (finc d) (finiteSmoothRightAction F n (infc k.val) f.val) = _
    rw [← Module.End.mul_apply, ← map_mul]
  funext m
  rw [hf]
  change blockShapeConstantTerm B F f.val (Lemb (blockLeviScalars F B z) * (Lemb m * a)) =
    blockShapeLeviSlice F B (finiteSmoothRightAction F n a f.val) 1 (m * blockLeviScalars F B z)
  rw [blockShapeLeviSlice_rightAction, one_mul, blockShapeLeviSlice,
    ← (blockLeviScalars_commute F B z m).eq, map_mul, mul_assoc]

set_option maxHeartbeats 700000 in
/-- The span of all left block-centre translates of the full constant term of an
actual automorphic form is finite-dimensional. -/
theorem blockShapeConstantTerm_isFiniteVector (f : AutomorphicForms F n) :
    FiniteVectors.IsFiniteVector ρ (C f.val) := by
  let κ := automorphicCompactRightAction F n
  let : Module.Finite ℂ (Submodule.span ℂ (Set.range fun k => κ k f)) :=
    automorphicCompactRightAction_isFiniteVector F n f
  obtain ⟨t, ht, -, hspan, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ (Set.range fun k => κ k f)
  choose k hk using fun v : t => ht v.property
  have hs : Submodule.span ℂ (Set.range fun j => κ (k j) f) = FiniteVectors.orbitSpan κ f := by
    have he : Set.range (fun j => κ (k j) f) = (t : Set (AutomorphicForms F n)) := by
      ext v
      constructor
      · rintro ⟨j, rfl⟩
        rw [hk]
        exact j.property
      · intro hv
        exact ⟨⟨v, hv⟩, hk _⟩
    rw [he]
    exact hspan
  obtain ⟨L, hL⟩ := f.val.property.2
  let J := t × (finiteBlockParabolicDoubleCosetReps F B L)
  let P := FiniteVectors.orbitSpan ρ (C f.val)
  let v (j : J) := automorphicFiniteRightAction F n j.2.val (κ (k j.1) f)
  let W (j : J) := FiniteVectors.orbitSpan (blockLeviScalarAction F B)
    (blockLeviTermRestriction F B (v j).val)
  let : ∀ j : J, Module.Finite ℂ (W j) := fun j =>
    blockLeviTermRestriction_isFiniteVector F B (v j).val (v j).property.1
  let E (j : J) := constantTermSample F B (k j.1) j.2.val
  have hE (j : J) : P ≤ (W j).comap (E j) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change E j (ρ z (C f.val)) ∈ W j
    rw [show E j (ρ z (C f.val)) = _ from constantTermSample_orbit F B f (k j.1) j.2.val z]
    exact FiniteVectors.action_mem_orbitSpan _ _ _
  let e : P →ₗ[ℂ] (∀ j : J, W j) := LinearMap.pi fun j =>
    ((E j).domRestrict P).codRestrict (W j) (fun w => hE j w.property)
  apply Module.Finite.of_injective e
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro h hh
  have hz := LinearMap.mem_ker.mp hh
  apply blockConstantTermOrbit_detected F B f L (fun l => Subtype.ext (hL l)) k hs h
  intro j d m
  exact congrArg (fun F' : ∀ j : J, W j => (F' (j, d)).val m) hz

end Langlands.Automorphic
