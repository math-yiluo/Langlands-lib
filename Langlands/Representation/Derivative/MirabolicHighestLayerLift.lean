import Langlands.Representation.Derivative.MirabolicHighestLayerStatement
import Langlands.Representation.Derivative.LevelCalculus
import Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
import Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
import Langlands.Representation.Derivative.MirabolicLatticeBox
import Langlands.Group.GL.MirabolicProjection
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-! # Lifting invariant subspaces through one `Φ⁻` step

The highest layer is built intrinsically by iterating one `Φ⁻` step: for a representation
`B` of `P_(m+2)` and an invariant subspace `X` of `Φ⁻ B`, the vectors of the radical
relations of `B` all of whose translates have classes in `X` form an invariant
subspace mapping onto `X`. The lift is inverse to taking images on invariant
subspaces of the radical relations.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic.HighestLayer

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis RankinSelberg Topology
open Jacquet.Localization
open scoped Matrix

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ## Left exactness at the level of elements -/

/-- A vector of an invariant subspace that is a character relation of the radical in
the ambient representation is already a relation inside the subspace. -/
theorem mem_relations_subrepresentation (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (χ : radical n F.Carrier →* ℂˣ), IsOpen (χ.ker : Set (radical n F.Carrier)) →
      ∀ (S : Subrepresentation A.representation) (v : A) (hvS : v ∈ S.toSubmodule),
        v ∈ relations A.representation (radical n F.Carrier) χ →
          (⟨v, hvS⟩ : S.toSubmodule) ∈
            relations (SmoothRep.subrepresentation A S).representation
              (radical n F.Carrier) χ := by
  let := T.topology
  intro A χ hχ S v hvS hv
  cases n with
  | zero =>
    have h0 : relations A.representation (radical 0 F.Carrier) χ = ⊥ := by
      rw [eq_bot_iff, relations, Submodule.span_le]
      rintro _ ⟨⟨u, w⟩, rfl⟩
      rw [Subsingleton.elim u 1]
      simp
    rw [h0, Submodule.mem_bot] at hv
    subst hv
    exact Submodule.zero_mem _
  | succ m =>
    have := T.generalLinearTopologicalGroup (m + 1 + 1)
    refine (mk_eq_zero (SmoothRep.subrepresentation A S).representation _ χ _).mp ?_
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have hcover : ∀ n : radical (m + 1) F.Carrier, ∃ k : ℕ, n ∈ radicalBox T m k := by
      intro n
      obtain ⟨M, hM⟩ := exists_mem_latticeBox T (radicalCoordinates n)
      exact ⟨M.toNat, radicalBox_mono T m (Int.self_le_toNat M) hM⟩
    exact apply_eq_zero_of_mem_relations A.isSmooth hχ
      (fun k : ℕ => radicalBox T m k) (fun k => isCompact_radicalBox T m k)
      (fun j k hjk => radicalBox_mono T m (Nat.cast_le.mpr hjk)) hcover S.toSubmodule
      (fun n w hw => S.apply_mem_toSubmodule n hw)
      (f ∘ₗ mk (SmoothRep.subrepresentation A S).representation _ χ) (fun n w => by
        have h := congrArg f (mk_apply_subgroup
          (SmoothRep.subrepresentation A S).representation (radical (m + 1) F.Carrier) χ n w)
        rw [map_smul, smul_eq_mul] at h
        exact h) hvS hv

/-- The trivial character of the radical has open kernel. -/
theorem isOpen_ker_one (n : ℕ) :
    letI := T.topology
    IsOpen ((1 : radical n F.Carrier →* ℂˣ).ker : Set (radical n F.Carrier)) := by
  let := T.topology
  rw [MonoidHom.ker_one]
  exact isOpen_univ

/-! ## Averaging against the radical character -/

/-- Averaging a vector over a finite quotient of radical lattices against `θ_ψ⁻¹`
produces a vector with the same class whose Levi translates all have classes in a
successor-stable subspace containing the original class. The averaged vector stays in
every invariant subspace containing the original vector. Adapted from the proof of
`eq_bot_or_eq_top_of_radicalQuotient` (Worker 806). -/
theorem exists_levi_translates_mem (m : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (q : V →ₗ[ℂ] W) (σ : Submodule ℂ W)
    (hσ : ∀ (h : mirabolic m F.Carrier) (v : V), q v ∈ σ → q (ξ (successor h) v) ∈ σ)
    (S : Submodule ℂ V) (hS : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V), v ∈ S → ξ g v ∈ S) :
    letI := T.topology
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier, IsSmooth ξ →
      (∀ (c : Fin (m + 1) → F.Carrier) (v : V),
        q (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) =
          ψ.complex (c (Fin.last m)) • q v) →
      ∀ x ∈ S, q x ∈ σ → ∃ x'' ∈ S, q x'' = q x ∧
        ∀ g : Langlands.GeneralLinear (m + 1) F.Carrier, q (ξ (levi g) x'') ∈ σ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro ψ hs hrad x hxS hwσ
  by_cases hw0 : q x = 0
  · exact ⟨0, S.zero_mem, by rw [map_zero, hw0], fun g => by
      rw [map_zero, map_zero]
      exact σ.zero_mem⟩
  -- Conjugating a radical element past a Levi element.
  have hconj : ∀ (g : Langlands.GeneralLinear (m + 1) F.Carrier)
      (d : Fin (m + 1) → F.Carrier) (v : V),
      q (ξ (levi g) (ξ (radicalElement d : mirabolic (m + 1) F.Carrier) v)) =
        ψ.complex ((g.val *ᵥ d) (Fin.last m)) • q (ξ (levi g) v) := by
    intro g d v
    rw [← Module.End.mul_apply, ← map_mul, levi_mul_radicalElement, map_mul,
      Module.End.mul_apply, hrad]
  obtain ⟨K, hK⟩ := hs x
  have hfix : ∀ k ∈ K, ξ k x = x := fun k hk =>
    (Representation.mem_invariants _ x).mp hK ⟨k, hk⟩
  let J : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier) := K.toSubgroup.comap levi
  have hJopen : IsOpen (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    K.isOpen.preimage continuous_levi
  have hJfix : ∀ j ∈ J, ξ (levi j) x = x := fun j hj => hfix _ hj
  -- A lattice box of last rows coming from `J`.
  have hnhds : lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) ∈
      𝓝 (lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    lastRow_image_mem_nhds hJopen J.one_mem
  have hnhds0 : {d : Fin (m + 1) → F.Carrier |
      lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) + d ∈
        lastRow '' (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier))} ∈
      𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    have ht : Filter.Tendsto
        (fun d : Fin (m + 1) → F.Carrier =>
          lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) + d)
        (𝓝 0) (𝓝 (lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier))) := by
      exact (continuous_const.add continuous_id).tendsto'
        (0 : Fin (m + 1) → F.Carrier) _ (add_zero _)
    exact ht hnhds
  obtain ⟨n₀, hn₀⟩ := exists_latticeBox_subset T hnhds0
  -- A lattice box of radical coordinates fixing `x`.
  have hrad0 : {d : Fin (m + 1) → F.Carrier |
      (radicalElement d : mirabolic (m + 1) F.Carrier) ∈ K} ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (K.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact K.one_mem
  obtain ⟨l, hl⟩ := exists_latticeBox_subset T hrad0
  have hfixu : ∀ d ∈ latticeBox T (m + 1) l,
      ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x = x := fun d hd => hfix _ (hl hd)
  have hψl : ∀ d ∈ latticeBox T (m + 1) l, ψ.complex (d (Fin.last m)) = 1 := by
    intro d hd
    apply eq_one_of_smul_eq_self _ hw0
    rw [← hrad, hfixu d hd]
  -- The finite quotient of lattice boxes.
  let M : ℤ := max l (T.additiveConductor ψ - n₀)
  let B := latticeBox T (m + 1) M
  let L := (latticeBox T (m + 1) l).addSubgroupOf B
  have : Finite (B ⧸ L) := finite_latticeBox_quotient T (m + 1) M l
  let : Fintype (B ⧸ L) := Fintype.ofFinite _
  -- The averaged vector.
  let x' : V := ∑ c : B ⧸ L, ψ.complex (-((c.out : B) : Fin (m + 1) → F.Carrier) (Fin.last m)) •
    ξ (radicalElement ((c.out : B) : Fin (m + 1) → F.Carrier) : mirabolic (m + 1) F.Carrier) x
  -- The relevant additive character of radical coordinates.
  let χ : Langlands.GeneralLinear (m + 1) F.Carrier → AddChar B ℂ := fun g =>
    ψ.complex.compAddMonoidHom
      ((AddMonoidHom.mk' (fun d : Fin (m + 1) → F.Carrier =>
          (g.val *ᵥ d) (Fin.last m) - d (Fin.last m)) (by
            intro a b
            simp only [Matrix.mulVec_add, Pi.add_apply]
            ring)).comp B.subtype)
  have hχ : ∀ g (c : B), χ g c =
      ψ.complex ((g.val *ᵥ (c : Fin (m + 1) → F.Carrier)) (Fin.last m) -
        (c : Fin (m + 1) → F.Carrier) (Fin.last m)) := fun _ _ => rfl
  have hkey : ∀ g : Langlands.GeneralLinear (m + 1) F.Carrier,
      q (ξ (levi g) x') = (∑ c : B ⧸ L, χ g c.out) • q (ξ (levi g) x) := by
    intro g
    simp only [x', map_sum, map_smul, hconj, Finset.sum_smul, smul_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hχ, sub_eq_neg_add, AddChar.map_add_eq_mul, mul_comm]
  have hmem : ∀ g : Langlands.GeneralLinear (m + 1) F.Carrier, q (ξ (levi g) x') ∈ σ := by
    intro g
    rw [hkey g]
    by_cases hall : ∀ j, ∀ t ∈ T.additiveLattice M,
        ψ ((lastRow g j - lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) j) * t) = 1
    · -- The last row of `g` lies in the last-row image of `J`.
      have hbox : lastRow g - lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) ∈
          latticeBox T (m + 1) n₀ := by
        rw [mem_latticeBox]
        intro j
        have hj := T.mem_additiveLattice_of_forall_mul_eq_one ψ M _ (hall j)
        exact T.additiveLattice_mono (by omega) hj
      have himage := hn₀ hbox
      simp only [Set.mem_ofPred_eq, add_sub_cancel] at himage
      obtain ⟨a, j, rfl⟩ := (lastRow_mem_image_iff J g).mp himage
      refine σ.smul_mem _ ?_
      rw [map_mul, map_mul, Module.End.mul_apply, hJfix j.val j.property]
      exact hσ a x hwσ
    · push Not at hall
      obtain ⟨j₀, t, ht, hne⟩ := hall
      by_cases hy : q (ξ (levi g) x) = 0
      · rw [hy, smul_zero]
        exact σ.zero_mem
      · have hzero : ∑ c : B ⧸ L, χ g c.out = 0 := by
          refine sum_out_eq_zero L (χ g) ?_ (c₁ := ⟨Pi.single j₀ t, ?_⟩) ?_
          · intro c hc
            have hcl : (c : Fin (m + 1) → F.Carrier) ∈ latticeBox T (m + 1) l := hc
            rw [hχ, AddChar.map_sub_eq_div, hψl _ hcl, div_one]
            apply eq_one_of_smul_eq_self _ hy
            rw [← hconj, hfixu _ hcl]
          · rw [mem_latticeBox]
            intro j
            by_cases hj : j = j₀
            · subst hj
              simpa using ht
            · simp [hj]
          · rw [hχ]
            intro h
            apply hne
            have hval : (g.val *ᵥ Pi.single j₀ t) (Fin.last m) -
                (Pi.single j₀ t : Fin (m + 1) → F.Carrier) (Fin.last m) =
                (lastRow g j₀ -
                  lastRow (1 : Langlands.GeneralLinear (m + 1) F.Carrier) j₀) * t := by
              have hmv : (g.val *ᵥ Pi.single j₀ t) (Fin.last m) = g.val (Fin.last m) j₀ * t :=
                dotProduct_single _ _ _
              rw [hmv]
              simp only [lastRow, Units.val_one, Pi.single_apply, Matrix.one_apply]
              split_ifs <;> ring
            rw [hval] at h
            exact Circle.coe_eq_one.mp h
        rw [hzero, zero_smul]
        exact σ.zero_mem
  have hx'S : x' ∈ S := by
    refine S.sum_mem fun c _ => S.smul_mem _ (hS _ _ hxS)
  have hcard : (Fintype.card (B ⧸ L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx'1 : q x' = (Fintype.card (B ⧸ L) : ℂ) • q x := by
    have h1 := hkey 1
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply] at h1
    have hχ1 : ∀ c : B, χ 1 c = 1 := by
      intro c
      rw [hχ, Units.val_one, Matrix.one_mulVec, sub_self, AddChar.map_zero_eq_one]
    simp only [hχ1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1
    exact h1
  refine ⟨(Fintype.card (B ⧸ L) : ℂ)⁻¹ • x', S.smul_mem _ hx'S, ?_, fun g => ?_⟩
  · rw [map_smul, hx'1, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · rw [map_smul, map_smul]
    exact σ.smul_mem _ (hmem g)

/-! ## One `Φ⁻` step -/

section Step

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

/-- Every class of `Φ⁻` is the class of a multiple of one radical difference:
`[v] = (θ(u₀) - 1)⁻¹ [u₀ v - v]` for a fixed `u₀` with `θ(u₀) ≠ 1`. -/
theorem exists_radical_difference :
    letI := T.topology
    ∃ (c : ℂ) (u : radical (m + 1) F.Carrier),
      ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (v : B),
        phiMinusQuotient T ψ m B (c • (B.representation u v - v)) =
          phiMinusQuotient T ψ m B v := by
  let := T.topology
  obtain ⟨t, ht⟩ : ∃ t : F.Carrier, ψ t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact ψ.nontrivial (DFunLike.ext _ _ fun t => by rw [AddChar.one_apply]; exact hcon t)
  let u₀ : radical (m + 1) F.Carrier := radicalElement (Pi.single (Fin.last m) t)
  have hθ₀ : (T.mirabolicTheta ψ m u₀ : ℂ) = ψ.complex t := by
    have h := theta_radicalElement ψ m (Pi.single (Fin.last m) t)
    rw [Pi.single_eq_same] at h
    exact h
  have hne : (T.mirabolicTheta ψ m u₀ : ℂ) - 1 ≠ 0 := by
    rw [hθ₀, sub_ne_zero, UnitaryAdditiveCharacter.complex_apply]
    exact fun h => ht (Circle.coe_eq_one.mp h)
  refine ⟨((T.mirabolicTheta ψ m u₀ : ℂ) - 1)⁻¹, u₀, fun B v => ?_⟩
  rw [map_smul, map_sub, phiMinusQuotient_radical,
    show (T.mirabolicTheta ψ m u₀ : ℂ) • phiMinusQuotient T ψ m B v -
        phiMinusQuotient T ψ m B v =
      ((T.mirabolicTheta ψ m u₀ : ℂ) - 1) • phiMinusQuotient T ψ m B v by
      rw [sub_smul, one_smul],
    smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The lift of an invariant subspace `X` of `Φ⁻ B`: the radical relations of `B`
all of whose translates have classes in `X`. -/
def liftStep :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      Subrepresentation ((phiMinus T ψ m).obj B).representation →
        Subrepresentation B.representation := by
  letI := T.topology
  exact fun B X =>
    { toSubmodule :=
        { carrier := {v | v ∈ relations B.representation (radical (m + 1) F.Carrier) 1 ∧
            ∀ g : mirabolic (m + 1) F.Carrier,
              phiMinusQuotient T ψ m B (B.representation g v) ∈ X.toSubmodule}
          add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
            rw [map_add, map_add]
            exact X.toSubmodule.add_mem (ha.2 g) (hb.2 g)⟩
          zero_mem' := ⟨Submodule.zero_mem _, fun g => by
            rw [map_zero, map_zero]
            exact X.toSubmodule.zero_mem⟩
          smul_mem' := fun c v hv => ⟨Submodule.smul_mem _ c hv.1, fun g => by
            rw [map_smul, map_smul]
            exact X.toSubmodule.smul_mem c (hv.2 g)⟩ }
      apply_mem_toSubmodule := fun g v hv =>
        ⟨radicalRelations_stable B.representation g hv.1, fun g' => by
          rw [← Module.End.mul_apply, ← map_mul]
          exact hv.2 (g' * g)⟩ }

theorem mem_liftStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (X : Subrepresentation ((phiMinus T ψ m).obj B).representation) (v : B),
      v ∈ liftStep T ψ m B X ↔
        v ∈ relations B.representation (radical (m + 1) F.Carrier) 1 ∧
          ∀ g : mirabolic (m + 1) F.Carrier,
            phiMinusQuotient T ψ m B (B.representation g v) ∈ X :=
  fun _ _ _ => Iff.rfl

/-- The image of an invariant subspace of `B` in `Φ⁻ B`. -/
def imageStep :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      Subrepresentation B.representation →
        Subrepresentation ((phiMinus T ψ m).obj B).representation := by
  letI := T.topology
  exact fun B W =>
    { toSubmodule :=
        { carrier := {x | ∃ v ∈ W, phiMinusQuotient T ψ m B v = x}
          add_mem' := by
            rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
            exact ⟨a + b, W.toSubmodule.add_mem ha hb, map_add _ _ _⟩
          zero_mem' := ⟨0, W.toSubmodule.zero_mem, map_zero _⟩
          smul_mem' := by
            rintro c _ ⟨a, ha, rfl⟩
            exact ⟨c • a, W.toSubmodule.smul_mem c ha, map_smul _ _ _⟩ }
      apply_mem_toSubmodule := by
        rintro h _ ⟨v, hv, rfl⟩
        exact ⟨(realPowerCharacter ((T.determinantNorm (m + 1)).comp
            (mirabolic m F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ) •
              B.representation (successor h) v,
          W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule _ hv), by
            rw [map_smul]
            exact (phiMinus_action T ψ m B h v).symm⟩ }

theorem mem_imageStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (W : Subrepresentation B.representation) (x : (phiMinus T ψ m).obj B),
      x ∈ imageStep T ψ m B W ↔ ∃ v ∈ W, phiMinusQuotient T ψ m B v = x :=
  fun _ _ _ => Iff.rfl

/-- Invariant subspaces of `Φ⁻ B` are stable under successor translates of
representatives. -/
theorem successor_mem :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (X : Subrepresentation ((phiMinus T ψ m).obj B).representation)
      (h : mirabolic m F.Carrier) (v : B), phiMinusQuotient T ψ m B v ∈ X →
        phiMinusQuotient T ψ m B (B.representation (successor h) v) ∈ X := by
  let := T.topology
  intro B X h v hv
  have h2 : phiMinusQuotient T ψ m B (B.representation (successor h) v) =
      (realPowerCharacter ((T.determinantNorm (m + 1)).comp
          (mirabolic m F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ)⁻¹ •
        ((phiMinus T ψ m).obj B).representation h (phiMinusQuotient T ψ m B v) := by
    rw [phiMinus_action]
    exact (inv_smul_smul₀ (Units.ne_zero _) _).symm
  rw [h2]
  exact X.toSubmodule.smul_mem _ (X.apply_mem_toSubmodule h hv)

/-- A vector of an invariant subspace `S` whose class lies in `X` has the same class as
a vector of `S` in the lift of `X`. -/
theorem exists_mem_liftStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (X : Subrepresentation ((phiMinus T ψ m).obj B).representation)
      (S : Subrepresentation B.representation) (b : B), b ∈ S →
        phiMinusQuotient T ψ m B b ∈ X →
          ∃ s ∈ liftStep T ψ m B X, s ∈ S ∧
            phiMinusQuotient T ψ m B s = phiMinusQuotient T ψ m B b := by
  let := T.topology
  intro B X S b hbS hbX
  set q := phiMinusQuotient T ψ m B with hq
  have hrad : ∀ (c : Fin (m + 1) → F.Carrier) (v : B),
      q (B.representation (radicalElement c : mirabolic (m + 1) F.Carrier) v) =
        ψ.complex (c (Fin.last m)) • q v := by
    intro c v
    rw [hq, phiMinusQuotient_radical T ψ m B (radicalElement c) v]
    congr 1
    exact theta_radicalElement ψ m c
  obtain ⟨x, hxS, hxq, hlevi⟩ := exists_levi_translates_mem T m B.representation q
    X.toSubmodule (fun h v hv => successor_mem T ψ m B X h v hv)
    S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) ψ B.isSmooth hrad b hbS hbX
  have hall : ∀ g : mirabolic (m + 1) F.Carrier, q (B.representation g x) ∈ X := by
    intro g
    rw [eq_radicalElement_mul_levi g, map_mul, Module.End.mul_apply, hrad]
    exact X.toSubmodule.smul_mem _ (hlevi _)
  obtain ⟨c, u, hcu⟩ := exists_radical_difference T ψ m
  refine ⟨c • (B.representation u x - x), ⟨?_, fun g => ?_⟩, ?_, ?_⟩
  · refine Submodule.smul_mem _ c ?_
    simpa using sub_mem_relations B.representation (radical (m + 1) F.Carrier) 1 u x
  · rw [map_smul, map_sub, ← Module.End.mul_apply, ← map_mul, map_smul, map_sub]
    exact X.toSubmodule.smul_mem c (X.toSubmodule.sub_mem (hall _) (hall g))
  · exact S.toSubmodule.smul_mem c (S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ hxS) hxS)
  · rw [hq, hcu B x, ← hq, hxq]

/-- Taking images undoes the lift. -/
theorem imageStep_liftStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (X : Subrepresentation ((phiMinus T ψ m).obj B).representation),
      imageStep T ψ m B (liftStep T ψ m B X) = X := by
  let := T.topology
  intro B X
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have h := hv.2 1
    rwa [map_one, Module.End.one_apply] at h
  · intro x hx
    obtain ⟨b, rfl⟩ := phiMinusQuotient_surjective T ψ m B x
    obtain ⟨s, hs, -, hsb⟩ := exists_mem_liftStep T ψ m B X ⊤ b trivial hx
    exact ⟨s, hs, hsb⟩

theorem le_liftStep_imageStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (W : Subrepresentation B.representation),
      W.toSubmodule ≤ relations B.representation (radical (m + 1) F.Carrier) 1 →
        W ≤ liftStep T ψ m B (imageStep T ψ m B W) := by
  let := T.topology
  intro B W hW v hv
  exact ⟨hW hv, fun g => ⟨B.representation g v, W.apply_mem_toSubmodule g hv, rfl⟩⟩

/-- Lifting undoes taking images on invariant subspaces of the radical relations: the
quotient of the lift by the subspace has vanishing `Ψ⁻` and `Φ⁻`. -/
theorem liftStep_imageStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (W : Subrepresentation B.representation),
      W.toSubmodule ≤ relations B.representation (radical (m + 1) F.Carrier) 1 →
        liftStep T ψ m B (imageStep T ψ m B W) = W := by
  let := T.topology
  intro B W hW
  have hWL := le_liftStep_imageStep T ψ m B W hW
  refine le_antisymm ?_ hWL
  let L := liftStep T ψ m B (imageStep T ψ m B W)
  let D := SmoothRep.subrepresentation B L
  let W' : Subrepresentation D.representation :=
    { toSubmodule := W.toSubmodule.comap L.toSubmodule.subtype
      apply_mem_toSubmodule := fun g v hv => W.apply_mem_toSubmodule g hv }
  let Z := SmoothRep.quotient D W'
  have hZ : Subsingleton Z := by
    refine subsingleton_of_psiMinus_phiMinus T ψ m Z ?_ ?_
    · refine subsingleton_of_forall_eq 0 fun z => ?_
      obtain ⟨z, rfl⟩ := psiMinusQuotient_surjective T (m + 1) Z z
      obtain ⟨y, rfl⟩ := SmoothRep.mkQ_surjective D W' z
      have hy := mem_relations_subrepresentation T (m + 1) B 1 (isOpen_ker_one T (m + 1)) L
        y.1 y.2 ((mem_liftStep T ψ m B _ y.1).mp y.2).1
      have h0 : psiMinusQuotient T (m + 1) D y = 0 := by
        rw [← LinearMap.mem_ker, ker_psiMinusQuotient]
        exact hy
      have h3 := psiMinus_map_quotient T (m + 1) (SmoothRep.mkQ D W') y
      have h4 : SmoothRep.hom ((psiMinus T (m + 1)).map (SmoothRep.mkQ D W'))
          (psiMinusQuotient T (m + 1) D y) = 0 := by
        rw [h0]
        exact map_zero _
      exact h3.symm.trans h4
    · refine subsingleton_of_forall_eq 0 fun z => ?_
      obtain ⟨z, rfl⟩ := phiMinusQuotient_surjective T ψ m Z z
      obtain ⟨y, rfl⟩ := SmoothRep.mkQ_surjective D W' z
      obtain ⟨w, hw, hwq⟩ : ∃ w ∈ W, phiMinusQuotient T ψ m B w =
          phiMinusQuotient T ψ m B y.1 := by
        have h := ((mem_liftStep T ψ m B _ y.1).mp y.2).2 1
        rw [map_one, Module.End.one_apply] at h
        exact h
      have hwL : w ∈ L.toSubmodule := hWL hw
      have hdiff : y.1 - w ∈
          relations B.representation (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) := by
        rw [← ker_phiMinusQuotient, LinearMap.mem_ker, map_sub, hwq, sub_self]
      have hrel := mem_relations_subrepresentation T (m + 1) B (T.mirabolicTheta ψ m)
        (T.mirabolicTheta_isOpen_ker ψ m) L (y.1 - w) (L.toSubmodule.sub_mem y.2 hwL) hdiff
      let w' : D := (⟨w, hwL⟩ : L.toSubmodule)
      have hq0 : phiMinusQuotient T ψ m D (y - w') = 0 := by
        rw [← LinearMap.mem_ker, ker_phiMinusQuotient]
        exact hrel
      have hqe : phiMinusQuotient T ψ m D y = phiMinusQuotient T ψ m D w' :=
        sub_eq_zero.mp ((map_sub (phiMinusQuotient T ψ m D) y w').symm.trans hq0)
      have hw0 : SmoothRep.hom (SmoothRep.mkQ D W') w' = 0 :=
        (Submodule.Quotient.mk_eq_zero W'.toSubmodule).mpr hw
      have h3 := phiMinus_map_quotient T ψ m (SmoothRep.mkQ D W') y
      have h4 := phiMinus_map_quotient T ψ m (SmoothRep.mkQ D W') w'
      rw [hqe, h4, hw0] at h3
      rw [← h3]
      exact map_zero _
  intro l hl
  let l' : D := (⟨l, hl⟩ : L.toSubmodule)
  have h0 : SmoothRep.hom (SmoothRep.mkQ D W') l' = 0 := Subsingleton.elim _ _
  have h1 : l' ∈ W'.toSubmodule := (Submodule.Quotient.mk_eq_zero W'.toSubmodule).mp h0
  exact h1

end Step


/-! ## The lattice below a lift -/

section Lattice

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

theorem ne_bot_iff_exists {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (U : Subrepresentation ρ) :
    U ≠ ⊥ ↔ ∃ v ∈ U, v ≠ 0 := by
  constructor
  · intro hU
    by_contra h
    push Not at h
    apply hU
    apply Subrepresentation.toSubmodule_injective
    exact eq_bot_iff.mpr fun v hv => (Submodule.mem_bot ℂ).mpr (h v hv)
  · rintro ⟨v, hv, hv0⟩ rfl
    exact hv0 ((Submodule.mem_bot ℂ).mp (show v ∈ (⊥ : Submodule ℂ V) from hv))

theorem liftStep_mono :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {X Y : Subrepresentation ((phiMinus T ψ m).obj B).representation}, X ≤ Y →
        liftStep T ψ m B X ≤ liftStep T ψ m B Y := by
  let := T.topology
  intro B X Y h v hv
  exact ⟨hv.1, fun g => h (hv.2 g)⟩

theorem imageStep_mono :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {W W' : Subrepresentation B.representation}, W ≤ W' →
        imageStep T ψ m B W ≤ imageStep T ψ m B W' := by
  let := T.topology
  rintro B W W' h _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

theorem imageStep_bot :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier),
      imageStep T ψ m B ⊥ = ⊥ := by
  let := T.topology
  intro B
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [(Submodule.mem_bot ℂ).mp (show v ∈ (⊥ : Submodule ℂ B) from hv), map_zero]
  exact Submodule.zero_mem _

/-- The lift identifies the invariant subspaces below it with those below `X`. -/
def stepIso :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      (X : Subrepresentation ((phiMinus T ψ m).obj B).representation) →
        Set.Iic (liftStep T ψ m B X) ≃o Set.Iic X := by
  letI := T.topology
  exact fun B X =>
    { toFun := fun W => ⟨imageStep T ψ m B W.1,
        (imageStep_mono T ψ m B W.2).trans (imageStep_liftStep T ψ m B X).le⟩
      invFun := fun Y => ⟨liftStep T ψ m B Y.1, liftStep_mono T ψ m B Y.2⟩
      left_inv := fun W => Subtype.ext
        (liftStep_imageStep T ψ m B W.1 fun v hv => (W.2 hv).1)
      right_inv := fun Y => Subtype.ext (imageStep_liftStep T ψ m B Y.1)
      map_rel_iff' := by
        intro W W'
        change imageStep T ψ m B W.1 ≤ imageStep T ψ m B W'.1 ↔ W.1 ≤ W'.1
        constructor
        · intro h
          have h1 := liftStep_imageStep T ψ m B W.1 fun v hv => (W.2 hv).1
          have h2 := liftStep_imageStep T ψ m B W'.1 fun v hv => (W'.2 hv).1
          exact h1.symm.le.trans ((liftStep_mono T ψ m B h).trans h2.le)
        · exact fun h => imageStep_mono T ψ m B h }

/-- A lift meets an invariant subspace `S` exactly when `X` meets the image of `S`. -/
theorem inf_imageStep_ne_bot_iff :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (X : Subrepresentation ((phiMinus T ψ m).obj B).representation)
      (S : Subrepresentation B.representation),
      X ⊓ imageStep T ψ m B S ≠ ⊥ ↔ liftStep T ψ m B X ⊓ S ≠ ⊥ := by
  let := T.topology
  intro B X S
  constructor
  · rw [ne_bot_iff_exists, ne_bot_iff_exists]
    rintro ⟨_, ⟨hxX, ⟨b, hbS, rfl⟩⟩, hx0⟩
    obtain ⟨s, hs, hsS, hsq⟩ := exists_mem_liftStep T ψ m B X S b hbS hxX
    refine ⟨s, ⟨hs, hsS⟩, fun h0 => hx0 (hsq.symm.trans ?_)⟩
    rw [h0]
    exact map_zero _
  · intro h hbot
    apply h
    have hWR : (liftStep T ψ m B X ⊓ S).toSubmodule ≤
        relations B.representation (radical (m + 1) F.Carrier) 1 := fun v hv => hv.1.1
    have himg : imageStep T ψ m B (liftStep T ψ m B X ⊓ S) = ⊥ := by
      refine eq_bot_iff.mpr ((le_inf ?_ (imageStep_mono T ψ m B inf_le_right)).trans hbot.le)
      exact (imageStep_mono T ψ m B inf_le_left).trans (imageStep_liftStep T ψ m B X).le
    have h1 := liftStep_imageStep T ψ m B _ hWR
    rw [himg, ← imageStep_bot T ψ m B, liftStep_imageStep T ψ m B ⊥ bot_le] at h1
    exact h1.symm

end Lattice

/-! ## Left exactness for invariant subspaces -/

section Exact

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

theorem phiMinus_map_subtype_injective :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (S : Subrepresentation B.representation),
      Function.Injective (SmoothRep.hom ((phiMinus T ψ m).map (SmoothRep.subtype B S))) := by
  let := T.topology
  intro B S x y hxy
  obtain ⟨s, rfl⟩ := phiMinusQuotient_surjective T ψ m (SmoothRep.subrepresentation B S) x
  obtain ⟨t, rfl⟩ := phiMinusQuotient_surjective T ψ m (SmoothRep.subrepresentation B S) y
  rw [phiMinus_map_quotient, phiMinus_map_quotient] at hxy
  have h1 := (mk_eq_iff _ _ _ _ _).mp hxy
  have h2 := mem_relations_subrepresentation T (m + 1) B (T.mirabolicTheta ψ m)
    (T.mirabolicTheta_isOpen_ker ψ m) S (s.1 - t.1) (S.toSubmodule.sub_mem s.2 t.2) h1
  exact (mk_eq_iff _ _ _ _ _).mpr h2

theorem psiMinus_map_subtype_injective (n : ℕ) :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (S : Subrepresentation B.representation),
      Function.Injective (SmoothRep.hom ((psiMinus T n).map (SmoothRep.subtype B S))) := by
  let := T.topology
  intro B S x y hxy
  obtain ⟨s, rfl⟩ := psiMinusQuotient_surjective T n (SmoothRep.subrepresentation B S) x
  obtain ⟨t, rfl⟩ := psiMinusQuotient_surjective T n (SmoothRep.subrepresentation B S) y
  rw [psiMinus_map_quotient, psiMinus_map_quotient] at hxy
  have h1 := (mk_eq_iff _ _ _ _ _).mp hxy
  have h2 := mem_relations_subrepresentation T n B 1 (isOpen_ker_one T n) S (s.1 - t.1)
    (S.toSubmodule.sub_mem s.2 t.2) h1
  exact (mk_eq_iff _ _ _ _ _).mpr h2

theorem range_phiMinus_map_subtype :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (S : Subrepresentation B.representation),
      (SmoothRep.hom ((phiMinus T ψ m).map (SmoothRep.subtype B S))).range =
        imageStep T ψ m B S := by
  let := T.topology
  intro B S
  apply SetLike.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := phiMinusQuotient_surjective T ψ m (SmoothRep.subrepresentation B S) y
    exact ⟨s.1, s.2, (phiMinus_map_quotient T ψ m (SmoothRep.subtype B S) s).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨phiMinusQuotient T ψ m (SmoothRep.subrepresentation B S) (⟨v, hv⟩ : S.toSubmodule),
      phiMinus_map_quotient T ψ m (SmoothRep.subtype B S) (⟨v, hv⟩ : S.toSubmodule)⟩

/-- `Φ⁻` of an invariant subspace is the image of the subspace in `Φ⁻ B`. -/
def phiMinusSubIso :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      (S : Subrepresentation B.representation) →
        ((phiMinus T ψ m).obj (SmoothRep.subrepresentation B S) ≅
          SmoothRep.subrepresentation ((phiMinus T ψ m).obj B) (imageStep T ψ m B S)) := by
  letI := T.topology
  exact fun B S => (LevelCalculus.isoRange _ (phiMinus_map_subtype_injective T ψ m B S)).trans
    (eqToIso (congrArg (SmoothRep.subrepresentation ((phiMinus T ψ m).obj B))
      (range_phiMinus_map_subtype T ψ m B S)))

end Exact

/-! ## `Ψ⁻` when the radical acts trivially -/

section Base

theorem nontrivial_iff_of_bijective {α β : Type*} (f : α → β) (hi : Function.Injective f)
    (hs : Function.Surjective f) : Nontrivial α ↔ Nontrivial β :=
  ⟨fun _ => hi.nontrivial, fun _ => hs.nontrivial⟩

theorem nontrivial_subrepresentation_iff {G : Type*} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, _, uV} ℂ G) (S : Subrepresentation A.representation) :
    Nontrivial (SmoothRep.subrepresentation A S) ↔ S ≠ ⊥ := by
  constructor
  · intro hn hS
    obtain ⟨x, y, hxy⟩ := hn.exists_pair_ne
    apply hxy
    subst hS
    have hx : x.1 = 0 := (Submodule.mem_bot ℂ).mp x.2
    have hy : y.1 = 0 := (Submodule.mem_bot ℂ).mp y.2
    exact Subtype.ext (hx.trans hy.symm)
  · exact LevelCalculus.subrepresentation_nontrivial S

theorem psiMinusQuotient_injective (n : ℕ) :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (∀ (u : radical n F.Carrier) (v : B), B.representation (u : mirabolic n F.Carrier) v = v) →
        Function.Injective (psiMinusQuotient T n B) := by
  let := T.topology
  intro B h
  rw [← LinearMap.ker_eq_bot, ker_psiMinusQuotient]
  exact relations_one_eq_bot B.representation h

theorem radical_trivial_subrepresentation (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)),
      (∀ (u : radical n F.Carrier) (v : A), A.representation (u : mirabolic n F.Carrier) v = v) →
      ∀ (S : Subrepresentation A.representation) (u : radical n F.Carrier)
        (v : SmoothRep.subrepresentation A S),
        (SmoothRep.subrepresentation A S).representation (u : mirabolic n F.Carrier) v = v := by
  let := T.topology
  intro A h S u v
  exact Subtype.ext (h u v.1)

/-- The image of an invariant subspace in `Ψ⁻ B`. -/
def psiImage (n : ℕ) :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      Subrepresentation B.representation →
        Subrepresentation ((psiMinus T n).obj B).representation := by
  letI := T.topology
  exact fun B W =>
    { toSubmodule :=
        { carrier := {x | ∃ v ∈ W, psiMinusQuotient T n B v = x}
          add_mem' := by
            rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
            exact ⟨a + b, W.toSubmodule.add_mem ha hb, map_add _ _ _⟩
          zero_mem' := ⟨0, W.toSubmodule.zero_mem, map_zero _⟩
          smul_mem' := by
            rintro c _ ⟨a, ha, rfl⟩
            exact ⟨c • a, W.toSubmodule.smul_mem c ha, map_smul _ _ _⟩ }
      apply_mem_toSubmodule := by
        rintro g _ ⟨v, hv, rfl⟩
        exact ⟨(realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
            B.representation (levi g) v,
          W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule _ hv), by
            rw [map_smul]
            exact (psiMinus_action T n B g v).symm⟩ }

/-- The preimage of an invariant subspace of `Ψ⁻ B`, when the radical acts trivially. -/
def psiPreimage (n : ℕ) :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (∀ (u : radical n F.Carrier) (v : B), B.representation (u : mirabolic n F.Carrier) v = v) →
      Subrepresentation ((psiMinus T n).obj B).representation →
        Subrepresentation B.representation := by
  letI := T.topology
  exact fun B h X =>
    { toSubmodule :=
        { carrier := {v | psiMinusQuotient T n B v ∈ X}
          add_mem' := fun {a b} ha hb => by
            change psiMinusQuotient T n B (a + b) ∈ X
            rw [map_add]
            exact X.toSubmodule.add_mem ha hb
          zero_mem' := by
            change psiMinusQuotient T n B 0 ∈ X
            rw [map_zero]
            exact X.toSubmodule.zero_mem
          smul_mem' := fun c v hv => by
            change psiMinusQuotient T n B (c • v) ∈ X
            rw [map_smul]
            exact X.toSubmodule.smul_mem c hv }
      apply_mem_toSubmodule := fun g v hv => by
        change psiMinusQuotient T n B (B.representation g v) ∈ X
        rw [eq_radicalElement_mul_levi g, map_mul, Module.End.mul_apply, h]
        have h2 : psiMinusQuotient T n B (B.representation (levi (projection g)) v) =
            (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) (projection g) : ℂ)⁻¹ •
              ((psiMinus T n).obj B).representation (projection g)
                (psiMinusQuotient T n B v) := by
          rw [psiMinus_action]
          exact (inv_smul_smul₀ (Units.ne_zero _) _).symm
        rw [h2]
        exact X.toSubmodule.smul_mem _ (X.apply_mem_toSubmodule _ hv) }

/-- When the radical acts trivially, `Ψ⁻` identifies invariant subspaces. -/
def psiIso (n : ℕ) :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (∀ (u : radical n F.Carrier) (v : B), B.representation (u : mirabolic n F.Carrier) v = v) →
        Subrepresentation B.representation ≃o
          Subrepresentation ((psiMinus T n).obj B).representation := by
  letI := T.topology
  exact fun B h =>
    { toFun := psiImage T n B
      invFun := psiPreimage T n B h
      left_inv := fun W => by
        apply SetLike.ext
        intro v
        constructor
        · rintro ⟨v', hv', hq⟩
          rw [← psiMinusQuotient_injective T n B h hq]
          exact hv'
        · intro hv
          exact ⟨v, hv, rfl⟩
      right_inv := fun X => by
        apply SetLike.ext
        intro x
        obtain ⟨v, rfl⟩ := psiMinusQuotient_surjective T n B x
        constructor
        · rintro ⟨v', hv', hq⟩
          change psiMinusQuotient T n B v ∈ X
          rw [← hq]
          exact hv'
        · intro hx
          exact ⟨v, hx, rfl⟩
      map_rel_iff' := by
        intro W W'
        change psiImage T n B W ≤ psiImage T n B W' ↔ W ≤ W'
        constructor
        · intro hle v hv
          obtain ⟨v', hv', hq⟩ := hle ⟨v, hv, rfl⟩
          rw [← psiMinusQuotient_injective T n B h hq]
          exact hv'
        · rintro hle _ ⟨v, hv, rfl⟩
          exact ⟨v, hle hv, rfl⟩ }

end Base

/-! ## Levels of invariant subspaces -/

section Levels

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem radical_trivial_of_level_le_one (N : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier), level T ψ A ≤ 1 →
      ∀ (u : radical N F.Carrier) (v : A), A.representation (u : mirabolic N F.Carrier) v = v := by
  let := T.topology
  intro A hA
  cases N with
  | zero => exact radical_acts_trivially_zero T A
  | succ M =>
    apply radical_acts_trivially_of_phiMinus T ψ M A
    rw [← not_nontrivial_iff_subsingleton, LevelCalculus.nontrivial_phiMinus_iff T ψ A]
    omega

theorem hasNonzeroDerivative_one_of_subrepresentation (N : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (S : Subrepresentation A.representation),
      HasNonzeroDerivative T ψ (SmoothRep.subrepresentation A S) 1 →
        HasNonzeroDerivative T ψ A 1 := by
  let := T.topology
  rintro A S ⟨hk, hS⟩
  refine ⟨hk, ?_⟩
  rw [mirabolicDerivativeOfOrder_one] at hS ⊢
  exact (psiMinus_map_subtype_injective T N A S).nontrivial

/-- A nonzero derivative of an invariant subspace is a nonzero derivative of the
ambient representation, by left exactness of `Φ⁻` and `Ψ⁻` on invariant subspaces. -/
theorem hasNonzeroDerivative_of_subrepresentation (N : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (S : Subrepresentation A.representation) (k : ℕ),
      HasNonzeroDerivative T ψ (SmoothRep.subrepresentation A S) k →
        HasNonzeroDerivative T ψ A k := by
  let := T.topology
  induction N with
  | zero =>
    intro A S k hS
    obtain ⟨⟨hk1, hk2⟩, -⟩ := id hS
    obtain rfl : k = 1 := by omega
    exact hasNonzeroDerivative_one_of_subrepresentation T ψ 0 A S hS
  | succ M ih =>
    intro A S k hS
    obtain ⟨⟨hk1, hk2⟩, -⟩ := id hS
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      exact hasNonzeroDerivative_one_of_subrepresentation T ψ (M + 1) A S hS
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 + 1 := ⟨k - 2, by omega⟩
      rw [LevelCalculus.hasNonzeroDerivative_succ_iff T ψ A (k := i + 1) (by omega)]
      rw [LevelCalculus.hasNonzeroDerivative_succ_iff T ψ (SmoothRep.subrepresentation A S)
          (k := i + 1) (by omega),
        LevelCalculus.hasNonzeroDerivative_iff_of_iso T ψ (phiMinusSubIso T ψ M A S)] at hS
      exact ih _ _ _ hS

theorem level_subrepresentation_le {N : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (S : Subrepresentation A.representation),
      level T ψ (SmoothRep.subrepresentation A S) ≤ level T ψ A := by
  intro A S
  exact LevelCalculus.level_le_of_imp T ψ _ _ (hasNonzeroDerivative_of_subrepresentation T ψ N A S)

end Levels

/-! ## Determinant normalization and the Haar modulus of the radical -/

section Normalization

open MeasureTheory
open scoped NNReal ENNReal

/-- In column coordinates of the radical of `P_(n+1)`, the inverse of conjugation by
the Levi element of `g` is `X ↦ g⁻¹ X`. -/
theorem levi_inv_conj_column {n : ℕ} (g : Langlands.GeneralLinear n F.Carrier)
    (X : Matrix (Fin n) (Fin 1) F.Carrier) :
    (levi g)⁻¹ * (radicalElement (fun i => X i 0)).val * levi g =
      (radicalElement (fun i =>
        (((g⁻¹ : Langlands.GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) *
          X) i 0)).val := by
  have h := levi_conjugate_radicalElement g⁻¹ (fun i => X i 0)
  rw [map_inv, inv_inv] at h
  exact h

/-- Pushing any additive Haar measure on radical column coordinates forward along
`X ↦ g⁻¹ X` multiplies it by the residue-normalized `|det g|`: the Haar modulus of
conjugation by `g` on the radical is `|det g|`. -/
theorem map_inv_mul_haar (n : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin n) (Fin 1) F.Carrier)]
      [BorelSpace (Matrix (Fin n) (Fin 1) F.Carrier)]
      (μ : Measure (Matrix (Fin n) (Fin 1) F.Carrier)) [μ.IsAddHaarMeasure]
      (g : Langlands.GeneralLinear n F.Carrier),
      μ.map (fun X =>
          ((g⁻¹ : Langlands.GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) * X) =
        (T.determinantNorm n g : ℝ≥0) • μ := by
  let := T.topology
  intro _ _ μ _ g
  have h := HarmonicAnalysis.padicRectangularHaarScaling F T n 1 μ g⁻¹ 1
  simpa only [inv_one, Units.val_one, Matrix.mul_one, map_inv, map_one, Units.val_inv_eq_inv_val,
    one_pow, div_one, pow_one, inv_inv] using h

/-- The Haar modulus is determined by its defining identity: a scalar `c` satisfies
`μ.map (X ↦ g⁻¹ X) = c • μ` exactly when `c = |det g|`. -/
theorem map_inv_mul_haar_iff (n : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin n) (Fin 1) F.Carrier)]
      [BorelSpace (Matrix (Fin n) (Fin 1) F.Carrier)]
      (μ : Measure (Matrix (Fin n) (Fin 1) F.Carrier)) [μ.IsAddHaarMeasure]
      (g : Langlands.GeneralLinear n F.Carrier) (c : ℝ≥0),
      μ.map (fun X =>
          ((g⁻¹ : Langlands.GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) * X) =
        c • μ ↔ c = (T.determinantNorm n g : ℝ≥0) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have : LocallyCompactSpace (Matrix (Fin n) (Fin 1) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin 1 → F.Carrier))
  intro _ _ μ _ g c
  rw [map_inv_mul_haar T n μ g]
  constructor
  · intro h
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : Matrix (Fin n) (Fin 1) F.Carrier)
    have hpos : μ K ≠ 0 := (μ.measure_pos_of_mem_nhds hKn).ne'
    have htop : μ K ≠ ∞ := hK.measure_lt_top.ne
    have hK' := congrArg (fun ν : Measure (Matrix (Fin n) (Fin 1) F.Carrier) => ν K) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hK'
    exact (ENNReal.coe_inj.mp ((ENNReal.mul_left_inj hpos htop).mp hK')).symm
  · rintro rfl
    rfl

/-- The `Ψ⁻` normalization `|det|^(-1/2)` is the source normalization `mod_V^(-1/2)` by
the Haar modulus of conjugation on the radical. -/
theorem psiMinusCharacter_eq_modulus (n : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin n) (Fin 1) F.Carrier)]
      [BorelSpace (Matrix (Fin n) (Fin 1) F.Carrier)]
      (μ : Measure (Matrix (Fin n) (Fin 1) F.Carrier)) [μ.IsAddHaarMeasure]
      (g : Langlands.GeneralLinear n F.Carrier) (c : ℝ≥0),
      μ.map (fun X =>
          ((g⁻¹ : Langlands.GeneralLinear n F.Carrier) : Matrix (Fin n) (Fin n) F.Carrier) * X) =
        c • μ →
        (psiMinusCharacter T n g : ℂ) = (((c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  let := T.topology
  intro _ _ μ _ g c hc
  rw [(map_inv_mul_haar_iff T n μ g c).mp hc]
  rfl

/-- The `Φ⁻` normalization `|det|^(-1/2)` on `P_(n+1)` is `mod_V^(-1/2)` for the Haar
modulus of conjugation by the successor embedding on the radical of `P_(n+2)`. -/
theorem phiMinusCharacter_eq_modulus (n : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin (n + 1)) (Fin 1) F.Carrier)]
      [BorelSpace (Matrix (Fin (n + 1)) (Fin 1) F.Carrier)]
      (μ : Measure (Matrix (Fin (n + 1)) (Fin 1) F.Carrier)) [μ.IsAddHaarMeasure]
      (h : mirabolic n F.Carrier) (c : ℝ≥0),
      μ.map (fun X =>
          (((h : Langlands.GeneralLinear (n + 1) F.Carrier)⁻¹ :
            Langlands.GeneralLinear (n + 1) F.Carrier) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) * X) = c • μ →
        (phiMinusCharacter T n h : ℂ) = (((c : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  let := T.topology
  intro _ _ μ _ h c hc
  rw [(map_inv_mul_haar_iff T (n + 1) μ (h : Langlands.GeneralLinear (n + 1) F.Carrier) c).mp hc]
  rfl

end Normalization

end Langlands.Derivative.Mirabolic.HighestLayer
