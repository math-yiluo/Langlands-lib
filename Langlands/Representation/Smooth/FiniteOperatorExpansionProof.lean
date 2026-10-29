import Langlands.Representation.Smooth.FiniteOperatorExpansionStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.Uniformizer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Proof of the finite operator expansion of a smooth representation of `Fˣ`

Finitely many vectors separate a finite-dimensional space of operators, so the
intersection of their open stabilizers acts trivially and `b ↦ σ b` is locally
constant. Left multiplication by `σ (ϖ ^ n)` is an injective endomorphism of the
finite-dimensional bounded span, hence surjective, which puts every `σ b` in the
bounded span. The expansion uses the coordinates of a basis of the operator span.
-/

noncomputable section

namespace Langlands

universe uF uV uG

section Generic

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A finite-dimensional space of endomorphisms is separated by finitely many vectors. -/
theorem exists_finset_eq_zero_of_apply_eq_zero (S : Submodule ℂ (Module.End ℂ V))
    [FiniteDimensional ℂ S] :
    ∃ t : Finset V, ∀ f ∈ S, (∀ v ∈ t, f v = 0) → f = 0 := by
  classical
  let K (t : Finset V) : Submodule ℂ S :=
    ⨅ v ∈ t, LinearMap.ker ((LinearMap.applyₗ (R := ℂ) v).comp S.subtype)
  have hK (t : Finset V) (x : S) : x ∈ K t ↔ ∀ v ∈ t, (x : Module.End ℂ V) v = 0 := by
    simp [K, Submodule.mem_iInf]
  obtain ⟨M, ⟨t, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal (Set.range K) ⟨K ∅, ∅, rfl⟩
  refine ⟨t, fun f hf ht => ?_⟩
  ext w
  have hle : K (insert w t) ≤ K t := fun x hx =>
    (hK t x).mpr fun v hv => (hK _ x).mp hx v (Finset.mem_insert_of_mem hv)
  have heq : K (insert w t) = K t :=
    eq_of_le_of_not_lt hle (hmin _ ⟨insert w t, rfl⟩)
  have hf' : (⟨f, hf⟩ : S) ∈ K (insert w t) := by
    rw [heq]
    exact (hK t _).mpr ht
  simpa using (hK _ _).mp hf' w (Finset.mem_insert_self w t)

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A smooth representation whose operators span a finite-dimensional space is
locally constant as a map into operators. -/
theorem isLocallyConstant_of_finiteDimensional_span (σ : Representation ℂ G V)
    (hσ : IsSmooth σ) [FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ))] :
    IsLocallyConstant (fun g : G => σ g) := by
  classical
  obtain ⟨t, ht⟩ := exists_finset_eq_zero_of_apply_eq_zero (Submodule.span ℂ (Set.range σ))
  choose K hK using hσ
  have hone (k : G) (hk : ∀ v ∈ t, k ∈ K v) : σ k = 1 := by
    have h1 : (1 : Module.End ℂ V) ∈ Submodule.span ℂ (Set.range σ) := by
      rw [← map_one σ]
      exact Submodule.subset_span ⟨1, rfl⟩
    have hmem : σ k - 1 ∈ Submodule.span ℂ (Set.range σ) :=
      Submodule.sub_mem _ (Submodule.subset_span ⟨k, rfl⟩) h1
    refine sub_eq_zero.mp (ht _ hmem fun v hv => ?_)
    have hfix : σ k v = v := hK v ⟨k, hk v hv⟩
    simp [hfix]
  apply (IsLocallyConstant.iff_exists_open _).2
  intro a
  refine ⟨{b | ∀ v ∈ t, a⁻¹ * b ∈ K v}, ?_, ?_, ?_⟩
  · have hopen : IsOpen (⋂ v ∈ t, {b : G | a⁻¹ * b ∈ K v}) :=
      isOpen_biInter_finset fun v _ =>
        (K v).isOpen.preimage (continuous_const.mul continuous_id)
    convert hopen using 1
    ext b
    simp
  · intro v _
    simp
  · intro b hb
    calc σ b = σ a * σ (a⁻¹ * b) := by rw [← map_mul, mul_inv_cancel_left]
      _ = σ a := by rw [hone _ hb, mul_one]

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The operators of units with normalized absolute value at most one span the
whole finite-dimensional operator span. -/
theorem boundedSpan_eq_span (σ : Representation ℂ F.Carrierˣ V)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ))] :
    Submodule.span ℂ {B : Module.End ℂ V |
        ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧ σ b = B} =
      Submodule.span ℂ (Set.range σ) := by
  set Bd := Submodule.span ℂ {B : Module.End ℂ V |
    ∃ b : F.Carrierˣ, T.normalizedAbs (b : F.Carrier) ≤ 1 ∧ σ b = B} with hBd
  have hle : Bd ≤ Submodule.span ℂ (Set.range σ) := by
    apply Submodule.span_mono
    rintro _ ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩
  have : FiniteDimensional ℂ Bd := Submodule.finiteDimensional_of_le hle
  have hmul (c : F.Carrierˣ) (hc : T.normalizedAbs (c : F.Carrier) ≤ 1)
      (x : Module.End ℂ V) (hx : x ∈ Bd) : σ c * x ∈ Bd := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      refine Submodule.subset_span ⟨c * b, ?_, by rw [map_mul]⟩
      rw [Units.val_mul, T.normalizedAbs_mul]
      exact (mul_le_of_le_one_left (T.normalizedAbs_nonneg _) hc).trans hb
    | zero => simp
    | add x y _ _ h₁ h₂ => simpa [mul_add] using Bd.add_mem h₁ h₂
    | smul r x _ h => simpa [mul_smul_comm] using Bd.smul_mem r h
  have hq : (1 : ℝ) ≤ T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one.le
  have hq0 : (T.residueCardinality : ℝ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
  refine le_antisymm hle (Submodule.span_le.mpr ?_)
  rintro _ ⟨b, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -T.ord (b : F.Carrier) ≤ n := ⟨_, Int.self_le_toNat _⟩
  let c : F.Carrierˣ := LocalFactor.PadicAbelian.uniformizerUnit T ^ (n : ℤ)
  have hcabs : T.normalizedAbs (c : F.Carrier) = (T.residueCardinality : ℝ) ^ (-(n : ℤ)) :=
    LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T n
  have hc : T.normalizedAbs (c : F.Carrier) ≤ 1 := by
    rw [hcabs]
    exact zpow_le_one_of_nonpos₀ hq (by omega)
  have hcb : T.normalizedAbs ((c * b : F.Carrierˣ) : F.Carrier) ≤ 1 := by
    rw [Units.val_mul, T.normalizedAbs_mul, hcabs, T.normalizedAbs_of_ne_zero b.ne_zero,
      ← zpow_add₀ hq0]
    exact zpow_le_one_of_nonpos₀ hq (by omega)
  have hinv (x : Module.End ℂ V) : σ c⁻¹ * (σ c * x) = x := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  let L : Bd →ₗ[ℂ] Bd :=
    { toFun x := ⟨σ c * x.val, hmul c hc x.val x.property⟩
      map_add' x y := by ext1; simp [mul_add]
      map_smul' r x := by ext1; simp }
  have hL : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    rw [← hinv x.val, ← hinv y.val]
    exact congrArg (fun z : Bd => σ c⁻¹ * z.val) hxy
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hL
    ⟨σ (c * b), Submodule.subset_span ⟨c * b, hcb, rfl⟩⟩
  have hyb : y.val = σ b := by
    rw [← hinv y.val]
    have h : σ c * y.val = σ (c * b) := congrArg Subtype.val hy
    rw [h, map_mul, hinv]
  rw [← hyb]
  exact y.property

end Padic

/-- JPS (1979), p.181: the complete bounded-span equality and the uniform finite
operator expansion, for every prime, field, topology and smooth representation. -/
theorem finiteOperatorExpansion : FiniteOperatorExpansionStatement.{uF,uV} := by
  classical
  intro p _ F T V _ _ σ hσ hfin
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hBd := boundedSpan_eq_span T σ
  refine ⟨hBd, ?_⟩
  rw [hBd]
  let S := Submodule.span ℂ (Set.range σ)
  let s (a : F.Carrierˣ) : S := ⟨σ a, Submodule.subset_span ⟨a, rfl⟩⟩
  have hspan : Submodule.span ℂ (Set.range s) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff S _).mpr rfl
  let B := Module.finBasis ℂ S
  let χ (i : Fin (Module.finrank ℂ S)) (a : F.Carrierˣ) : ℂ := B.coord i (s a)
  have hχ : Function.Injective χ := by
    intro i j hij
    apply B.linearIndependent_coord.injective
    apply LinearMap.ext_on_range hspan
    intro a
    exact congrFun hij a
  have hs : IsLocallyConstant s := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro a
    exact ((isLocallyConstant_of_finiteDimensional_span σ hσ).eventually_eq a).mono
      fun b hb => Subtype.ext hb
  have hcont (i : Fin (Module.finrank ℂ S)) : Continuous (χ i) :=
    (hs.comp (B.coord i)).continuous
  have hmul (b : F.Carrierˣ) (x : Module.End ℂ V) (hx : x ∈ S) : σ b * x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact Submodule.subset_span ⟨b * a, by simp [map_mul]⟩
    | zero => simp
    | add x y hx hy h₁ h₂ => simpa [mul_add] using S.add_mem h₁ h₂
    | smul r x hx h => simpa [mul_smul_comm] using S.smul_mem r h
  let L (b : F.Carrierˣ) : S →ₗ[ℂ] S :=
    { toFun x := ⟨σ b * x.val, hmul b x.val x.property⟩
      map_add' x y := by ext; simp [mul_add]
      map_smul' r x := by ext; simp }
  let E : (S →ₗ[ℂ] ℂ) →ₗ[ℂ] (F.Carrierˣ → ℂ) :=
    { toFun f a := f (s a)
      map_add' f g := rfl
      map_smul' r f := rfl }
  have hfinite (i : Fin (Module.finrank ℂ S)) :
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => χ i (b * a))) := by
    have hle : Submodule.span ℂ
        (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => χ i (b * a)) ≤ E.range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      refine ⟨(B.coord i).comp (L b), ?_⟩
      funext a
      change B.coord i (L b (s a)) = B.coord i (s (b * a))
      congr 1
      apply Subtype.ext
      simp [L, s, map_mul]
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let A : (F.Carrierˣ → ℂ) → Module.End ℂ V :=
    Function.extend χ (fun i => (B i : Module.End ℂ V)) (fun _ => 0)
  have hA (i : Fin (Module.finrank ℂ S)) : A (χ i) = (B i : Module.End ℂ V) :=
    hχ.extend_apply _ _ i
  refine ⟨Finset.univ.image χ, A, ?_, ?_, ?_⟩
  · intro η hη
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hη
    exact ⟨hcont i, hfinite i⟩
  · intro η hη
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hη
    rw [hA]
    exact (B i).property
  · intro a
    rw [Finset.sum_image (fun i _ j _ hij => hχ hij)]
    simp_rw [hA]
    simpa only [χ, Module.Basis.coord_apply, Submodule.coe_sum, Submodule.coe_smul] using
      (congrArg Subtype.val (B.sum_repr (s a))).symm

end Langlands
