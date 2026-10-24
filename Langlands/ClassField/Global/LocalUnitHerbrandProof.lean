import Langlands.ClassField.Global.LocalUnitLattice
import Langlands.ClassField.Global.LocalUnitHerbrandStatement
import Langlands.ClassField.Global.LocalUnitVanishing
import Langlands.Cohomology.HerbrandQuotient

/-! # The Herbrand quotient of the valuation units of a completion

For a finite place `w` of `E` over `v` and `G = Gal(E_w / F_v)`, the normal-basis filtration
of `LocalUnitLattice` gives an open subgroup `V ⊆ U_w` of finite index on which every
multiplicative `1`- and `2`-cocycle is a coboundary. Hence `H¹(G, V) = H²(G, V) = 0`, and for
cyclic `G` the Herbrand quotient of `U_w` equals that of `V`, namely `1`. At unramified places
Hilbert 90 and a fixed uniformizer give `H¹(G, U_w) = 0`, hence also `H²(G, U_w) = 0`.
-/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory groupCohomology

namespace LocalUnitHerbrand

open LocalUnitLattice Langlands.Cohomology.CompleteFiltration Langlands.Cohomology.Herbrand

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] localUnitsAction

/-- Local automorphisms preserve the valuation of `E_w`. -/
theorem valued_localAut (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : w.adicCompletion E) : Valued.v (σ x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := unitsExponent_localAut v w σ (Units.mk0 x hx)
  have e1 := valued_units w (Units.map (σ : w.adicCompletion E →* w.adicCompletion E)
    (Units.mk0 x hx))
  rw [h, ← valued_units w] at e1
  simpa using e1

/-- Local automorphisms preserve the norm of `E_w`. -/
theorem norm_localAut (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : w.adicCompletion E) : ‖σ x‖ = ‖x‖ :=
  le_antisymm (Valued.toNormedField.norm_le_iff.2 (valued_localAut v w σ x).le)
    (Valued.toNormedField.norm_le_iff.2 (valued_localAut v w σ x).ge)

/-- A uniformizer of `F_v` has norm strictly between `0` and `1` in `E_w`. -/
theorem exists_ϖ : ∃ ϖ : v.adicCompletion F,
    0 < ‖algebraMap (v.adicCompletion F) (w.adicCompletion E) ϖ‖ ∧
      ‖algebraMap (v.adicCompletion F) (w.adicCompletion E) ϖ‖ < 1 := by
  obtain ⟨π₀, hπ₀⟩ := exists_unitsExponent_eq_neg_one v
  refine ⟨π₀, norm_pos_iff.2 ?_, ?_⟩
  · exact (map_ne_zero _).2 π₀.ne_zero
  · rw [Valued.toNormedField.norm_lt_one_iff]
    change Valued.v (FiniteExtension.completionMap v w (π₀ : v.adicCompletion F)) < 1
    rw [FiniteExtension.valuation_completionMap, valued_units, hπ₀]
    exact pow_lt_one₀ zero_le (WithZero.exp_lt_one_iff.2 (by norm_num))
      (w.asIdeal.ramificationIdx_pos (𝓞 F)).ne'

section Lattice

variable [FiniteDimensional (v.adicCompletion F) (w.adicCompletion E)]
  (D : LatticeData (v.adicCompletion F) (w.adicCompletion E))

theorem unitFiltration_le_localUnits : D.unitFiltration 0 ≤ localUnits w := fun u hu =>
  (mem_localUnits_iff w u).2
    (Valued.toNormedField.norm_eq_one_iff.1 (D.norm_eq_one_of_mem_unitFiltration hu))

/-- The open subgroup `V = V_{c+1}` of the valuation units. -/
def openUnits : Subgroup (localUnits w) := (D.unitFiltration 0).subgroupOf (localUnits w)

theorem mem_openUnits (x : localUnits w) :
    x ∈ openUnits v w D ↔ (x : (w.adicCompletion E)ˣ) ∈ D.unitFiltration 0 :=
  Subgroup.mem_subgroupOf

theorem smul_mem_openUnits (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    {x : localUnits w} (hx : x ∈ openUnits v w D) : σ • x ∈ openUnits v w D := by
  rw [mem_openUnits, coe_localUnits_smul]
  exact D.smul_mem_unitFiltration 0 σ ((mem_openUnits v w D x).1 hx)

/-- The Galois action on `V`. -/
@[instance_reducible]
def openUnitsAction :
    MulDistribMulAction (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
      (openUnits v w D) where
  smul σ x := ⟨σ • (x : localUnits w), smul_mem_openUnits v w D σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : localUnits w))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : localUnits w))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : localUnits w) y)

attribute [local instance] openUnitsAction

theorem coe_openUnits_smul (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)
    (x : openUnits v w D) :
    (((σ • x : openUnits v w D) : localUnits w) : (w.adicCompletion E)ˣ) =
      σ • ((x : localUnits w) : (w.adicCompletion E)ˣ) := rfl

/-- `V` as a representation of `Gal(E_w / F_v)`. -/
abbrev openUnitsRepresentation :
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u}
      (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) :=
  NormalizedTwoCocycle.coefficientRepresentation _ (openUnits v w D)

/-- The inclusion `V → U_w`. -/
def openUnitsInclusion : openUnitsRepresentation v w D ⟶ localUnitsRepresentation v w :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => Additive.ofMul
            ((@Additive.toMul (openUnits v w D) x : openUnits v w D) : localUnits w)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }

theorem openUnitsInclusion_injective : Function.Injective (openUnitsInclusion v w D).hom := by
  intro x y h
  have h' : ((@Additive.toMul (openUnits v w D) x : openUnits v w D) : localUnits w) =
      ((@Additive.toMul (openUnits v w D) y : openUnits v w D) : localUnits w) :=
    congrArg Additive.toMul h
  exact congrArg Additive.ofMul (Subtype.ext h')

variable [CompleteSpace (w.adicCompletion E)]

theorem subsingleton_H1_openUnits :
    Subsingleton (groupCohomology (openUnitsRepresentation v w D) 1) := by
  have hz : ∀ a : groupCohomology (openUnitsRepresentation v w D) 1, a = 0 := by
    intro a
    refine H1_induction_on a fun x => (H1π_eq_zero_iff x).2 ?_
    let f : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
        (w.adicCompletion E)ˣ := fun g =>
      ((Additive.toMul (show Additive (openUnits v w D) from x g) : openUnits v w D) : localUnits w)
    have hc : IsMulCocycle₁ f := by
      intro g h
      exact congrArg (fun y : Additive (openUnits v w D) =>
          (((Additive.toMul y : openUnits v w D) : localUnits w) : (w.adicCompletion E)ˣ))
        ((mem_cocycles₁_iff x).1 x.2 g h)
    have hf0 : ∀ g, f g ∈ D.unitFiltration 0 := fun g =>
      (mem_openUnits v w D _).1 (Additive.toMul (show Additive (openUnits v w D) from x g)).2
    obtain ⟨s, hs, hsf⟩ := D.exists_coboundary1_eq_of_mem f hc hf0
    let s' : openUnits v w D :=
      ⟨⟨s, unitFiltration_le_localUnits v w D hs⟩, (mem_openUnits v w D _).2 hs⟩
    refine ⟨Additive.ofMul s', funext fun g => ?_⟩
    exact congrArg Additive.ofMul (Subtype.ext (Subtype.ext (hsf g)))
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem subsingleton_H2_openUnits :
    Subsingleton (groupCohomology (openUnitsRepresentation v w D) 2) := by
  have hz : ∀ a : groupCohomology (openUnitsRepresentation v w D) 2, a = 0 := by
    intro a
    refine H2_induction_on a fun x => (H2π_eq_zero_iff x).2 ?_
    let f : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) ×
        (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
        (w.adicCompletion E)ˣ := fun p =>
      ((Additive.toMul (show Additive (openUnits v w D) from x p) : openUnits v w D) : localUnits w)
    have hc : IsMulCocycle₂ f := by
      intro g h j
      exact congrArg (fun y : Additive (openUnits v w D) =>
          (((Additive.toMul y : openUnits v w D) : localUnits w) : (w.adicCompletion E)ˣ))
        ((mem_cocycles₂_iff x).1 x.2 g h j)
    have hf0 : ∀ p, f p ∈ D.unitFiltration 0 := fun p =>
      (mem_openUnits v w D _).1 (Additive.toMul (show Additive (openUnits v w D) from x p)).2
    obtain ⟨s, hs, hsf⟩ := D.exists_coboundary2_eq_of_mem f hc hf0
    let s' : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) → openUnits v w D :=
      fun g => ⟨⟨s g, unitFiltration_le_localUnits v w D (hs g)⟩, (mem_openUnits v w D _).2 (hs g)⟩
    refine ⟨Additive.ofMul ∘ s', funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    exact congrArg Additive.ofMul (Subtype.ext (Subtype.ext (hsf g h)))
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Lattice

section FiniteIndex

variable [FiniteDimensional (v.adicCompletion F) (w.adicCompletion E)]
  (D : LatticeData (v.adicCompletion F) (w.adicCompletion E))

theorem algebraMap_integers_apply (b : 𝓞 E) :
    algebraMap (𝓞 E) (w.adicCompletion E) b =
      algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E b) :=
  IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E) b

theorem norm_algebraMap_integers_le_one (b : 𝓞 E) :
    ‖algebraMap (𝓞 E) (w.adicCompletion E) b‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, algebraMap_integers_apply]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  exact w.intValuation_le_one b

/-- Elements of norm at most `1` are approximated by algebraic integers. -/
theorem exists_integer_approx (x : w.adicCompletion E) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ b : 𝓞 E, ‖x - algebraMap (𝓞 E) (w.adicCompletion E) b‖ < D.radius ^ n := by
  have hε : 0 < D.radius ^ n := pow_pos D.radius_pos n
  obtain ⟨y, hy⟩ := (w.denseRange_algebraMap E).exists_dist_lt x hε
  rw [dist_eq_norm] at hy
  have hy1 : ‖algebraMap E (w.adicCompletion E) y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max x (-(x - algebraMap E (w.adicCompletion E) y))
    rw [norm_neg, show x + -(x - algebraMap E (w.adicCompletion E) y) =
      algebraMap E (w.adicCompletion E) y by abel] at h
    exact h.trans (max_le hx (hy.le.trans (pow_le_one₀ D.radius_pos.le D.radius_lt_one.le)))
  have hyv : w.valuation E y ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff] at hy1
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, valuedAdicCompletion_eq_valuation'] using hy1
  have hz0 : Valued.v (algebraMap (v.adicCompletion F) (w.adicCompletion E) (D.ϖ ^ n)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact D.ϖ_pow_ne_zero n
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer (K := E) hyv (Units.mk0 _ hz0)
  refine ⟨a, ?_⟩
  have ha' : ‖algebraMap (𝓞 E) (w.adicCompletion E) a - algebraMap E (w.adicCompletion E) y‖ <
      D.radius ^ n := by
    rw [← D.norm_ϖ_pow n, Valued.toNormedField.norm_lt_iff, algebraMap_integers_apply, ← map_sub]
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, valuedAdicCompletion_eq_valuation', Units.val_mk0] using ha
  calc ‖x - algebraMap (𝓞 E) (w.adicCompletion E) a‖
      = ‖(x - algebraMap E (w.adicCompletion E) y) +
          -(algebraMap (𝓞 E) (w.adicCompletion E) a - algebraMap E (w.adicCompletion E) y)‖ := by
        congr 1; ring
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ < D.radius ^ n := by rw [norm_neg]; exact max_lt hy ha'

/-- The ideal of algebraic integers of norm `< ‖ϖ‖ ^ n` in `E_w`. -/
def smallIdeal (n : ℕ) : Ideal (𝓞 E) where
  carrier := {b | ‖algebraMap (𝓞 E) (w.adicCompletion E) b‖ < D.radius ^ n}
  zero_mem' := by simp [pow_pos D.radius_pos n]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  smul_mem' c {b} hb := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_algebraMap_integers_le_one w c)).trans_lt hb

theorem smallIdeal_ne_bot (n : ℕ) : smallIdeal v w D n ≠ ⊥ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hlt : ‖algebraMap (𝓞 E) (w.adicCompletion E) b‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, algebraMap_integers_apply]
    simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
    exact (w.intValuation_lt_one_iff_mem b).2 hb
  have hpos : 0 < ‖algebraMap (𝓞 E) (w.adicCompletion E) b‖ := by
    rw [norm_pos_iff, algebraMap_integers_apply]
    exact (map_ne_zero _).2 ((map_ne_zero_iff _ RingOfIntegers.coe_injective).2 hb0)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (pow_pos D.radius_pos n) hlt
  intro h
  have hmem : b ^ k ∈ smallIdeal v w D n := by
    change ‖algebraMap (𝓞 E) (w.adicCompletion E) (b ^ k)‖ < D.radius ^ n
    rw [map_pow, norm_pow]
    exact hk
  rw [h, Ideal.mem_bot] at hmem
  exact hb0 ((pow_eq_zero_iff' (M₀ := 𝓞 E)).1 hmem).1


theorem finite_quotient_openUnits : Finite (localUnits w ⧸ openUnits v w D) := by
  set N := D.c + (D.c + 1)
  have happrox : ∀ u : localUnits w, ∃ b : 𝓞 E,
      ‖((u : (w.adicCompletion E)ˣ) : w.adicCompletion E) -
        algebraMap (𝓞 E) (w.adicCompletion E) b‖ < D.radius ^ N := fun u =>
    exists_integer_approx v w D _
      (le_of_eq (Valued.toNormedField.norm_eq_one_iff.2 ((mem_localUnits_iff w _).1 u.2))) N
  choose b hb using happrox
  have : Finite (𝓞 E ⧸ smallIdeal v w D N) :=
    Ring.HasFiniteQuotients.finiteQuotient (smallIdeal_ne_bot v w D N)
  refine Finite.of_injective (fun q : localUnits w ⧸ openUnits v w D =>
    Ideal.Quotient.mk (smallIdeal v w D N) (b q.out)) ?_
  intro q₁ q₂ h
  rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
  have h' : ‖algebraMap (𝓞 E) (w.adicCompletion E) (b q₁.out - b q₂.out)‖ < D.radius ^ N :=
    Ideal.Quotient.eq.1 h
  rw [map_sub] at h'
  set x₁ : w.adicCompletion E := ((q₁.out : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  set x₂ : w.adicCompletion E := ((q₂.out : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  set a₁ := algebraMap (𝓞 E) (w.adicCompletion E) (b q₁.out)
  set a₂ := algebraMap (𝓞 E) (w.adicCompletion E) (b q₂.out)
  have hd : ‖x₂ - x₁‖ < D.radius ^ N := by
    have e : x₂ - x₁ = ((x₂ - a₂) + -(x₁ - a₁)) + -(a₁ - a₂) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hb _) ?_)
      rw [norm_neg]; exact hb _
    · rw [norm_neg]; exact h'
  have hx₁ : ‖x₁‖ = 1 := Valued.toNormedField.norm_eq_one_iff.2 ((mem_localUnits_iff w _).1 q₁.out.2)
  have hx₁0 : x₁ ≠ 0 := by intro h0; rw [h0, norm_zero] at hx₁; exact zero_ne_one hx₁
  rw [mem_openUnits]
  apply D.mem_unitFiltration_zero_of_norm_le
  have hval : (((q₁.out⁻¹ * q₂.out : localUnits w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      x₁⁻¹ * x₂ := by
    simp [x₁, x₂, Units.val_inv_eq_inv_val]
  rw [hval, show x₁⁻¹ * x₂ - 1 = x₁⁻¹ * (x₂ - x₁) by field_simp, norm_mul, norm_inv, hx₁, inv_one,
    one_mul]
  exact hd.le

theorem finite_coker : Finite ((localUnitsRepresentation v w) ⧸
    LinearMap.range (openUnitsInclusion v w D).hom.toLinearMap) := by
  have := finite_quotient_openUnits v w D
  have hsurj := Submodule.Quotient.mk_surjective
    (LinearMap.range (openUnitsInclusion v w D).hom.toLinearMap)
  choose sec hsec using hsurj
  refine Finite.of_injective (fun z => (QuotientGroup.mk
    (@Additive.toMul (localUnits w) (sec z)) : localUnits w ⧸ openUnits v w D)) ?_
  intro z₁ z₂ h
  rw [← hsec z₁, ← hsec z₂, Submodule.Quotient.eq]
  have hm := QuotientGroup.eq.1 h
  refine ⟨Additive.ofMul ⟨_, (openUnits v w D).inv_mem hm⟩, ?_⟩
  show Additive.ofMul ((@Additive.toMul (localUnits w) (sec z₁))⁻¹ *
      @Additive.toMul (localUnits w) (sec z₂))⁻¹ =
    Additive.ofMul (@Additive.toMul (localUnits w) (sec z₁) /
      @Additive.toMul (localUnits w) (sec z₂))
  congr 1
  rw [mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]

end FiniteIndex

theorem hasHerbrandQuotient_localUnits [IsGalois F E]
    [IsCyclic (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)] :
    HasHerbrandQuotient (localUnitsRepresentation v w) 1 := by
  have : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) :=
    FiniteExtension.local_finite v w
  have : IsGalois (v.adicCompletion F) (w.adicCompletion E) := isGalois_adicCompletion v w
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ϖ v w
  obtain ⟨D, -⟩ := exists_latticeData (norm_localAut v w) ϖ hϖ0 hϖ1
  have := subsingleton_H1_openUnits v w D
  have := subsingleton_H2_openUnits v w D
  have := finite_coker v w D
  have hV : HasHerbrandQuotient (openUnitsRepresentation v w D) 1 := by
    refine ⟨Finite.of_subsingleton, Finite.of_subsingleton, ?_⟩
    rw [Nat.card_of_subsingleton (0 : groupCohomology (openUnitsRepresentation v w D) 2),
      Nat.card_of_subsingleton (0 : groupCohomology (openUnitsRepresentation v w D) 1)]
    norm_num
  exact (hasHerbrandQuotient_iff_of_injective (openUnitsInclusion v w D)
    (openUnitsInclusion_injective v w D)).1 hV

/-- At an unramified place, Hilbert 90 and a fixed uniformizer give `H¹(G, U_w) = 0`. -/
theorem subsingleton_H1_localUnits_of_unramified [IsGalois F E]
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    Subsingleton (groupCohomology (localUnitsRepresentation v w) 1) := by
  have : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) :=
    FiniteExtension.local_finite v w
  obtain ⟨π, hπ1, hπ⟩ := exists_fixed_uniformizer v w he
  have hz : ∀ a : groupCohomology (localUnitsRepresentation v w) 1, a = 0 := by
    intro a
    refine H1_induction_on a fun x => (H1π_eq_zero_iff x).2 ?_
    let f : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
        (w.adicCompletion E)ˣ := fun g =>
      ((Additive.toMul (show Additive (localUnits w) from x g) : localUnits w) :
        (w.adicCompletion E)ˣ)
    have hc : IsMulCocycle₁ f := by
      intro g h
      exact congrArg (fun y : Additive (localUnits w) =>
          ((Additive.toMul y : localUnits w) : (w.adicCompletion E)ˣ))
        ((mem_cocycles₁_iff x).1 x.2 g h)
    obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hc
    set k := Multiplicative.toAdd (unitsExponent w β) with hk
    have hβ' : β * π ^ k ∈ localUnits w := by
      rw [localUnits, MonoidHom.mem_ker, map_mul, map_zpow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_zpow, hπ1, toAdd_one, smul_eq_mul, ← hk]
      ring
    refine ⟨Additive.ofMul ⟨_, hβ'⟩, funext fun g => ?_⟩
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    show g • (β * π ^ k) / (β * π ^ k) = f g
    rw [smul_mul', smul_zpow', hπ, mul_div_mul_right_eq_div, hβ g]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end LocalUnitHerbrand

/-- `h(U_w) = 1` for every cyclic extension of completions of number fields. -/
theorem cyclicCompletionUnitHerbrand : CyclicCompletionUnitHerbrand.{u} := by
  intro F E _ _ _ _ _ _ v w _ _
  obtain ⟨h1, h2, h3⟩ := LocalUnitHerbrand.hasHerbrandQuotient_localUnits v w
  refine ⟨h1, h2, ?_⟩
  exact_mod_cast h3.trans (one_mul _)

/-- At unramified places the first and second cohomology of the valuation units vanish. -/
theorem unramifiedCompletionUnitVanishing : UnramifiedCompletionUnitVanishing.{u} := by
  intro F E _ _ _ _ _ _ v w _ he
  have := isCyclic_localGal v w he
  have h1 := LocalUnitHerbrand.subsingleton_H1_localUnits_of_unramified v w he
  obtain ⟨_, _, h3⟩ := cyclicCompletionUnitHerbrand F E v w
  refine ⟨h1, ?_⟩
  have hc1 : Nat.card (groupCohomology (localUnitsRepresentation v w) 1 : Type u) = 1 :=
    Nat.card_of_subsingleton 0
  rw [hc1] at h3
  exact (Nat.card_eq_one_iff_unique.1 h3).1

/-- The bridge from local cohomology existence holds, since both conclusions are proved
unconditionally. -/
theorem completionUnitHerbrandFromCohomologyExistence :
    CompletionUnitHerbrandFromCohomologyExistence.{u} :=
  fun _ => ⟨cyclicCompletionUnitHerbrand, unramifiedCompletionUnitVanishing⟩

end Langlands.ClassField.Global
