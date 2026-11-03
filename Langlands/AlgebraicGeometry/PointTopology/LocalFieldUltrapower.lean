import Mathlib.Order.Filter.FilterProduct
import Mathlib.RingTheory.Valuation.ValuationSubring
import Langlands.AlgebraicGeometry.PointTopology.LocalFieldInverseBound

/-! # Ultrapowers of locally compact fields and their convergent germs -/

noncomputable section

universe u

open Filter Topology Set

namespace Langlands.AlgebraicGeometry.PointTopology

section Dichotomy

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] [LocallyCompactSpace K]

/-- Along an ultrafilter, a family in a nondiscrete locally compact Hausdorff field either
converges or has inverses tending to zero. -/
theorem ultrafilter_tendsto_or_tendsto_inv_zero (hnd : ¬ DiscreteTopology K)
    {I : Type*} (𝒰 : Ultrafilter I) (g : I → K) :
    (∃ c, Tendsto g 𝒰 (𝓝 c)) ∨ Tendsto (fun i => (g i)⁻¹) 𝒰 (𝓝 0) := by
  obtain ⟨C, hC, hcover⟩ := exists_isCompact_mem_or_inv_mem hnd
  by_cases hgC : ∀ᶠ i in (𝒰 : Filter I), g i ∈ C
  · obtain ⟨c, -, hc⟩ := hC.ultrafilter_le_nhds (𝒰.map g)
      (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hgC)
    exact Or.inl ⟨c, by rwa [Ultrafilter.coe_map] at hc⟩
  have hinvC : ∀ᶠ i in (𝒰 : Filter I), (g i)⁻¹ ∈ C :=
    (Ultrafilter.eventually_not.2 hgC).mono fun i hi => (hcover (g i)).resolve_left hi
  obtain ⟨c, -, hc⟩ := hC.ultrafilter_le_nhds (𝒰.map fun i => (g i)⁻¹)
    (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hinvC)
  rw [Ultrafilter.coe_map] at hc
  by_cases hc0 : c = 0
  · exact Or.inr (hc0 ▸ hc)
  · refine Or.inl ⟨c⁻¹, ?_⟩
    have := (continuousAt_inv₀ hc0).tendsto.comp hc
    simpa [Function.comp_def] using this

end Dichotomy

section Ultrapower

variable (K : Type u) [Field K] {I : Type u} (𝒰 : Ultrafilter I)

/-- The ultrapower `K^I / 𝒰`, the field of germs of `K`-valued functions along `𝒰`. -/
abbrev UltrapowerField : Type u := (𝒰 : Filter I).Germ K

/-- The `K`-algebra structure on the ultrapower, using the existing scalar action on germs. -/
instance ultrapowerAlgebra : Algebra K (UltrapowerField K 𝒰) :=
  Algebra.ofModule
    (fun r x y => Germ.inductionOn₂ x y fun f g => by
      rw [← Germ.coe_smul, ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_smul, smul_mul_assoc])
    (fun r x y => Germ.inductionOn₂ x y fun f g => by
      rw [← Germ.coe_smul, ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_smul, mul_smul_comm])

/-- The quotient map from `K`-valued families to the ultrapower. -/
def ultrapowerMap : (I → K) →ₐ[K] UltrapowerField K 𝒰 :=
  AlgHom.mk' (Germ.coeRingHom (𝒰 : Filter I)) fun c f => Germ.coe_smul c f

variable {K 𝒰}

@[simp]
theorem ultrapowerMap_apply (f : I → K) :
    ultrapowerMap K 𝒰 f = (f : (𝒰 : Filter I).Germ K) :=
  rfl

theorem ultrapowerMap_surjective : Function.Surjective (ultrapowerMap K 𝒰) :=
  fun x => Germ.inductionOn x fun f => ⟨f, rfl⟩

theorem ultrapowerMap_eq_iff {f g : I → K} :
    ultrapowerMap K 𝒰 f = ultrapowerMap K 𝒰 g ↔ ∀ᶠ i in (𝒰 : Filter I), f i = g i :=
  Germ.coe_eq

theorem eventually_ne_zero_of_ultrapowerMap_ne_zero {f : I → K}
    (hf : ultrapowerMap K 𝒰 f ≠ 0) : ∀ᶠ i in (𝒰 : Filter I), f i ≠ 0 := by
  by_contra h
  apply hf
  rw [← map_zero (ultrapowerMap K 𝒰), ultrapowerMap_eq_iff]
  exact (Ultrafilter.eventually_not.2 h).mono fun i hi => by simpa using hi

theorem algebraMap_ultrapowerField_apply (r : K) :
    algebraMap K (UltrapowerField K 𝒰) r = ultrapowerMap K 𝒰 (fun _ => r) := by
  rw [← (ultrapowerMap K 𝒰).commutes]
  rfl

end Ultrapower

section ConvergentGerms

variable (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] [LocallyCompactSpace K] {I : Type u} (𝒰 : Ultrafilter I)

/-- The germs that converge along `𝒰`; they form a valuation subring of the ultrapower. -/
def convergentGerms (hnd : ¬ DiscreteTopology K) : ValuationSubring (UltrapowerField K 𝒰) where
  carrier := {x | ∃ c, x.Tendsto (𝓝 c)}
  zero_mem' := ⟨0, (tendsto_const_nhds : Tendsto (fun _ : I => (0 : K)) 𝒰 (𝓝 0))⟩
  one_mem' := ⟨1, (tendsto_const_nhds : Tendsto (fun _ : I => (1 : K)) 𝒰 (𝓝 1))⟩
  add_mem' := by
    rintro x y ⟨c, hx⟩ ⟨d, hy⟩
    induction x using Germ.inductionOn
    induction y using Germ.inductionOn
    exact ⟨c + d, Germ.coe_tendsto.2 (Germ.coe_tendsto.1 hx |>.add (Germ.coe_tendsto.1 hy))⟩
  mul_mem' := by
    rintro x y ⟨c, hx⟩ ⟨d, hy⟩
    induction x using Germ.inductionOn
    induction y using Germ.inductionOn
    exact ⟨c * d, Germ.coe_tendsto.2 (Germ.coe_tendsto.1 hx |>.mul (Germ.coe_tendsto.1 hy))⟩
  neg_mem' := by
    rintro x ⟨c, hx⟩
    induction x using Germ.inductionOn
    exact ⟨-c, Germ.coe_tendsto.2 (Germ.coe_tendsto.1 hx).neg⟩
  mem_or_inv_mem' := by
    intro x
    induction x using Germ.inductionOn with
    | h f =>
      rcases ultrafilter_tendsto_or_tendsto_inv_zero hnd 𝒰 f with h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, h⟩

variable {K 𝒰} {hnd : ¬ DiscreteTopology K}

theorem mem_convergentGerms_iff' {x : UltrapowerField K 𝒰} :
    x ∈ convergentGerms K 𝒰 hnd ↔ ∃ c, x.Tendsto (𝓝 c) :=
  Iff.rfl

variable (K 𝒰 hnd) in
theorem mem_convergentGerms_iff {f : I → K} :
    ultrapowerMap K 𝒰 f ∈ convergentGerms K 𝒰 hnd ↔ ∃ c, Tendsto f 𝒰 (𝓝 c) :=
  Iff.rfl

variable (K 𝒰 hnd) in
/-- The `K`-algebra structure on the convergent germs, through constant families. -/
instance convergentGermsAlgebra : Algebra K (convergentGerms K 𝒰 hnd) :=
  ((algebraMap K (UltrapowerField K 𝒰)).codRestrict (convergentGerms K 𝒰 hnd) fun r => by
    rw [algebraMap_ultrapowerField_apply, mem_convergentGerms_iff]
    exact ⟨r, tendsto_const_nhds⟩).toAlgebra

variable (K 𝒰 hnd) in
instance convergentGerms_isScalarTower :
    IsScalarTower K (convergentGerms K 𝒰 hnd) (UltrapowerField K 𝒰) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [Field K] [IsTopologicalDivisionRing K] [LocallyCompactSpace K] in
theorem germ_tendsto_nhds_unique {x : UltrapowerField K 𝒰} {c d : K}
    (hc : x.Tendsto (𝓝 c)) (hd : x.Tendsto (𝓝 d)) : c = d := by
  induction x using Germ.inductionOn
  exact tendsto_nhds_unique (Germ.coe_tendsto.1 hc) (Germ.coe_tendsto.1 hd)

/-- The limit of a convergent germ. -/
def germLimit (a : convergentGerms K 𝒰 hnd) : K :=
  Classical.choose (mem_convergentGerms_iff'.1 a.2)

theorem germ_tendsto_germLimit (a : convergentGerms K 𝒰 hnd) :
    (a : UltrapowerField K 𝒰).Tendsto (𝓝 (germLimit a)) :=
  Classical.choose_spec (mem_convergentGerms_iff'.1 a.2)

theorem germLimit_eq_of_tendsto (a : convergentGerms K 𝒰 hnd) {c : K}
    (h : (a : UltrapowerField K 𝒰).Tendsto (𝓝 c)) : germLimit a = c :=
  germ_tendsto_nhds_unique (germ_tendsto_germLimit a) h

omit [T2Space K] [LocallyCompactSpace K] in
theorem germ_tendsto_add {x y : UltrapowerField K 𝒰} {c d : K}
    (hx : x.Tendsto (𝓝 c)) (hy : y.Tendsto (𝓝 d)) : (x + y).Tendsto (𝓝 (c + d)) := by
  induction x using Germ.inductionOn
  induction y using Germ.inductionOn
  exact Germ.coe_tendsto.2 (Germ.coe_tendsto.1 hx |>.add (Germ.coe_tendsto.1 hy))

omit [T2Space K] [LocallyCompactSpace K] in
theorem germ_tendsto_mul {x y : UltrapowerField K 𝒰} {c d : K}
    (hx : x.Tendsto (𝓝 c)) (hy : y.Tendsto (𝓝 d)) : (x * y).Tendsto (𝓝 (c * d)) := by
  induction x using Germ.inductionOn
  induction y using Germ.inductionOn
  exact Germ.coe_tendsto.2 (Germ.coe_tendsto.1 hx |>.mul (Germ.coe_tendsto.1 hy))

variable (K 𝒰 hnd) in
/-- The standard part map: the limit along `𝒰` of a convergent germ. -/
def standardPart : convergentGerms K 𝒰 hnd →ₐ[K] K where
  toFun := germLimit
  map_one' := germLimit_eq_of_tendsto 1
    (Germ.coe_tendsto.2 (tendsto_const_nhds : Tendsto (fun _ : I => (1 : K)) 𝒰 (𝓝 1)))
  map_mul' a b := germLimit_eq_of_tendsto (a * b)
    (germ_tendsto_mul (germ_tendsto_germLimit a) (germ_tendsto_germLimit b))
  map_zero' := germLimit_eq_of_tendsto 0
    (Germ.coe_tendsto.2 (tendsto_const_nhds : Tendsto (fun _ : I => (0 : K)) 𝒰 (𝓝 0)))
  map_add' a b := germLimit_eq_of_tendsto (a + b)
    (germ_tendsto_add (germ_tendsto_germLimit a) (germ_tendsto_germLimit b))
  commutes' r := germLimit_eq_of_tendsto _ (by
    show (algebraMap K (UltrapowerField K 𝒰) r).Tendsto (𝓝 r)
    rw [algebraMap_ultrapowerField_apply]
    exact Germ.coe_tendsto.2 tendsto_const_nhds)

theorem standardPart_apply (a : convergentGerms K 𝒰 hnd) :
    standardPart K 𝒰 hnd a = germLimit a :=
  rfl

variable (K 𝒰 hnd) in
theorem tendsto_standardPart (a : convergentGerms K 𝒰 hnd) {f : I → K}
    (h : (a : UltrapowerField K 𝒰) = ultrapowerMap K 𝒰 f) :
    Tendsto f 𝒰 (𝓝 (standardPart K 𝒰 hnd a)) := by
  have := germ_tendsto_germLimit a
  rw [h] at this
  exact Germ.coe_tendsto.1 this

theorem standardPart_eq_of_tendsto (a : convergentGerms K 𝒰 hnd) {f : I → K} {c : K}
    (h : (a : UltrapowerField K 𝒰) = ultrapowerMap K 𝒰 f) (hf : Tendsto f 𝒰 (𝓝 c)) :
    standardPart K 𝒰 hnd a = c :=
  tendsto_nhds_unique (tendsto_standardPart K 𝒰 hnd a h) hf

end ConvergentGerms

end Langlands.AlgebraicGeometry.PointTopology
