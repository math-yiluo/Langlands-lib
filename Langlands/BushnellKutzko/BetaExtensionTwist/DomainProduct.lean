import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.RelativeLatticeChain

/-! # Centralizer units in the common intertwining domain -/

noncomputable section
open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

section Projection

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  {ι : Type*} (b : Module.Basis ι E V)

/-- Extend the values on an `E`-basis `E`-linearly and restrict scalars to `F`. -/
def basisProjectionToRelativeEnd : A →+ A where
  toFun x := (b.constr E (fun j => x (b j))).restrictScalars F
  map_zero' := by
    change (b.constr E (0 : ι → V)).restrictScalars F = 0
    rw [map_zero, LinearMap.restrictScalars_zero]
  map_add' x y := by
    change (b.constr E ((fun j => x (b j)) + (fun j => y (b j)))).restrictScalars F = _
    rw [map_add, LinearMap.restrictScalars_add]

omit [ValuativeRel F] in
private theorem basisProjectionToRelativeEnd_eq_self {x : A}
    (hx : ∀ (a : E) v, x (a • v) = a • x v) : basisProjectionToRelativeEnd b x = x := by
  let z : Module.End E V := { x with map_smul' := hx }
  change (b.constr E (fun j => z (b j))).restrictScalars F = x
  rw [b.constr_self E]
  rfl

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

omit [ValuativeRel F] in
private theorem basisProjectionToRelativeEnd_preserves [Fintype ι] {π : 𝒪[E]} (hπ : Irreducible π)
    (C : LatticeChain 𝒪[E] E V) (hb : C.Splits b) {x : A} (m : ℤ)
    (hx : ∀ i v, v ∈ C.lattice i → x v ∈ C.lattice (i + m)) :
    ∀ i v, v ∈ C.lattice i → basisProjectionToRelativeEnd b x v ∈ C.lattice (i + m) := by
  intro i v hv
  change b.constr E (fun j => x (b j)) v ∈ C.lattice (i + m)
  rw [b.constr_apply_fintype E]
  refine Submodule.sum_mem _ fun j _ => ?_
  let t := b.repr v j
  change t • x (b j) ∈ C.lattice (i + m)
  by_cases ht : t = 0
  · simp [ht]
  have h := hb (fun l => b.repr v l) i (by simpa only [b.sum_repr] using hv) j
  change t • b j ∈ C.lattice i at h
  rw [C.smul_mem_iff hπ ht] at h ⊢
  simpa only [sub_add_eq_add_sub] using hx _ _ h

end Projection

section Congruence

variable (L : LatticeChain 𝒪[F] F V)

private theorem unitFiltration_one_of_sub_one {a : G} (ha : (a : A) - 1 ∈ L.endFiltration 1) :
    a ∈ L.unitFiltration 1 := by
  obtain ⟨b, hb, heq⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl ha
  have : b = a := Units.ext (by rw [heq]; abel)
  rwa [this] at hb

private theorem inv_mul_mem_unitFiltration_one {a b : G} (ha : a ∈ L.unitFiltration 0)
    (hab : (b : A) - (a : A) ∈ L.endFiltration 1) : a⁻¹ * b ∈ L.unitFiltration 1 := by
  apply unitFiltration_one_of_sub_one L
  have heq : ((a⁻¹ * b : G) : A) - 1 = (a⁻¹ : G) * ((b : A) - (a : A)) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul]
  rw [heq]
  simpa only [zero_add] using L.mul_mem_endFiltration
    (L.mem_order_iff_mem_endFiltration.mp ha.2.1) hab

private theorem unitFiltration_zero_of_congruent {a b : G} (ha : a ∈ L.unitFiltration 0)
    (hab : (b : A) - (a : A) ∈ L.endFiltration 1) : b ∈ L.unitFiltration 0 := by
  have h := L.unitFiltration_antitone (Nat.zero_le 1) (inv_mul_mem_unitFiltration_one L ha hab)
  simpa only [mul_inv_cancel_left] using (L.unitFiltration 0).mul_mem ha h

end Congruence

section Simple

private theorem finiteCriticalDepth_pos (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) :
    0 < finiteCriticalDepth S.chain S.n S.b := by
  have hn : 0 < S.n := hr ▸ S.r_lt_n
  unfold finiteCriticalDepth simpleCriticalDepth
  cases hk : criticalExponent S.chain S.b using WithBot.recBotCoe with
  | bot => exact hn
  | coe k =>
    have hk' : (k : WithBot ℤ) < ((-S.r : ℤ) : WithBot ℤ) := hk ▸ hs.2
    have hneg := WithBot.coe_lt_coe.mp hk'
    simp only [WithTop.untopD_coe]
    omega

private theorem simpleJLattice_le_centralizer_add_radical (S : Stratum 𝒪[F] F V)
    (hr : S.r = 0) (hs : S.IsSimple) (tail : List A) :
    simpleJLattice S.chain S.n S.b tail ≤ centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 := by
  have hn : 0 < S.n := hr ▸ S.r_lt_n
  have hd := finiteCriticalDepth_pos S hr hs
  cases tail with
  | nil =>
    change centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration (simpleJCutoff S.n) ≤ _
    exact sup_le_sup_left (S.chain.endFiltration_antitone (by unfold simpleJCutoff; omega)) _
  | cons γ tail =>
    apply sup_le_sup_left
    exact inf_le_right.trans (S.chain.endFiltration_antitone (by unfold simpleJCutoff; omega))

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem conjugation_mul_inv (y : G) (x : A) :
    (y : A) * (((y⁻¹ : G) : A) * x * (y : A)) * ((y⁻¹ : G) : A) = x := by
  calc
    _ = ((y : A) * ((y⁻¹ : G) : A)) * x * ((y : A) * ((y⁻¹ : G) : A)) := by
      simp only [mul_assoc]
    _ = x := by rw [Units.mul_inv, one_mul, mul_one]

/-- A common relative splitting basis gives a projection onto the centralizer
preserving the radical step of a lattice chain and its centralizer translate. -/
theorem exists_common_centralizer_projection (L : LatticeChain 𝒪[F] F V) (β₀ : A)
    (hField : IsField (elementAlgebra β₀))
    (hnormal : letI := hField.toField
      ∀ a : (elementAlgebra β₀)ˣ, subfieldUnits F (elementAlgebra β₀) V a ∈ L.stabilizer)
    (y : G) (hy : y ∈ centralizerUnitGroup β₀) :
    ∃ p : A →ₗ[F] A, (∀ x, adjointMap F β₀ (p x) = 0) ∧
      (∀ x, adjointMap F β₀ x = 0 → p x = x) ∧
      (∀ x ∈ L.endFiltration 1, p x ∈ L.endFiltration 1) ∧
      (∀ x, (y : A) * x * ((y⁻¹ : G) : A) ∈ L.endFiltration 1 →
        (y : A) * p x * ((y⁻¹ : G) : A) ∈ L.endFiltration 1) := by
  classical
  let E := elementAlgebra β₀
  let : Field E := hField.toField
  have : FiniteDimensional F V := L.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra β₀))
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer := hnormal
  have hInt : ∀ a : E, IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[E] := isIntegral_iff_mem_spectralInteger F E
  let C := L.relativeLatticeChain hE hInt
  have hC := L.mem_relativeLatticeChain hE hInt
  let β : E := ⟨β₀, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  have hlin {x : A} (hx : Commute β₀ x) (a : E) (v : V) : x (a • v) = a • x v :=
    LinearMap.congr_fun (Algebra.commute_of_mem_adjoin_singleton_of_commute a.property hx.symm).eq v
  have hyB : Commute β₀ (y : A) := hy
  let g : V ≃ₗ[E] V :=
    { toFun := fun v => (y : A) v
      invFun := fun v => ((y⁻¹ : G) : A) v
      left_inv := fun v => LinearMap.congr_fun (Units.inv_mul y) v
      right_inv := fun v => LinearMap.congr_fun (Units.mul_inv y) v
      map_add' := map_add (y : A)
      map_smul' := hlin hy }
  let C' := C.linearEquivMap g.symm
  have hC' (i : ℤ) (v : V) : v ∈ C'.lattice i ↔ (y : A) v ∈ L.lattice i :=
    (C.mem_linearEquivMap g.symm i v).trans (hC _ _)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨n₀, b₀, hb₀⟩ := C.exists_basis_splits hπ
  obtain ⟨n, b, hb', hb⟩ := C'.exists_basis_splits_of_splits hπ C b₀ hb₀
  let p : A →ₗ[F] A :=
    { toFun := basisProjectionToRelativeEnd b
      map_add' := (basisProjectionToRelativeEnd b).map_add
      map_smul' := by
        intro c x
        change (b.constr F ((c : F) • fun j => x (b j))).restrictScalars F = _
        rw [map_smul, LinearMap.restrictScalars_smul]
        rfl }
  have hproj (x : A) : Commute β₀ (p x) := by
    apply LinearMap.ext
    intro v
    change β • (b.constr E (fun j => x (b j)) v) = b.constr E (fun j => x (b j)) (β • v)
    rw [map_smul]
  have hP {x : A} (hx : x ∈ L.endFiltration 1) : p x ∈ L.endFiltration 1 := by
    intro i v hv
    apply (hC _ _).mp
    exact basisProjectionToRelativeEnd_preserves b hπ C hb 1
      (fun j w hw => (hC _ _).mpr (hx j w ((hC _ _).mp hw))) i v ((hC _ _).mpr hv)
  have hP' {x : A} (hx : (y : A) * x * ((y⁻¹ : G) : A) ∈ L.endFiltration 1) :
      (y : A) * p x * ((y⁻¹ : G) : A) ∈ L.endFiltration 1 := by
    have hm (j : ℤ) (w : V) (hw : w ∈ C'.lattice j) : x w ∈ C'.lattice (j + 1) := by
      apply (hC' _ _).mpr
      have hh := hx j ((y : A) w) ((hC' _ _).mp hw)
      change (y : A) (x (((y⁻¹ : G) : A) ((y : A) w))) ∈ L.lattice (j + 1) at hh
      rwa [show ((y⁻¹ : G) : A) ((y : A) w) = w from g.symm_apply_apply w] at hh
    intro j w hw
    change (y : A) (p x (((y⁻¹ : G) : A) w)) ∈ L.lattice (j + 1)
    apply (hC' _ _).mp
    apply basisProjectionToRelativeEnd_preserves b hπ C' hb' 1 hm
    apply (hC' _ _).mpr
    rwa [show (y : A) (((y⁻¹ : G) : A) w) = w from g.apply_symm_apply w]
  exact ⟨p, fun x => sub_eq_zero.mpr (hproj x),
    fun x hx => basisProjectionToRelativeEnd_eq_self b (hlin (sub_eq_zero.mp hx)),
    fun _ hx => hP hx, fun _ hx => hP' hx⟩

/-- On the common domain of a centralizer element, the level-zero group factors as
its relative-unit part followed by its level-one part. The level-zero carrier
description comes from the subgroup properties of a simple stratum. -/
theorem simpleJ_intertwiningDomain_product (S : Stratum 𝒪[F] F V) (hr : S.r = 0)
    (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    (hcarrier : (simpleJ S.chain S.n S.b q.tail : Set G) =
      simpleJCarrier S.chain S.n S.b q.tail 0)
    (y : G) (hy : y ∈ centralizerUnitGroup S.b) :
    let J := simpleJ S.chain S.n S.b q.tail
    let K := simpleJGroup S.chain S.n S.b q.tail 1
    let U := relativeUnitFiltration S.chain S.b 0
    ∀ d : intertwiningDomain J J y,
      ∃ u : intertwiningDomain U U y, ∃ k : intertwiningDomain K K y,
        (u : G) * (k : G) = (d : G) := by
  classical
  intro J K U d
  let L := S.chain
  let Q := centralizerUnitGroup S.b
  have hUJ : U ≤ J := relativeUnitFiltration_le_simpleJ L S.n S.b q.tail
  have hJL : J ≤ L.unitFiltration 0 := simpleJGroup_le_unitFiltration L S.n S.b q.tail 0
  have hd : (d : G) ∈ J := d.property.2
  have hdy : y * (d : G) * y⁻¹ ∈ J := d.property.1
  have hlat {x : G} (hx : x ∈ J) : (x : A) ∈ centralizerLattice L S.b 0 ⊔ L.endFiltration 1 := by
    have hx' : x ∈ simpleJCarrier L S.n S.b q.tail 0 := hcarrier ▸ hx
    exact simpleJLattice_le_centralizer_add_radical S hr hs q.tail hx'.2
  have hprincipal {x : G} (hx : x ∈ J) (h1 : x ∈ L.unitFiltration 1) : x ∈ K := by
    have hx' : x ∈ simpleJCarrier L S.n S.b q.tail 0 := hcarrier ▸ hx
    exact Subgroup.subset_closure ⟨h1, hx'.2⟩
  obtain ⟨hField, hnormal⟩ := hs.1.1
  obtain ⟨p, hproj, hfix, hP, hP'⟩ := exists_common_centralizer_projection L S.b hField hnormal y hy
  have hyB : Commute S.b (y : A) := hy
  have Δ : p (d : G) - ((d : G) : A) ∈ L.endFiltration 1 := by
    obtain ⟨z, hz, x, hx, hzx⟩ := Submodule.mem_sup.mp (hlat hd)
    rw [← hzx, map_add, hfix z hz.2, add_sub_add_left_eq_sub]
    exact sub_mem (hP _ hx) hx
  have Δ' : (y : A) * (p ((d : G) : A) - ((d : G) : A)) * ((y⁻¹ : G) : A) ∈ L.endFiltration 1 := by
    obtain ⟨z, hz, x, hx, hzx⟩ := Submodule.mem_sup.mp (hlat hdy)
    let z' : A := ((y⁻¹ : G) : A) * z * (y : A)
    let x' : A := ((y⁻¹ : G) : A) * x * (y : A)
    have hxy : (y : A) * x' * ((y⁻¹ : G) : A) = x := conjugation_mul_inv y x
    have hzx' : z' + x' = ((d : G) : A) := by
      dsimp [z', x']
      rw [← add_mul, ← mul_add, hzx]
      exact conjugation_mul_inv y⁻¹ ((d : G) : A)
    have hzp : p z' = z' := by
      apply hfix
      apply sub_eq_zero.mpr
      have hzcomm : Commute S.b z := sub_eq_zero.mp (show adjointMap 𝒪[F] S.b z = 0 from hz.2)
      exact (hyB.units_inv_right.mul_right hzcomm).mul_right hyB
    rw [← hzx', map_add, hzp, add_sub_add_left_eq_sub, mul_sub, sub_mul, hxy]
    exact sub_mem (hP' _ (hxy.symm ▸ hx)) hx
  have hi : (((d : G)⁻¹ : G) : A) * (p ((d : G) : A) - ((d : G) : A)) ∈ L.endFiltration 1 := by
    simpa only [zero_add] using L.mul_mem_endFiltration
      (L.mem_order_iff_mem_endFiltration.mp (hJL hd).2.1) Δ
  obtain ⟨v, hv, hv'⟩ := L.exists_mem_unitFiltration (n := 1) le_rfl hi
  let u : G := (d : G) * v
  have hu : (u : A) = p ((d : G) : A) := by
    simp only [u, Units.val_mul, hv', mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    abel
  have huL : u ∈ L.unitFiltration 0 := (L.unitFiltration 0).mul_mem (hJL hd)
    (L.unitFiltration_antitone (Nat.zero_le 1) hv)
  have huQ : u ∈ Q := by
    change Commute S.b (u : A)
    rw [hu]
    exact sub_eq_zero.mp (hproj _)
  have huc : (y * u * y⁻¹ : G) ∈ L.unitFiltration 0 := by
    apply unitFiltration_zero_of_congruent L (hJL hdy)
    simpa only [Units.val_mul, hu, mul_sub, sub_mul] using Δ'
  have huD : u ∈ intertwiningDomain U U y :=
    ⟨⟨Q.mul_mem (Q.mul_mem hy huQ) (Q.inv_mem hy), huc⟩, ⟨huQ, huL⟩⟩
  let k : G := u⁻¹ * (d : G)
  have hkL : k ∈ L.unitFiltration 1 := by
    apply inv_mul_mem_unitFiltration_one L huL
    simpa only [hu, neg_sub] using neg_mem Δ
  have hkc : y * k * y⁻¹ = (y * u * y⁻¹)⁻¹ * (y * (d : G) * y⁻¹) := by dsimp [k]; group
  have hkcL : y * k * y⁻¹ ∈ L.unitFiltration 1 := by
    rw [hkc]
    apply inv_mul_mem_unitFiltration_one L huc
    simp only [Units.val_mul, hu]
    rw [← neg_sub]
    exact neg_mem (by simpa only [mul_sub, sub_mul] using Δ')
  have hkD : k ∈ intertwiningDomain K K y := by
    constructor
    · apply hprincipal _ hkcL
      rw [hkc]
      exact J.mul_mem (J.inv_mem (hUJ huD.1)) hdy
    · exact hprincipal (J.mul_mem (J.inv_mem (hUJ huD.2)) hd) hkL
  exact ⟨⟨u, huD⟩, ⟨k, hkD⟩, by dsimp [k]; group⟩

end Simple

end Langlands.BushnellKutzko
