import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.RelativeLatticeChain
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Centralizer intersection of sums of conjugated filtration steps -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Conjugation by an ambient unit on the endomorphism algebra, viewed as a
linear equivalence over the ring of integers. -/
def endUnitConjugation (g : G) : A ≃ₗ[O] A :=
  ((LinearMap.GeneralLinearGroup.toLinearEquiv g).conjAlgEquiv F).toLinearEquiv.restrictScalars O

@[simp]
theorem endUnitConjugation_apply (g : G) (x : A) :
    endUnitConjugation g x = (g : A) * x * (↑g⁻¹ : A) := rfl

@[simp]
theorem endUnitConjugation_symm (g : G) : (endUnitConjugation g).symm = endUnitConjugation g⁻¹ := by
  ext x v
  rfl

section RelativeProjection

variable {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

/-- Extend the values of an `F`-linear map on a chosen `E`-basis `E`-linearly. -/
private def relativeLinearPart {ι : Type*} (b : Module.Basis ι E V) (x : A) : A :=
  (b.constr E (fun i => x (b i))).restrictScalars F

omit [ValuativeRel F] in
private theorem relativeLinearPart_add {ι : Type*} (b : Module.Basis ι E V) (x y : A) :
    relativeLinearPart b (x + y) = relativeLinearPart b x + relativeLinearPart b y := by
  change (b.constr E ((fun i => x (b i)) + (fun i => y (b i)))).restrictScalars F = _
  rw [map_add, LinearMap.restrictScalars_add]
  rfl

omit [ValuativeRel F] in
private theorem relativeLinearPart_restrict {ι : Type*} (b : Module.Basis ι E V)
    (x : Module.End E V) : relativeLinearPart b (x.restrictScalars F) = x.restrictScalars F := by
  change (b.constr E (fun i => x (b i))).restrictScalars F = _
  rw [b.constr_self E]

omit [ValuativeRel F] in
private theorem relativeLinearPart_commute {ι : Type*} (b : Module.Basis ι E V) (β : E) (x : A) :
    Commute (subfieldEmbedding F E V β) (relativeLinearPart b x) :=
  (restrictScalars_commute (b.constr E (fun i => x (b i))) β).symm

variable [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

omit [ValuativeRel F] in
/-- A common splitting basis gives a centralizer retraction preserving every
step of each split chain. -/
private theorem relativeLinearPart_preserves {ι : Type*} [Fintype ι] (b : Module.Basis ι E V)
    (C : LatticeChain 𝒪[E] E V) (hb : C.Splits b) {π : 𝒪[E]} (hπ : Irreducible π)
    {k : ℤ} {x : A} (hx : ∀ i v, v ∈ C.lattice i → x v ∈ C.lattice (i + k)) :
    ∀ i v, v ∈ C.lattice i → relativeLinearPart b x v ∈ C.lattice (i + k) := by
  intro i v hv
  change b.constr E (fun j => x (b j)) v ∈ C.lattice (i + k)
  rw [b.constr_apply_fintype E]
  refine Submodule.sum_mem _ fun j _ => ?_
  let t := b.repr v j
  change t • x (b j) ∈ C.lattice (i + k)
  by_cases ht : t = 0
  · simp [ht]
  have hj : t • b j ∈ C.lattice i := hb (fun j => b.repr v j) i (by simpa only [b.sum_repr] using hv) j
  rw [C.smul_mem_iff hπ ht] at hj ⊢
  simpa only [sub_add_eq_add_sub] using hx _ _ hj

end RelativeProjection

section CentralizerSum

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

local notation "P" => LatticeChain.endFiltration
local notation "Q" => centralizerLattice

/-- The centralizer intersection of two conjugate filtration steps in a sum
is the sum of their centralizer intersections. This is the case of the
lattice-sum property in BK93 (1.3.16) with one simultaneous conjugation. -/
theorem endFiltration_sup_conj_inf_centralizer
    (L : LatticeChain O F V) (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (β : E) (hβ : Algebra.adjoin F ({β} : Set E) = ⊤)
    (g : (Module.End E V)ˣ) (i j : ℤ) :
    let b := subfieldEmbedding F E V β
    let u : G := relativeEndUnits E g
    let e := (endUnitConjugation u : A →ₗ[O] A)
    (P L i ⊔ (P L j).map e) ⊓ (adjointMap O b).ker = Q L b i ⊔ (Q L b j).map e := by
  let := L.finiteDimensional
  let := L.finiteDimensional_subfield E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let C := L.relativeLatticeChain hE (isIntegral_iff_mem_spectralInteger F E)
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv g
  let D := C.linearEquivMap f
  let u : G := relativeEndUnits E g
  let e := endUnitConjugation u
  let b := subfieldEmbedding F E V β
  let K := (adjointMap O b).ker
  change (P L i ⊔ (P L j).map e.toLinearMap) ⊓ K = Q L b i ⊔ (Q L b j).map e.toLinearMap
  have heK (x : A) : e x ∈ K ↔ x ∈ K := by
    have hu : Commute b (u : A) := (restrictScalars_commute (g : Module.End E V) β).symm
    change b * ((u : A) * x * (↑u⁻¹ : A)) - ((u : A) * x * (↑u⁻¹ : A)) * b = 0 ↔
      b * x - x * b = 0
    have heq : b * ((u : A) * x * (↑u⁻¹ : A)) - ((u : A) * x * (↑u⁻¹ : A)) * b =
        e (b * x - x * b) := by
      rw [endUnitConjugation_apply, mul_sub, sub_mul]
      rw [← mul_assoc b ((u : A) * x), ← mul_assoc b (u : A) x, hu.eq]
      rw [mul_assoc ((u : A) * x), (Commute.units_inv_right hu).eq.symm]
      simp only [mul_assoc]
    rw [heq]
    exact ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => h ▸ e.map_zero⟩
  have hC (x : A) : x ∈ P L i ↔ ∀ k v, v ∈ C.lattice k → x v ∈ C.lattice (k + i) := Iff.rfl
  have hD (x : A) : x ∈ (P L j).map e.toLinearMap ↔
      ∀ k v, v ∈ D.lattice k → x v ∈ D.lattice (k + j) := by
    rw [Submodule.mem_map_equiv]
    constructor
    · intro hx k v hv
      rw [C.mem_linearEquivMap] at hv ⊢
      have h := hx k (f.symm v) hv
      change f.symm (x (f (f.symm v))) ∈ C.lattice (k + j) at h
      simpa only [f.apply_symm_apply] using h
    · intro hx k v hv
      change f.symm (x (f v)) ∈ C.lattice (k + j)
      have hvC : v ∈ C.lattice k := hv
      have hvD : f v ∈ D.lattice k := (C.mem_linearEquivMap f k (f v)).mpr
        (by simpa only [f.symm_apply_apply] using hvC)
      have h := hx k (f v) hvD
      exact (C.mem_linearEquivMap f _ _).mp h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨d, b₀, hb₀⟩ := C.exists_basis_splits hπ
  obtain ⟨d', w, hwD, hwC⟩ := D.exists_basis_splits_of_splits hπ C b₀ hb₀
  have hker (x : A) : relativeLinearPart w x ∈ K := by
    change b * relativeLinearPart w x - relativeLinearPart w x * b = 0
    exact sub_eq_zero.mpr (relativeLinearPart_commute w β x).eq
  have hfix {x : A} (hx : x ∈ K) : relativeLinearPart w x = x := by
    have hc : Commute b x := sub_eq_zero.mp hx
    obtain ⟨x', rfl⟩ := exists_restrictScalars_of_commute hβ hc.symm
    exact relativeLinearPart_restrict w x'
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro x ⟨hx, hxK⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hy' := (hC _).mpr (relativeLinearPart_preserves w C hwC hπ ((hC _).mp hy))
    have hz' := (hD _).mpr (relativeLinearPart_preserves w D hwD hπ ((hD _).mp hz))
    have hzy : relativeLinearPart w z ∈ (Q L b j).map e.toLinearMap := by
      rw [Submodule.mem_map_equiv] at hz' ⊢
      exact ⟨hz', (heK _).mp (by simpa only [e.apply_symm_apply] using hker z)⟩
    refine Submodule.mem_sup.mpr ⟨_, ⟨hy', hker y⟩, _, hzy, ?_⟩
    rw [← relativeLinearPart_add, hfix hxK]
  · exact le_inf (inf_le_left.trans le_sup_left) inf_le_right
  · apply le_inf (Submodule.map_mono inf_le_left |>.trans le_sup_right)
    rintro _ ⟨x, hx, rfl⟩
    exact (heK _).mpr hx.2

end CentralizerSum

section Decomposition

variable {R W : Type*} [Ring R] [AddCommGroup W] [Module R W]

/-- The intersection of two sums with a common kernel splits when the sum of
the deeper submodules already has its kernel intersection split. -/
theorem inf_sup_eq_of_deep_kernel_split {M N D E K : Submodule R W}
    (hD : D ≤ M) (hE : E ≤ N)
    (hsplit : (D ⊔ E) ⊓ K = (D ⊓ K) ⊔ (E ⊓ K)) :
    ((M ⊓ K) ⊔ D) ⊓ ((N ⊓ K) ⊔ E) = ((M ⊓ K) ⊓ (N ⊓ K)) ⊔ (D ⊓ E) := by
  refine le_antisymm ?_ (sup_le (le_inf (inf_le_left.trans le_sup_left)
    (inf_le_right.trans le_sup_left)) (le_inf (inf_le_left.trans le_sup_right)
    (inf_le_right.trans le_sup_right)))
  rintro x ⟨hxM, hxN⟩
  obtain ⟨a, ha, d, hd, hx₁⟩ := Submodule.mem_sup.mp hxM
  obtain ⟨b, hb, e, he, hx₂⟩ := Submodule.mem_sup.mp hxN
  have hde : d - e = b - a := by
    calc
      d - e = (a + d) - (b + e) + (b - a) := by abel
      _ = b - a := by rw [hx₁, hx₂, sub_self, zero_add]
  have hdeK : d - e ∈ (D ⊔ E) ⊓ K :=
    ⟨by
      change d - e ∈ D ⊔ E
      rw [sub_eq_add_neg]
      exact Submodule.add_mem_sup hd (E.neg_mem he),
      hde.symm ▸ sub_mem hb.2 ha.2⟩
  rw [hsplit] at hdeK
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hdeK
  have hz : d - p = e + q := by
    calc
      d - p = e + (d - e) - p := by abel
      _ = e + q := by
        rw [← hpq]
        abel
  have hab : a + p = b - q := by
    rw [eq_sub_iff_add_eq]
    calc
      a + p + q = a + (d - e) := by rw [add_assoc, hpq]
      _ = b := by
        rw [hde]
        abel
  refine Submodule.mem_sup.mpr ⟨a + p, ⟨⟨add_mem ha.1 (hD hp.1), add_mem ha.2 hp.2⟩, ?_⟩,
    d - p, ⟨sub_mem hd hp.1, hz.symm ▸ add_mem he hq.1⟩, ?_⟩
  · rw [hab]
    exact ⟨sub_mem hb.1 (hE hq.1), sub_mem hb.2 hq.2⟩
  · rw [← hx₁]
    abel

end Decomposition

end Langlands.BushnellKutzko
