import Langlands.BushnellKutzko.AdditiveDualityProof
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Character dual of a relative filtration step -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "O" => 𝒪[F]
local notation "tr" => LinearMap.trace F V

/-- The character dual of an integral submodule in the endomorphism algebra,
as an integral submodule for the trace character. -/
def traceDualLattice (ψ : AddChar F ℂ) (M : Submodule O A) : Submodule O A where
  carrier := additiveDual (traceCharacter ψ) (M : Set A)
  zero_mem' := by
    intro y _
    simp
  add_mem' := by
    intro x z hx hz y hy
    rw [add_mul, AddChar.map_add_eq_mul, hx y hy, hz y hy, mul_one]
  smul_mem' := by
    intro a x hx y hy
    have h := hx (a • y) (M.smul_mem a hy)
    change traceCharacter ψ (x * ((a : F) • y)) = 1 at h
    change traceCharacter ψ (((a : F) • x) * y) = 1
    simpa only [mul_smul_comm, smul_mul_assoc] using h

@[simp]
theorem coe_traceDualLattice (ψ : AddChar F ℂ) (M : Submodule O A) :
    (traceDualLattice ψ M : Set A) = additiveDual (traceCharacter ψ) (M : Set A) := rfl

theorem traceDualLattice_antitone (ψ : AddChar F ℂ) :
    Antitone (traceDualLattice (V := V) ψ) :=
  fun _ _ h _ hx y hy => hx y (h hy)

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The filtration steps are dual in complementary degrees `k` and `1-k`. -/
theorem traceDualLattice_endFiltration (L : LatticeChain O F V)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) (k : ℤ) :
    traceDualLattice ψ (L.endFiltration k) = L.endFiltration (1 - k) :=
  SetLike.coe_injective ((additiveDuality F V L ψ hψ.1 hψ.2).1 k)

/-- Testing the trace character on an integral submodule is equivalent to
requiring all of its trace products to belong to the conductor ideal. -/
theorem mem_additiveDual_iff_trace (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ)
    (M : Submodule O A) (x : A) :
    x ∈ additiveDual (traceCharacter ψ) (M : Set A) ↔
      ∀ y ∈ M, tr (x * y) ∈ maximalIdealInField O F := by
  constructor
  · intro hx y hy
    apply (mem_maximalIdealInField_iff_annihilates_integers ψ hψ.1 hψ.2 _).mpr
    intro a
    have h := hx (a • y) (M.smul_mem a hy)
    change traceCharacter ψ (x * ((a : F) • y)) = 1 at h
    simpa only [traceCharacter_apply, mul_smul_comm, map_smul, smul_eq_mul] using h
  · intro hx y hy
    simpa only [traceCharacter_apply, OneMemClass.coe_one, one_mul] using
      (mem_maximalIdealInField_iff_annihilates_integers ψ hψ.1 hψ.2 _).mp (hx y hy) 1

private noncomputable def traceProduct : LinearMap.BilinForm F A := (LinearMap.mul F A).compr₂ tr

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem traceProduct_nondegenerate [FiniteDimensional F V] :
    (traceProduct (F := F) (V := V)).Nondegenerate := by
  have hleft : (traceProduct (F := F) (V := V)).SeparatingLeft := by
    intro x hx
    ext v
    by_contra hv
    have hm : x v ∉ (⊥ : Submodule F V) := by simpa using hv
    obtain ⟨f, _, hf⟩ := LinearMap.exists_extend_of_notMem (0 : (⊥ : Submodule F V) →ₗ[F] F)
      hm 1
    have heq : x * f.smulRight v = f.smulRight (x v) := by
      ext w
      simp [Module.End.mul_apply]
    have ht := hx (f.smulRight v)
    change tr (x * f.smulRight v) = 0 at ht
    rw [heq, LinearMap.trace_smulRight, hf] at ht
    exact one_ne_zero ht
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  change tr (y * x) = 0
  rw [LinearMap.trace_mul_comm F]
  exact hy x

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The adjoint of a commutator map for the trace product is its negative. -/
theorem trace_adjointMap_mul (b x y : A) :
    tr (adjointMap F b x * y) = -tr (x * adjointMap F b y) := by
  change tr ((b * x - x * b) * y) = -tr (x * (b * y - y * b))
  rw [sub_mul, mul_sub, map_sub, map_sub, mul_assoc b x y, mul_assoc x b y,
    LinearMap.trace_mul_comm F b (x * y), mul_assoc x y b]
  abel

/-- The dual of `𝔓^k ∩ B_b` is the sum of `𝔓^(1-k)` and the image of `a_b`. -/
theorem mem_dual_centralizerLattice_iff (L : LatticeChain O F V)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) (b x : A) (k : ℤ) :
    x ∈ additiveDual (traceCharacter ψ) (centralizerLattice L b k : Set A) ↔
      x ∈ L.endFiltration (1 - k) ⊔ ((adjointMap F b).range.restrictScalars O) := by
  let _ := L.finiteDimensional
  rw [mem_additiveDual_iff_trace ψ hψ]
  let R := (adjointMap F b).range
  let p := R.mkQ
  constructor
  · intro hx
    by_contra hn
    let M := (L.endFiltration (1 - k)).map (p.restrictScalars O)
    have hn' : p x ∉ M := by
      rintro ⟨z, hz, heq⟩
      change p z = p x at heq
      have hsub : p (x - z) = 0 := by rw [map_sub, ← heq, sub_self]
      have hr : x - z ∈ R := by
        rw [← Submodule.ker_mkQ R, LinearMap.mem_ker]
        exact hsub
      exact hn (Submodule.mem_sup.mpr ⟨z, hz, x - z, hr, by abel⟩)
    obtain ⟨f, hf, hfx⟩ := separates_fg_submodule (K := F) M ((L.fg_endFiltration _).map _) hn'
    let e := (traceProduct (F := F) (V := V)).toDual traceProduct_nondegenerate
    obtain ⟨y, hy⟩ := e.surjective (f.comp p)
    have htr (a : A) : tr (y * a) = f (p a) := by
      exact LinearMap.congr_fun hy a
    have hyP : y ∈ L.endFiltration k := by
      have h := (L.mem_endFiltration_iff_trace_mul (1 - k) y).mpr
        (fun w hw => htr w ▸ hf (p w) (Submodule.mem_map_of_mem hw))
      rwa [show 1 - (1 - k) = k by omega] at h
    have hcomm : adjointMap F b y = 0 := by
      apply traceProduct_nondegenerate.1
      intro a
      change tr (adjointMap F b y * a) = 0
      have hzero : p (adjointMap F b a) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [Submodule.ker_mkQ]
        exact LinearMap.mem_range_self _ _
      rw [trace_adjointMap_mul, htr, hzero, map_zero, neg_zero]
    have hyQ : y ∈ centralizerLattice L b k := ⟨hyP, hcomm⟩
    apply hfx
    rw [← htr, LinearMap.trace_mul_comm F]
    exact hx y hyQ
  · rintro hz y hy
    obtain ⟨v, hv, _, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
    rw [add_mul, map_add, trace_adjointMap_mul]
    have hzero : adjointMap F b y = 0 := hy.2
    rw [hzero, mul_zero, map_zero, neg_zero, add_zero]
    exact (L.mem_endFiltration_iff_trace_mul k v).mp hv y hy.1

/-- The dual of a relative step, as an equality of integral submodules. -/
theorem traceDualLattice_centralizerLattice (L : LatticeChain O F V)
    (ψ : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψ) (b : A) (k : ℤ) :
    traceDualLattice ψ (centralizerLattice L b k) =
      L.endFiltration (1 - k) ⊔ ((adjointMap F b).range.restrictScalars O) := by
  ext x
  exact mem_dual_centralizerLattice_iff L ψ hψ b x k

end Langlands.BushnellKutzko
