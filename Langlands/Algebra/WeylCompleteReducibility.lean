import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Semisimple
import Langlands.Algebra.LieCasimir

/-!
# Complete reducibility for Lie algebras with central radical

Authors: Worker 1429
-/

noncomputable section

open Module LieModule LieAlgebra

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.Algebra.WeylCompleteReducibility

variable {k : Type u} [Field k] [CharZero k]
variable {L : Type v} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- An ideal and its Killing orthogonal meet inside the centre when the radical is central. -/
theorem inf_killingCompl_le_center [HasCentralRadical k L] (K : LieIdeal k L) :
    K ⊓ K.killingCompl ≤ center k L := by
  rw [← radical_eq_center (R := k) (L := L), ← LieIdeal.solvable_iff_le_radical]
  apply LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero
  intro x hx y hy
  have hyI : y ∈ K ⊓ K.killingCompl := LieSubmodule.lie_le_left _ _ hy
  rw [LieModule.traceForm_comm]
  exact (LieIdeal.mem_killingCompl k L K).mp hx.2 y hyI.1

omit [CharZero k] [FiniteDimensional k L] in
/-- The centre is Killing-orthogonal to the whole Lie algebra. -/
theorem center_le_killingCompl_top : center k L ≤ LieIdeal.killingCompl k L ⊤ := by
  intro z hz
  rw [LieIdeal.mem_killingCompl]
  intro y _
  have hz0 : toEnd k L L z = 0 := by
    ext w
    simp only [toEnd_apply_apply, LinearMap.zero_apply]
    rw [← lie_skew, (LieModule.mem_maxTrivSubmodule k L L z).mp hz w, neg_zero]
  simp [LieModule.traceForm_apply_apply, hz0]

/-- An ideal and its Killing orthogonal span the Lie algebra when the radical is central. -/
theorem sup_killingCompl_eq_top [HasCentralRadical k L] (K : LieIdeal k L) :
    K ⊔ K.killingCompl = ⊤ := by
  have hle : K ⊓ K.killingCompl ≤ K ⊓ LieIdeal.killingCompl k L ⊤ :=
    le_inf inf_le_left ((inf_killingCompl_le_center K).trans center_le_killingCompl_top)
  have hge : K ⊓ LieIdeal.killingCompl k L ⊤ ≤ K ⊓ K.killingCompl := by
    refine le_inf inf_le_left (inf_le_right.trans ?_)
    intro x hx
    rw [LieIdeal.mem_killingCompl] at hx ⊢
    exact fun y _ => hx y (LieSubmodule.mem_top y)
  have heq : (K ⊓ K.killingCompl : LieIdeal k L) = K ⊓ LieIdeal.killingCompl k L ⊤ :=
    le_antisymm hle hge
  have h1 := (killingForm k L).finrank_add_finrank_orthogonal
    (LieModule.traceForm_isSymm k L L).isRefl K.toSubmodule
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq K.toSubmodule K.killingCompl.toSubmodule
  have h3 : K.toSubmodule ⊓ K.killingCompl.toSubmodule =
      K.toSubmodule ⊓ (killingForm k L).orthogonal ⊤ := by
    have := congrArg LieSubmodule.toSubmodule heq
    simpa using this
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule]
  apply Submodule.eq_top_of_finrank_eq
  rw [h3, LieIdeal.toSubmodule_killingCompl] at h2
  rw [LieIdeal.toSubmodule_killingCompl]
  omega


omit [CharZero k] in
/-- A Lie algebra morphism intertwines iterated adjoint actions. -/
theorem map_ad_pow {L' A : Type*} [LieRing L'] [LieAlgebra k L'] [LieRing A] [LieAlgebra k A]
    (φ : L' →ₗ⁅k⁆ A) (d e : L') (n : ℕ) :
    φ (((ad k L' d) ^ n) e) = ((ad k A (φ d)) ^ n) (φ e) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ad_apply, LieHom.map_lie, ih, pow_succ',
      Module.End.mul_apply, ad_apply]

variable {M : Type w} [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M]
  [FiniteDimensional k M]

/-- If the radical is central and the centre acts trivially on `M`, then an element whose
trace-form pairing with everything vanishes acts trivially on `M`. -/
theorem toEnd_eq_zero_of_traceForm_eq_zero [HasCentralRadical k L]
    (hc : ∀ z ∈ center k L, toEnd k L M z = 0) (x : L)
    (hx : ∀ y, traceForm k L M x y = 0) : toEnd k L M x = 0 := by
  let K : LieIdeal k L := LieModule.ker k L M
  have memK : ∀ y, y ∈ K ↔ toEnd k L M y = 0 := fun y => LieHom.mem_ker
  let R : LieIdeal k L :=
    LieAlgebra.InvariantForm.orthogonal (traceForm k L M) (traceForm_lieInvariant k L M) ⊤
  have memR : ∀ y, y ∈ R ↔ ∀ z, traceForm k L M z y = 0 := fun y => by
    simp [R, LieAlgebra.InvariantForm.mem_orthogonal]
  have hKR : K ≤ R := by
    intro y hy
    rw [memR]
    intro z
    rw [traceForm_apply_apply, (memK y).mp hy, LinearMap.comp_zero, map_zero]
  let J : LieIdeal k L := K.killingCompl ⊓ R
  have tf : traceForm k J M = 0 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    change traceForm k L M a b = 0
    exact (memR b).mp ((LieSubmodule.mem_inf _ _ _).mp hb).2 a
  have module_nilp : LieModule.IsNilpotent (derivedSeries k J 1) M :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero tf
  let DJ : LieIdeal k L := ⁅J, J⁆
  have hnilp : ∀ y ∈ DJ, IsNilpotent (toEnd k L M y) := by
    intro y hy
    have hyJ : y ∈ J := LieSubmodule.lie_le_left J J hy
    refine (LieModule.isNilpotent_iff_forall' (R := k)).mp module_nilp ⟨⟨y, hyJ⟩, ?_⟩
    rwa [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, LieIdeal.mem_comap]
  have hDJ : LieRing.IsNilpotent DJ := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := k)]
    intro d
    obtain ⟨N, hN⟩ := LieAlgebra.ad_nilpotent_of_nilpotent (R := k) (hnilp d d.2)
    refine ⟨N + 1, ?_⟩
    ext e
    set f := ((ad k DJ d) ^ N) e with hf
    have hf0 : toEnd k L M (f : L) = 0 := by
      have := map_ad_pow ((toEnd k L M).comp DJ.incl) d e N
      simp only [LieHom.coe_comp, Function.comp_apply, LieIdeal.incl_apply] at this
      rw [← hf] at this
      rw [this, hN, LinearMap.zero_apply]
    have hfc : (f : L) ∈ center k L := by
      apply inf_killingCompl_le_center K
      refine (LieSubmodule.mem_inf _ _ _).mpr ⟨(memK _).mpr hf0, ?_⟩
      exact ((LieSubmodule.mem_inf _ _ _).mp (LieSubmodule.lie_le_left J J f.2)).1
    rw [pow_succ', Module.End.mul_apply, ← hf, ad_apply, LinearMap.zero_apply]
    change ⁅(d : L), (f : L)⁆ = 0
    exact (LieModule.mem_maxTrivSubmodule k L L _).mp hfc d
  have hJ : IsSolvable J := by
    obtain ⟨n, hn⟩ := IsSolvable.solvable k DJ
    rw [LieIdeal.derivedSeries_eq_bot_iff] at hn
    refine IsSolvable.mk (k := n + 1) ((LieIdeal.derivedSeries_eq_bot_iff J (n + 1)).mpr ?_)
    rwa [derivedSeriesOfIdeal_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
  have hJK : J ≤ K := by
    have := (LieIdeal.solvable_iff_le_radical k L J).mp hJ
    rw [HasCentralRadical.radical_eq_center] at this
    intro y hy
    exact (memK y).mpr (hc y (this hy))
  have hRK : R ≤ K := by
    have h := sup_inf_assoc_of_le (K.killingCompl) hKR
    rw [sup_killingCompl_eq_top, top_inf_eq] at h
    rw [h]
    exact sup_le le_rfl hJK
  apply (memK x).mp
  apply hRK
  rw [memR]
  intro z
  rw [traceForm_comm]
  exact hx z

/-- When the radical is central and the centre acts trivially on a nonzero representation, the
image of `L` in `End M` carries a Casimir operator for the trace form of `M`: it commutes with
the action, is not nilpotent, and maps `M` into every subspace containing `⁅L, M⁆`. -/
theorem exists_casimir [HasCentralRadical k L]
    (hc : ∀ z ∈ center k L, toEnd k L M z = 0) (hρ : ∃ x : L, toEnd k L M x ≠ 0) :
    ∃ c : Module.End k M, (∀ x, Commute (toEnd k L M x) c) ∧ ¬ IsNilpotent c ∧
      ∀ W : Submodule k M, (∀ (x : L) (m : M), ⁅x, m⁆ ∈ W) → ∀ m, c m ∈ W := by
  let 𝔤 : LieSubalgebra k (Module.End k M) := (toEnd k L M).range
  have hmem : ∀ X : 𝔤, ∃ x : L, toEnd k L M x = X := fun X => (LieHom.mem_range _ _).mp X.2
  let B : LinearMap.BilinForm k 𝔤 := traceForm k 𝔤 M
  have hBapp : ∀ X Y : 𝔤, B X Y = LinearMap.trace k M ((X : Module.End k M) * Y) :=
    fun X Y => rfl
  have hB : B.Nondegenerate := by
    refine ((traceForm_isSymm k 𝔤 M).isRefl.nondegenerate_iff_separatingLeft).mpr ?_
    intro X hX
    obtain ⟨x, hx⟩ := hmem X
    have h0 : toEnd k L M x = 0 := by
      apply toEnd_eq_zero_of_traceForm_eq_zero hc x
      intro y
      have := hX ⟨toEnd k L M y, LieHom.mem_range_self _ y⟩
      rw [hBapp, ← hx] at this
      rw [traceForm_apply_apply]
      exact this
    apply Subtype.ext
    rw [← hx, h0]
    rfl
  have hInv : ∀ X Y Z : 𝔤, B ⁅X, Y⁆ Z = B X ⁅Y, Z⁆ := traceForm_apply_lie_apply k 𝔤 M
  let b := Module.finBasis k 𝔤
  let c : Module.End k M := LieCasimir.casimirImage B hB b 𝔤.incl
  refine ⟨c, fun x => ?_, ?_, ?_⟩
  · exact LieCasimir.casimirImage_commutes_generator B hB hInv b 𝔤.incl
      ⟨_, LieHom.mem_range_self _ x⟩
  · intro hnil
    have htr : LinearMap.trace k M c = (finrank k 𝔤 : k) := by
      simp only [c, LieCasimir.casimirImage, map_sum]
      have hi : ∀ i, LinearMap.trace k M (𝔤.incl (b i) * 𝔤.incl (B.dualBasis hB b i)) = 1 := by
        intro i
        change LinearMap.trace k M ((b i : Module.End k M) * (B.dualBasis hB b i : Module.End k M))
          = 1
        rw [← hBapp, traceForm_comm]
        change B (B.dualBasis hB b i) (b i) = 1
        rw [LinearMap.BilinForm.apply_dualBasis_left]; simp
      simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
    have h0 : (finrank k 𝔤 : k) = 0 := by
      rw [← htr]
      exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    have h0' : finrank k 𝔤 = 0 := by exact_mod_cast h0
    obtain ⟨x, hx⟩ := hρ
    have hne : (⟨toEnd k L M x, LieHom.mem_range_self _ x⟩ : 𝔤) ≠ 0 := by
      intro h
      exact hx (congrArg Subtype.val h)
    exact hne (finrank_zero_iff_forall_zero.mp h0' _)
  · intro W hW m
    simp only [c, LieCasimir.casimirImage]
    rw [LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨y, hy⟩ := hmem (b i)
    change (b i : Module.End k M) ((B.dualBasis hB b i : Module.End k M) m) ∈ W
    rw [← hy]
    exact hW y _

omit [CharZero k] [FiniteDimensional k L] in
/-- If a non-nilpotent operator commuting with the action maps `M` into a proper Lie submodule `W`
that contains `⁅L, M⁆` and has no Lie submodules other than `⊥` and `W`, then some vector outside
`W` is killed by `L`. -/
theorem exists_lie_eq_zero_of_commute (W : LieSubmodule k L M) (hW : W ≠ ⊤)
    (hmin : ∀ N : LieSubmodule k L M, N ≤ W → N = ⊥ ∨ N = W)
    (hLW : ∀ (x : L) (m : M), ⁅x, m⁆ ∈ W)
    (T : Module.End k M) (hT : ∀ x, Commute (toEnd k L M x) T) (hTn : ¬ IsNilpotent T)
    (hTW : ∀ m, T m ∈ W) :
    ∃ v ∉ W, ∀ x : L, ⁅x, v⁆ = 0 := by
  let K : LieSubmodule k L M :=
    { toSubmodule := LinearMap.ker T
      lie_mem := fun {x m} hm => by
        have hm' : T m = 0 := hm
        change T ⁅x, m⁆ = 0
        have := LinearMap.congr_fun (hT x).eq m
        simp only [Module.End.mul_apply, toEnd_apply_apply] at this
        rw [← this, hm', lie_zero] }
  rcases hmin (K ⊓ W) inf_le_right with h | h
  · have hdim : finrank k (LinearMap.range T) + finrank k (LinearMap.ker T) = finrank k M :=
      LinearMap.finrank_range_add_finrank_ker T
    have hrange : LinearMap.range T ≤ W.toSubmodule := by
      rintro _ ⟨m, rfl⟩
      exact hTW m
    have hlt : finrank k W.toSubmodule < finrank k M :=
      Submodule.finrank_lt (fun h' => hW ((LieSubmodule.toSubmodule_eq_top W).mp h'))
    have h1 := Submodule.finrank_mono hrange
    have hker : LinearMap.ker T ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hdim
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    refine ⟨v, fun hvW => hv0 ?_, fun x => ?_⟩
    · have : v ∈ K ⊓ W := (LieSubmodule.mem_inf _ _ _).mpr ⟨hv, hvW⟩
      rw [h] at this
      exact (LieSubmodule.mem_bot v).mp this
    · have : ⁅x, v⁆ ∈ K ⊓ W := (LieSubmodule.mem_inf _ _ _).mpr ⟨K.lie_mem hv, hLW x v⟩
      rw [h] at this
      exact (LieSubmodule.mem_bot _).mp this
  · exfalso
    apply hTn
    refine ⟨2, ?_⟩
    ext m
    rw [pow_two, Module.End.mul_apply, LinearMap.zero_apply]
    have : T m ∈ K ⊓ W := by
      rw [h]
      exact hTW m
    exact ((LieSubmodule.mem_inf _ _ _).mp this).1

omit [CharZero k] [FiniteDimensional k L] in
/-- Semisimplicity passes along a surjection intertwining two endomorphisms. -/
theorem isSemisimple_of_surjective {M' : Type*} [AddCommGroup M'] [Module k M']
    {f : Module.End k M} {g : Module.End k M'} (π : M →ₗ[k] M') (hπ : Function.Surjective π)
    (hfg : g ∘ₗ π = π ∘ₗ f) (hf : f.IsSemisimple) : g.IsSemisimple := by
  have hpow : ∀ (n : ℕ) (m : M), (g ^ n) (π m) = π ((f ^ n) m) := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ n ih =>
      intro m
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      exact LinearMap.congr_fun hfg _
  have key : ∀ (p : Polynomial k) (m : M),
      Polynomial.aeval g p (π m) = π (Polynomial.aeval f p m) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => intro m; simp only [map_add, LinearMap.add_apply, hp, hq]
    | monomial n a =>
      intro m
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
        hpow, map_smul]
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree
  ext m'
  obtain ⟨m, rfl⟩ := hπ m'
  rw [key, minpoly.aeval, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

/-- If the centre acts semisimply and `L` maps `V` into a proper subspace `W`, then some vector
outside `W` is killed by `L`. The proof is by strong induction on the dimension of `V`. -/
theorem exists_lie_eq_zero_of_lie_mem [HasCentralRadical k L] (n : ℕ) :
    ∀ (V : Type w) [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
      [FiniteDimensional k V], finrank k V = n →
      (∀ z ∈ center k L, (toEnd k L V z).IsSemisimple) →
      ∀ W : Submodule k V, W ≠ ⊤ → (∀ (x : L) (m : V), ⁅x, m⁆ ∈ W) →
      ∃ v ∉ W, ∀ x : L, ⁅x, v⁆ = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ _ _ hn hss W hW hLW
  let W' : LieSubmodule k L V := { toSubmodule := W, lie_mem := fun {x m} _ => hLW x m }
  have hW'top : W' ≠ ⊤ := fun h => hW ((LieSubmodule.toSubmodule_eq_top W').mpr h)
  by_cases hsplit : ∃ N : LieSubmodule k L V, N ≠ ⊥ ∧ N ≤ W' ∧ N ≠ W'
  · obtain ⟨N, hN0, hNW, hNW'⟩ := hsplit
    -- Pass to the quotient by `N`.
    let π : V →ₗ[k] V ⧸ N := (LieSubmodule.Quotient.mk' N : V →ₗ⁅k,L⁆ V ⧸ N)
    have hπ : Function.Surjective π := LieSubmodule.Quotient.surjective_mk' N
    let WQ : Submodule k (V ⧸ N) := W.map π
    have hNWlt : N.toSubmodule < W :=
      lt_of_le_of_ne hNW (fun h => hNW' (LieSubmodule.toSubmodule_injective h))
    have hWlt : finrank k W < n := hn ▸ Submodule.finrank_lt hW
    have hNlt := Submodule.finrank_lt_finrank_of_lt hNWlt
    have hfinQ : finrank k (V ⧸ N) < n := by
      have h1 := Submodule.finrank_quotient_add_finrank N.toSubmodule
      have h2 : 0 < finrank k N.toSubmodule := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
          (fun h => hN0 ((LieSubmodule.toSubmodule_eq_bot N).mp h))
        exact ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
      change finrank k (V ⧸ N.toSubmodule) < n
      omega
    have hWQ : WQ ≠ ⊤ := by
      intro h
      apply hW
      have := (Submodule.map_mkQ_eq_top N.toSubmodule W).mp h
      rwa [sup_eq_right.mpr (show N.toSubmodule ≤ W from hNW)] at this
    have hLWQ : ∀ (x : L) (q : V ⧸ N), ⁅x, q⁆ ∈ WQ := by
      intro x q
      obtain ⟨m, rfl⟩ := hπ q
      exact ⟨⁅x, m⁆, hLW x m, (LieSubmodule.Quotient.mk' N).map_lie x m⟩
    have hssQ : ∀ z ∈ center k L, (toEnd k L (V ⧸ N) z).IsSemisimple := fun z hz =>
      isSemisimple_of_surjective π hπ (LieSubmodule.Quotient.toEnd_comp_mk' N z) (hss z hz)
    obtain ⟨q, hqW, hq⟩ := ih _ hfinQ (V ⧸ N) rfl hssQ WQ hWQ hLWQ
    obtain ⟨v, rfl⟩ := hπ q
    have hvW : v ∉ W := fun h => hqW ⟨v, h, rfl⟩
    have hvN : ∀ x : L, ⁅x, v⁆ ∈ N := by
      intro x
      rw [← LieSubmodule.Quotient.mk_eq_zero]
      exact ((LieSubmodule.Quotient.mk' N).map_lie x v).trans (hq x)
    -- The Lie submodule `N + k v`.
    have hXN : ∀ (x : L) (m : V), m ∈ N.toSubmodule ⊔ k ∙ v → ⁅x, m⁆ ∈ N := by
      intro x m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      rw [lie_add, lie_smul]
      exact N.add_mem (N.lie_mem ha) (N.smul_mem c (hvN x))
    let X : LieSubmodule k L V :=
      { toSubmodule := N.toSubmodule ⊔ k ∙ v
        lie_mem := fun {x m} hm => Submodule.mem_sup_left (hXN x m hm) }
    have hv0 : v ≠ 0 := fun h => hvW (h ▸ W.zero_mem)
    have hfinX : finrank k X < n := by
      have h3 := Submodule.finrank_add_le_finrank_add_finrank N.toSubmodule (k ∙ v)
      rw [finrank_span_singleton hv0] at h3
      change finrank k (N.toSubmodule ⊔ k ∙ v : Submodule k V) < n
      omega
    let WX : Submodule k X := N.toSubmodule.comap (X.incl : X →ₗ[k] V)
    have hvX : v ∈ X := Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    have hWX : WX ≠ ⊤ := by
      intro h
      have : (⟨v, hvX⟩ : X) ∈ WX := h ▸ Submodule.mem_top
      exact hvW (hNW this)
    have hLWX : ∀ (x : L) (u : X), ⁅x, u⁆ ∈ WX := fun x u => hXN x u u.2
    have hssX : ∀ z ∈ center k L, (toEnd k L X z).IsSemisimple := fun z hz =>
      (hss z hz).restrict (p := X.toSubmodule) (fun m hm => X.lie_mem hm)
    obtain ⟨u, huW, hu⟩ := ih _ hfinX X rfl hssX WX hWX hLWX
    refine ⟨u, fun huW' => ?_, fun x => congrArg Subtype.val (hu x)⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp u.2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    by_cases hc : c = 0
    · apply huW
      change (u : V) ∈ N
      rw [← hab, hc, zero_smul, add_zero]
      exact ha
    · apply hvW
      have hcv : c • v ∈ W := by
        have := W.sub_mem huW' (hNW ha)
        rwa [← hab, add_sub_cancel_left] at this
      have := W.smul_mem c⁻¹ hcv
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · push Not at hsplit
    have hmin : ∀ N : LieSubmodule k L V, N ≤ W' → N = ⊥ ∨ N = W' := by
      intro N hN
      by_cases h0 : N = ⊥
      · exact Or.inl h0
      · exact Or.inr (hsplit N h0 hN)
    by_cases hz : ∃ z ∈ center k L, toEnd k L V z ≠ 0
    · obtain ⟨z, hzc, hz0⟩ := hz
      refine exists_lie_eq_zero_of_commute W' hW'top hmin hLW (toEnd k L V z) (fun x => ?_)
        (fun hnil => hz0 (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil (hss z hzc)))
        (fun m => hLW z m)
      have h := congrArg (toEnd k L V) ((LieModule.mem_maxTrivSubmodule k L L z).mp hzc x)
      rw [LieHom.map_lie, map_zero, LieRing.of_associative_ring_bracket] at h
      exact sub_eq_zero.mp h
    · push Not at hz
      by_cases hρ : ∃ x : L, toEnd k L V x ≠ 0
      · obtain ⟨c, hc1, hc2, hc3⟩ := exists_casimir hz hρ
        exact exists_lie_eq_zero_of_commute W' hW'top hmin hLW c hc1 hc2 (hc3 W hLW)
      · push Not at hρ
        obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
          by_contra h
          push Not at h
          exact hW (eq_top_iff.mpr fun v _ => h v)
        exact ⟨v, hv, fun x => LinearMap.congr_fun (hρ x) v⟩

/-- **Complete reducibility.** Over a field of characteristic zero, if the radical of `L` is
central and every central element acts semisimply on `M`, then every Lie submodule of `M` has a
complementary Lie submodule. The proof applies `exists_lie_eq_zero_of_lie_mem` to the
`L`-module of endomorphisms of `M` that map `M` into `W` and act on `W` by a scalar. -/
theorem exists_isCompl [HasCentralRadical k L]
    (hss : ∀ z ∈ center k L, (toEnd k L M z).IsSemisimple) (W : LieSubmodule k L M) :
    ∃ W' : LieSubmodule k L M, IsCompl W W' := by
  by_cases hW0 : W = ⊥
  · exact ⟨⊤, hW0 ▸ isCompl_bot_top⟩
  have hlieE : ∀ (x : L) (f : M →ₗ[k] M) (m : M), ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
    fun x f m => LieHom.lie_apply f x m
  let V : LieSubmodule k L (M →ₗ[k] M) :=
    { carrier := {f | (∀ m, f m ∈ W) ∧ ∃ a : k, ∀ w ∈ W, f w = a • w}
      add_mem' := by
        rintro f g ⟨hf1, a, ha⟩ ⟨hg1, b, hb⟩
        refine ⟨fun m => W.add_mem (hf1 m) (hg1 m), a + b, fun w hw => ?_⟩
        rw [LinearMap.add_apply, ha w hw, hb w hw, add_smul]
      zero_mem' := ⟨fun _ => W.zero_mem, 0, fun w _ => by simp⟩
      smul_mem' := by
        rintro c f ⟨hf1, a, ha⟩
        refine ⟨fun m => W.smul_mem c (hf1 m), c * a, fun w hw => ?_⟩
        rw [LinearMap.smul_apply, ha w hw, smul_smul]
      lie_mem := by
        rintro x f ⟨hf1, a, ha⟩
        refine ⟨fun m => ?_, 0, fun w hw => ?_⟩
        · rw [hlieE]
          exact W.sub_mem (W.lie_mem (hf1 m)) (hf1 _)
        · rw [hlieE, ha w hw, ha _ (W.lie_mem hw), lie_smul, sub_self, zero_smul] }
  have memV : ∀ f : M →ₗ[k] M, f ∈ V ↔ (∀ m, f m ∈ W) ∧ ∃ a : k, ∀ w ∈ W, f w = a • w :=
    fun f => Iff.rfl
  let U : Submodule k V :=
    { carrier := {f | ∀ w ∈ W, (f : M →ₗ[k] M) w = 0}
      add_mem' := by
        intro f g hf hg w hw
        change (f : M →ₗ[k] M) w + (g : M →ₗ[k] M) w = 0
        rw [hf w hw, hg w hw, add_zero]
      zero_mem' := fun w _ => rfl
      smul_mem' := by
        intro c f hf w hw
        change c • (f : M →ₗ[k] M) w = 0
        rw [hf w hw, smul_zero] }
  -- A linear projection onto `W` lies in `V` but not in `U`.
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W.toSubmodule
  let p : M →ₗ[k] M := W.toSubmodule.projection q hq
  have hpV : p ∈ V := (memV p).mpr ⟨fun m => Submodule.projection_apply_mem hq m, 1,
    fun w hw => by rw [one_smul]; exact Submodule.projection_apply_of_mem_left hq hw⟩
  have hU : U ≠ ⊤ := by
    intro h
    have hpU : (⟨p, hpV⟩ : V) ∈ U := h ▸ Submodule.mem_top
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (fun h' => hW0 ((LieSubmodule.toSubmodule_eq_bot W).mp h'))
    exact hw0 ((Submodule.projection_apply_of_mem_left hq hw).symm.trans (hpU w hw))
  have hLU : ∀ (x : L) (f : V), ⁅x, f⁆ ∈ U := by
    intro x f w hw
    obtain ⟨_, a, ha⟩ := f.2
    change ⁅x, (f : M →ₗ[k] M)⁆ w = 0
    rw [hlieE, ha w hw, ha _ (W.lie_mem hw), lie_smul, sub_self]
  have hadE : ∀ z : L, toEnd k L (M →ₗ[k] M) z = ad k (Module.End k M) (toEnd k L M z) := by
    intro z
    ext f m
    rw [toEnd_apply_apply, hlieE, ad_apply, LieRing.of_associative_ring_bracket]
    simp [Module.End.mul_apply]
  have hssV : ∀ z ∈ center k L, (toEnd k L V z).IsSemisimple := by
    intro z hz
    have hE : (toEnd k L (M →ₗ[k] M) z).IsSemisimple := by
      rw [hadE]
      exact ad_isSemisimple_of_isSemisimple (hss z hz)
    exact hE.restrict (p := V.toSubmodule) (fun f hf => V.lie_mem hf)
  obtain ⟨f, hfU, hf⟩ := exists_lie_eq_zero_of_lie_mem (finrank k V) V rfl hssV U hU hLU
  obtain ⟨hf1, a, ha⟩ := f.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfU fun w hw => by rw [ha w hw, zero_smul]
  have hcomm : ∀ (x : L) (m : M), (f : M →ₗ[k] M) ⁅x, m⁆ = ⁅x, (f : M →ₗ[k] M) m⁆ := by
    intro x m
    have h := LinearMap.congr_fun (congrArg Subtype.val (hf x)) m
    rw [LieSubmodule.coe_bracket, hlieE] at h
    exact (sub_eq_zero.mp h).symm
  let W' : LieSubmodule k L M :=
    { toSubmodule := LinearMap.ker (f : M →ₗ[k] M)
      lie_mem := fun {x m} hm => by
        change (f : M →ₗ[k] M) ⁅x, m⁆ = 0
        rw [hcomm, LinearMap.mem_ker.mp hm, lie_zero] }
  refine ⟨W', ?_⟩
  rw [← LieSubmodule.isCompl_toSubmodule]
  constructor
  · rw [Submodule.disjoint_def]
    intro m hmW hmK
    have h1 : a • m = 0 := (ha m hmW).symm.trans hmK
    exact (smul_eq_zero.mp h1).resolve_left ha0
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    have hm : m = a⁻¹ • (f : M →ₗ[k] M) m + (m - a⁻¹ • (f : M →ₗ[k] M) m) := by abel
    rw [hm]
    refine Submodule.add_mem_sup (W.smul_mem _ (hf1 m)) ?_
    change (f : M →ₗ[k] M) (m - a⁻¹ • (f : M →ₗ[k] M) m) = 0
    rw [map_sub, map_smul, ha _ (hf1 m), smul_smul, inv_mul_cancel₀ ha0, one_smul, sub_self]

/-- Over a field of characteristic zero, if the radical of `L` is central and every central element
acts semisimply on `M`, then the lattice of Lie submodules of `M` is complemented. -/
theorem complementedLattice_of_isSemisimple_center [HasCentralRadical k L]
    (hss : ∀ z ∈ center k L, (toEnd k L M z).IsSemisimple) :
    ComplementedLattice (LieSubmodule k L M) :=
  ⟨fun W => exists_isCompl hss W⟩

end Langlands.Algebra.WeylCompleteReducibility
