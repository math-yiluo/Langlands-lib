import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Traces through the stable image of an Iwahori compression

For a compact open subgroup `K` and an element `g` satisfying the abstract
Iwahori contraction conditions, the trace on the `K`-fixed vectors of the
compression by `g` followed by any commuting endomorphism equals the trace of the
corresponding endomorphism of the `K ∩ M`-fixed coinvariants.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

section Trace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  {K : OpenSubgroup G} (hK : IsCompact (K : Set G)) {N M Nbar : Subgroup G} {g : G}

/-- The trace of compression followed by a commuting endomorphism `X` of the
`K`-fixed vectors is the trace of any endomorphism `Z` of the `K ∩ M`-fixed
coinvariants that `C ∘ X` induces through the quotient map. The power-kernel
part contributes nothing, and the stable image is carried isomorphically onto
the coinvariant fixed space. -/
theorem trace_compressedAction_mul_of_iwahoriContraction
    (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (X : Module.End ℂ (fixedVectors ρ K.toSubgroup))
    (hX : Commute (compressedAction ρ hρ K hK g) X)
    (Z : Module.End ℂ (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)))
    (hZ : ∀ x, fixedJacquetMap ρ N M hMN K.toSubgroup (compressedAction ρ hρ K hK g (X x)) =
      Z (fixedJacquetMap ρ N M hMN K.toSubgroup x)) :
    LinearMap.trace ℂ _ (compressedAction ρ hρ K hK g * X) = LinearMap.trace ℂ _ Z := by
  classical
  set C := compressedAction ρ hρ K hK g with hCdef
  set P := powerKernelSup ρ hρ K hK g with hPdef
  set S := stableImage ρ hρ K hK g with hSdef
  have hcompl : IsCompl P S := powerKernelSup_isCompl_stableImage ρ hρ K hK g hfin
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp C.eventually_iSup_ker_pow_eq
  have hP : P = LinearMap.ker (C ^ n) := hn n le_rfl
  have hXP : Set.MapsTo X P P := by
    intro x hx
    rw [SetLike.mem_coe, hP, LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, (hX.pow_left n).eq, Module.End.mul_apply, hx, map_zero]
  have hCP : Set.MapsTo C P P := by
    intro x hx
    rw [SetLike.mem_coe, hP, LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]
  have hXS : Set.MapsTo X S S := by
    intro x hx
    rw [SetLike.mem_coe, hSdef, mem_stableImage] at hx ⊢
    intro r
    obtain ⟨w, rfl⟩ := hx r
    refine ⟨X w, ?_⟩
    change (C ^ r) (X w) = X ((C ^ r) w)
    rw [← Module.End.mul_apply, (hX.pow_left r).eq, Module.End.mul_apply]
  have hCS : Set.MapsTo C S S := fun x hx => compressedAction_mem_stableImage ρ hρ K hK g x hx
  let Nb : Bool → Submodule ℂ (fixedVectors ρ K.toSubgroup) := fun b => cond b P S
  have hint : DirectSum.IsInternal Nb :=
    (DirectSum.isInternal_submodule_iff_isCompl Nb (i := true) (j := false) (by decide)
      (by ext b; cases b <;> simp)).mpr hcompl
  have hYb : ∀ b, Set.MapsTo (C * X) (Nb b) (Nb b) := by
    intro b
    cases b
    · exact hCS.comp hXS
    · exact hCP.comp hXP
  rw [LinearMap.trace_eq_sum_trace_restrict hint hYb, Fintype.sum_bool]
  -- The power-kernel summand is nilpotent.
  have hpow : ∀ (k : ℕ) (x : Nb true),
      ((((C * X).restrict (hYb true)) ^ k) x : fixedVectors ρ K.toSubgroup) =
        ((C * X) ^ k) (x : fixedVectors ρ K.toSubgroup) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      exact congrArg (C * X) (ih x)
  have hnil : IsNilpotent ((C * X).restrict (hYb true)) := by
    refine ⟨n, LinearMap.ext fun x => Subtype.ext ?_⟩
    rw [hpow n x, LinearMap.zero_apply, ZeroMemClass.coe_zero]
    have hx : (X ^ n) (x : fixedVectors ρ K.toSubgroup) ∈ LinearMap.ker (C ^ n) := by
      rw [← hP]
      exact Module.End.pow_apply_mem_of_forall_mem n (fun y hy => hXP hy) _ x.property
    rw [hX.mul_pow, Module.End.mul_apply]
    exact hx
  have h0 : LinearMap.trace ℂ (Nb true) ((C * X).restrict (hYb true)) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [h0, zero_add]
  -- The stable-image summand is conjugate to `Z`.
  let e := LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
    (stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ hK h hMN hfin)
  have hconj : e.conj ((C * X).restrict (hYb false)) = Z := by
    apply LinearMap.ext
    intro w
    obtain ⟨s, rfl⟩ := e.surjective w
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact hZ (s : fixedVectors ρ K.toSubgroup)
  rw [← hconj, LinearMap.trace_conj']
  rfl

end Trace

end Langlands.Jacquet
