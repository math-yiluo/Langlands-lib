import Langlands.LinearAlgebra.ConstantRootImage
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-! # A normalized bilinear form for a symmetric root pairing -/

noncomputable section

namespace Langlands.LinearAlgebra.SymmetricRootPairingForm

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N) [P.IsRootSystem]
  (hs : ∀ i j, P.pairing i j = P.pairing j i)

include hs in
private theorem exists_form :
    ∃ B : LinearMap.BilinForm ℚ M,
      B.IsSymm ∧ ∀ i j, B (P.root i) (P.root j) = P.pairing i j := by
  classical
  let r : (ι →₀ ℚ) →ₗ[ℚ] M := Finsupp.linearCombination ℚ P.root
  let s : (ι →₀ ℚ) →ₗ[ℚ] Module.Dual ℚ M :=
    Finsupp.linearCombination ℚ P.coroot'
  have heval (v : ι →₀ ℚ) (i : ι) :
      s v (P.root i) = P.coroot' i (r v) := by
    simp only [r, s, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      RootPairing.root_coroot'_eq_pairing, smul_eq_mul, hs]
  have hker : r.ker ≤ s.ker := by
    intro v hv
    apply LinearMap.ext_on_range
      (RootPairing.IsRootSystem.span_root_eq_top (P := P))
    intro i
    change s v (P.root i) = 0
    rw [heval, LinearMap.mem_ker.mp hv, map_zero]
  have hr : Function.Surjective r :=
    (span_range_eq_top_iff_surjective_finsuppLinearCombination ℚ).mp
      (RootPairing.IsRootSystem.span_root_eq_top (P := P))
  let B : LinearMap.BilinForm ℚ M :=
    (r.ker.liftQ s hker).comp (r.quotKerEquivOfSurjective hr).symm.toLinearMap
  have hroot (i : ι) : B (P.root i) = P.coroot' i := by
    have hsingle : r (Finsupp.single i 1) = P.root i := by simp [r]
    change r.ker.liftQ s hker
      ((r.quotKerEquivOfSurjective hr).symm (P.root i)) = _
    rw [← hsingle, LinearMap.quotKerEquivOfSurjective_symm_apply,
      Submodule.liftQ_apply]
    simp [s]
  have hpair (i j : ι) : B (P.root i) (P.root j) = P.pairing i j := by
    rw [hroot, RootPairing.root_coroot'_eq_pairing, hs]
  refine ⟨B, ?_, hpair⟩
  constructor
  intro x y
  have hflip : B = B.flip := by
    apply LinearMap.ext_on_range
      (RootPairing.IsRootSystem.span_root_eq_top (P := P))
    intro i
    apply LinearMap.ext_on_range
      (RootPairing.IsRootSystem.span_root_eq_top (P := P))
    intro j
    change B (P.root i) (P.root j) = B (P.root j) (P.root i)
    rw [hpair, hpair, hs]
  exact LinearMap.congr_fun (LinearMap.congr_fun hflip x) y

/-- A symmetric form whose evaluations on roots equal the symmetric
root-coroot pairing. -/
def form : LinearMap.BilinForm ℚ M :=
  (exists_form P hs).choose

theorem form_isSymm : (form P hs).IsSymm :=
  (exists_form P hs).choose_spec.1

theorem form_apply_root_root (i j : ι) :
    form P hs (P.root i) (P.root j) = P.pairing i j :=
  (exists_form P hs).choose_spec.2 i j

/-- Every root has squared length two in the normalized form. -/
theorem form_apply_root_self (i : ι) :
    form P hs (P.root i) (P.root i) = 2 := by
  rw [form_apply_root_root, P.pairing_same]

section Image

variable {κ X Y : Type*} [AddCommGroup X] [Module ℚ X]
  [AddCommGroup Y] [Module ℚ Y]
  (Q : RootPairing κ ℚ X Y) [Q.IsRootSystem] [Q.IsIrreducible]

include hs in
/-- A linear map taking every root of an irreducible rational root system to
a root of a system with symmetric full pairing is injective. -/
theorem injective_of_mapsTo_roots
    (f : X →ₗ[ℚ] M) (hf : Set.MapsTo f (Set.range Q.root) (Set.range P.root)) :
    Function.Injective f := by
  apply ConstantRootImage.injective_of_hasConstantRootImageLength
    (P := Q) f (form P hs) (form_isSymm P hs)
  refine ⟨2, by norm_num, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hf (Set.mem_range_self i)
  rw [← hj, form_apply_root_self]

end Image

end Langlands.LinearAlgebra.SymmetricRootPairingForm
