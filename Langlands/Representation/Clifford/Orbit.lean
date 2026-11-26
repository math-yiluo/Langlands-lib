import Langlands.Representation.Clifford.Fiber
import Langlands.Representation.Classification.Cosocle

/-!
# The classes of a normal subgroup under one type form one orbit
-/

noncomputable section

namespace Langlands.Clifford

open Representation FiniteRepresentation

universe uG uV uW

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
  [NonarchimedeanGroup G] {N : Subgroup G} [N.Normal]

omit [N.Normal] in
/-- In a compact nonarchimedean group, every type lies over some open-kernel irreducible class of
`N`. -/
theorem exists_over (B : TypeObj.{uG, uW} G) : ∃ A : WildObj.{uG, uW} N, Over N B A := by
  classical
  let ρ := B.1.representation.comp N.subtype
  let emb : Subrepresentation ρ ↪o Submodule ℂ B.1 :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  have : WellFoundedGT (Subrepresentation ρ) := emb.wellFoundedGT
  have := B.2.2
  have : Nontrivial B.1 :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) (Representation.asModule B.1.representation)
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ :=
    fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  obtain ⟨W, hW, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  let π := Representation.quotient ρ W.toSubmodule fun g _ hw => W.apply_mem_toSubmodule g hw
  let q : Representation.IntertwiningMap ρ π :=
    { toLinearMap := W.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hker : q.ker = W :=
    Subrepresentation.toSubmodule_injective (Submodule.ker_mkQ W.toSubmodule)
  have hπ : π.IsIrreducible :=
    (Langlands.Classification.isIrreducible_iff_isCoatom_ker q hq).mpr (by rw [hker]; exact hW)
  have hBo : IsOpen (B.1.representation.ker : Set G) :=
    (isContinuous_iff_isOpen_ker B.1).mp B.2.1
  have hle : ρ.ker ≤ π.ker := by
    intro n hn
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (ρ n v) = Submodule.Quotient.mk v
      rw [MonoidHom.mem_ker.mp hn, Module.End.one_apply]
  have hπo : IsOpen (π.ker : Set N) :=
    Subgroup.isOpen_mono hle (hBo.preimage continuous_subtype_val)
  refine ⟨⟨FiniteRepresentation.of π, hπ, hπo⟩, q, fun h0 => hW.1 ?_⟩
  apply Subrepresentation.toSubmodule_injective
  apply eq_top_iff.mpr
  intro v _
  have h1 : q v = 0 := by rw [h0]; rfl
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

omit [CompactSpace G] in
/-- A type lying over `A` also lies over the conjugate representatives of `A`. -/
theorem over_smul (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N) (h : Over N B A) (g : G) :
    Over N B (conjugateOpenKernelIrreducible N g A) := by
  obtain ⟨T, hT⟩ := h
  let T' : IntertwiningMap (B.1.representation.comp N.subtype)
      (conjugateOpenKernelIrreducible N g A).1.representation :=
    { toLinearMap := T.toLinearMap ∘ₗ B.1.representation g⁻¹
      isIntertwining' := fun n => by
        apply LinearMap.ext
        intro v
        change T (B.1.representation g⁻¹ (B.1.representation n v)) =
          A.1.representation (MulAut.conjNormal g⁻¹ n) (T (B.1.representation g⁻¹ v))
        have h1 := Representation.IntertwiningMap.isIntertwining _ _ T
          (MulAut.conjNormal g⁻¹ n) (B.1.representation g⁻¹ v)
        rw [← h1]
        change T (B.1.representation g⁻¹ (B.1.representation n v)) =
          T (B.1.representation (g⁻¹ * n * g⁻¹⁻¹) (B.1.representation g⁻¹ v))
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 3
        group }
  refine ⟨T', fun h0 => hT ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 := congrArg (fun F : IntertwiningMap _ _ => F (B.1.representation g v)) h0
  change T (B.1.representation g⁻¹ (B.1.representation g v)) = 0 at h1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  exact h1

omit [CompactSpace G] in
/-- Pulling back along a continuous automorphism preserving `N` preserves the relation `Over`. -/
theorem over_pullback (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N) (h : Over N B A)
    (α : G ≃ₜ* G) (hN : ∀ x, x ∈ N ↔ α x ∈ N) :
    Over N (typeObjPullback α B) (wildObjPullback α hN A) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨⟨T.toLinearMap, fun n => T.isIntertwining' (restrictAut α.toMulEquiv hN n)⟩,
    fun h0 => hT ?_⟩
  apply Representation.IntertwiningMap.ext
  have h1 := congrArg Representation.IntertwiningMap.toLinearMap h0
  exact h1

variable (hab : CommutatorsIn N) (hcyc : CyclicOpenQuotients N)

include hab hcyc in
/-- When every commutator lies in `N` and `CyclicOpenQuotients N` holds, the rank of a type over a
class is the index of the stabilizer times the rank of the class. -/
theorem finrank_of_over (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N) (h : Over N B A) :
    Module.finrank ℂ B.1 =
      (MulAction.stabilizer G (wildClass A)).index * Module.finrank ℂ A.1 := by
  obtain ⟨θ, hθ, hθo⟩ := exists_extension_stabilizer hab hcyc A
  obtain ⟨χ, hχ, heq⟩ := exists_phiObj_eq A θ hθ hθo hab B h
  obtain ⟨E⟩ := (typeClass_eq_iff _ _).mp heq
  rw [E.toLinearEquiv.finrank_eq]
  exact finrank_coindObj _ _

include hab hcyc in
/-- When every commutator lies in `N` and `CyclicOpenQuotients N` holds, the classes of `N` under
one type form one orbit. -/
theorem exists_smul_eq_of_over (B : TypeObj.{uG, uW} G) (A A' : WildObj.{uG, uW} N)
    (h : Over N B A) (h' : Over N B A') : ∃ g : G, wildClass A' = g • wildClass A := by
  obtain ⟨θ, hθ, hθo⟩ := exists_extension_stabilizer hab hcyc A
  obtain ⟨χ, hχ, heq⟩ := exists_phiObj_eq A θ hθ hθo hab B h
  obtain ⟨E⟩ := (typeClass_eq_iff _ _).mp heq
  obtain ⟨T', hT'⟩ := h'
  let τ := Langlands.twist χ θ
  let e : Representation.Equiv (τ.coind (MulAction.stabilizer G (wildClass A)).subtype)
      (phiObj A θ hθ hθo χ hχ).1.representation :=
    coindObjEquiv (MulAction.stabilizer G (wildClass A)) τ
  let ψ : IntertwiningMap ((τ.coind (MulAction.stabilizer G (wildClass A)).subtype).comp
      N.subtype) A'.1.representation :=
    { toLinearMap := T'.toLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ e.toLinearMap
      isIntertwining' := fun n => by
        apply LinearMap.ext
        intro f
        change T' (E.symm (e (τ.coind _ (n : G) f))) = A'.1.representation n (T' (E.symm (e f)))
        rw [show e (τ.coind _ (n : G) f) =
            (phiObj A θ hθ hθo χ hχ).1.representation (n : G) (e f) from
          Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap _ f]
        rw [show E.symm ((phiObj A θ hθ hθo χ hχ).1.representation (n : G) (e f)) =
            B.1.representation (n : G) (E.symm (e f)) from
          Representation.IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap _ _]
        exact Representation.IntertwiningMap.isIntertwining _ _ T' n _ }
  have hψ : ψ ≠ 0 := by
    intro h0
    apply hT'
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have h1 := congrArg (fun F : IntertwiningMap _ _ => F (e.symm (E v))) h0
    change T' (E.symm (e (e.symm (E v)))) = 0 at h1
    rw [Representation.Equiv.apply_symm_apply, Representation.Equiv.symm_apply_apply] at h1
    exact h1
  by_contra hne
  push Not at hne
  apply hψ
  refine intertwining_eq_zero (hNH := le_stabilizer _) ψ fun x T => ?_
  by_contra hT
  have hτ := restrict_twist_eq A θ hθ hχ.1
  let ce := conjugateEquiv (le_stabilizer (wildClass A)) (Fixed.equivOfEq' hτ) x
  let T'' : IntertwiningMap (conjugateOpenKernelIrreducible N x⁻¹ A).1.representation
      A'.1.representation := T.comp ce.symm.toIntertwiningMap
  have hT'' : T'' ≠ 0 := by
    intro h0
    apply hT
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have h1 := congrArg (fun F : IntertwiningMap _ _ => F (ce v)) h0
    simpa [T''] using h1
  obtain ⟨iso⟩ := Langlands.FiniteRepresentation.SplitDegree.nonempty_equiv_of_ne_zero _ _ (conjugateOpenKernelIrreducible N x⁻¹ A).2.1
    A'.2.1 T'' hT''
  apply hne x⁻¹
  rw [smul_wildClass]
  exact ((wildClass_eq_iff _ _).mpr ⟨iso⟩).symm

include hab hcyc in
/-- When every commutator lies in `N` and `CyclicOpenQuotients N` holds, triviality of a type on a
normal subgroup contained in `N` can be read off from a class under the type. -/
theorem trivial_iff_of_over (B : TypeObj.{uG, uW} G) (A : WildObj.{uG, uW} N) (h : Over N B A)
    (M : Subgroup G) [M.Normal] (hMN : M ≤ N) :
    (∀ m ∈ M, B.1.representation m = 1) ↔
      (∀ n : N, (n : G) ∈ M → A.1.representation n = 1) := by
  constructor
  · intro hB n hn
    obtain ⟨T, hT⟩ := h
    have := A.2.1
    have hs := (Representation.IsIrreducible.surjective_or_eq_zero T).resolve_right hT
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hs w
    rw [← Representation.IntertwiningMap.isIntertwining _ _ T n v, Module.End.one_apply]
    change T (B.1.representation (n : G) v) = T v
    rw [hB _ hn, Module.End.one_apply]
  · intro hA m hm
    obtain ⟨θ, hθ, hθo⟩ := exists_extension_stabilizer hab hcyc A
    obtain ⟨χ, hχ, heq⟩ := exists_phiObj_eq A θ hθ hθo hab B h
    obtain ⟨E⟩ := (typeClass_eq_iff _ _).mp heq
    let τ := Langlands.twist χ θ
    have hτ := restrict_twist_eq A θ hθ hχ.1
    have hcoind : τ.coind (MulAction.stabilizer G (wildClass A)).subtype m = 1 := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext y
      change f.1 (y * m) = f.1 y
      have hym : y * m * y⁻¹ ∈ M := ‹M.Normal›.conj_mem m hm y
      have hymH : y * m * y⁻¹ ∈ MulAction.stabilizer G (wildClass A) :=
        le_stabilizer _ (hMN hym)
      have h1 := f.2 ⟨_, hymH⟩ y
      have h2 : τ ⟨_, hymH⟩ = 1 := by
        have h3 := congrArg (fun F => F ⟨_, hMN hym⟩) hτ
        change τ (Subgroup.inclusion (le_stabilizer _) ⟨_, hMN hym⟩) = A.1.representation _ at h3
        rw [hA _ hym] at h3
        exact h3
      rw [h2, Module.End.one_apply] at h1
      rw [← h1]
      show f.1 (y * m) = f.1 (y * m * y⁻¹ * y)
      rw [inv_mul_cancel_right]
    have hrep : (coindObj (MulAction.stabilizer G (wildClass A)) τ).representation m = 1 := by
      have : m ∈ (coindRep (MulAction.stabilizer G (wildClass A)) τ).ker := by
        rw [ker_coindRep]
        exact hcoind
      exact this
    apply LinearMap.ext
    intro v
    apply E.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap m v
    change E (B.1.representation m v) = _ at h1
    change E (B.1.representation m v) = E v
    rw [h1]
    exact (LinearMap.congr_fun hrep (E v)).trans (Module.End.one_apply _)

end Orbit

end Langlands.Clifford
