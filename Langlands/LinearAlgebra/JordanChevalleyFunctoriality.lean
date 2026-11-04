import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Prod
import Langlands.GroupScheme.Lie.RepresentationSubquotient

/-! # Functorial additive Jordan decomposition -/

noncomputable section

universe u v w

open Algebra Polynomial Module

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    {W : Type w} [AddCommGroup W] [Module k W]

/-- Intertwining endomorphisms also intertwines every common polynomial. -/
theorem aeval_intertwines {f : End k V} {g : End k W} (T : V →ₗ[k] W)
    (h : g.comp T = T.comp f) (P : k[X]) :
    (aeval g P).comp T = T.comp (aeval f P) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun y => P.coeff i • y)
    (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) x)

/-- Nilpotence passes through a surjective linear intertwiner. -/
theorem isNilpotent_of_surjective_intertwiner
    {f : End k V} {g : End k W} (T : V →ₗ[k] W)
    (hT : Function.Surjective T) (h : g.comp T = T.comp f)
    (hf : IsNilpotent f) : IsNilpotent g := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, LinearMap.ext fun w => ?_⟩
  obtain ⟨v, rfl⟩ := hT w
  have hv := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h n) v
  simpa only [LinearMap.comp_apply, hn, LinearMap.zero_apply, map_zero] using hv

/-- An endomorphism commutes with its polynomial, hence so does their difference. -/
theorem commute_sub_aeval (f : End k V) (P : k[X]) :
    Commute (f - aeval f P) (aeval f P) := by
  have hmem : aeval f P ∈ adjoin k {f} := by
    rw [adjoin_singleton_eq_range_aeval]
    exact ⟨P, rfl⟩
  exact (commute_of_mem_adjoin_self hmem).sub_left (Commute.refl _)

variable [PerfectField k] [FiniteDimensional k V] [FiniteDimensional k W]

/-- One polynomial gives the additive Jordan components of two endomorphisms
simultaneously, even when the vector spaces have different dimensions. -/
theorem exists_common_jordan_polynomial (f : End k V) (g : End k W) :
    ∃ P : k[X],
      IsNilpotent (f - aeval f P) ∧ (aeval f P).IsSemisimple ∧
      IsNilpotent (g - aeval g P) ∧ (aeval g P).IsSemisimple := by
  let F : End k (V × W) := f.prodMap g
  obtain ⟨n, _, s, hs, hn, hss, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := F)
  rw [adjoin_singleton_eq_range_aeval] at hs
  obtain ⟨P, hP⟩ := hs
  change aeval F P = s at hP
  have hnP : aeval F (X - P) = n := by
    rw [map_sub, aeval_X, hP, hsum]
    abel
  have hfst : f.comp (LinearMap.fst k V W) = (LinearMap.fst k V W).comp F := rfl
  have hsnd : g.comp (LinearMap.snd k V W) = (LinearMap.snd k V W).comp F := rfl
  have hnf := isNilpotent_of_surjective_intertwiner (LinearMap.fst k V W)
    (fun v => ⟨(v, 0), rfl⟩) (aeval_intertwines _ hfst (X - P))
    (hnP.symm ▸ hn)
  have hng := isNilpotent_of_surjective_intertwiner (LinearMap.snd k V W)
    (fun w => ⟨(0, w), rfl⟩) (aeval_intertwines _ hsnd (X - P))
    (hnP.symm ▸ hn)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · simpa only [map_sub, aeval_X] using hnf
  · apply Langlands.GroupScheme.Lie.isSemisimple_of_surjective_intertwiner
      (LinearMap.fst k V W) (fun v => ⟨(v, 0), rfl⟩)
      (aeval_intertwines _ hfst P).symm
    rwa [hP]
  · simpa only [map_sub, aeval_X] using hng
  · apply Langlands.GroupScheme.Lie.isSemisimple_of_surjective_intertwiner
      (LinearMap.snd k V W) (fun w => ⟨(0, w), rfl⟩)
      (aeval_intertwines _ hsnd P).symm
    rwa [hP]

omit [FiniteDimensional k W] in
/-- The canonical semisimple component of an endomorphism over a perfect field. -/
def jordanSemisimplePart (f : End k V) : End k V :=
  (Module.End.exists_isNilpotent_isSemisimple (f := f)).choose_spec.2.choose

omit [FiniteDimensional k W] in
/-- The complementary nilpotent component. -/
def jordanNilpotentPart (f : End k V) : End k V :=
  f - jordanSemisimplePart f

omit [FiniteDimensional k W] in
theorem jordanSemisimplePart_properties (f : End k V) :
    jordanSemisimplePart f ∈ adjoin k {f} ∧
      IsNilpotent (jordanNilpotentPart f) ∧
      (jordanSemisimplePart f).IsSemisimple ∧
      Commute (jordanNilpotentPart f) (jordanSemisimplePart f) := by
  let n₀ := (Module.End.exists_isNilpotent_isSemisimple (f := f)).choose
  let s₀ := jordanSemisimplePart f
  obtain ⟨hs, hn, hss, hsum⟩ :=
    (Module.End.exists_isNilpotent_isSemisimple (f := f)).choose_spec.2.choose_spec
  change s₀ ∈ adjoin k {f} at hs
  change IsNilpotent n₀ at hn
  change s₀.IsSemisimple at hss
  change f = n₀ + s₀ at hsum
  have hnil : jordanNilpotentPart f = n₀ := by
    change f - s₀ = n₀
    exact (congrArg (fun z => z - s₀) hsum).trans (add_sub_cancel_right _ _)
  refine ⟨hs, ?_, hss, ?_⟩
  · exact hnil.symm ▸ hn
  · rw [adjoin_singleton_eq_range_aeval] at hs
    obtain ⟨P, hP⟩ := hs
    change aeval f P = s₀ at hP
    change Commute (f - jordanSemisimplePart f) (jordanSemisimplePart f)
    rw [show jordanSemisimplePart f = aeval f P from hP.symm]
    exact commute_sub_aeval f P

omit [FiniteDimensional k W] in
/-- Any commuting nilpotent plus semisimple decomposition has the chosen parts. -/
theorem jordanSemisimplePart_eq_of_decomposition
    (f n s : End k V) (hn : IsNilpotent n) (hs : s.IsSemisimple)
    (hc : Commute n s) (hsum : f = n + s) :
    jordanSemisimplePart f = s := by
  obtain ⟨_, hn₀, hs₀, hc₀⟩ := jordanSemisimplePart_properties f
  exact (Module.End.isNilpotent_isSemisimple_unique hn₀ hs₀ hn hs hc₀ hc
    (by rw [jordanNilpotentPart, sub_add_cancel, ← hsum])).2

/-- Every linear intertwiner preserves the canonical semisimple components. -/
theorem jordanSemisimplePart_intertwines {f : End k V} {g : End k W}
    (T : V →ₗ[k] W) (h : g.comp T = T.comp f) :
    (jordanSemisimplePart g).comp T = T.comp (jordanSemisimplePart f) := by
  obtain ⟨P, hnf, hsf, hng, hsg⟩ := exists_common_jordan_polynomial f g
  have hf := jordanSemisimplePart_eq_of_decomposition f (f - aeval f P)
    (aeval f P) hnf hsf (commute_sub_aeval f P) (sub_add_cancel _ _).symm
  have hg := jordanSemisimplePart_eq_of_decomposition g (g - aeval g P)
    (aeval g P) hng hsg (commute_sub_aeval g P) (sub_add_cancel _ _).symm
  rw [hf, hg]
  exact aeval_intertwines T h P

/-- Every linear intertwiner preserves the canonical nilpotent components. -/
theorem jordanNilpotentPart_intertwines {f : End k V} {g : End k W}
    (T : V →ₗ[k] W) (h : g.comp T = T.comp f) :
    (jordanNilpotentPart g).comp T = T.comp (jordanNilpotentPart f) := by
  simp only [jordanNilpotentPart, LinearMap.sub_comp, LinearMap.comp_sub,
    h, jordanSemisimplePart_intertwines T h]

end Langlands.LinearAlgebra
