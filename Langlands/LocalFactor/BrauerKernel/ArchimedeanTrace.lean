import Langlands.Global.Factors.RelativeWeilAssemblyGlobal
import Langlands.LocalFactor.BrauerKernel.ArchimedeanTrivial

/-! # Real components of trace additive characters -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.HeckeFunctionalEquation
open scoped NumberField.LiesOver

variable {k M : Type u} [Field k] [Field M] [Algebra k M]

/-- At a real place `u` over a real place `r`, the completion map is compatible with the real
identifications of the two completions: every ring endomorphism of `ℝ` is the identity. -/
theorem ringEquivRealOfIsReal_completionMap (r : NumberField.InfinitePlace k)
    (u : NumberField.InfinitePlace M) [u.LiesOver r] (hr : r.IsReal) (hu : u.IsReal)
    (y : r.Completion) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hu
        (NumberField.LiesOver.completionMap (v := r) (w := u) y) =
      InfinitePlace.Completion.ringEquivRealOfIsReal hr y := by
  let φ : ℝ →+* ℝ := (InfinitePlace.Completion.ringEquivRealOfIsReal hu).toRingHom.comp
    ((NumberField.LiesOver.completionMap (v := r) (w := u)).comp
      (InfinitePlace.Completion.ringEquivRealOfIsReal hr).symm.toRingHom)
  have hφ : φ = RingHom.id ℝ := Subsingleton.elim _ _
  have h := congrArg (fun f : ℝ →+* ℝ => f (InfinitePlace.Completion.ringEquivRealOfIsReal hr y)) hφ
  simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, RingHom.id_apply] at h
  exact h

/-- At a real place `u` over a real place `r`, the local trace is read as the identity of `ℝ`. -/
theorem ringEquivRealOfIsReal_localTrace (r : NumberField.InfinitePlace k)
    (u : NumberField.InfinitePlace M) [u.LiesOver r] (hr : r.IsReal) (hu : u.IsReal)
    (x : u.Completion) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hr (InfiniteExtension.localTrace r u x) =
      InfinitePlace.Completion.ringEquivRealOfIsReal hu x := by
  set y := (InfinitePlace.Completion.ringEquivRealOfIsReal hr).symm
    (InfinitePlace.Completion.ringEquivRealOfIsReal hu x) with hy
  have hx : NumberField.LiesOver.completionMap (v := r) (w := u) y = x := by
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal hu).injective
    rw [ringEquivRealOfIsReal_completionMap r u hr hu y, hy, RingEquiv.apply_symm_apply]
  rw [← hx]
  have hfin : Module.finrank r.Completion u.Completion = 1 :=
    (isUnramified_of_isReal (F := k) hu).finrank_eq_one r
  have ht : InfiniteExtension.localTrace r u (NumberField.LiesOver.completionMap y) = y := by
    change Algebra.trace r.Completion u.Completion (algebraMap r.Completion u.Completion y) = y
    rw [Algebra.trace_algebraMap, hfin, one_smul]
  rw [ht, ringEquivRealOfIsReal_completionMap r u hr hu y]

section Adelic

variable [NumberField k] [NumberField M]

omit [NumberField k] in
open scoped Classical in
/-- The infinite adelic trace of an adele supported at one infinite place `u` above `r` is
supported at `r`, with the local trace there. -/
theorem infiniteAdeleTrace_single (r : NumberField.InfinitePlace k)
    (u : NumberField.InfinitePlace M) [hu : u.LiesOver r] (x : u.Completion) :
    infiniteAdeleTrace (K := k) (Pi.single u x : InfiniteAdeleRing M) =
      Pi.single r (InfiniteExtension.localTrace r u x) := by
  funext p
  change (∑ q : InfinitePlacesAbove M p, InfiniteExtension.localTrace p q.1
    ((Pi.single u x : (j : NumberField.InfinitePlace M) → j.Completion) q.1)) =
    (Pi.single r (InfiniteExtension.localTrace r u x) :
      (j : NumberField.InfinitePlace k) → j.Completion) p
  by_cases hp : p = r
  · subst hp
    rw [Pi.single_eq_same]
    rw [Finset.sum_eq_single ⟨u, hu⟩]
    · rw [Pi.single_eq_same]
    · intro q _ hq
      have hqu : q.1 ≠ u := fun h => hq (Subtype.ext h)
      rw [Pi.single_eq_of_ne hqu, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Pi.single_eq_of_ne hp]
    refine Finset.sum_eq_zero fun q _ => ?_
    have hqu : q.1 ≠ u := by
      intro h
      apply hp
      have h1 := @InfinitePlace.LiesOver.comap_eq _ _ _ _ _ q.1 p q.2
      have h2 := @InfinitePlace.LiesOver.comap_eq _ _ _ _ _ u r hu
      rw [← h1, ← h2, h]
    rw [Pi.single_eq_of_ne hqu, map_zero]

/-- **Real components of trace characters.** If `ψ` has real component `a` at a real place
`r` of `k`, then `ψ ∘ Tr` has real component `a` at every real place `u` of `M` above `r`. -/
theorem isRealAdditiveComponent_traceAdditiveCharacter
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles k))
    (hψ : ∀ x : k, ψ (diagonal k x) = 1) (r : NumberField.InfinitePlace k)
    (u : NumberField.InfinitePlace M) [u.LiesOver r] (hr : r.IsReal) (hu : u.IsReal) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ r hr a) :
    IsRealAdditiveComponent (traceAdditiveCharacter (L := M) ψ hψ) u hu a := by
  classical
  intro x
  change ψ (adeleTrace (K := k) (((Pi.single u x : InfiniteAdeles M), (0 : FiniteAdeles M)) :
    Adeles M)) = _
  have h : adeleTrace (K := k) (((Pi.single u x : InfiniteAdeles M), (0 : FiniteAdeles M)) :
      Adeles M) = ((Pi.single r (InfiniteExtension.localTrace r u x) : InfiniteAdeles k),
        (0 : FiniteAdeles k)) := by
    refine Prod.ext ?_ ?_
    · exact infiniteAdeleTrace_single r u x
    · exact map_zero (finiteAdeleTrace (K := k) (L := M))
  rw [h]
  have hr' := ha (InfiniteExtension.localTrace r u x)
  rw [ringEquivRealOfIsReal_localTrace r u hr hu x] at hr'
  exact hr'

end Adelic

end Langlands.LocalFactor.NonabelianBrauer
