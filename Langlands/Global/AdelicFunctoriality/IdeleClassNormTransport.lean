import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.AdelicFunctoriality.Isomorphism
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation

/-! # Naturality of the idele-class norm under arithmetic isomorphisms -/

noncomputable section

universe uK uL uK' uL'

set_option autoImplicit false

namespace Langlands.Global.AdelicFunctoriality

open NumberField (RingOfIntegers)
open scoped NumberField

private theorem denseRange_finiteCompletionProduct (L : Type uL) [Field L] [NumberField L] :
    DenseRange (fun x : L => fun q : FinitePlace L => algebraMap L (FiniteCompletion L q) x) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨a, ha⟩ := hne
  obtain ⟨S, V, hV, hVU⟩ := isOpen_pi_iff.mp hU a ha
  obtain ⟨x, hx, _⟩ := exists_algebraMap_mem_open S (fun q => V q.1)
    (fun q => (hV q.1 q.2).1) (fun q => ⟨a q.1, (hV q.1 q.2).2⟩)
    (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.univ_nonempty)
  exact ⟨_, hVU (fun q hq => hx ⟨q, hq⟩), x, rfl⟩

variable {K : Type uK} {L : Type uL} {K' : Type uK'} {L' : Type uL'}
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']

/-- The adelic norm commutes with a square of field isomorphisms.
Continuity and weak approximation let us check each norm on the diagonal. -/
theorem adeleNorm_equiv (e : K ≃+* K') (f : L ≃+* L')
    (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x))
    (x : NumberField.AdeleRing (𝓞 L) L) :
    adeleNorm (K := K') (adeleEquiv f x) = adeleEquiv e (adeleNorm (K := K) x) := by
  have hnorm (y : L) : Algebra.norm K' (f y) = e (Algebra.norm K y) := by
    rw [Algebra.norm_eq_of_equiv_equiv e f (RingHom.ext fun z => (he z).symm) y,
      RingEquiv.apply_symm_apply]
  apply Prod.ext
  · have hdiag (y : L) : infiniteAdeleNorm (K := K) (algebraMap L (NumberField.InfiniteAdeleRing L) y) =
        algebraMap K (NumberField.InfiniteAdeleRing K) (Algebra.norm K y) :=
      congrArg Prod.fst (adeleNorm_principal (K := K) y)
    have hdiag' (y : L') : infiniteAdeleNorm (K := K') (algebraMap L' (NumberField.InfiniteAdeleRing L') y) =
        algebraMap K' (NumberField.InfiniteAdeleRing K') (Algebra.norm K' y) :=
      congrArg Prod.fst (adeleNorm_principal (K := K') y)
    refine congrFun ((NumberField.InfiniteAdeleRing.denseRange_algebraMap L).equalizer
      ((continuous_infiniteAdeleNorm (K := K') (L := L')).comp (continuous_infiniteAdeleEquiv f))
      ((continuous_infiniteAdeleEquiv e).comp (continuous_infiniteAdeleNorm (K := K) (L := L)))
      ?_) x.1
    funext y
    simp only [Function.comp_apply, infiniteAdeleEquiv_diagonal, hdiag, hdiag', hnorm]
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro p
    let transported (z : (q : FinitePlace L) → FiniteCompletion L q) (q : FinitePlace L') :=
      finiteCompletionEquiv f q (z (finitePlaceEquiv f q))
    have hcontinuous : Continuous transported := continuous_pi fun q =>
      (continuous_finiteCompletionEquiv f q).comp (continuous_apply (finitePlaceEquiv f q))
    have hdiag (q : FinitePlace K) (y : L) :
        finiteNormComponent q (fun r => algebraMap L (FiniteCompletion L r) y) =
          algebraMap K (FiniteCompletion K q) (Algebra.norm K y) :=
      congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2 q)
        (adeleNorm_principal (K := K) y)
    have hdiag' (q : FinitePlace K') (y : L') :
        finiteNormComponent q (fun r => algebraMap L' (FiniteCompletion L' r) y) =
          algebraMap K' (FiniteCompletion K' q) (Algebra.norm K' y) :=
      congrArg (fun z : NumberField.AdeleRing (𝓞 K') K' => z.2 q)
        (adeleNorm_principal (K := K') y)
    refine congrFun ((denseRange_finiteCompletionProduct L).equalizer
      ((continuous_finiteNormComponent (L := L') p).comp hcontinuous)
      ((continuous_finiteCompletionEquiv e p).comp
        (continuous_finiteNormComponent (L := L) (finitePlaceEquiv e p))) ?_) (fun r => x.2 r)
    funext y
    have hy : transported (fun r => algebraMap L (FiniteCompletion L r) y) =
        fun r => algebraMap L' (FiniteCompletion L' r) (f y) :=
      funext fun r => finiteCompletionEquiv_coe f r y
    simp only [Function.comp_apply, hy, hdiag, hdiag', finiteCompletionEquiv_coe, hnorm]

/-- The norm on actual idele classes commutes with the two arithmetic isomorphisms. -/
theorem ideleClassNorm_equiv (e : K ≃+* K') (f : L ≃+* L')
    (he : ∀ x, f (algebraMap K L x) = algebraMap K' L' (e x)) (x : IdeleClasses L) :
    ideleClassNorm (K := K') (ideleClassEquiv f x) =
      ideleClassEquiv e (ideleClassNorm (K := K) x) := by
  induction x using Quotient.inductionOn with
  | h y =>
    simp only [ideleClassEquiv_mk, ideleClassNorm_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    exact adeleNorm_equiv e f he y.val

end Langlands.Global.AdelicFunctoriality
