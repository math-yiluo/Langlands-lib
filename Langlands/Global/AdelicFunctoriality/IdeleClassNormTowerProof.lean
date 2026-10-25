import Langlands.Global.AdelicFunctoriality.IdeleClassNormLawsStatement
import Mathlib.RingTheory.Norm.Transitivity

/-! # Tower transitivity of the actual idele-class norm -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain
open scoped NumberField

universe u v w

/-- Weak approximation in the unrestricted product of the actual finite completions. -/
private theorem denseRange_finiteCompletionProduct (K : Type u) [Field K] [NumberField K] :
    DenseRange (fun x : K => fun p : HeightOneSpectrum (𝓞 K) =>
      algebraMap K (p.adicCompletion K) x) := by
  classical
  have hfinite (I : Finset (HeightOneSpectrum (𝓞 K))) :
      DenseRange (fun x : K => fun p : I => algebraMap K (p.1.adicCompletion K) x) := by
    have h := AbsoluteValue.denseRange_algebraMap_pi
      (v := fun p : I => NumberField.HeightOneSpectrum.adicAbv K p.1)
      (fun p => finiteAdicAbv_isNontrivial p.1)
      (fun p q hpq h => hpq (Subtype.ext ((finiteAdicAbv_isEquiv_iff p.1 q.1).mp h)))
    exact (DenseRange.piMap (fun p : I => finiteWithAbsEmbedding_denseRange p.1)).comp h
      (.piMap fun p => (finiteWithAbsEmbedding_isometry p.1).continuous)
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨a, ha⟩ := hne
  obtain ⟨I, V, hV, hVU⟩ := isOpen_pi_iff.mp hU a ha
  have hopen : IsOpen (Set.univ.pi (fun p : I => V p.1)) :=
    isOpen_set_pi Set.finite_univ (fun p _ => (hV p.1 p.2).1)
  have hnonempty : (Set.univ.pi (fun p : I => V p.1)).Nonempty :=
    ⟨fun p => a p.1, fun p _ => (hV p.1 p.2).2⟩
  obtain ⟨x, hx⟩ := (hfinite I).exists_mem_open hopen hnonempty
  exact ⟨_, hVU (fun p hp => hx ⟨p, hp⟩ (Set.mem_univ _)), x, rfl⟩

section Tower

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [Field L] [Field M] [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

private theorem finiteNormComponent_principal (p : HeightOneSpectrum (𝓞 K)) (x : L) :
    finiteNormComponent p (fun q => algebraMap L (q.adicCompletion L) x) =
      algebraMap K (p.adicCompletion K) (Algebra.norm K x) := by
  exact congrArg (fun a : AdeleRing (𝓞 K) K => a.2 p) (adeleNorm_principal (K := K) x)

/-- Transitivity at a finite coordinate, proved in the unrestricted product topology. -/
theorem finiteNormComponent_tower (p : HeightOneSpectrum (𝓞 K))
    (a : (r : HeightOneSpectrum (𝓞 M)) → r.adicCompletion M) :
    finiteNormComponent p a =
      finiteNormComponent (L := L) p (fun q => finiteNormComponent q a) := by
  have h := (denseRange_finiteCompletionProduct M).equalizer
    (continuous_finiteNormComponent (L := M) p)
    ((continuous_finiteNormComponent (L := L) p).comp
      (continuous_pi fun q => continuous_finiteNormComponent (L := M) q)) ?_
  · exact congrFun h a
  · funext x
    simp only [Function.comp_apply, finiteNormComponent_principal, Algebra.norm_norm]

/-- Transitivity of the infinite-adele norm, by weak approximation. -/
theorem infiniteAdeleNorm_tower (a : InfiniteAdeleRing M) :
    infiniteAdeleNorm (K := K) (L := M) a =
      infiniteAdeleNorm (K := K) (L := L) (infiniteAdeleNorm (K := L) (L := M) a) := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap M).equalizer
    (continuous_infiniteAdeleNorm (K := K) (L := M))
    ((continuous_infiniteAdeleNorm (K := K) (L := L)).comp
      (continuous_infiniteAdeleNorm (K := L) (L := M))) ?_
  · exact congrFun h a
  · funext x
    change infiniteAdeleNorm (K := K) (L := M) (algebraMap M (InfiniteAdeleRing M) x) =
      infiniteAdeleNorm (K := K) (L := L)
        (infiniteAdeleNorm (K := L) (L := M) (algebraMap M (InfiniteAdeleRing M) x))
    rw [show infiniteAdeleNorm (K := L) (L := M) (algebraMap M (InfiniteAdeleRing M) x) =
      algebraMap L (InfiniteAdeleRing L) (Algebra.norm L x) from
        congrArg Prod.fst (adeleNorm_principal (K := L) x)]
    rw [show infiniteAdeleNorm (K := K) (L := L)
        (algebraMap L (InfiniteAdeleRing L) (Algebra.norm L x)) =
      algebraMap K (InfiniteAdeleRing K) (Algebra.norm K (Algebra.norm L x)) from
        congrArg Prod.fst (adeleNorm_principal (K := K) (Algebra.norm L x))]
    rw [Algebra.norm_norm]
    exact congrArg Prod.fst (adeleNorm_principal (K := K) x)

/-- Transitivity on the actual adele rings. -/
theorem adeleNorm_tower (a : AdeleRing (𝓞 M) M) :
    adeleNorm (K := K) (L := M) a =
      adeleNorm (K := K) (L := L) (adeleNorm (K := L) (L := M) a) := by
  apply Prod.ext
  · exact infiniteAdeleNorm_tower (L := L) a.1
  · apply FiniteAdeleRing.ext
    intro p
    exact finiteNormComponent_tower (L := L) p a.2

/-- Transitivity on actual idele units. -/
theorem ideleNorm_tower (a : IdeleGroup (𝓞 M) M) :
    ideleNorm (K := K) (L := M) a =
      ideleNorm (K := K) (L := L) (ideleNorm (K := L) (L := M) a) := by
  apply Units.ext
  exact adeleNorm_tower (L := L) (a : AdeleRing (𝓞 M) M)

end Tower

/-- The actual idele-class norm is transitive for every compatible number-field tower. -/
theorem ideleClassNormTower : IdeleClassNormTower.{u, v, w} := by
  intro K L M _ _ _ _ _ _ _ _ _ _ x
  induction x using Quotient.inductionOn with
  | h a =>
    simp only [ideleClassNorm_mk]
    exact congrArg QuotientGroup.mk (ideleNorm_tower (K := K) (L := L) a)

end Langlands.Global.AdelicFunctoriality
