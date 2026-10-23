import Langlands.ClassField.Global.IdeleClassNormGaloisProductStatement
import Mathlib.RingTheory.Norm.Transitivity

/-! # Proof of the Galois product formula for the idele-class norm -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField BigOperators
open Langlands.Global.AdelicFunctoriality

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]

omit [NumberField K] [NumberField L] [IsGalois K L] in
private theorem relative_finitePlace_under (σ : L ≃ₐ[K] L)
    (q : HeightOneSpectrum (𝓞 L)) :
    (finitePlaceEquiv σ.toRingEquiv q).under (𝓞 K) = q.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro x
  change RingOfIntegers.mapRingEquiv σ.toRingEquiv (algebraMap (𝓞 K) (𝓞 L) x) ∈
    q.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ q.asIdeal
  have h : RingOfIntegers.mapRingEquiv σ.toRingEquiv (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K) (𝓞 L) x := by
    apply RingOfIntegers.coe_injective
    exact σ.commutes (x : K)
  rw [h]

private theorem finite_galois_product [Fintype (L ≃ₐ[K] L)]
    (a : FiniteAdeleRing (𝓞 L) L) (q : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleInclusion (finiteAdeleNorm (K := K) a) q =
      ∏ σ : L ≃ₐ[K] L, finiteAdeleEquiv σ.toRingEquiv a q := by
  let p := q.under (𝓞 K)
  let r (σ : L ≃ₐ[K] L) : FinitePlacesAbove L p :=
    ⟨finitePlaceEquiv σ.toRingEquiv q, ⟨congrArg HeightOneSpectrum.asIdeal
      (relative_finitePlace_under σ q).symm⟩⟩
  let f (b : (w : FinitePlacesAbove L p) → w.1.adicCompletion L) :=
    FiniteExtension.completionMap p q
      (∏ w : FinitePlacesAbove L p, FiniteExtension.localNorm p w.1 (b w))
  let g (b : (w : FinitePlacesAbove L p) → w.1.adicCompletion L) :=
    ∏ σ : L ≃ₐ[K] L, finiteCompletionEquiv σ.toRingEquiv q (b (r σ))
  have hf : Continuous f :=
    (FiniteExtension.continuous_completionMap p q).comp
      (continuous_finsetProd _ fun w _ =>
        (FiniteExtension.continuous_localNorm p w.1).comp (continuous_apply w))
  have hg : Continuous g := continuous_finsetProd _ fun σ _ =>
    (continuous_finiteCompletionEquiv σ.toRingEquiv q).comp (continuous_apply (r σ))
  have hfg : f = g := (denseRange_finiteAbove (L := L) p).equalizer hf hg (by
    funext x
    dsimp [f, g, r]
    rw [finiteNorm_principal_of_bijective p ((completedTensorComparison K L).1 p),
      FiniteExtension.completionMap_coe, Algebra.norm_eq_prod_automorphisms,
      map_prod]
    apply Finset.prod_congr (by ext; simp)
    intro σ _
    exact (finiteCompletionEquiv_coe σ.toRingEquiv q x).symm)
  exact congrFun hfg (fun w => a w.1)

private theorem infinite_galois_product [Fintype (L ≃ₐ[K] L)]
    (a : InfiniteAdeleRing L) :
    infiniteAdeleMap (algebraMap K L) (infiniteAdeleNorm (K := K) a) =
      ∏ σ : L ≃ₐ[K] L, infiniteAdeleEquiv σ.toRingEquiv a := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap L).equalizer
    ((continuous_infiniteAdeleMap (algebraMap K L)).comp
      (continuous_infiniteAdeleNorm (K := K) (L := L)))
    (continuous_finsetProd Finset.univ fun (σ : L ≃ₐ[K] L) _ => continuous_infiniteAdeleEquiv σ.toRingEquiv)
    (by
      funext x
      have hn : infiniteAdeleNorm (K := K)
          (algebraMap L (InfiniteAdeleRing L) x) =
          algebraMap K (InfiniteAdeleRing K) (Algebra.norm K x) :=
        congrArg Prod.fst (adeleNorm_principal (K := K) x)
      dsimp only [Function.comp_apply]
      rw [hn, infiniteAdeleMap_diagonal, Algebra.norm_eq_prod_automorphisms, map_prod]
      apply Finset.prod_congr (by ext; simp)
      intro σ _
      exact (infiniteAdeleEquiv_diagonal σ.toRingEquiv x).symm)
  exact congrFun h a

private theorem adele_galois_product [Fintype (L ≃ₐ[K] L)]
    (a : AdeleRing (𝓞 L) L) :
    adeleInclusion (adeleNorm (K := K) a) =
      ∏ σ : L ≃ₐ[K] L, adeleEquiv σ.toRingEquiv a := by
  apply Prod.ext
  · exact (infinite_galois_product (K := K) a.1).trans
      (map_prod (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
        (fun σ : L ≃ₐ[K] L => adeleEquiv σ.toRingEquiv a) Finset.univ).symm
  · have h : finiteAdeleInclusion (finiteAdeleNorm (K := K) a.2) =
        ∏ σ : L ≃ₐ[K] L, finiteAdeleEquiv σ.toRingEquiv a.2 := by
      apply FiniteAdeleRing.ext
      intro q
      exact (finite_galois_product a.2 q).trans
        (map_prod (RestrictedProduct.evalMonoidHom _ q)
          (fun σ : L ≃ₐ[K] L => finiteAdeleEquiv σ.toRingEquiv a.2) Finset.univ).symm
    exact h.trans
      (map_prod (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
        (fun σ : L ≃ₐ[K] L => adeleEquiv σ.toRingEquiv a) Finset.univ).symm

/-- The actual quotient norm, followed by inclusion, is the Galois product. -/
theorem ideleClassNormGaloisProduct : IdeleClassNormGaloisProduct.{u, v} := by
  classical
  intro K L _ _ _ _ _ _
  let : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  intro x
  refine QuotientGroup.induction_on x fun a => ?_
  rw [ideleClassNorm_mk, ideleClassInclusion_mk]
  have h : ideleInclusion (ideleNorm (K := K) a) =
      ∏ σ : L ≃ₐ[K] L, ideleEquiv σ.toRingEquiv a := by
    apply Units.ext
    change adeleInclusion (adeleNorm (K := K) a.val) =
      (Units.coeHom _) (∏ σ : L ≃ₐ[K] L, ideleEquiv σ.toRingEquiv a)
    rw [map_prod]
    exact adele_galois_product (K := K) a.val
  rw [h]
  exact map_prod (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)) _ _

end Langlands.ClassField.Global
