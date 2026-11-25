import Langlands.Automorphic.RankOneHeckeConjugateSelfDual
import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.Automorphic.Unramified.WeakInduction
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.ClassFieldTheory.Global.CohomologyMaps
import Langlands.ClassFieldTheory.Global.IdeleClassPlaceProduct
import Langlands.ClassFieldTheory.Global.RelativeWeilUnramifiedTwist
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Representation.Unramified.WeakTransfer

/-!
# Restricting a Hecke character along an extension of degree one

For an extension `L/K` of number fields of degree one and a Hecke character `ξ` of `L`, the
restriction `ξ ∘ ι` along the idele-class inclusion `ι : C_K → C_L` is a Hecke character of
`K`. Above every place of `K` there is exactly one place of `L`, with ramification index and
inertia degree one, and the local components of `ξ ∘ ι` are those of `ξ` read through the
completion maps. Consequently the `GL(1)` realization of `ξ ∘ ι` is a weak automorphic
induction of `ξ`, its complex-place parameters are those of `ξ` transported to `K`, and the
restriction keeps conjugate inversion when both fields are CM.
-/

noncomputable section

universe u uP

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Langlands.Automorphic.RankOneHecke

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open Langlands.Automorphic.Unramified Langlands.Automorphic.Unramified.WeakInduction
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField NumberField.LiesOver

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The restriction of a Hecke character of `L` to `K` along the idele-class inclusion. -/
def restriction (ξ : HeckeCharacter L) : HeckeCharacter K :=
  ξ.comp (ideleClassInclusion (K := K) (L := L))

/-! ## Places in degree one -/

/-- In degree one, every finite place above `p` has ramification index and inertia degree
with product one. -/
theorem ramificationIdx_mul_inertiaDeg_eq_one (h : Module.finrank K L = 1)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) :
    q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := L) p
  rw [h] at hsum
  have hle : q.1.asIdeal.ramificationIdx (𝓞 K) * q.1.asIdeal.inertiaDeg (𝓞 K) ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun r : FinitePlacesAbove L p =>
      r.1.asIdeal.ramificationIdx (𝓞 K) * r.1.asIdeal.inertiaDeg (𝓞 K))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  have hpos := Nat.mul_pos (q.1.asIdeal.ramificationIdx_pos (𝓞 K))
    (q.1.asIdeal.inertiaDeg_pos (𝓞 K))
  omega

theorem ramificationIdx_eq_one (h : Module.finrank K L = 1)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) :
    q.1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
  (mul_eq_one.mp (ramificationIdx_mul_inertiaDeg_eq_one h p q)).1

theorem inertiaDeg_eq_one (h : Module.finrank K L = 1)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) :
    q.1.asIdeal.inertiaDeg (𝓞 K) = 1 :=
  (mul_eq_one.mp (ramificationIdx_mul_inertiaDeg_eq_one h p q)).2

/-- In degree one, exactly one finite place lies above each finite place. -/
theorem card_finitePlacesAbove (h : Module.finrank K L = 1) (p : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (FinitePlacesAbove L p) = 1 := by
  have hsum := finitePlacesAbove_sum_ramification_inertia (L := L) p
  rw [h, Finset.sum_congr rfl fun q _ => ramificationIdx_mul_inertiaDeg_eq_one h p q,
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at hsum
  exact hsum

theorem finitePlacesAbove_eq (h : Module.finrank K L = 1) {p : HeightOneSpectrum (𝓞 K)}
    (q q' : FinitePlacesAbove L p) : q = q' :=
  Fintype.card_le_one_iff.mp (card_finitePlacesAbove h p).le q q'

/-- In degree one, exactly one infinite place lies above each complex place. -/
theorem card_infinitePlacesAbove (h : Module.finrank K L = 1) (v : NumberField.InfinitePlace K)
    (hv : v.IsComplex) : Fintype.card (InfinitePlacesAbove L v) = 1 := by
  have hsum := infiniteLocalDegree_sum (L := L) v
  rw [h, Finset.sum_congr rfl fun q _ => (Unramified.isUnramified_of_isComplex v hv q).finrank_eq_one v,
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at hsum
  exact hsum

theorem infinitePlacesAbove_eq (h : Module.finrank K L = 1) {v : NumberField.InfinitePlace K}
    (hv : v.IsComplex) (w w' : InfinitePlacesAbove L v) : w = w' :=
  Fintype.card_le_one_iff.mp (card_infinitePlacesAbove h v hv).le w w'

/-! ## Finite components -/

/-- In degree one, the finite component of the restriction at `p` is the component of `ξ` at
the place above `p`, read through the completion map. -/
theorem restriction_finiteComponent (h : Module.finrank K L = 1) (ξ : HeckeCharacter L)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) (a : (p.adicCompletion K)ˣ) :
    (restriction (K := K) ξ).finiteComponent p a =
      ξ.finiteComponent q.1 (Units.map (FiniteExtension.completionMap p q.1).toMonoidHom a) := by
  change ξ (QuotientGroup.mk (ideleInclusion (L := L)
      (IdeleGroup.ofAdicCompletion (𝓞 K) K p a))) = _
  rw [ideleInclusion_ofAdicCompletion, Fintype.prod_eq_single q
    fun r hr => absurd (finitePlacesAbove_eq h r q) hr]
  rfl

/-- In degree one, the uniformizer value of the restriction at `p` is that of `ξ` at the
place above `p`, when `ξ` is unramified there. -/
theorem restriction_finiteUniformizerValue (h : Module.finrank K L = 1) (ξ : HeckeCharacter L)
    (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) (hξ : ξ.IsUnramifiedAt q.1) :
    (restriction (K := K) ξ).finiteUniformizerValue p = ξ.finiteUniformizerValue q.1 := by
  let ϖ : (p.adicCompletion K)ˣ :=
    LocalFactor.PadicAbelian.uniformizerUnit
      (CompletionPadic.padicField p).canonicalTopologicalData
  have hϖ : Valued.v (ϖ : p.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    have h1 := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value
      (CompletionPadic.padicField p).canonicalTopologicalData 1
    rw [zpow_one, Langlands.ClassFieldTheory.Global.RelativeWeilGroup.discreteValuation_padicField p]
      at h1
    exact h1
  change (restriction (K := K) ξ).finiteComponent p ϖ = _
  rw [restriction_finiteComponent h ξ p q ϖ]
  refine HeckeCharacter.finiteComponent_eq_finiteUniformizerValue ξ q.1 hξ _ ?_
  change Valued.v (FiniteExtension.completionMap p q.1 (ϖ : p.adicCompletion K)) = _
  rw [FiniteExtension.valuation_completionMap, ramificationIdx_eq_one h p q, pow_one, hϖ]

/-! ## Infinite components -/

/-- In degree one, the idele equal to `x` at the complex place `v` and to `1` elsewhere maps
to the idele equal to the completion map of `x` at the place above `v` and to `1`
elsewhere. -/
theorem ideleInclusion_infiniteIdeleInclusion (h : Module.finrank K L = 1)
    {v : NumberField.InfinitePlace K} (hv : v.IsComplex) (w : InfinitePlacesAbove L v)
    (x : (InfiniteCompletion K v)ˣ) :
    ideleInclusion (L := L) (infiniteIdeleInclusion K v x) =
      infiniteIdeleInclusion L w.1
        (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w.1)).toMonoidHom x) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext q
    change (adeleInclusion (K := K) (L := L)
        (infiniteIdeleInclusion K v x : AdeleRing (𝓞 K) K)).1 q =
      InfiniteAdeleRing.ofCompletion w.1
        (NumberField.LiesOver.completionMap (v := v) (w := w.1) (x : v.Completion)) q
    rw [adeleInclusion_infinite_apply]
    change infiniteCompletionMap (algebraMap K L) q
        (InfiniteAdeleRing.ofCompletion v (x : v.Completion) (q.comap (algebraMap K L))) = _
    by_cases hq : q = w.1
    · subst hq
      rw [infiniteCompletionMap_comap_eq v w.1, InfiniteAdeleRing.ofCompletion_apply,
        InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have hc : q.comap (algebraMap K L) ≠ v := fun hc =>
        hq (congrArg Subtype.val (infinitePlacesAbove_eq h hv ⟨q, by subst hc; exact ⟨rfl⟩⟩ w))
      rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hc, map_one,
        InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hq]
  · exact map_one (finiteAdeleInclusion (K := K) (L := L))

/-- In degree one, the component of the restriction at a complex place `v` is the component
of `ξ` at the place above `v`, read through the completion map. -/
theorem restriction_infiniteComponent (h : Module.finrank K L = 1) (ξ : HeckeCharacter L)
    {v : NumberField.InfinitePlace K} (hv : v.IsComplex) (w : InfinitePlacesAbove L v)
    (x : (InfiniteCompletion K v)ˣ) :
    (restriction (K := K) ξ).infiniteComponent v x =
      ξ.infiniteComponent w.1
        (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w.1)).toMonoidHom x) := by
  change ξ (ideleClassInclusion (K := K) (L := L)
      (QuotientGroup.mk (infiniteIdeleInclusion K v x))) =
    ξ (QuotientGroup.mk (infiniteIdeleInclusion L w.1 _))
  rw [← ideleInclusion_infiniteIdeleInclusion h hv w x]
  rfl

/-- In degree one, if `ξ` has the parameter `d` at the place `w` above the complex place `v`,
then its restriction has at `v` the parameter `d` read in the coordinates of `v`. -/
theorem restriction_hasComplexPlaceParameter (h : Module.finrank K L = 1)
    {ξ : HeckeCharacter L} (v : {v : NumberField.InfinitePlace K // v.IsComplex})
    (w : InfinitePlacesAbove L v.1) {d : ComplexCharacterData}
    (hd : ξ.HasComplexPlaceParameter (complexPlaceAbove v w) d) :
    (restriction (K := K) ξ).HasComplexPlaceParameter v (normParameter v w d) := by
  intro x
  rw [restriction_infiniteComponent h ξ v.2 w x]
  refine (hd _).trans ?_
  unfold normParameter
  split_ifs with hc
  · congr 1
    apply Units.ext
    exact extensionEmbedding_completionMap_of_comp_eq v.1 w hc (x : v.1.Completion)
  · change d.character _ = d.character (complexConjugation _)
    congr 1
    apply Units.ext
    rw [coe_complexConjugation]
    exact extensionEmbedding_completionMap_of_comp_ne v.1 w hc (x : v.1.Completion)

/-- With a single place above `v`, the Langlands sum of singletons is the singleton of the
transported parameter. -/
theorem complexPlaceLanglandsSum_fin_one (v : {v : NumberField.InfinitePlace K // v.IsComplex})
    (e : Fin 1 ≃ InfinitePlacesAbove L v.1)
    (a : InfinitePlacesAbove L v.1 → ComplexCharacterData) :
    complexPlaceLanglandsSum v e (fun w => [a w]) = [normParameter v (e 0) (a (e 0))] := by
  classical
  by_cases hc : (e 0).1.embedding.comp (algebraMap K L) = v.1.embedding
  · simp only [complexPlaceLanglandsSum, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil, complexPlaceParameterTransport, normParameter, hc,
      ↓reduceIte]
  · simp only [complexPlaceLanglandsSum, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil, complexPlaceParameterTransport, normParameter, hc,
      ↓reduceIte, List.map_cons, List.map_nil]

/-! ## Complex conjugation -/

/-- For CM fields `K ⊆ L`, complex conjugation of `L` restricts to that of `K`. -/
theorem complexConj_algebraMap [IsCMField K] [IsCMField L] (a : K) :
    IsCMField.complexConj L (algebraMap K L a) =
      algebraMap K L (IsCMField.complexConj K a) := by
  obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
  apply φ.injective
  have h1 := IsCMField.complexEmbedding_complexConj K (φ.comp (algebraMap K L)) a
  rw [IsCMField.complexEmbedding_complexConj]
  exact h1.symm

/-- The restriction of a conjugate-inverse Hecke character of a CM field is conjugate
inverse. -/
theorem restriction_ideleClassComplexConj [IsCMField K] [IsCMField L] {ξ : HeckeCharacter L}
    (hξ : ∀ x, ξ (ideleClassComplexConj x) = (ξ x)⁻¹) :
    ∀ x, restriction (K := K) ξ (ideleClassComplexConj x) = (restriction (K := K) ξ x)⁻¹ := by
  intro x
  change ξ (ideleClassInclusion (ideleClassEquiv (IsCMField.complexConj K).toRingEquiv x)) =
    (ξ (ideleClassInclusion x))⁻¹
  rw [Langlands.ClassFieldTheory.Global.ideleClassInclusion_ideleClassEquiv _
    (IsCMField.complexConj L).toRingEquiv (fun a => complexConj_algebraMap a)]
  exact hξ _

/-! ## Algebraic characters -/

/-- Conjugating the data of `z ↦ z^a z̄^b` gives the data of `z ↦ z^b z̄^a`. -/
theorem exponentData_conj (a b : ℤ) : (exponentData a b).conj = exponentData b a := by
  refine ComplexCharacterDataLemmas.ext ?_ (by change -(a - b) = b - a; ring) ?_
  · ext z
    change ((exponentData a b).character (complexConjugation z) : ℂ) =
      ((exponentData b a).character z : ℂ)
    rw [exponentData_character_apply, exponentData_character_apply, coe_complexConjugation,
      starRingEnd_apply, star_star, mul_comm]
  · change ((a + b : ℤ) : ℂ) / 2 = ((b + a : ℤ) : ℂ) / 2
    rw [add_comm a b]

/-- If the archimedean character of `ξ` is the character of the infinity type `t`, then at
every complex place `w` the character `ξ` has the parameter of `z ↦ z^(t σ) z̄^(t σ̄)`, for
the embedding `σ` of `w`. -/
theorem hasComplexPlaceParameter_of_atInfinity [IsTotallyComplex L] {ξ : HeckeCharacter L}
    (t : InfinityType L)
    (ht : ∀ x : (InfiniteAdeles L)ˣ, (ξ.atInfinity x : ℂ) = (InfinityType.toCharacter t x : ℂ))
    (w : {w : NumberField.InfinitePlace L // w.IsComplex}) :
    ξ.HasComplexPlaceParameter w
      (exponentData (t w.1.embedding) (t (ComplexEmbedding.conjugate w.1.embedding))) := by
  classical
  intro y
  apply Units.ext
  have h1 : ξ.infiniteComponent w.1 y =
      ξ.atInfinity (Units.map (InfiniteAdeleRing.ofCompletion w.1) y) := by
    change ξ (ideleClassMap L (infiniteIdeleInclusion L w.1 y)) =
      ξ (ideleClassMap L (infiniteIdelesInclusion L _))
    rw [ComplexPlaceHeckeTwist.infiniteIdelesInclusion_ofCompletion]
  rw [h1, ht, InfinityType.toCharacter_apply, Units.coe_prod, Finset.prod_eq_single w.1]
  · rw [exponentData_character_apply, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, Units.coe_star, InfinityType.coordinate_apply]
    change (extensionEmbedding w.1 (InfiniteAdeleRing.ofCompletion w.1 (y : w.1.Completion) w.1))
        ^ _ * star (extensionEmbedding w.1
          (InfiniteAdeleRing.ofCompletion w.1 (y : w.1.Completion) w.1)) ^ _ =
      (extensionEmbedding w.1 (y : w.1.Completion)) ^ _ *
        star (extensionEmbedding w.1 (y : w.1.Completion)) ^ _
    rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_same]
  · intro τ _ hτ
    have hc : (InfinityType.coordinate τ (Units.map (InfiniteAdeleRing.ofCompletion w.1) y) :
        ℂ) = 1 := by
      rw [InfinityType.coordinate_apply]
      change extensionEmbedding τ (InfiniteAdeleRing.ofCompletion w.1 (y : w.1.Completion) τ) = 1
      rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hτ, map_one]
    have hc' : InfinityType.coordinate τ (Units.map (InfiniteAdeleRing.ofCompletion w.1) y) = 1 :=
      Units.ext hc
    rw [hc', one_zpow, star_one, one_zpow, mul_one, Units.val_one]
  · intro hw
    exact absurd (Finset.mem_univ _) hw

variable [CompactSpace (AdeleQuotient K)]

/-- In degree one, the spectral system of the `GL(1)` realization of the restriction of `ξ`
is weakly induced from `ξ`. -/
theorem presentation_restriction_isWeakInductionOf (h : Module.finrank K L = 1)
    (ξ : HeckeCharacter L) :
    (presentation.{u, uP} (restriction (K := K) ξ)).spectralSystem.IsWeakInductionOf ξ := by
  refine ⟨h.symm, ?_⟩
  obtain ⟨T, hT⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt L ξ
  filter_upwards [Langlands.Unramified.SpectralSystem.eventually_avoidsAbove (F := K) T]
    with p hp hv
  refine ⟨fun q => ⟨ramificationIdx_eq_one h p q, hT q.1 (hp q)⟩, fun ϖ hϖ => ?_⟩
  rw [presentation_eulerPolynomial]
  let q : FinitePlacesAbove L p := placeAbove L p
  unfold inducedEulerPolynomial
  rw [Fintype.prod_eq_single q fun r hr => absurd (finitePlacesAbove_eq h r q) hr,
    inertiaDeg_eq_one h p q, pow_one,
    HeckeCharacter.finiteComponent_eq_finiteUniformizerValue ξ q.1 (hT q.1 (hp q)) (ϖ q) (hϖ q),
    restriction_finiteUniformizerValue h ξ p q (hT q.1 (hp q))]

/-- In degree one, the `GL(1)` realization of the restriction of `ξ` is a weak automorphic
induction of `ξ`. -/
theorem cuspidal_restriction_isWeakAutomorphicInductionOf (h : Module.finrank K L = 1)
    (ξ : HeckeCharacter L) :
    (cuspidal (restriction (K := K) ξ)).isoClass.IsWeakAutomorphicInductionOf.{u, u, uP} ξ :=
  (CuspidalOperatorRealization.IsoClass.isWeakAutomorphicInductionOf_iff _ ξ).mpr
    ⟨presentation.{u, uP} (restriction (K := K) ξ), presentation_restriction_isWeakInductionOf h ξ⟩

end Langlands.Automorphic.RankOneHecke
