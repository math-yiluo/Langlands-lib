import Langlands.ClassField.Global.CompletionTower
import Langlands.ClassField.Global.CyclicReciprocityParts
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.ReciprocityTower
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof
import Mathlib.RingTheory.Complex

/-! # The Hasse norm theorem for cyclic number-field extensions -/

noncomputable section

universe u

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.LiesOver Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

namespace Langlands.Global

open AdelicFunctoriality
open ClassField.Global ClassFieldTheory.Local CyclicClassAlgebra

private theorem nonempty_cyclicCoordinate (G : Type u) [Group G] [Finite G] [IsCyclic G] :
    Nonempty (G ≃* Multiplicative (ZMod (Nat.card G))) := by
  let n := Nat.card G
  let : NeZero n := ⟨Nat.card_pos.ne'⟩
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := G)
  have hg : orderOf g = n := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hmod (m : ℕ) : g ^ (m % n) = g ^ m := by rw [← hg, pow_mod_orderOf]
  let f : Multiplicative (ZMod n) →* G :=
    { toFun := fun z => g ^ z.toAdd.val
      map_one' := by simp
      map_mul' := fun z w => by
        change g ^ (z.toAdd + w.toAdd).val = g ^ z.toAdd.val * g ^ w.toAdd.val
        rw [ZMod.val_add, hmod, pow_add] }
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr (hgen x)
    refine ⟨Multiplicative.ofAdd (m : ZMod n), ?_⟩
    change g ^ ((m : ZMod n).val) = x
    rw [ZMod.val_natCast, hmod]
    exact hm
  have hbij := hsur.bijective_of_nat_card_le (by rw [Nat.card_eq_fintype_card (α := Multiplicative (ZMod n)), Fintype.card_multiplicative, ZMod.card])
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual determinant norm from a complex completion to a real completion is
nonnegative under the real completion embedding. -/
theorem extensionEmbedding_localNorm_real_nonneg {F E : Type u} [Field F] [Field E]
    [Algebra F E] {v : InfinitePlace F} {w : InfinitePlace E} [w.LiesOver v]
    (hv : v.IsReal) (hw : w.IsComplex) (x : w.Completion) :
    0 ≤ (InfinitePlace.Completion.extensionEmbedding v (InfiniteExtension.localNorm v w x)).re := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let d := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let h := InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  have hcompat : (algebraMap ℝ ℂ).comp e.toRingHom =
      d.toRingHom.comp (algebraMap v.Completion w.Completion) := by
    apply RingHom.ext
    intro y
    change ↑(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv y) =
      InfinitePlace.Completion.extensionEmbedding w (algebraMap v.Completion w.Completion y)
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact (congrArg (fun f : v.Completion →+* ℂ => f y) h.over).symm
  have hn := Algebra.norm_eq_of_equiv_equiv e d hcompat x
  rw [Algebra.norm_complex_apply] at hn
  change 0 ≤ (InfinitePlace.Completion.extensionEmbedding v (Algebra.norm v.Completion x)).re
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, Complex.ofReal_re]
  change 0 ≤ e (Algebra.norm v.Completion x)
  rw [hn, RingEquiv.apply_symm_apply]
  exact Complex.normSq_nonneg _

/-- A unit is a global norm from a finite cyclic extension of number fields if its images
are norms from the actual field extensions at every pair of places. -/
def CyclicNumberFieldHasseNormStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [IsCyclic Gal(E/F)] (a : Fˣ),
    (∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
      Units.map (algebraMap F (v.adicCompletion F)) a ∈
        (FiniteExtension.localUnitNorm v w).toMonoidHom.range) →
    (∀ (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v],
      Units.map (algebraMap F v.Completion) a ∈
        (InfiniteExtension.localUnitNorm v w).toMonoidHom.range) →
    a ∈ LocalClassField.normSubgroup F E

/-- The local norm hypotheses kill the carry class, and the norm criterion turns the
vanishing of that global class into a global norm. -/
theorem cyclicNumberFieldHasseNorm : CyclicNumberFieldHasseNormStatement.{u} := by
  classical
  intro F E _ _ _ _ _ _ _ _ a hfin hinf
  let n := Nat.card Gal(E/F)
  let : NeZero n := ⟨Nat.card_pos.ne'⟩
  obtain ⟨χ⟩ := nonempty_cyclicCoordinate Gal(E/F)
  apply (cyclicClass_eq_zero_iff χ a).mp
  apply Reciprocity.eq_zero_of_local_eq_zero ideleClassH1Vanishing
    (fun p _ => localInvariantFamily unramifiedH2Exhaustion p)
    (fun p _ => localInvariantFamilyRelativeImages unramifiedH2Exhaustion p)
  · intro v w hw
    let K := v.adicCompletion F
    let M := w.adicCompletion E
    let : FiniteDimensional K M := FiniteExtension.local_finite v w
    let : IsGalois K M := isGalois_adicCompletion v w
    rw [CompletionTower.unitsLocalMap_cyclicClass]
    exact (cyclicClass_eq_zero_iff_of_injective _
      (χ.injective.comp (decompositionHom_injective v w)) _).mpr (hfin v w)
  · intro w
    by_cases ht : ∀ c ∈ MulAction.stabilizer Gal(E/F) w, c = 1
    · exact CyclicReciprocity.archimedeanInvariant_eq_zero_of_stabilizer w ht _
    push Not at ht
    obtain ⟨c, hc, hc₁⟩ := ht
    have hcj := Reciprocity.isConj_of_mem_stabilizer w hc hc₁
    have hw : w.IsComplex := by
      apply InfinitePlace.not_isReal_iff_isComplex.mp
      intro hr
      apply hc₁
      apply AlgEquiv.ext
      intro x
      apply w.embedding.injective
      exact (hcj.eq x).trans (congrArg (fun p : E →+* ℂ => p x)
        (InfinitePlace.conjugate_embedding_eq_of_isReal hr))
    let v := w.comap (algebraMap F E)
    let : w.LiesOver v := ⟨rfl⟩
    have hv : v.IsReal := by
      change (w.comap (algebraMap F E)).IsReal
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
      exact hcj.isReal_comp
    obtain ⟨b, hb⟩ := hinf v w
    have hN := extensionEmbedding_localNorm_real_nonneg hv hw (b : w.Completion)
    have hbval := congrArg Units.val hb
    change InfiniteExtension.localNorm v w (b : w.Completion) =
      algebraMap F v.Completion (a : F) at hbval
    rw [hbval, extensionEmbedding_algebraMap] at hN
    rw [CyclicReciprocity.archimedeanInvariant_cyclicClass w χ.toMonoidHom χ.injective a c hc hc₁,
      CyclicReciprocity.re_embedding_algebraMap w v, ite_eq_right (not_lt.mpr hN)]

end Langlands.Global
