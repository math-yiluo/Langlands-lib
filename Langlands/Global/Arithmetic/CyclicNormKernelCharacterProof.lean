import Langlands.ClassField.Global.FundamentalClassProof
import Langlands.ClassField.Global.IdeleClassBaseImage
import Langlands.ClassField.Global.RelativeWeilTransferReciprocityProof
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.Global.AdelicFunctoriality.IdeleNormOpen
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterStatement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Norm-kernel Hecke characters for cyclic number-field extensions -/

noncomputable section

universe uF uE

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open Langlands.ClassField.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality
open scoped BigOperators

/-- Descend the cyclic Galois projection along the surjective Weil transfer. -/
private theorem exists_normReciprocitySameUniverse
    (F E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] :
    ∃ r : IdeleClasses F →* (E ≃ₐ[F] E),
      Function.Surjective r ∧ r.ker = (ideleClassNorm (K := F) (L := E)).toMonoidHom.range := by
  choose I hI using localRelativeClassFormation.{uE}
  have hI' : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    fun p _ => ⟨(hI p).2.1, (hI p).1⟩
  obtain ⟨c, hc⟩ := fundamentalClass_exists I hI'
  obtain ⟨hsurj, hker⟩ := RelativeWeilGroup.relativeWeilTransferReciprocity I hI' c hc F E
  let transfer := RelativeWeilGroup.transfer c F E
  let projection := RelativeWeilGroup.projection c F E
  let inclusion := RelativeWeilGroup.inclusion c F E
  have hle : transfer.ker ≤ projection.ker :=
    hker.le.trans (Abelianization.commutator_subset_ker projection)
  let r := transfer.liftOfSurjective hsurj ⟨projection, hle⟩
  have hr (t : RelativeWeilGroup c F E) : r (transfer t) = projection t :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  have hexact : inclusion.range = projection.ker := RelativeWeilGroup.exact c F E
  refine ⟨r, ?_, ?_⟩
  · intro σ
    obtain ⟨t, ht⟩ := RelativeWeilGroup.projection_surjective c F E σ
    exact ⟨transfer t, (hr t).trans ht⟩
  · ext x
    change r x = 1 ↔ ∃ y, ideleClassNorm (K := F) (L := E) y = x
    constructor
    · obtain ⟨t, rfl⟩ := hsurj x
      rw [hr]
      intro ht
      have hin : t ∈ inclusion.range := hexact.symm ▸ (show t ∈ projection.ker from ht)
      obtain ⟨y, rfl⟩ := hin
      exact ⟨y, (RelativeWeilGroup.transfer_inclusion c F E y).symm⟩
    · rintro ⟨y, rfl⟩
      rw [← RelativeWeilGroup.transfer_inclusion c F E y, hr]
      have hy : inclusion y ∈ inclusion.range := ⟨y, rfl⟩
      exact (hexact ▸ hy : inclusion y ∈ projection.ker)

/-- Compare the two base idele-class groups through the same fixed subgroup of
`C_E`, then transport the norm using the product of Galois conjugates. -/
private theorem exists_normReciprocity
    (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] :
    ∃ r : IdeleClasses F →* (E ≃ₐ[F] E),
      Function.Surjective r ∧ r.ker = (ideleClassNorm (K := F) (L := E)).toMonoidHom.range := by
  let B := (⊥ : IntermediateField F E)
  let autEquiv : (E ≃ₐ[F] E) ≃* (E ≃ₐ[B] E) := baseImageAutEquiv F E
  let : IsCyclic (E ≃ₐ[B] E) := autEquiv.isCyclic.mp inferInstance
  have haction (σ : E ≃ₐ[F] E) (x : IdeleClasses E) :
      relativeIdeleClassAut F E σ x = relativeIdeleClassAut B E (autEquiv σ) x :=
    congrArg (fun e : IdeleClasses E ≃* IdeleClasses E => e x)
      (relativeIdeleClassAut_baseImage F E σ).symm
  obtain ⟨r, hsurj, hker⟩ := exists_normReciprocitySameUniverse B E
  let iF := (ideleClassInclusion (K := F) (L := E)).toMonoidHom
  let iB := (ideleClassInclusion (K := B) (L := E)).toMonoidHom
  have hF := ideleClassGaloisDescent F E
  have hB := ideleClassGaloisDescent B E
  have hrange : iF.range = iB.range := by
    ext x
    change (∃ a, ideleClassInclusion (K := F) (L := E) a = x) ↔
      (∃ b, ideleClassInclusion (K := B) (L := E) b = x)
    rw [← hF.2 x, ← hB.2 x]
    exact autEquiv.toEquiv.forall_congr fun σ =>
      iff_of_eq (congrArg (· = x) (haction σ x))
  let compare : IdeleClasses F ≃* IdeleClasses B :=
    (MonoidHom.ofInjective (f := iF) hF.1).trans
      ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective (f := iB) hB.1).symm)
  have hcompare (x : IdeleClasses F) :
      ideleClassInclusion (K := B) (L := E) (compare x) =
        ideleClassInclusion (K := F) (L := E) x :=
    MonoidHom.apply_ofInjective_symm (f := iB) hB.1 _
  have hnorm (x : IdeleClasses E) :
      compare (ideleClassNorm (K := F) (L := E) x) = ideleClassNorm (K := B) (L := E) x := by
    let : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
    let : Fintype (E ≃ₐ[B] E) := Fintype.ofFinite _
    apply hB.1
    rw [hcompare, ideleClassNormGaloisProduct F E, ideleClassNormGaloisProduct B E]
    exact Fintype.prod_equiv autEquiv.toEquiv
      (fun σ => relativeIdeleClassAut F E σ x)
      (fun σ => relativeIdeleClassAut B E σ x) fun σ => haction σ x
  refine ⟨autEquiv.symm.toMonoidHom.comp (r.comp compare.toMonoidHom),
    autEquiv.symm.surjective.comp (hsurj.comp compare.surjective), ?_⟩
  ext x
  change autEquiv.symm (r (compare x)) = 1 ↔
    ∃ y, ideleClassNorm (K := F) (L := E) y = x
  rw [← autEquiv.symm.map_one, autEquiv.symm.injective.eq_iff, ← MonoidHom.mem_ker, hker]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, compare.injective ((hnorm y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (hnorm y).symm⟩

/-- The norm quotient has a faithful Hecke character of order `[E : F]`.
The powers of every such character exhaust the characters trivial on norms. -/
theorem cyclicNormKernelCharacter : CyclicNormKernelCharacterStatement.{uF, uE} := by
  intro F E _ _ _ _ _ _ _
  let norm := ideleClassNorm (K := F) (L := E)
  let N := norm.toMonoidHom.range
  let : N.Normal := ⟨fun a ha b => by rwa [mul_comm b a, mul_inv_cancel_right]⟩
  let Q := IdeleClasses F ⧸ N
  let q : IdeleClasses F →* Q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hqker (x : IdeleClasses F) : q x = 1 ↔ x ∈ Set.range norm :=
    QuotientGroup.eq_one_iff x
  have hopen : IsOpen (N : Set (IdeleClasses F)) := by
    change IsOpen (Set.range norm)
    rw [← Set.image_univ]
    exact isOpenMap_ideleClassNorm _ isOpen_univ
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hopen
  obtain ⟨r, hr, hker⟩ := exists_normReciprocity F E
  let equiv : Q ≃* (E ≃ₐ[F] E) :=
    (QuotientGroup.quotientMulEquivOfEq (show N = r.ker from hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  let n := Module.finrank F E
  let : NeZero n := ⟨Module.finrank_pos.ne'⟩
  have hcard : Nat.card Q = n :=
    (Nat.card_congr equiv.toEquiv).trans (IsGalois.card_aut_eq_finrank F E)
  let : IsCyclic Q := equiv.isCyclic.mpr inferInstance
  let rootsEquiv : Q ≃* rootsOfUnity n ℂ :=
    mulEquivOfCyclicCardEq (hcard.trans (Complex.card_rootsOfUnity n).symm)
  let faithful : Q →* ℂˣ := (rootsOfUnity n ℂ).subtype.comp rootsEquiv.toMonoidHom
  have hfaithful : Function.Injective faithful :=
    Subtype.val_injective.comp rootsEquiv.injective
  let η₀ : HeckeCharacter F :=
    { toMonoidHom := faithful.comp q
      continuous_toFun := (continuous_of_discreteTopology : Continuous faithful).comp
        (QuotientGroup.continuous_mk : Continuous q) }
  refine ⟨⟨η₀, ?_⟩, ?_⟩
  · intro x
    change faithful (q x) = 1 ↔ x ∈ Set.range norm
    rw [← faithful.map_one, hfaithful.eq_iff, hqker]
  let descend (χ : HeckeCharacter F) (hχ : χ.IsTrivialOnNorm E) : Q →* ℂˣ :=
    QuotientGroup.lift N χ.toMonoidHom (by
      rintro _ ⟨y, rfl⟩
      exact hχ y)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  have hgOrder : orderOf g = n := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  intro η hη
  let ηQ := descend η hη.isTrivialOnNorm
  have hηQ : Function.Injective ηQ := by
    apply ηQ.ker_eq_bot_iff.mp
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨x, rfl⟩ := hq z
    exact (hqker x).2 ((hη x).1 hz)
  have hηOrder : orderOf (ηQ g) = n := (orderOf_injective ηQ hηQ g).trans hgOrder
  constructor
  · apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hη.isTrivialOnNorm.pow_finrank_eq_one E))
    change n ∣ orderOf η
    rw [← hηOrder]
    apply orderOf_dvd_of_pow_eq_one
    obtain ⟨x, hx⟩ := hq g
    rw [← hx]
    change (η x) ^ orderOf η = 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun, Pi.one_apply]
      using congrArg (fun χ : HeckeCharacter F => χ x) (pow_orderOf_eq_one η)
  · intro χ
    constructor
    · intro hχ
      let χQ := descend χ hχ
      have hprim : IsPrimitiveRoot (ηQ g) n := hηOrder ▸ IsPrimitiveRoot.orderOf (ηQ g)
      have hroot : χQ g ∈ rootsOfUnity n ℂ := by
        rw [mem_rootsOfUnity, ← map_pow, ← hgOrder, pow_orderOf_eq_one, map_one]
      obtain ⟨i, hi, hpow⟩ := hprim.eq_pow_of_mem_rootsOfUnity hroot
      have hχQ : χQ = ηQ ^ i := (MonoidHom.eq_iff_eq_on_generator hg _ _).mpr (by
        simpa only [MonoidHom.pow_apply] using hpow.symm)
      refine ⟨i, hi, ContinuousMonoidHom.ext fun x => ?_⟩
      rw [ContinuousMonoidHom.pow_apply]
      change χQ (q x) = ηQ (q x) ^ i
      simpa only [MonoidHom.pow_apply] using DFunLike.congr_fun hχQ (q x)
    · rintro ⟨i, _, rfl⟩ x
      rw [ContinuousMonoidHom.pow_apply, hη.isTrivialOnNorm x, one_pow]

end Langlands.Global.HeckeCharacter
