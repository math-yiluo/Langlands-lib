import Langlands.Global.Arithmetic.HarrisCyclicDescentCorrectionStatement
import Langlands.Global.Arithmetic.CharacterPrescriptionAssembly
import Langlands.Global.Arithmetic.CMHalfWeightLocalNormControl
import Langlands.Global.Arithmetic.SUnitIdeleTopology
import Langlands.Global.NormOneIdeleClassCompact
import Langlands.ClassFieldTheory.Global.IdeleClassNormGaloisProductProof
import Langlands.ClassFieldTheory.Global.PrincipalIdeleUnits
import Langlands.ClassFieldTheory.Global.CohomologyMaps

/-! # Extending a finite real-subfield character to a CM field -/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.Harris.CMFiniteRealCharacterExtension

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum _root_.Topology
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Global
open scoped NumberField

section Conjugation

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

/-- The arithmetic CM involution on the actual ideles. -/
abbrev ideleConj : Ideles E ≃ₜ* Ideles E := ideleEquiv (IsCMField.complexConj E).toRingEquiv

/-- The idele CM involution is an involution. -/
theorem ideleConj_ideleConj (x : Ideles E) : ideleConj (ideleConj x) = x := by
  have h : (IsCMField.complexConj E).toRingEquiv.trans
      (IsCMField.complexConj E).toRingEquiv = RingEquiv.refl E := by
    ext a
    exact IsCMField.complexConj_apply_apply E a
  have hh := ideleEquiv_trans (IsCMField.complexConj E).toRingEquiv
    (IsCMField.complexConj E).toRingEquiv
  rw [h, ideleEquiv_refl] at hh
  exact (DFunLike.congr_fun hh x).symm

/-- Included real-subfield ideles are fixed by the idele CM involution. -/
theorem ideleConj_ideleInclusion (r : Ideles (maximalRealSubfield E)) :
    ideleConj (ideleInclusion (L := E) r) = ideleInclusion r := by
  apply Units.ext
  have h := adeleInclusion_adeleEquiv (E := maximalRealSubfield E) (L := E)
    (RingEquiv.refl _) (IsCMField.complexConj E).toRingEquiv
    (fun a => (IsCMField.complexConj E).commutes a) r.val
  rw [adeleEquiv_refl] at h
  exact h.symm

/-- On principal ideles the idele CM involution is the field involution. -/
theorem ideleConj_diagonalUnits (a : Eˣ) :
    ideleConj (diagonalUnits E a) =
      diagonalUnits E (Units.mapEquiv (IsCMField.complexConj E).toRingEquiv.toMulEquiv a) :=
  ideleEquiv_diagonal _ a

end Conjugation

section Local

variable {F : Type u} {E : Type u} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E]

/-- Every neighbourhood of one in a finite local unit group contains an open subgroup. -/
theorem exists_openSubgroup_subset (q : FinitePlace E) {U : Set (FiniteCompletion E q)ˣ}
    (hU : U ∈ 𝓝 1) :
    ∃ W : OpenSubgroup (FiniteCompletion E q)ˣ, (W : Set (FiniteCompletion E q)ˣ) ⊆ U := by
  let : ValuativeRel (FiniteCompletion E q) :=
    (CompletionPadic.topologicalData q).valuativeRel
  let : IsNonarchimedeanLocalField (FiniteCompletion E q) :=
    (CompletionPadic.topologicalData q).localField
  let : TotallyDisconnectedSpace (FiniteCompletion E q) := inferInstance
  let : TotallyDisconnectedSpace (FiniteCompletion E q)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  obtain ⟨W, _, hW⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
  exact ⟨W, hW⟩

/-- Every neighbourhood of one in the base completion's unit group contains the preimage of some
open subgroup of the extension completion's unit group under the completed inclusion. -/
theorem exists_openSubgroup_pullback (p : FinitePlace F) (q : FinitePlace E)
    [q.asIdeal.LiesOver p.asIdeal] {t : Set (FiniteCompletion F p)ˣ} (ht : t ∈ 𝓝 1) :
    ∃ B : OpenSubgroup (FiniteCompletion E q)ˣ,
      ∀ a : (FiniteCompletion F p)ˣ, CMHalfWeight.completionUnitInclusion p q a ∈ B → a ∈ t := by
  have hemb := CMHalfWeight.isEmbedding_completionUnitInclusion p q
  rw [hemb.isInducing.nhds_eq_comap, map_one] at ht
  obtain ⟨U, hU, hUt⟩ := ht
  obtain ⟨B, hB⟩ := exists_openSubgroup_subset q hU
  exact ⟨B, fun a ha => hUt (hB ha)⟩

/-- An idele of the base whose inclusion is integral is integral. -/
theorem mem_integralIdeles_of_ideleInclusion {r : Ideles F}
    (hr : ideleInclusion (L := E) r ∈ integralIdeles E) : r ∈ integralIdeles F := by
  intro p
  let q := placeAbove E p
  let : q.1.asIdeal.LiesOver p.asIdeal := q.2
  have h := hr q.1
  change Valued.v (ideleCoordinate q.1 (ideleInclusion (L := E) r) :
    FiniteCompletion E q.1) = 1 at h
  rw [CMHalfWeight.ideleCoordinate_ideleInclusion p q.1 r] at h
  change Valued.v (FiniteExtension.completionMap p q.1
    (ideleCoordinate p r : FiniteCompletion F p)) = 1 at h
  rw [FiniteExtension.valuation_completionMap] at h
  have he := (q.1.asIdeal.ramificationIdx_pos (𝓞 F)).ne'
  exact le_antisymm ((pow_le_one_iff_of_nonneg zero_le he).mp h.le)
    ((one_le_pow_iff_of_nonneg zero_le he).mp h.ge)

end Local

section Places

variable (E : Type u) [Field E] [NumberField E]

/-- A number field has a finite place, since its ring of integers is not a field. -/
theorem nonempty_finitePlace : Nonempty (FinitePlace E) := by
  obtain ⟨P, hP, hPr⟩ :=
    (Ring.not_isField_iff_exists_prime (R := 𝓞 E)).mp (RingOfIntegers.not_isField E)
  exact ⟨⟨P, hPr, hP⟩⟩

/-- The coordinate at a finite place of the principal idele of a global unit. -/
def unitCoordinate (w : FinitePlace E) (ζ : (𝓞 E)ˣ) : (FiniteCompletion E w)ˣ :=
  ideleCoordinate w (diagonalUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom ζ))

/-- Distinct global units have distinct coordinates at every finite place. -/
theorem unitCoordinate_injective (w : FinitePlace E) : Function.Injective (unitCoordinate E w) := by
  intro ζ ξ h
  have h' := congrArg (fun x : (FiniteCompletion E w)ˣ => (x : FiniteCompletion E w)) h
  change algebraMap E (FiniteCompletion E w) ((ζ : 𝓞 E) : E) =
    algebraMap E (FiniteCompletion E w) ((ξ : 𝓞 E) : E) at h'
  exact Units.ext (RingOfIntegers.ext ((algebraMap E (FiniteCompletion E w)).injective h'))

/-- One finite place and an open subgroup there meeting no nontrivial root of unity. -/
theorem exists_torsion_separating :
    ∃ (w : FinitePlace E) (B : OpenSubgroup (FiniteCompletion E w)ˣ),
      ∀ ζ : (𝓞 E)ˣ, ζ ∈ Units.torsion E → unitCoordinate E w ζ ∈ B → ζ = 1 := by
  classical
  obtain ⟨w⟩ := nonempty_finitePlace E
  let S : Set (FiniteCompletion E w)ˣ :=
    (fun ζ : Units.torsion E => unitCoordinate E w ζ) '' {ζ | ζ ≠ 1}
  have hS : S.Finite := Set.toFinite _
  have hU : Sᶜ ∈ 𝓝 (1 : (FiniteCompletion E w)ˣ) := by
    apply hS.isClosed.isOpen_compl.mem_nhds
    rintro ⟨ζ, hζ, hζ1⟩
    apply hζ
    apply Subtype.ext
    apply unitCoordinate_injective E w
    refine hζ1.trans ?_
    apply Units.ext
    rfl
  obtain ⟨B, hB⟩ := exists_openSubgroup_subset w hU
  refine ⟨w, B, fun ζ hζ hB' => ?_⟩
  by_contra hne
  exact hB hB' ⟨⟨ζ, hζ⟩, fun h => hne (congrArg Subtype.val h), rfl⟩

end Places

section Box

open Langlands.Global.Arithmetic

variable {K : Type u} [Field K] [NumberField K]

/-- Integral ideles are the S-unit ideles for the empty set of places. -/
theorem mem_sUnitIdeles_empty_of_integral {z : Ideles K} (hz : z ∈ integralIdeles K) :
    z ∈ IdeleSUnits.sUnitIdeles K ∅ :=
  IdeleSUnits.mem_sUnitIdeles_iff.2 fun v _ =>
    (IdeleSUnits.ideleExponent_eq_one_iff v z).2 (hz v)

/-- An open subgroup containing the whole archimedean factor contains every
integral idele whose coordinates at finitely many finite places lie in given
neighbourhoods of one. -/
theorem exists_integral_box (U : Subgroup (Ideles K)) (hU : IsOpen (U : Set (Ideles K)))
    (hinf : ∀ a, infiniteIdelesInclusion K a ∈ U) :
    ∃ (I : Finset (FinitePlace K)) (t : (p : FinitePlace K) → Set (FiniteCompletion K p)ˣ),
      (∀ p, t p ∈ 𝓝 1) ∧
      ∀ z ∈ integralIdeles K, (∀ p ∈ I, ideleCoordinate p z ∈ t p) → z ∈ U := by
  classical
  let e := SUnitIdeleTopology.productEquiv K ∅
  let O : Set (SUnitIdeleTopology.model K ∅) :=
    {y | ((e y : IdeleSUnits.sUnitIdeles K ∅) : Ideles K) ∈ U}
  have hO : IsOpen O := hU.preimage (continuous_subtype_val.comp e.continuous)
  have h1 : (1 : SUnitIdeleTopology.model K ∅) ∈ O := by
    change ((e 1 : IdeleSUnits.sUnitIdeles K ∅) : Ideles K) ∈ U
    rw [map_one]
    exact U.one_mem
  have hOn : O ∈ 𝓝 (1 : SUnitIdeleTopology.model K ∅) := hO.mem_nhds h1
  rw [Prod.one_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at hOn
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hOn
  rw [nhds_pi, Filter.mem_pi] at ht₂
  obtain ⟨I, hI, t, ht, hIt⟩ := ht₂
  choose u hu hut using fun p => (mem_nhds_subtype _ _ _).1 (ht p)
  refine ⟨hI.toFinset, u, hu, fun z hz hzI => ?_⟩
  let s : IdeleSUnits.sUnitIdeles K ∅ := ⟨z, mem_sUnitIdeles_empty_of_integral hz⟩
  let y := e.symm s
  have hy : ((1 : (InfiniteAdeles K)ˣ), y.2) ∈ O := by
    apply hsub
    refine ⟨mem_of_mem_nhds ht₁, hIt fun p hp => hut p ?_⟩
    exact hzI p (hI.mem_toFinset.2 hp)
  have he1 : ((e (y.1, 1) : IdeleSUnits.sUnitIdeles K ∅) : Ideles K) =
      infiniteIdelesInclusion K y.1 := by
    change (ideleProductEquiv K).symm (y.1, SUnitIdeleTopology.finiteAssemble K ∅ 1) =
      (ideleProductEquiv K).symm (y.1, 1)
    rw [map_one]
  have hyy : y = (y.1, 1) * ((1 : (InfiniteAdeles K)ˣ), y.2) := by
    apply Prod.ext
    · exact (mul_one y.1).symm
    · exact (one_mul y.2).symm
  have hz' : z = infiniteIdelesInclusion K y.1 *
      ((e ((1 : (InfiniteAdeles K)ˣ), y.2) : IdeleSUnits.sUnitIdeles K ∅) : Ideles K) := by
    have hs : (e y : IdeleSUnits.sUnitIdeles K ∅) = s := e.apply_symm_apply s
    have h2 := congrArg (fun x : IdeleSUnits.sUnitIdeles K ∅ => (x : Ideles K)) hs
    rw [← he1, ← Subgroup.coe_mul, ← map_mul, ← hyy]
    exact h2.symm
  rw [hz']
  exact U.mul_mem (hinf _) hy

end Box

section FiniteIndex

variable {K : Type u} [Field K] [NumberField K]

/-- An integral idele is its archimedean part times an integral idele with
trivial archimedean part, which lies in the compact box of radius one. -/
theorem exists_infinite_mul_mem_ideleBox {x : Ideles K} (hx : x ∈ integralIdeles K) :
    ∃ (a : (InfiniteAdeles K)ˣ) (y : Ideles K),
      y ∈ NormOneIdeleClass.ideleBox K 1 ∧ x = infiniteIdelesInclusion K a * y := by
  let b := ideleProductEquiv K x
  refine ⟨b.1, finiteIdelesInclusion K b.2, ?_, ?_⟩
  · have hxi : x⁻¹ ∈ integralIdeles K := inv_mem hx
    refine ⟨⟨fun w => ?_, ?_⟩, ⟨fun w => ?_, ?_⟩⟩
    · change ‖(1 : InfiniteCompletion K w)‖ ≤ 1
      rw [norm_one]
    · exact NormOneIdeleClass.finite_mem_integralFiniteAdeles hx
    · change ‖(1 : InfiniteCompletion K w)‖ ≤ 1
      rw [norm_one]
    · exact NormOneIdeleClass.finite_mem_integralFiniteAdeles hxi
  · change x = (ideleProductEquiv K).symm (b.1, 1) * (ideleProductEquiv K).symm (1, b.2)
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    exact ((ideleProductEquiv K).symm_apply_apply x).symm

/-- An open subgroup of the ideles containing the whole archimedean factor has
an image of finite index in the idele classes. -/
theorem finiteIndex_map_of_isOpen (V : Subgroup (Ideles K)) (hV : IsOpen (V : Set (Ideles K)))
    (hinf : ∀ a, infiniteIdelesInclusion K a ∈ V) :
    (V.map (ideleClassMap K).toMonoidHom).FiniteIndex := by
  classical
  let N := V.map (ideleClassMap K).toMonoidHom
  let : N.Normal := ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  let π : Ideles K →* IdeleClasses K ⧸ N :=
    (QuotientGroup.mk' N).comp (ideleClassMap K).toMonoidHom
  have hπV {v : Ideles K} (hv : v ∈ V) : π v = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_map_of_mem _ hv)
  have hπd (a : Kˣ) : π (diagonalUnits K a) = 1 := by
    change QuotientGroup.mk' N (ideleClassMap K (diagonalUnits K a)) = 1
    rw [ideleClassMap_diagonalUnits, map_one]
  obtain ⟨t, -, hcover⟩ := (NormOneIdeleClass.isCompact_ideleBox K 1).elim_nhds_subcover
    (fun y => {x : Ideles K | y⁻¹ * x ∈ V}) (fun y _ => by
      apply ((continuous_const.mul continuous_id).isOpen_preimage _ hV).mem_nhds
      change y⁻¹ * y ∈ V
      rw [inv_mul_cancel]
      exact V.one_mem)
  let : Finite (IntegralIdeleClassQuotient K) := integralIdeleClassQuotientFinite K
  let φ : t × IntegralIdeleClassQuotient K → IdeleClasses K ⧸ N :=
    fun p => π (p.1.1 * NormOneIdeleClass.representative K p.2)
  have hφ : Function.Surjective φ := by
    intro c
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (principalIdeles K) c
    obtain ⟨u, a, hu, hx⟩ := NormOneIdeleClass.exists_integral_mul_principal x
    obtain ⟨b, y, hy, hub⟩ := exists_infinite_mul_mem_ideleBox hu
    have hy' := hcover hy
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    refine ⟨(⟨z, hz⟩, NormOneIdeleClass.toIntegralQuotient K x), ?_⟩
    have hyz : π y = π z := by
      have h := hπV hzy
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
    change π (z * NormOneIdeleClass.representative K _) = π x
    conv_rhs => rw [hx, hub]
    simp only [map_mul]
    rw [hπV (hinf b), hπd a, hyz, one_mul, mul_one]
  let : Finite (IdeleClasses K ⧸ N) := Finite.of_surjective φ hφ
  exact Subgroup.finiteIndex_of_finite_quotient

end FiniteIndex

section Separation

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

/-- The conjugate of an archimedean idele has trivial finite coordinates. -/
theorem ideleCoordinate_ideleConj_infinite (a : (InfiniteAdeles E)ˣ) (w : FinitePlace E) :
    ideleCoordinate w (ideleConj (infiniteIdelesInclusion E a)) = 1 := by
  apply Units.ext
  change finiteCompletionEquiv (IsCMField.complexConj E).toRingEquiv w
    ((1 : FiniteAdeles E) (finitePlaceEquiv (IsCMField.complexConj E).toRingEquiv w)) = 1
  exact map_one _

/-- The open subgroup used to separate the real-subfield character. It is
stable under CM conjugation, contains the archimedean factor, consists of
integral ideles, meets no nontrivial root of unity, and pulls back into the
given open subgroup of the real-subfield ideles. -/
theorem exists_separating_subgroup (U : Subgroup (Ideles (maximalRealSubfield E)))
    (hU : IsOpen (U : Set (Ideles (maximalRealSubfield E))))
    (hinf : ∀ a, infiniteIdelesInclusion (maximalRealSubfield E) a ∈ U) :
    ∃ W : Subgroup (Ideles E), IsOpen (W : Set (Ideles E)) ∧
      W ≤ integralIdeles E ∧
      (∀ a, infiniteIdelesInclusion E a ∈ W) ∧
      (∀ x ∈ W, ideleConj x ∈ W) ∧
      (∀ ζ : (𝓞 E)ˣ, ζ ∈ Units.torsion E →
        diagonalUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom ζ) ∈ W → ζ = 1) ∧
      (∀ r : Ideles (maximalRealSubfield E), ideleInclusion (L := E) r ∈ W → r ∈ U) := by
  classical
  obtain ⟨I, t, ht, hbox⟩ := exists_integral_box U hU hinf
  let q (p : FinitePlace (maximalRealSubfield E)) := placeAbove E p
  have hB (p : FinitePlace (maximalRealSubfield E)) :
      ∃ B : OpenSubgroup (FiniteCompletion E (q p).1)ˣ,
        ∀ a : (FiniteCompletion (maximalRealSubfield E) p)ˣ,
          (letI := (q p).2; CMHalfWeight.completionUnitInclusion p (q p).1 a) ∈ B → a ∈ t p := by
    let := (q p).2
    exact exists_openSubgroup_pullback p (q p).1 (ht p)
  choose B hB using hB
  obtain ⟨w₀, B₀, hB₀⟩ := exists_torsion_separating E
  let H : OpenSubgroup (Ideles E) :=
    ⟨integralIdeles E, CMUnramifiedInfinity.isOpen_integralIdeles⟩
  let T (p : FinitePlace (maximalRealSubfield E)) : OpenSubgroup (Ideles E) :=
    (B p).comap (ideleCoordinate (q p).1)
      ((continuous_finiteProjection E (q p).1).units_map _)
  let T₀ : OpenSubgroup (Ideles E) :=
    B₀.comap (ideleCoordinate w₀) ((continuous_finiteProjection E w₀).units_map _)
  have hmem' (A : Finset (FinitePlace (maximalRealSubfield E))) (x : Ideles E) :
      x ∈ A.inf T ↔ ∀ p ∈ A, x ∈ T p := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert p A hp ih => simp only [Finset.inf_insert, OpenSubgroup.mem_inf, ih,
        Finset.mem_insert, forall_eq_or_imp]
  have hmem := hmem' I
  let W₀ : OpenSubgroup (Ideles E) := H ⊓ T₀ ⊓ I.inf T
  let W : OpenSubgroup (Ideles E) :=
    W₀ ⊓ W₀.comap (ideleConj (E := E)).toMulEquiv.toMonoidHom (ideleConj (E := E)).continuous
  have hW₀ {x : Ideles E} (hx : ∀ w : FinitePlace E, ideleCoordinate w x = 1) : x ∈ W₀ := by
    refine ⟨⟨fun w => ?_, ?_⟩, (hmem x).2 fun p _ => ?_⟩
    · change Valued.v (ideleCoordinate w x : FiniteCompletion E w) = 1
      rw [hx w, Units.val_one, map_one]
    · change ideleCoordinate w₀ x ∈ B₀
      rw [hx w₀]
      exact B₀.one_mem
    · change ideleCoordinate (q p).1 x ∈ B p
      rw [hx (q p).1]
      exact (B p).one_mem
  refine ⟨W.toSubgroup, W.isOpen, fun x hx => hx.1.1.1, fun a => ⟨hW₀ fun w => Units.ext rfl,
    hW₀ fun w => ideleCoordinate_ideleConj_infinite a w⟩, fun x hx => ⟨hx.2, ?_⟩, ?_, ?_⟩
  · change ideleConj (ideleConj x) ∈ W₀
    rw [ideleConj_ideleConj]
    exact hx.1
  · intro ζ hζ hx
    exact hB₀ ζ hζ hx.1.1.2
  · intro r hr
    have hrI : r ∈ integralIdeles (maximalRealSubfield E) :=
      mem_integralIdeles_of_ideleInclusion hr.1.1.1
    apply hbox r hrI
    intro p hp
    apply hB p
    have h := (hmem _).1 hr.1.2 p hp
    change ideleCoordinate (q p).1 (ideleInclusion (L := E) r) ∈ B p at h
    let := (q p).2
    rwa [CMHalfWeight.ideleCoordinate_ideleInclusion p (q p).1 r] at h

end Separation

section Descent

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

/-- If an included real-subfield idele is a principal idele times an element of
a separating subgroup, the conjugate ratio of the principal factor is a root of
unity in that subgroup, hence trivial, and the idele lies in the given subgroup. -/
theorem mem_of_ideleInclusion_eq (U : Subgroup (Ideles (maximalRealSubfield E)))
    (hprin : ∀ f, diagonalUnits (maximalRealSubfield E) f ∈ U)
    (W : Subgroup (Ideles E)) (hWint : W ≤ integralIdeles E)
    (hWconj : ∀ x ∈ W, ideleConj x ∈ W)
    (hWtors : ∀ ζ : (𝓞 E)ˣ, ζ ∈ Units.torsion E →
      diagonalUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom ζ) ∈ W → ζ = 1)
    (hWpull : ∀ r : Ideles (maximalRealSubfield E), ideleInclusion (L := E) r ∈ W → r ∈ U)
    {y : Ideles (maximalRealSubfield E)} {e : Eˣ} {w : Ideles E} (hw : w ∈ W)
    (hy : ideleInclusion (L := E) y = diagonalUnits E e * w) : y ∈ U := by
  let c := IsCMField.complexConj E
  let ζ : Eˣ := Units.mapEquiv c.toRingEquiv.toMulEquiv e * e⁻¹
  have hζW : diagonalUnits E ζ ∈ W := by
    have h := congrArg ideleConj hy
    rw [ideleConj_ideleInclusion, map_mul, ideleConj_diagonalUnits, hy] at h
    have h' : diagonalUnits E ζ = w * (ideleConj w)⁻¹ := by
      change diagonalUnits E (Units.mapEquiv c.toRingEquiv.toMulEquiv e * e⁻¹) = _
      rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_right_comm, ← h,
        mul_comm (diagonalUnits E e) w, mul_inv_cancel_right]
    rw [h']
    exact W.mul_mem hw (W.inv_mem (hWconj w hw))
  obtain ⟨ε, hε⟩ := (principalIdeleUnitCriterion E ζ).1 (hWint hζW)
  have hεt : ε ∈ Units.torsion E := by
    rw [Units.mem_torsion]
    intro v
    have hv : v (ζ : E) = 1 := by
      change v (c (e : E) * ((e⁻¹ : Eˣ) : E)) = 1
      rw [map_mul, IsCMField.infinitePlace_complexConj, Units.val_inv_eq_inv_val, map_inv₀,
        mul_inv_cancel₀ ((map_ne_zero v).2 e.ne_zero)]
    rw [← hv, ← hε]
    rfl
  have hε1 : ε = 1 := hWtors ε hεt (by rw [hε]; exact hζW)
  have hζ1 : ζ = 1 := by rw [← hε, hε1, map_one]
  have hce : c (e : E) = e := by
    have h := congrArg (fun z : Eˣ => (z : E)) hζ1
    change c (e : E) * ((e⁻¹ : Eˣ) : E) = 1 at h
    rwa [Units.val_inv_eq_inv_val, mul_inv_eq_one₀ e.ne_zero] at h
  have heF : (e : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E _).1 hce
  let f : (maximalRealSubfield E)ˣ :=
    Units.mk0 ⟨e, heF⟩ (fun h => e.ne_zero (congrArg Subtype.val h))
  have hfe : diagonalUnits E e = ideleInclusion (L := E) (diagonalUnits (maximalRealSubfield E) f) := by
    rw [ideleInclusion_diagonal]
    exact congrArg (diagonalUnits E) (Units.ext rfl)
  have hwr : ideleInclusion (L := E) (y * (diagonalUnits (maximalRealSubfield E) f)⁻¹) = w := by
    rw [map_mul, map_inv, hy, ← hfe, mul_comm (diagonalUnits E e) w, mul_inv_cancel_right]
  have h := hWpull _ (hwr ▸ hw)
  have hy' : y = y * (diagonalUnits (maximalRealSubfield E) f)⁻¹ *
      diagonalUnits (maximalRealSubfield E) f := by group
  rw [hy']
  exact U.mul_mem h (hprin f)

end Descent

section Product

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

/-- The norm to the real subfield, included back, is the product of an idele
class and its CM conjugate. -/
theorem ideleClassInclusion_ideleClassNorm (x : IdeleClasses E) :
    ideleClassInclusion (K := maximalRealSubfield E) (L := E)
        (ideleClassNorm (K := maximalRealSubfield E) (L := E) x) =
      x * ideleClassComplexConj x := by
  classical
  let : Fintype (E ≃ₐ[maximalRealSubfield E] E) := Fintype.ofFinite _
  have h := ideleClassNormGaloisProduct.{u, u} (maximalRealSubfield E) E x
  refine h.trans ?_
  have hne : (1 : E ≃ₐ[maximalRealSubfield E] E) ≠ IsCMField.complexConj E :=
    (IsCMField.complexConj_ne_one E).symm
  have hcard : Fintype.card (E ≃ₐ[maximalRealSubfield E] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) =
      {1, IsCMField.complexConj E} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Finset.card_pair hne, hcard]
  rw [huniv, Finset.prod_pair hne, map_one]
  rfl

end Product


section Assembly

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]

/-- The kernel condition for extending through the quotient by the image of
the separating subgroup and of the included kernel ideles. -/
theorem character_eq_one_of_mem (η₀ : HeckeCharacter (maximalRealSubfield E))
    (U : Subgroup (Ideles (maximalRealSubfield E)))
    (hUη : ∀ y ∈ U, η₀ (ideleClassMap _ y) = 1)
    (hprin : ∀ f, diagonalUnits (maximalRealSubfield E) f ∈ U)
    (W : Subgroup (Ideles E)) (hWint : W ≤ integralIdeles E)
    (hWconj : ∀ x ∈ W, ideleConj x ∈ W)
    (hWtors : ∀ ζ : (𝓞 E)ˣ, ζ ∈ Units.torsion E →
      diagonalUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom ζ) ∈ W → ζ = 1)
    (hWpull : ∀ r : Ideles (maximalRealSubfield E), ideleInclusion (L := E) r ∈ W → r ∈ U)
    (x : IdeleClasses (maximalRealSubfield E))
    (hx : ideleClassInclusion (K := maximalRealSubfield E) (L := E) x ∈
      (W ⊔ U.map (ideleInclusion (L := E)).toMonoidHom).map (ideleClassMap E).toMonoidHom) :
    η₀ x = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 hx
  change (QuotientGroup.mk m : IdeleClasses E) =
    QuotientGroup.mk (ideleInclusion (L := E) y) at hmy
  obtain ⟨e, he⟩ := QuotientGroup.eq.1 hmy
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup.1 hm
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hz
  change diagonalUnits E e = (w * ideleInclusion (L := E) u)⁻¹ * ideleInclusion y at he
  have h1 : ideleInclusion (L := E) y = w * ideleInclusion (L := E) u * diagonalUnits E e := by
    rw [he, mul_inv_cancel_left]
  have hyu : ideleInclusion (L := E) (y * u⁻¹) = diagonalUnits E e * w := by
    rw [map_mul, map_inv, h1, mul_right_comm w, mul_inv_cancel_right, mul_comm]
  have h := mem_of_ideleInclusion_eq U hprin W hWint hWconj hWtors hWpull hw hyu
  have hyU : y ∈ U := by
    have := U.mul_mem h hu
    rwa [inv_mul_cancel_right] at this
  exact hUη y hyU

/-- The extension of a finite real-subfield character trivial at infinity. -/
theorem exists_extension (η₀ : HeckeCharacter (maximalRealSubfield E)) (n : ℕ) (hn : 0 < n)
    (hηn : η₀ ^ n = 1) (hinf : η₀.atInfinity = 1) :
    ∃ α : HeckeCharacter E, α.HasFiniteOrder ∧
      α.comp (ideleClassInclusion (K := maximalRealSubfield E) (L := E)) = η₀ := by
  let K₀ := complexCharacterOpenKernel (A := IdeleClasses (maximalRealSubfield E)) η₀ n hn hηn
  let U : Subgroup (Ideles (maximalRealSubfield E)) :=
    K₀.toSubgroup.comap (ideleClassMap (maximalRealSubfield E)).toMonoidHom
  have hUη : ∀ y ∈ U, η₀ (ideleClassMap _ y) = 1 := fun y hy => hy
  have hUo : IsOpen (U : Set (Ideles (maximalRealSubfield E))) :=
    K₀.isOpen.preimage (ideleClassMap (maximalRealSubfield E)).continuous
  have hUinf (a : (InfiniteAdeles (maximalRealSubfield E))ˣ) :
      infiniteIdelesInclusion (maximalRealSubfield E) a ∈ U :=
    DFunLike.congr_fun hinf a
  have hUprin (f : (maximalRealSubfield E)ˣ) : diagonalUnits (maximalRealSubfield E) f ∈ U := by
    change η₀ (ideleClassMap _ (diagonalUnits (maximalRealSubfield E) f)) = 1
    rw [ideleClassMap_diagonalUnits, map_one]
  obtain ⟨W, hWo, hWint, hWinf, hWconj, hWtors, hWpull⟩ :=
    exists_separating_subgroup U hUo hUinf
  let M : Subgroup (Ideles E) := W ⊔ U.map (ideleInclusion (L := E)).toMonoidHom
  let N : Subgroup (IdeleClasses E) := M.map (ideleClassMap E).toMonoidHom
  let : N.Normal := ⟨fun a ha g => by rwa [mul_comm g a, mul_inv_cancel_right]⟩
  have hMo : IsOpen (M : Set (Ideles E)) := Subgroup.isOpen_mono le_sup_left hWo
  let : N.FiniteIndex :=
    finiteIndex_map_of_isOpen M hMo fun a => Subgroup.mem_sup_left (hWinf a)
  have hNo : IsOpen (N : Set (IdeleClasses E)) := by
    rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ hMo
  have hker : N.comap (ideleClassInclusion (K := maximalRealSubfield E) (L := E)).toMonoidHom ≤
      η₀.toMonoidHom.ker := fun x hx =>
    character_eq_one_of_mem η₀ U hUη hUprin W hWint hWconj hWtors hWpull x hx
  obtain ⟨α, hαm, hα⟩ := Langlands.Topology.exists_character_of_open_finite_quotient
    (A := IdeleClasses (maximalRealSubfield E)) (C := IdeleClasses E)
    (ideleClassInclusion (K := maximalRealSubfield E) (L := E)) η₀ N hNo N.index
    (fun x => N.pow_index_mem x) hker
  exact ⟨α, ⟨N.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, hαm⟩, hα⟩

/-- The product of an extension with its CM conjugate is the norm pullback. -/
theorem mul_complexConj_eq (η₀ : HeckeCharacter (maximalRealSubfield E)) (α : HeckeCharacter E)
    (hα : α.comp (ideleClassInclusion (K := maximalRealSubfield E) (L := E)) = η₀) :
    α * α.complexConj = η₀.comp (ideleClassNorm (K := maximalRealSubfield E) (L := E)) := by
  subst hα
  apply ContinuousMonoidHom.ext
  intro x
  change α x * α (ideleClassComplexConj x) =
    α (ideleClassInclusion (K := maximalRealSubfield E) (L := E)
      (ideleClassNorm (K := maximalRealSubfield E) (L := E) x))
  rw [ideleClassInclusion_ideleClassNorm, map_mul]

end Assembly

end Langlands.Global.Harris.CMFiniteRealCharacterExtension

namespace Langlands.Global.Harris

open CMFiniteRealCharacterExtension in
/-- Harris 1998, Lemma 1.6: a finite-order character of the maximal totally real
subfield, trivial on the archimedean ideles, extends to a finite-order character
of the CM field whose product with its CM conjugate is the norm pullback. -/
theorem cmFiniteRealCharacterExtension :
    CMFiniteRealCharacterExtensionStatement.{u} := by
  intro E _ _ _ η₀ hfin hinf
  obtain ⟨n, hn, hηn⟩ := hfin
  obtain ⟨α, hαfin, hα⟩ := exists_extension η₀ n hn hηn hinf
  exact ⟨α, hαfin, hα, mul_complexConj_eq η₀ α hα⟩

end Langlands.Global.Harris
