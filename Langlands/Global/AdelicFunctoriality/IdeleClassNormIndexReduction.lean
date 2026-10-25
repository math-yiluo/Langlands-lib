import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexFiniteStatement
import Langlands.Global.AdelicFunctoriality.IdeleNormLift
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.ClassField.Global.LocalUnitPowers
import Langlands.ClassField.Global.IntegralIdeleClassQuotientFiniteStatement
import Mathlib.GroupTheory.Schreier

/-! # Reduction of the idele-class norm index lemma to the finiteness of `C_K / C∞`

For number fields `K` and `L` with `Algebra K L`, in independent universes, the range `H` of the
actual idele-class norm `C_L → C_K` has finite index dividing a power of `[L : K]`, provided the
quotient of `C_K` by the integral idele classes is finite. This is the first lemma of
Artin–Tate VI §1: an integral idele whose coordinates are local-degree powers at the finitely
many ramified places and at the infinite places is a norm, and such ideles have finite index in
the integral ideles.
-/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField
open Langlands.ClassField.Global

universe u v

section Choices

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- An infinite place of `L` lies above its restriction to `K`. -/
theorem infinitePlace_liesOver_of_comap_eq {w : InfinitePlace L} {v : InfinitePlace K}
    (h : w.comap (algebraMap K L) = v) : w.LiesOver v := by
  subst h
  exact ⟨rfl⟩

variable (L) in
/-- A chosen infinite place of `L` above the infinite place `v` of `K`. -/
def infinitePlaceAbove (v : InfinitePlace K) : InfinitePlacesAbove L v :=
  ⟨(InfinitePlace.comap_surjective (k := K) (K := L) v).choose,
    infinitePlace_liesOver_of_comap_eq
      (InfinitePlace.comap_surjective (k := K) (K := L) v).choose_spec⟩

open scoped FiniteExtension in
/-- The local degree `[L_q : K_p]` at the chosen finite place `q = wf p` above `p`. -/
def chosenFiniteDegree (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (p : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Module.finrank (p.adicCompletion K) ((wf p).1.adicCompletion L)

open scoped NumberField.LiesOver in
/-- The local degree `[L_w : K_v]` at the chosen infinite place `w = wi v` above `v`. -/
def chosenInfiniteDegree (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (v : InfinitePlace K) : ℕ :=
  Module.finrank v.Completion (wi v).1.Completion

open scoped FiniteExtension in
theorem chosenFiniteDegree_ne_zero (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (p : HeightOneSpectrum (𝓞 K)) : chosenFiniteDegree wf p ≠ 0 := by
  have := FiniteExtension.local_finite p (wf p).1
  exact Module.finrank_pos.ne'

open scoped NumberField.LiesOver in
omit [NumberField K] in
/-- An infinite local degree is one, or two over a real place. -/
theorem chosenInfiniteDegree_eq (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (v : InfinitePlace K) :
    chosenInfiniteDegree wi v = 1 ∨ (chosenInfiniteDegree wi v = 2 ∧ v.IsReal) := by
  rcases (wi v).1.isUnramified_or_isRamified K with h | h
  · exact Or.inl (h.finrank_eq_one v)
  · refine Or.inr ⟨h.finrank_eq_two v, ?_⟩
    have := (InfinitePlace.isRamified_iff.mp h).2
    rwa [InfinitePlace.LiesOver.comap_eq (wi v).1 v] at this

omit [NumberField K] in
theorem infiniteUnitPowers_chosenInfiniteDegree_finiteIndex
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) (v : InfinitePlace K) :
    (infiniteUnitPowers v (chosenInfiniteDegree wi v)).FiniteIndex := by
  rcases chosenInfiniteDegree_eq wi v with h | ⟨h, hv⟩
  · rw [h, infiniteUnitPowers_one]
    infer_instance
  · rw [h]
    exact infiniteUnitPowers_two_finiteIndex v hv

/-- The finite places of `K` whose chosen place above is ramified. -/
def ramifiedChosenPlaces (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p) :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {p | (wf p).1.asIdeal.ramificationIdx (𝓞 K) ≠ 1}

theorem finite_ramifiedChosenPlaces (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p) :
    (ramifiedChosenPlaces wf).Finite := by
  refine (Filter.eventually_cofinite.1 (eventually_ramificationIdx_eq_one K L)).subset ?_
  intro p hp h
  exact hp (h (wf p).1 (wf p).2)

end Choices

section Residues

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (K) in
/-- The finite coordinate at `p` of an integral idele, as a valuation unit. -/
def integralUnitCoordinate (p : HeightOneSpectrum (𝓞 K)) : integralIdeles K →* localUnits p where
  toFun x := ⟨ideleCoordinate p (x : IdeleGroup (𝓞 K) K),
    (mem_integralIdeles_iff_localUnits _).1 x.2 p⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem coe_integralUnitCoordinate (p : HeightOneSpectrum (𝓞 K)) (x : integralIdeles K) :
    (((integralUnitCoordinate K p x : localUnits p) : (p.adicCompletion K)ˣ) :
      p.adicCompletion K) = ((x : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 p := rfl

variable (K) in
/-- The coordinate at an infinite place `v` of an integral idele, as a unit of `K_v`. -/
def integralInfiniteCoordinate (v : InfinitePlace K) : integralIdeles K →* (v.Completion)ˣ :=
  (Units.map
    { toFun := fun x : AdeleRing (𝓞 K) K => x.1 v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }).comp (integralIdeles K).subtype

@[simp] theorem coe_integralInfiniteCoordinate (v : InfinitePlace K) (x : integralIdeles K) :
    ((integralInfiniteCoordinate K v x : (v.Completion)ˣ) : v.Completion) =
      ((x : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 v := rfl

/-- The group of local power residues: local units modulo local-degree powers at the finitely
many places whose chosen place above is ramified, and infinite local units modulo
local-degree powers. -/
abbrev LocalPowerResidues (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) :=
  (∀ p : ramifiedChosenPlaces wf,
      localUnits p.1 ⧸ localUnitPowers p.1 (chosenFiniteDegree wf p.1)) ×
    (∀ v : InfinitePlace K, (v.Completion)ˣ ⧸ infiniteUnitPowers v (chosenInfiniteDegree wi v))

/-- The local power residues of an integral idele: its unit coordinates modulo local-degree
powers at the finitely many places whose chosen place above is ramified, and its infinite
coordinates modulo local-degree powers. -/
def localPowerResidue (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) :
    integralIdeles K →* LocalPowerResidues wf wi :=
  MonoidHom.prod
    (MonoidHom.pi fun p => (QuotientGroup.mk' _).comp (integralUnitCoordinate K p.1))
    (MonoidHom.pi fun v => (QuotientGroup.mk' _).comp (integralInfiniteCoordinate K v))

/-- The integral ideles with trivial local power residues have finite index. -/
theorem localPowerResidue_ker_finiteIndex
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) :
    (localPowerResidue wf wi).ker.FiniteIndex := by
  have : Finite (ramifiedChosenPlaces wf) := (finite_ramifiedChosenPlaces wf).to_subtype
  have : ∀ p : ramifiedChosenPlaces wf,
      Finite (localUnits p.1 ⧸ localUnitPowers p.1 (chosenFiniteDegree wf p.1)) := fun p =>
    have := localUnitPowers_finiteIndex p.1 _ (chosenFiniteDegree_ne_zero wf p.1)
    inferInstance
  have : ∀ v : InfinitePlace K,
      Finite ((v.Completion)ˣ ⧸ infiniteUnitPowers v (chosenInfiniteDegree wi v)) := fun v =>
    have := infiniteUnitPowers_chosenInfiniteDegree_finiteIndex wi v
    inferInstance
  have : Finite (LocalPowerResidues wf wi) := inferInstance
  exact Subgroup.finiteIndex_ker (G' := LocalPowerResidues wf wi) (localPowerResidue wf wi)

open scoped FiniteExtension in
/-- **Local powers are norms.** An integral idele with trivial local power residues is the norm
of an idele of `L`: at a place whose chosen place above is unramified its unit coordinate is a
local norm of a unit, and elsewhere its coordinate is a local-degree power. -/
theorem mem_range_ideleNorm_of_localPowerResidue_eq_one
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) (x : integralIdeles K)
    (hx : localPowerResidue wf wi x = 1) :
    (x : IdeleGroup (𝓞 K) K) ∈ (ideleNorm (K := K) (L := L)).toMonoidHom.range := by
  classical
  have hfin : ∀ p : HeightOneSpectrum (𝓞 K), ∃ c : ((wf p).1.adicCompletion L)ˣ,
      (p ∉ ramifiedChosenPlaces wf → Valued.v (c : (wf p).1.adicCompletion L) = 1) ∧
      FiniteExtension.localNorm p (wf p).1 (c : (wf p).1.adicCompletion L) =
        ((x : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 p := by
    intro p
    by_cases hp : p ∈ ramifiedChosenPlaces wf
    · have h1 : (QuotientGroup.mk' (localUnitPowers p (chosenFiniteDegree wf p))
          (integralUnitCoordinate K p x)) = 1 :=
        congrFun (congrArg Prod.fst hx) ⟨p, hp⟩
      obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 h1
      refine ⟨Units.map (FiniteExtension.completionMap p (wf p).1).toMonoidHom
        (y : (p.adicCompletion K)ˣ), fun h => absurd hp h, ?_⟩
      change FiniteExtension.localNorm p (wf p).1 (FiniteExtension.completionMap p (wf p).1
        ((y : (p.adicCompletion K)ˣ) : p.adicCompletion K)) = _
      rw [FiniteExtension.localNorm_algebraMap]
      have hy' := congrArg
        (fun z : localUnits p => ((z : (p.adicCompletion K)ˣ) : p.adicCompletion K)) hy
      simp only [powMonoidHom_apply, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
        coe_integralUnitCoordinate] at hy'
      exact hy'
    · have he : (wf p).1.asIdeal.ramificationIdx (𝓞 K) = 1 := not_not.1 hp
      obtain ⟨c, hc, hcn⟩ := FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one p
        (wf p).1 he (ideleCoordinate p (x : IdeleGroup (𝓞 K) K))
        ((mem_integralIdeles_iff _).1 x.2 p)
      exact ⟨c, fun _ => hc, hcn⟩
  choose c hc hcn using hfin
  have hinf : ∀ v : InfinitePlace K, ∃ d : ((wi v).1.Completion)ˣ,
      InfiniteExtension.localNorm v (wi v).1 (d : (wi v).1.Completion) =
        ((x : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 v := by
    intro v
    have h1 : (QuotientGroup.mk' (infiniteUnitPowers v (chosenInfiniteDegree wi v))
        (integralInfiniteCoordinate K v x)) = 1 :=
      congrFun (congrArg Prod.snd hx) v
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 h1
    refine ⟨Units.map (NumberField.LiesOver.completionMap (v := v) (w := (wi v).1)).toMonoidHom y,
      ?_⟩
    change InfiniteExtension.localNorm v (wi v).1
      (NumberField.LiesOver.completionMap (y : v.Completion)) = _
    rw [InfiniteExtension.localNorm_algebraMap]
    have hy' := congrArg (fun z : (v.Completion)ˣ => (z : v.Completion)) hy
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
      coe_integralInfiniteCoordinate] at hy'
    exact hy'
  choose d hdn using hinf
  refine mem_range_ideleNorm_of_local wf wi _ c ?_ hcn d hdn
  refine ((finite_ramifiedChosenPlaces wf).eventually_cofinite_notMem).mono fun p hp => ?_
  have h1 := hc p hp
  refine ⟨(mem_adicCompletionIntegers (𝓞 L) L (wf p).1).2 (le_of_eq h1), ?_⟩
  rw [mem_adicCompletionIntegers (𝓞 L) L (wf p).1, Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]

/-- The image in `C_K` of the integral ideles with trivial local power residues. -/
def residueFreeIdeleClasses (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (localPowerResidue wf wi).ker.map
    ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp (integralIdeles K).subtype)

theorem residueFreeIdeleClasses_le_range
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v) :
    residueFreeIdeleClasses wf wi ≤ (ideleClassNorm (K := K) (L := L)).toMonoidHom.range := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := mem_range_ideleNorm_of_localPowerResidue_eq_one wf wi x hx
  exact ⟨QuotientGroup.mk y, (ideleClassNorm_mk y).trans (congrArg QuotientGroup.mk hy)⟩

/-- If `C_K / C∞` is finite, the residue-free idele classes have finite index in `C_K`. -/
theorem residueFreeIdeleClasses_finiteIndex
    (wf : ∀ p : HeightOneSpectrum (𝓞 K), FinitePlacesAbove L p)
    (wi : ∀ v : InfinitePlace K, InfinitePlacesAbove L v)
    (hK : Finite (IntegralIdeleClassQuotient K)) :
    (residueFreeIdeleClasses wf wi).FiniteIndex := by
  let P := integralIdeleClasses K
  let π : integralIdeles K →* P :=
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).subgroupMap (integralIdeles K)
  have hπ : Function.Surjective π := MonoidHom.subgroupMap_surjective _ _
  have hQP : residueFreeIdeleClasses wf wi ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, x.2, rfl⟩
  have hP : P.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hker := localPowerResidue_ker_finiteIndex wf wi
  have hle : (localPowerResidue wf wi).ker.map π ≤ (residueFreeIdeleClasses wf wi).subgroupOf P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hrel : (residueFreeIdeleClasses wf wi).relIndex P ≠ 0 := by
    intro h
    apply hker.index_ne_zero
    have h2 := (Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hπ)
    rw [← Subgroup.relIndex, h] at h2
    exact Nat.eq_zero_of_zero_dvd h2
  constructor
  rw [← Subgroup.relIndex_mul_index hQP]
  exact mul_ne_zero hrel hP.index_ne_zero

end Residues

section Index

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- If `C_K / C∞` is finite, the range of the idele-class norm has finite index. -/
theorem ideleClassNorm_range_finiteIndex (hK : Finite (IntegralIdeleClassQuotient K)) :
    (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.FiniteIndex := by
  have := residueFreeIdeleClasses_finiteIndex (fun p => placeAbove L p)
    (fun v => infinitePlaceAbove L v) hK
  exact Subgroup.finiteIndex_of_le
    (residueFreeIdeleClasses_le_range (fun p => placeAbove L p) (fun v => infinitePlaceAbove L v))

/-- A finite-index norm range has index dividing a power of the degree: the quotient is a finite
abelian group killed by `[L : K]`, by the norm-of-inclusion law. -/
theorem ideleClassNorm_range_index_dvd
    (hH : (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.FiniteIndex) :
    ∃ r : ℕ, (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
      (Module.finrank K L) ^ r := by
  have : (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.Normal :=
    ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  -- The generic commutative-quotient instance is not found here; state it directly.
  let _ : CommGroup
      (IdeleClassGroup (𝓞 K) K ⧸ (ideleClassNorm (K := K) (L := L)).toMonoidHom.range) :=
    { (inferInstance : Group
        (IdeleClassGroup (𝓞 K) K ⧸ (ideleClassNorm (K := K) (L := L)).toMonoidHom.range)) with
      mul_comm := fun a b => QuotientGroup.induction_on a fun a =>
        QuotientGroup.induction_on b fun b =>
          congrArg (QuotientGroup.mk' (ideleClassNorm (K := K) (L := L)).toMonoidHom.range)
            (mul_comm a b) }
  have : Finite (IdeleClassGroup (𝓞 K) K ⧸ (ideleClassNorm (K := K) (L := L)).toMonoidHom.range) :=
    Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Group.rank
    (IdeleClassGroup (𝓞 K) K ⧸ (ideleClassNorm (K := K) (L := L)).toMonoidHom.range), ?_⟩
  rw [Subgroup.index]
  refine card_dvd_exponent_pow_rank' _ fun g => ?_
  induction g using QuotientGroup.induction_on with
  | H c =>
    exact (QuotientGroup.eq_one_iff (c ^ Module.finrank K L)).2
      ⟨ideleClassInclusion (K := K) (L := L) c, ideleClassNormInclusionPower K L c⟩

/-- **Reduction of the norm-index lemma.** If the quotient of the idele class group by the
integral idele classes is finite for every number field in universe `u`, then for every
extension `L/K` the idele-class norm range has finite index dividing a power of `[L : K]`. -/
theorem ideleClassNormIndexFinite_of_integralIdeleClassQuotientFinite
    (h : IntegralIdeleClassQuotientFinite.{u}) : IdeleClassNormIndexFinite.{u, v} := by
  intro K _ _ L _ _ _ H
  have hfi := ideleClassNorm_range_finiteIndex (K := K) (L := L) (h K)
  exact ⟨hfi, ideleClassNorm_range_index_dvd hfi⟩

end Index

end Langlands.Global.AdelicFunctoriality
