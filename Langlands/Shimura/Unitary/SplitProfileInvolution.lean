import Langlands.Global.Arithmetic.CyclicNonsplitPrimeProof
import Langlands.Global.AdelicFunctoriality.UniquePlaceCompletion
import Langlands.Shimura.Unitary.ScalarConjugateCompletion
import Langlands.Shimura.Unitary.UnitaryProfileBrauerAlgebra

/-! # A unitary involution on the central simple algebra of a split profile -/

noncomputable section

universe u v w

namespace Langlands.Shimura

open NumberField _root_.Algebra

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]

/-- Convert the scalar-semilinear involution predicate to a second-kind
involution over the specified real field. -/
def SecondKindInvolution.ofUnitaryInvolution {A : Type w} [Ring A]
    [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    (τ : A → A) (hτ : IsUnitaryInvolution (cmConjugation E K) τ) :
    SecondKindInvolution E K A where
  involution :=
    { linear :=
        { toFun := τ
          map_add' := hτ.1
          map_smul' := fun r a => by
            change τ (r • a) = r • τ a
            have hfix : τ (algebraMap E A r) = algebraMap E A r := by
              rw [IsScalarTower.algebraMap_apply E K A, hτ.2.2.2,
                (cmConjugation E K).commutes]
            rw [Algebra.smul_def, Algebra.smul_def, hτ.2.1, hfix, Algebra.commutes] }
      map_one := by
        change τ 1 = 1
        simpa only [map_one] using hτ.2.2.2 1
      map_mul := hτ.2.1
      involutive := hτ.2.2.1 }
  onCenter := hτ.2.2.2

namespace FiniteUnitary

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local Langlands.Algebra.CentralSimple
open scoped NumberField FiniteExtension Pointwise

local notation "FinitePlace" => Langlands.Global.FinitePlace
local notation "c" => cmConjugation E K
local notation "cRing" => AlgEquiv.toRingEquiv (cmConjugation E K)
local notation "conjPlace" => finitePlaceEquiv (AlgEquiv.toRingEquiv (cmConjugation E K))

omit [NumberField E] in
private theorem conjPlace_involutive : Function.Involutive conjPlace := by
  intro q
  have hc : (cRing).trans cRing = RingEquiv.refl K :=
    RingEquiv.ext (cmConjugation_involutive E K)
  change ((conjPlace).trans conjPlace) q = q
  rw [← finitePlaceEquiv_trans, hc, finitePlaceEquiv_refl]
  rfl

private theorem exists_conjPlace_fixed (s : Finset (FinitePlace E)) :
    ∃ q : FinitePlace K, q.under (𝓞 E) ∉ s ∧ conjPlace q = q := by
  classical
  have hdegree : 1 < Module.finrank E K := by rw [IsQuadraticExtension.finrank_eq_two]; decide
  obtain ⟨p, hp, q, hq, hd⟩ := cyclicNonsplitPrimeStatement E K hdegree s
  let w : FinitePlacesAbove K p := ⟨q, hq⟩
  let d (r : FinitePlacesAbove K p) := Module.finrank (FiniteCompletion E p) (FiniteCompletion K r.val)
  have hw : 2 ≤ d w := by
    have hp : 0 < d w := Module.finrank_pos
    have hn : d w ≠ 1 := hd
    omega
  have huniq (r : FinitePlacesAbove K p) : r = w := by
    by_contra hn
    have hsum : ∑ r, d r ≤ 2 :=
      (IsQuadraticExtension.finrank_eq_two E K) ▸ finiteLocalDegree_sum_le (L := K) p
    have hpair : d w + d r ≤ 2 := calc
      _ = ∑ t ∈ ({w, r} : Finset (FinitePlacesAbove K p)), d t := by
        rw [Finset.sum_pair (Ne.symm hn)]
      _ ≤ ∑ t, d t := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 2 := hsum
    have hpos : 0 < d r := Module.finrank_pos
    omega
  exact ⟨q, finitePlacesAbove_under p w ▸ hp, finitePlaceEquiv_eq_of_unique w huniq c⟩

omit [IsTotallyReal E] [IsTotallyComplex K] in
private theorem exists_automorphism_of_above {p : FinitePlace E}
    (q r : FinitePlacesAbove K p) :
    ∃ g : K ≃ₐ[E] K, finitePlaceEquiv g.toRingEquiv q.val = r.val := by
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 E) (𝓞 K) (K ≃ₐ[E] K)
    r.val.asIdeal q.val.asIdeal
    ((Ideal.LiesOver.over (P := r.val.asIdeal) (p := p.asIdeal)).symm.trans
      (Ideal.LiesOver.over (P := q.val.asIdeal) (p := p.asIdeal)))
  refine ⟨g, IsDedekindDomain.HeightOneSpectrum.ext ?_⟩
  rw [finitePlaceEquiv_asIdeal, hg]
  ext x
  rw [Ideal.mem_comap]
  exact Ideal.smul_mem_pointwise_smul_iff

private theorem conjPlace_otherPlace {p : FinitePlace E}
    (h : SplitPlaceIdentification E K p) (q : FinitePlacesAbove K p) :
    conjPlace q.val = (h.otherPlace q).val := by
  obtain ⟨g, hg⟩ := exists_automorphism_of_above q (h.otherPlace q)
  have hg₁ : g ≠ 1 := by
    intro he
    rw [he] at hg
    change finitePlaceEquiv (RingEquiv.refl K) q.val = _ at hg
    rw [finitePlaceEquiv_refl] at hg
    exact h.otherPlace_ne q (Subtype.ext hg.symm)
  have hcard : Nat.card (K ≃ₐ[E] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, IsQuadraticExtension.finrank_eq_two]
  obtain ⟨g', -, hg''⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[E] K)).mp hcard
  have he : g = c := (hg'' g hg₁).trans (hg'' c (cmConjugation_ne_one E K)).symm
  simpa only [he] using hg

omit [IsTotallyComplex K] in
private theorem finiteInvariant_eq_of_completed {A : CSA.{v, v} K}
    {q : FinitePlace K} {x : RationalModIntegers}
    (h : HasCompletedBrauerInvariant K A q x) :
    finiteBrauerInvariant K q (Brauer.classOf (Brauer.baseChange (FiniteCompletion K q) A)) = x := by
  obtain ⟨B, ⟨e⟩, hB⟩ := h
  rw [Brauer.classOf_eq_of_algEquiv (A := Brauer.baseChange (FiniteCompletion K q) A) e, hB]

/-- Realize the signed Brauer profile by a degree-`n` algebra with a second-kind
involution. Its finite invariants determine its Brauer class. -/
theorem exists_csa_with_involution_for_splitProfile
    {s : Finset (FinitePlace E)} {n : ℕ} (hn : 0 < n)
    (hs : ∀ p : s, IsSplitPlace E K p.val)
    (positive : ∀ p : s, FinitePlacesAbove K p.val) (a : s → ZMod n) :
    ∃ A : CSA.{v, v} K, Module.finrank K A = n * n ∧
      (∃ τ : A → A, IsUnitaryInvolution c τ) ∧
      (∀ (p : s) (q : FinitePlacesAbove K p.val),
        HasCompletedBrauerInvariant K A q.val
          (denominatorEquiv n hn (by classical exact if q = positive p then a p else -a p))) ∧
      ∀ (p : FinitePlace E), p ∉ s → ∀ q : FinitePlacesAbove K p,
        HasCompletedBrauerInvariant K A q.val 0 := by
  classical
  obtain ⟨A, hA, hSel, hOut⟩ := exists_csa_for_splitProfile hn hs positive a
  obtain ⟨q₀, hq₀, hfix⟩ := exists_conjPlace_fixed (K := K) s
  let upper : s ↪ FinitePlace K :=
    ⟨fun p => (positive p).val, fun {p p'} h => Subtype.ext
      ((finitePlacesAbove_under p.val (positive p)).symm.trans
        ((congrArg (fun q : FinitePlace K => q.under (𝓞 E)) h).trans
          (finitePlacesAbove_under p'.val (positive p'))))⟩
  let S := Finset.univ.map upper
  let x (p : s) : denominatorSubgroup n := denominatorEquiv n hn (a p)
  let f₀ := Function.extend upper x (fun _ => 0)
  let f₁ (q : FinitePlace K) : denominatorSubgroup n := if q = q₀ then -∑ p, x p else 0
  let f (q : FinitePlace K) : RationalModIntegers := (f₀ q + f₁ q : denominatorSubgroup n)
  have hf₀ (p : s) : f₀ (upper p) = x p := upper.injective.extend_apply _ _ _
  have hf₀zero (q : FinitePlace K) (hq : q ∉ S) : f₀ q = 0 :=
    Function.extend_apply' _ _ _ (by
      rintro ⟨p, rfl⟩
      exact hq (Finset.mem_map.mpr ⟨p, Finset.mem_univ _, rfl⟩))
  have hUnder (p : s) : (upper p).under (𝓞 E) = p.val := finitePlacesAbove_under _ _
  have hAbove (q : FinitePlace K) (hq : q.under (𝓞 E) ∉ s) : q ∉ S := by
    rintro h
    obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp h
    exact hq (hUnder p ▸ p.property)
  have hqS : q₀ ∉ S := hAbove q₀ hq₀
  have hfSupp (q : FinitePlace K) (hq : q ∉ insert q₀ S) : f q = 0 := by
    have h0 : q ≠ q₀ := fun h => hq (h ▸ Finset.mem_insert_self q₀ S)
    have hS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
    simp [f, f₁, h0, hf₀zero q hS]
  have hfSum : ∑ q ∈ insert q₀ S, f q = 0 := by
    rw [Finset.sum_insert hqS]
    have hs' : ∑ q ∈ S, f q = ∑ p : s, (x p : RationalModIntegers) := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hne : upper p ≠ q₀ := by
        intro hp
        exact hqS (hp ▸ Finset.mem_map.mpr ⟨p, Finset.mem_univ _, rfl⟩)
      simp [f, hf₀, f₁, hne]
    rw [hs']
    simp [f, hf₀zero q₀ hqS, f₁]
  obtain ⟨B, _, hB⟩ := Brauer.numberFieldBrauerProfileRealization K (insert q₀ S) f
    hfSupp n hn (fun q _ => (f₀ q + f₁ q).property) hfSum
  let C := Brauer.tensor B (ScalarConjugate.csa cRing (Brauer.opposite B))
  have hcSymm : (cRing).symm = cRing :=
    RingEquiv.ext fun y => (cRing).symm_apply_eq.mpr (cmConjugation_involutive E K y).symm
  have hValue (q : FinitePlace K) :
      finiteBrauerInvariant K q (Brauer.classOf (Brauer.baseChange (FiniteCompletion K q) C)) =
        (f₀ q : RationalModIntegers) - (f₀ (conjPlace q) : RationalModIntegers) := by
    let M := FiniteCompletion K q
    let I := (finiteBrauerInvariant K q).toAddMonoidHom.comp (Brauer.scalarExtension (K := K) M)
    have hB' (q : FinitePlace K) :
        finiteBrauerInvariant K q (Brauer.classOf (Brauer.baseChange (FiniteCompletion K q) B)) =
          f q := hB q
    have hfirst : I (Brauer.classOf B) = f q := hB' q
    have hsecond : I (Brauer.classOf (ScalarConjugate.csa cRing (Brauer.opposite B))) =
        -f (conjPlace q) := by
      change finiteBrauerInvariant K q (Brauer.classOf
        (Brauer.baseChange M (ScalarConjugate.csa cRing (Brauer.opposite B)))) = _
      have hcLoc := finiteBrauerInvariant_scalarConjugate cRing q (Brauer.opposite B)
      rw [hcSymm] at hcLoc
      rw [hcLoc]
      let L := FiniteCompletion K (conjPlace q)
      change (finiteBrauerInvariant K (conjPlace q)) (Brauer.scalarExtension L
        (Brauer.classOf (Brauer.opposite B))) = _
      rw [Brauer.classOf_opposite, map_neg, map_neg, Brauer.scalarExtension_classOf, hB']
    have haux : f₁ (conjPlace q) = f₁ q := by
      have hh : conjPlace q = q₀ ↔ q = q₀ := by
        exact ⟨fun he => (conjPlace).injective (he.trans hfix.symm), fun he => he ▸ hfix⟩
      simp only [f₁, hh]
    change I (Brauer.classOf C) = _
    rw [Brauer.classOf_tensor, map_add, hfirst, hsecond]
    simp only [f, AddSubgroup.coe_add, haux, sub_eq_add_neg]
    abel
  have hclass : Brauer.classOf C = Brauer.classOf A := by
    apply classOf_eq_of_finiteBrauerInvariants
    intro q
    rw [hValue]
    let p := q.under (𝓞 E)
    let r : FinitePlacesAbove K p := ⟨q, inferInstance⟩
    have hconjUnder := Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof.finitePlaceEquiv_under
      c q
    by_cases hp : p ∈ s
    · let p' : s := ⟨p, hp⟩
      let h := (hs p').some
      have hswap : conjPlace (upper p') = (h.otherPlace (positive p')).val :=
        conjPlace_otherPlace h (positive p')
      have hne : (h.otherPlace (positive p')).val ≠ upper p' := fun e =>
        h.otherPlace_ne (positive p') (Subtype.ext e)
      have hother : (h.otherPlace (positive p')).val ∉ S := by
        rintro hm
        obtain ⟨p'', -, he⟩ := Finset.mem_map.mp hm
        have hp'' : p'' = p' := Subtype.ext
          ((hUnder p'').symm.trans ((congrArg (fun t : FinitePlace K => t.under (𝓞 E)) he).trans
            (finitePlacesAbove_under p (h.otherPlace (positive p')))))
        subst p''
        exact hne he.symm
      have hs' := finiteInvariant_eq_of_completed (hSel p' r)
      change _ = finiteBrauerInvariant K r.val _
      rw [hs']
      rcases h.eq_or_eq_otherPlace (positive p') r with he | he
      · have he' : q = upper p' := congrArg Subtype.val he
        rw [ite_eq_left he, he', hf₀, hswap, hf₀zero _ hother]
        simp [x]
      · have he' : q = (h.otherPlace (positive p')).val := congrArg Subtype.val he
        have hq' : conjPlace q = upper p' := by
          rw [he', ← hswap]
          exact conjPlace_involutive (upper p')
        have hr : r ≠ positive p' := he ▸ h.otherPlace_ne (positive p')
        rw [ite_eq_right hr, hf₀zero q (he'.symm ▸ hother), hq', hf₀, map_neg]
        simp [x]
    · have hzero := finiteInvariant_eq_of_completed (hOut p hp r)
      have hq' : (conjPlace q).under (𝓞 E) ∉ s := hconjUnder ▸ hp
      rw [hzero, hf₀zero q (hAbove q hp), hf₀zero (conjPlace q) (hAbove _ hq')]
      simp
  have hc : ∃ k : K, c k ≠ k := by
    by_contra! h
    exact cmConjugation_ne_one E K (AlgEquiv.ext h)
  let τ := conjugateOppositeFlip cRing B (cmConjugation_involutive E K)
  have hτ : IsUnitaryInvolution c τ :=
    isUnitaryInvolution_conjugateOppositeFlip cRing B (cmConjugation_involutive E K)
  refine ⟨A, hA, ?_, hSel, hOut⟩
  exact exists_unitaryInvolution_of_brauerEquivalent cRing hc
    ((Brauer.classOf_eq_iff C A).mp hclass) τ hτ

end FiniteUnitary

end Langlands.Shimura
