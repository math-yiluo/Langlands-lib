import Langlands.Representation.Classification.CuspidalProductContragredient

/-!
# Determinant twists of supercuspidal supports

Twisting the actual constituent witness transports a support to its multiset
image under the same determinant-power twist.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uF

namespace SmoothRep

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A character twist preserves the actual subquotient relation. -/
theorem IsSubquotient.twist {B A : SmoothRep.{uR, uG, uV} R G}
    (h : IsSubquotient B A) (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G)) :
    IsSubquotient (B.twist χ hχ) (A.twist χ hχ) := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  exact isSubquotient_iff_exists.mpr
    ⟨C.twist χ hχ, (twistFunctor χ hχ).map i, (twistFunctor χ hχ).map q, hi, hq⟩

end SmoothRep

namespace PadicField.TopologicalData

open GeneralLinear
open Classification.CuspidalProductContragredient

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

set_option maxHeartbeats 2000000 in
/-- The published product-twist equivalence as an isomorphism of actual smooth
objects, before choosing cuspidal representatives. -/
def normalizedProductDeterminantTwistIso {n : ℕ} (B : BlockShape n) (s : ℝ)
    (A : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (((T.normalizedProductInductionFunctor B).obj A).twist
          (T.determinantPowerCharacter n s) (T.isOpen_ker_determinantPowerCharacter n s)) ≅
        (T.normalizedProductInductionFunctor B).obj
          (fun i => (A i).twist (T.determinantPowerCharacter (B.size i) s)
            (T.isOpen_ker_determinantPowerCharacter (B.size i) s)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let e := Classical.choice (nonempty_twist_productEquiv T B s
    (fun i => (A i).representation))
  refine SmoothRep.mkIso ?_
  simp only [SmoothRep.twist_representation, normalizedProductInductionFunctor_obj]
  exact e

/-- An irreducible cuspidal-product constituent remains such a constituent after
twisting both it and every supplied cuspidal datum by the same real power. -/
theorem IsCuspidalConstituent.twist {r : ℕ} {ρ : Fin r → T.CuspidalDatum.{uV, uF}}
    {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : T.IsCuspidalConstituent ρ π) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.IsCuspidalConstituent (fun i => (ρ i).twist s)
      (π.twist (T.determinantPowerCharacter n s)
        (T.isOpen_ker_determinantPowerCharacter n s)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨h, A, hA, hirr, hsub⟩ := hπ
  let As (i : Fin r) : SupercuspidalRep.{uF, uV}
      (F := F.Carrier) (n := (ρ i).rank) :=
    SupercuspidalRep.twist (T.determinantPowerCharacter (ρ i).rank s)
      (T.isOpen_ker_determinantPowerCharacter (ρ i).rank s)
      (T.ker_determinant_le_ker_determinantPowerCharacter (ρ i).rank s) (A i)
  refine ⟨h, As, ?_,
    (SmoothRep.isIrreducible_twist_iff _ _ π).mpr hirr, ?_⟩
  · intro i
    change (As i).isoClass = T.supercuspidalClassRealPowerTwist (ρ i).rank s (ρ i).cls
    rw [← show (A i).isoClass = (ρ i).cls from hA i]
    rfl
  · have hprod : T.cuspidalProductInduced (fun i => (ρ i).twist s) h As =
        (T.normalizedProductInductionFunctor.{uF, uV} (T.cuspidalShape ρ h)).obj
          (fun i => (As i).obj) := rfl
    rw [hprod]
    change SmoothRep.IsSubquotient π
      ((T.normalizedProductInductionFunctor (T.cuspidalShape ρ h)).obj
        (fun i => (A i).obj)) at hsub
    let eiso := normalizedProductDeterminantTwistIso (T.cuspidalShape ρ h) s
      (fun i => (A i).obj)
    exact (hsub.twist (T.determinantPowerCharacter n s)
      (T.isOpen_ker_determinantPowerCharacter n s)).of_iso_right eiso

/-- A determinant-power twist sends a supercuspidal support to its multiset
image under the corresponding twist of cuspidal data. -/
theorem IsSupercuspidalSupport.twist {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {a : Multiset T.CuspidalDatum.{uV, uF}}
    (ha : T.IsSupercuspidalSupport π a) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.IsSupercuspidalSupport
      (π.twist (T.determinantPowerCharacter n s)
        (T.isOpen_ker_determinantPowerCharacter n s))
      (a.map (CuspidalDatum.twist s)) := by
  obtain ⟨r, ρ, rfl, hρ⟩ := ha
  refine ⟨r, fun i => (ρ i).twist s, ?_, hρ.twist s⟩
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

end PadicField.TopologicalData

end Langlands
