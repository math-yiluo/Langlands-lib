/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Module.Torsion.Field
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Conditional coefficient hypotheses after a finite cover

Source: Stacks Project, Tag 03SD, `lemma-vanishing-easier`, first paragraph;
Tag 095R, `lemma-finite-pushforward-constructible`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

private theorem prime_nsmul_eq_zero (r : ℕ) [Fact r.Prime]
    {M : Type (u + 1)} [AddCommGroup M] [Module (ULift.{u + 1} (ZMod r)) M]
    (x : M) : r • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod r)),
    CharP.cast_eq_zero (ULift.{u + 1} (ZMod r)) r, zero_smul]

private theorem prime_dvd_of_nsmul_eq_zero (r : ℕ) [Fact r.Prime]
    {M : Type (u + 1)} [AddCommGroup M] [Module (ULift.{u + 1} (ZMod r)) M]
    {x : M} (hx : x ≠ 0) {n : ℕ} (hn : n • x = 0) : r ∣ n := by
  have hnx : (n : ULift.{u + 1} (ZMod r)) • x = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hn
  have hn0 := (smul_eq_zero.mp hnx).resolve_right hx
  exact (ZMod.natCast_eq_zero_iff n r).mp (congrArg ULift.down hn0)

private theorem isZero_of_stalk_zero {R : Type (u + 1)} [CommRing R]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ↥((Scheme.pointSmallEtale s).sheafFiber.obj F)), x = 0) :
    Limits.IsZero F := by
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  apply (Limits.IsZero.iff_id_eq_zero F).mpr
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro s
  have := (Scheme.pointSmallEtale (X.algClosurePoint s)).sheafFiber_additive
    (A := ModuleCat.{u + 1} R)
  ext x
  simpa using h _ (X.algClosurePoint s) x

private theorem finiteCoverLowerShriek_isZero {R : Type (u + 1)} [CommRing R]
    {X U V : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : V ⟶ U)
    (hF : Limits.IsZero ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj G)) :
    Limits.IsZero ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
        ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G))) := by
  have hG : Limits.IsZero G :=
    ((Etale.upperStar (ModuleCat.{u + 1} R) j).map_isZero hF).of_iso
      (asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} R) j).unit.app G))
  exact (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).map_isZero
    ((Etale.lowerStar (ModuleCat.{u + 1} R) v).map_isZero
      ((Etale.upperStar (ModuleCat.{u + 1} R) v).map_isZero hG))

/-- Finite etale pushforward preserves finite local constancy. Use the trivial
stratification on the open and extend by zero over its closed complement.
Source: Stacks Project, Tags 095B and 095R. -/
theorem finiteCoverLowerShriek_constructible {k : Type u}
    [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] :
    Scheme.IsConstructibleSheaf
      ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))) := by
  let R := ULift.{u + 1} (ZMod r)
  let H := (Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
    ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G)
  have : Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G) :=
    Scheme.IsFiniteLocallyConstantSheaf.upperStar v G
  have : Scheme.IsFiniteLocallyConstantSheaf H :=
    Scheme.finiteLocallyConstant_lowerStar_of_finite_etale v _
  have : Scheme.IsConstructibleSheaf H :=
    ⟨Scheme.Stratification.trivial U, fun _ ↦
      Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 U) H⟩
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  exact Scheme.IsConstructibleSheaf.openImmersionLowerShriek
    j j.closedComplement j.range_closedComplement H

/-- Torsion substatement retained as a separately reviewable obligation.
Source: Stacks Project, Tag 03SD.
(auxiliary lemma; not a blueprint node) -/
theorem finiteCoverLowerShriek_torsion {k : Type u}
    [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] :
    let R := ULift.{u + 1} (ZMod r)
    let F := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj G
    let K := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
        ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G))
    (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) K) ∧
      (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        Scheme.IsPrimaryTorsionSheaf R F p → Scheme.IsPrimaryTorsionSheaf R K p) := by
  let R := ULift.{u + 1} (ZMod r)
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let F := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj G
  let K := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
    ((Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
      ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G))
  change (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) K) ∧
    (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
      Scheme.IsPrimaryTorsionSheaf R F p → Scheme.IsPrimaryTorsionSheaf R K p)
  refine ⟨?_, ?_⟩
  · intro hF
    by_cases hr : IsUnit (r : Γ(Spec (.of k), ⊤))
    · refine ⟨fun Ω _ _ s x ↦ ⟨r, (Fact.out : r.Prime).pos, hr, ?_⟩⟩
      exact prime_nsmul_eq_zero r x
    · have hzF : Limits.IsZero F := isZero_of_stalk_zero F (by
        intro Ω _ _ s x
        by_contra hx
        obtain ⟨n, -, hn, hnx⟩ := hF.exists_isUnit_nsmul_eq_zero Ω s x
        obtain ⟨m, hm⟩ := prime_dvd_of_nsmul_eq_zero r hx hnx
        rw [hm, Nat.cast_mul] at hn
        exact hr (IsUnit.mul_iff.mp hn).1)
      have hzK : Limits.IsZero K := finiteCoverLowerShriek_isZero j G v hzF
      refine ⟨fun Ω _ _ s x ↦ ⟨1, Nat.zero_lt_one,
        by simpa only [Nat.cast_one] using
          (isUnit_one : IsUnit (1 : Γ(Spec (.of k), ⊤))), ?_⟩⟩
      have := (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} R)
      have := ModuleCat.subsingleton_of_isZero
        ((Scheme.pointSmallEtale s).sheafFiber.map_isZero hzK)
      exact Subsingleton.elim _ _
  · intro p _ _ hF
    by_cases hp : p = r
    · subst p
      intro Ω _ _ s x
      exact ⟨1, by simpa only [pow_one] using prime_nsmul_eq_zero r x⟩
    · have hzF : Limits.IsZero F := isZero_of_stalk_zero F (by
        intro Ω _ _ s x
        by_contra hx
        obtain ⟨n, hn⟩ := hF Ω s x
        have hd := prime_dvd_of_nsmul_eq_zero r hx hn
        have hdp := (Fact.out : r.Prime).dvd_of_dvd_pow hd
        exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime)
          (Fact.out : p.Prime)).mp hdp).symm)
      have hzK : Limits.IsZero K := finiteCoverLowerShriek_isZero j G v hzF
      intro Ω _ _ s x
      have := (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} R)
      have := ModuleCat.subsingleton_of_isZero
        ((Scheme.pointSmallEtale s).sheafFiber.map_isZero hzK)
      exact ⟨0, Subsingleton.elim _ _⟩


/-- The coefficient hypotheses needed for retract descent pass to the finite-cover sheaf.
This statement contains no cohomology assertions and does not assume a unit retraction.

Source: Stacks Project, Tag 03SD, `lemma-vanishing-easier`, first paragraph;
Tag 095R, `lemma-finite-pushforward-constructible`.
(auxiliary lemma; not a blueprint node)

Proof: Write F = j_!G and K = j_!(v_*v^*G). Pullback preserves finite locally constant
sheaves. A finite etale map is etale-locally a finite disjoint union of copies of its base;
a common trivializing refinement for the finitely many summands shows that v_*v^*G is
finite locally constant. This part is already stated as
`Scheme.finiteLocallyConstant_lowerStar_of_finite_etale`
(lem-weil-pbc-etale-finite-pushforward-locally-constant), whose finite-ring hypothesis
holds for R = ULift(ZMod r). The open U is Noetherian because it is open in a finite-type
curve over a field. Thus v_*v^*G is constructible; extension by zero preserves
constructibility (equivalently use Tag 095R for finite pushforward).
Every stalk of every R-module sheaf is killed by r, since r is zero in R.
If F is zero, the fully faithful extension by zero gives G zero; pullback and direct
image preserve zero, so K is zero and both torsion implications hold. Otherwise,
conservativity of geometric stalks gives a nonzero element x in a stalk of F.
If F is p-primary then p^n kills x for some n. When p differs from r, Bezout for r
and p^n would give x = 0, a contradiction. Thus p = r, and r itself kills every
stalk element of K, proving primary torsion with exponent one.
If F has invertible-order torsion, some positive n invertible on Spec k kills x.
The same Bezout argument shows r divides n. Writing n = r*m, invertibility of n
implies invertibility of r in the commutative ring of global sections of Spec k.
Since r kills every stalk element of K, choosing n = r proves invertible-order torsion.
These arguments also handle the empty open, empty cover, and zero G. -/
theorem finiteCoverLowerShriek_coefficient_compatibility {k : Type u}
    [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] :
    let R := ULift.{u + 1} (ZMod r)
    let F := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj G
    let K := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
        ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G))
    Scheme.IsConstructibleSheaf K ∧
      (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F →
        Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) K) ∧
      (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        Scheme.IsPrimaryTorsionSheaf R F p → Scheme.IsPrimaryTorsionSheaf R K p) := by
  let R := ULift.{u + 1} (ZMod r)
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let F := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj G
  let K := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
    ((Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
      ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G))
  change Scheme.IsConstructibleSheaf K ∧
    (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F →
      Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) K) ∧
    (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
      Scheme.IsPrimaryTorsionSheaf R F p → Scheme.IsPrimaryTorsionSheaf R K p)
  refine ⟨finiteCoverLowerShriek_constructible f j r G v, ?_, ?_⟩
  · intro hF
    by_cases hr : IsUnit (r : Γ(Spec (.of k), ⊤))
    · refine ⟨fun Ω _ _ s x ↦ ⟨r, (Fact.out : r.Prime).pos, hr, ?_⟩⟩
      exact prime_nsmul_eq_zero r x
    · have hzF : Limits.IsZero F := isZero_of_stalk_zero F (by
        intro Ω _ _ s x
        by_contra hx
        obtain ⟨n, -, hn, hnx⟩ := hF.exists_isUnit_nsmul_eq_zero Ω s x
        obtain ⟨m, hm⟩ := prime_dvd_of_nsmul_eq_zero r hx hnx
        rw [hm, Nat.cast_mul] at hn
        exact hr (IsUnit.mul_iff.mp hn).1)
      have hzK : Limits.IsZero K := finiteCoverLowerShriek_isZero j G v hzF
      refine ⟨fun Ω _ _ s x ↦ ⟨1, Nat.zero_lt_one,
        by simpa only [Nat.cast_one] using
          (isUnit_one : IsUnit (1 : Γ(Spec (.of k), ⊤))), ?_⟩⟩
      have := (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} R)
      have := ModuleCat.subsingleton_of_isZero
        ((Scheme.pointSmallEtale s).sheafFiber.map_isZero hzK)
      exact Subsingleton.elim _ _
  · intro p _ _ hF
    by_cases hp : p = r
    · subst p
      intro Ω _ _ s x
      exact ⟨1, by simpa only [pow_one] using prime_nsmul_eq_zero r x⟩
    · have hzF : Limits.IsZero F := isZero_of_stalk_zero F (by
        intro Ω _ _ s x
        by_contra hx
        obtain ⟨n, hn⟩ := hF Ω s x
        have hd := prime_dvd_of_nsmul_eq_zero r hx hn
        have hdp := (Fact.out : r.Prime).dvd_of_dvd_pow hd
        exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime)
          (Fact.out : p.Prime)).mp hdp).symm)
      have hzK : Limits.IsZero K := finiteCoverLowerShriek_isZero j G v hzF
      intro Ω _ _ s x
      have := (Scheme.pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} R)
      have := ModuleCat.subsingleton_of_isZero
        ((Scheme.pointSmallEtale s).sheafFiber.map_isZero hzK)
      exact ⟨0, Subsingleton.elim _ _⟩

end AlgebraicGeometry.IsCurve
