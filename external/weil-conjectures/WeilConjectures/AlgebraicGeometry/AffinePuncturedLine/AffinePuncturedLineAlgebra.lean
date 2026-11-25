/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Prod
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections

/-! # Units and Picard groups of the affine and punctured lines

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-affine-punctured-line-algebra; Stacks Project, Tags 03P4, 01HV, 0BCH and 01IB
(blueprint: lem-pur-affine-punctured-line-algebra).

The unit groups below are the actual values of the small etale unit sheaf at the terminal
object. Multiplicative notation reverses the additive convention of gmSheaf; ULift is retained.
The two summands of the cokernel are written as a product, their finite direct sum.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AffinePuncturedLine

/-- Global sections of the existing etale unit sheaf on Spec R, in multiplicative notation.
Source: Stacks, Tag 03P4 (2) (blueprint: lem-pur-affine-punctured-line-algebra). -/
abbrev specUnits (R : Type u) [CommRing R] :=
  Multiplicative ((Spec (CommRingCat.of R)).gmSheaf.obj.obj
    (op (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of R))))))

/-- A coordinate-ring unit as the corresponding actual global etale unit section.
This is the canonical Gamma(Spec R) identification, followed by the unit-sheaf type tags.
Source: Stacks, Tags 01HV (1) and 03P4 (2)
(blueprint: lem-pur-affine-punctured-line-algebra). -/
def specUnitSection (R : Type u) [CommRing R] (a : Rˣ) : specUnits R :=
  Multiplicative.ofAdd (ULift.up (Additive.ofMul
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom a)))

/-- The Laurent monomial a*t^n as a unit, with its specified inverse.
Source: blueprint lem-pur-affine-punctured-line-algebra, Laurent-unit computation
(blueprint: lem-pur-affine-punctured-line-algebra). -/
def laurentUnit (k : Type u) [Field k] (a : kˣ) (n : ℤ) : (LaurentPolynomial k)ˣ :=
  Units.map LaurentPolynomial.C.toMonoidHom a * (LaurentPolynomial.isUnit_T n).unit

private def specUnitEquiv (R : Type u) [CommRing R] : Rˣ ≃* specUnits R :=
  MulEquiv.ofBijective
    ({
      toFun := specUnitSection R
      map_one' := by
        change Multiplicative.ofAdd (ULift.up (Additive.ofMul _)) = _
        rw [map_one]
        rfl
      map_mul' := fun a b ↦ by
        change Multiplicative.ofAdd (ULift.up (Additive.ofMul _)) = _
        rw [map_mul]
        rfl } : Rˣ →* specUnits R)
    ((Multiplicative.ofAdd.bijective.comp ULift.up_bijective).comp
      (Additive.ofMul.bijective.comp (Units.map_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective)))
private theorem polyUnits (k : Type u) [Field k] :
    Function.Bijective (Units.map (Polynomial.C : k →+* Polynomial k).toMonoidHom) := by
  constructor
  · intro a b h
    apply Units.ext
    exact Polynomial.C_injective (congrArg Units.val h)
  · intro p
    obtain ⟨a, ⟨a, rfl⟩, ha⟩ := Polynomial.isUnit_iff.mp p.isUnit
    exact ⟨a, Units.ext ha⟩
private theorem laurentPID (k : Type u) [Field k] :
    IsPrincipalIdealRing (LaurentPolynomial k) := by
  refine ⟨fun J ↦ ?_⟩
  have h := (IsPrincipalIdealRing.principal (J.under (Polynomial k))).map_ringHom
    (algebraMap (Polynomial k) (LaurentPolynomial k))
  rwa [IsLocalization.map_under (Submonoid.powers (Polynomial.X : Polynomial k))] at h

private theorem laurentSurj (k : Type u) [Field k] :
    Function.Surjective (fun p : kˣ × ℤ ↦ laurentUnit k p.1 p.2) := by
  intro u
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (u : LaurentPolynomial k)
  have hpunit : IsUnit (algebraMap (Polynomial k) (LaurentPolynomial k) p) := by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, hp]
    exact u.isUnit.mul (LaurentPolynomial.isUnit_T _)
  obtain ⟨_, ⟨m, rfl⟩, hpm⟩ :=
    (IsLocalization.algebraMap_isUnit_iff (Submonoid.powers (Polynomial.X : Polynomial k))
      (S := LaurentPolynomial k)).mp hpunit
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (Polynomial.prime_X) m).mp hpm
  obtain ⟨c, hc⟩ := hi.symm
  obtain ⟨a, ha⟩ := (polyUnits k).2 c
  have hp' : p = Polynomial.X ^ i * Polynomial.C (a : k) := by
    rw [← hc, ← ha]
    rfl
  refine ⟨(a, (i : ℤ) - n), Units.ext ?_⟩
  apply (LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_injective
  change (LaurentPolynomial.C (a : k) * LaurentPolynomial.T ((i : ℤ) - n)) *
    LaurentPolynomial.T n = (u : LaurentPolynomial k) * LaurentPolynomial.T n
  rw [LaurentPolynomial.mul_T_assoc, sub_add_cancel, ← hp, hp', map_mul,
    Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, mul_comm]

private theorem picPID (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    Subsingleton (Spec (CommRingCat.of R)).Pic := by
  let X := Spec (CommRingCat.of R)
  let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(X, ⊤) := e.toMulEquiv.isDomain R
  have : IsPrincipalIdealRing Γ(X, ⊤) :=
    IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  have htriv (M : X.Modules) [M.IsInvertible] :
      Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) := by
    have := Scheme.Modules.invertible_sections_of_isAffineOpen M (isAffineOpen_top X)
    obtain ⟨f⟩ := CommRing.Pic.mk_eq_one_iff.mp
      (Subsingleton.elim (CommRing.Pic.mk Γ(X, ⊤) Γ(M, ⊤)) 1)
    have hg : Scheme.Modules.IsFreeGenerator (f.symm 1) :=
      Scheme.Modules.isFreeGenerator_of_bijective_smul M (isAffineOpen_top X) (by
        convert f.symm.bijective using 1
        ext r
        simp only [← map_smul, smul_eq_mul, mul_one])
    apply Scheme.Modules.nonempty_iso_of_isFreeGenerator
      (U := fun _ : Unit ↦ (⊤ : X.Opens)) (e := fun _ ↦ f.symm 1)
      (N := SheafOfModules.unit X.ringCatSheaf)
      (f := fun _ ↦ (1 : Γ(X, ⊤))) (by simp) (fun _ ↦ hg)
    · intro i j W hi hj a b hab
      have hh : a = b := (hg.map hi).smul_left_injective (by
        simpa only [Subsingleton.elim hj hi] using hab)
      subst b
      rfl
    · intro i
      exact Scheme.Modules.isFreeGenerator_one _
  refine ⟨fun L L' ↦ Scheme.Pic.eq_iff_nonempty_iso.mpr ?_⟩
  have := L.isInvertible
  have := L'.isInvertible
  have := Scheme.Modules.IsInvertible.of_sheafOfModules
    ((fromSkeleton X.Modules).obj L.val)
  have := Scheme.Modules.IsInvertible.of_sheafOfModules
    ((fromSkeleton X.Modules).obj L'.val)
  obtain ⟨f⟩ := htriv ((fromSkeleton X.Modules).obj L.val)
  obtain ⟨g⟩ := htriv ((fromSkeleton X.Modules).obj L'.val)
  exact ⟨f ≪≫ g.symm⟩

private theorem laurentInj (k : Type u) [Field k] :
    Function.Injective (fun p : kˣ × ℤ ↦ laurentUnit k p.1 p.2) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  have hval : LaurentPolynomial.C (a : k) * LaurentPolynomial.T n =
      LaurentPolynomial.C (b : k) * LaurentPolynomial.T m := congrArg Units.val h
  have hdeg := congrArg LaurentPolynomial.degree hval
  rw [LaurentPolynomial.degree_C_mul_T n _ a.ne_zero,
    LaurentPolynomial.degree_C_mul_T m _ b.ne_zero] at hdeg
  have hnm : n = m := WithBot.coe_injective hdeg
  subst m
  have ha : (a : k) = b := by
    have hh := (LaurentPolynomial.isUnit_T n).mul_left_injective hval
    have hc := congrArg (fun p : LaurentPolynomial k ↦ p.coeff 0) hh
    simpa using hc
  exact Prod.ext (Units.ext ha) rfl
private def laurentEquiv (k : Type u) [Field k] :
    (kˣ × Multiplicative ℤ) ≃* (LaurentPolynomial k)ˣ :=
  MulEquiv.ofBijective
    ({
      toFun := fun p ↦ laurentUnit k p.1 p.2.toAdd
      map_one' := by
        apply Units.ext
        change LaurentPolynomial.C (1 : k) * LaurentPolynomial.T 0 = 1
        simp
      map_mul' := fun a b ↦ by
        apply Units.ext
        change LaurentPolynomial.C ((a.1 : k) * b.1) *
          LaurentPolynomial.T (a.2.toAdd + b.2.toAdd) =
          (LaurentPolynomial.C (a.1 : k) * LaurentPolynomial.T a.2.toAdd) *
          (LaurentPolynomial.C (b.1 : k) * LaurentPolynomial.T b.2.toAdd)
        rw [map_mul, LaurentPolynomial.T_add]
        ring } : (kˣ × Multiplicative ℤ) →* (LaurentPolynomial k)ˣ)
    ⟨laurentInj k, laurentSurj k⟩
private def coordMap (k : Type u) [Field k] (N : ℕ) :
    (kˣ × Multiplicative ℤ) →*
      ((kˣ ⧸ (powMonoidHom N).range) × Multiplicative (ZMod N)) where
  toFun p := (QuotientGroup.mk p.1, Multiplicative.ofAdd (p.2.toAdd : ZMod N))
  map_one' := by
    apply Prod.ext
    · exact map_one (QuotientGroup.mk' _)
    · change Multiplicative.ofAdd ((0 : ℤ) : ZMod N) = 1
      simp
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul (QuotientGroup.mk' _) a.1 b.1
    · change Multiplicative.ofAdd ((a.2.toAdd + b.2.toAdd : ℤ) : ZMod N) = _
      rw [Int.cast_add]
      rfl
private theorem coordSurj (k : Type u) [Field k] (N : ℕ) :
    Function.Surjective (coordMap k N) := by
  rintro ⟨a, n⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective n.toAdd
  exact ⟨(a, Multiplicative.ofAdd n), Prod.ext rfl (congrArg Multiplicative.ofAdd hn)⟩
private theorem coordKer (k : Type u) [Field k] (N : ℕ) :
    (powMonoidHom N : (kˣ × Multiplicative ℤ) →* _).range = (coordMap k N).ker := by
  ext p
  change (∃ q : kˣ × Multiplicative ℤ, q ^ N = p) ↔ _
  change _ ↔ (QuotientGroup.mk p.1,
    Multiplicative.ofAdd (p.2.toAdd : ZMod N)) = (1, 1)
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, n⟩, rfl⟩
    constructor
    · exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    · change Multiplicative.ofAdd ((N • n.toAdd : ℤ) : ZMod N) = 1
      simp
  · rintro ⟨ha, hn⟩
    obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp ha
    have hn' : (p.2.toAdd : ZMod N) = 0 := congrArg Multiplicative.toAdd hn
    obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd p.2.toAdd N).mp hn'
    refine ⟨(a, Multiplicative.ofAdd n), Prod.ext ha ?_⟩
    apply Multiplicative.toAdd.injective
    change N • n = p.2.toAdd
    simpa [nsmul_eq_mul] using hn.symm
private def sectionEquiv (k : Type u) [Field k] :
    (kˣ × Multiplicative ℤ) ≃* specUnits (LaurentPolynomial k) :=
  (laurentEquiv k).trans (specUnitEquiv _)
private def quotientEquiv (k : Type u) [Field k] (N : ℕ) :
    (specUnits (LaurentPolynomial k) ⧸ (powMonoidHom N).range) ≃*
      ((kˣ ⧸ (powMonoidHom N).range) × Multiplicative (ZMod N)) :=
  QuotientGroup.liftEquiv _
    (φ := (coordMap k N).comp (sectionEquiv k).symm.toMonoidHom)
    ((coordSurj k N).comp (sectionEquiv k).symm.surjective) (by
      ext x
      change (∃ y : specUnits (LaurentPolynomial k), y ^ N = x) ↔
        coordMap k N ((sectionEquiv k).symm x) = 1
      rw [← MonoidHom.mem_ker, ← coordKer]
      change _ ↔ ∃ y : kˣ × Multiplicative ℤ, y ^ N = (sectionEquiv k).symm x
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨(sectionEquiv k).symm y, by rw [← map_pow, hy]⟩
      · rintro ⟨y, hy⟩
        exact ⟨sectionEquiv k y, by rw [← map_pow, hy, MulEquiv.apply_symm_apply]⟩)
private theorem quotientEquiv_apply (k : Type u) [Field k] (N : ℕ) (a : kˣ) (n : ℤ) :
    quotientEquiv k N
      (QuotientGroup.mk (specUnitSection (LaurentPolynomial k) (laurentUnit k a n))) =
        (QuotientGroup.mk a, Multiplicative.ofAdd (n : ZMod N)) := by
  change coordMap k N ((sectionEquiv k).symm (sectionEquiv k (a, .ofAdd n))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl
private theorem quotientCyclic (k : Type u) [Field k] (N : ℕ)
    (h : ∀ a : kˣ, ∃ b : kˣ, b ^ N = a)
    (x : specUnits (LaurentPolynomial k) ⧸ (powMonoidHom N).range) :
    ∃ n : ℤ, x = (QuotientGroup.mk
      (specUnitSection (LaurentPolynomial k) (laurentUnit k 1 1))) ^ n := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (quotientEquiv k N x).1
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (quotientEquiv k N x).2.toAdd
  refine ⟨n, (quotientEquiv k N).injective ?_⟩
  rw [map_zpow, quotientEquiv_apply]
  apply Prod.ext
  · change (quotientEquiv k N x).1 = (QuotientGroup.mk (1 : kˣ)) ^ n
    rw [← ha]
    have ha1 : (QuotientGroup.mk a : kˣ ⧸ (powMonoidHom N).range) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h a)
    simpa using ha1
  · apply Multiplicative.toAdd.injective
    simpa using hn.symm
private theorem scalarRoots (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ) (hN : 1 ≤ N)
    (a : kˣ) : ∃ b : kˣ, b ^ N = a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (show 0 < N from hN)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hb
    exact a.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩

/-- The canonical unit descriptions, the two Picard vanishings and the power-map cokernel.
Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-affine-punctured-line-algebra; Stacks, Tags 03P4, 01HV, 0BCH and 01IB
(blueprint: lem-pur-affine-punctured-line-algebra).

Proof:
1. By the defining value of gmSheaf at the terminal etale object, its global sections are
   Gamma(X, O_X)^units. GammaSpecIso identifies this group on Spec R with R^units.
2. If two nonzero polynomials multiply to one, their degrees add to zero. Both are constant;
   conversely every nonzero scalar is a unit [def-weil-field, def-weil-polynomial-ring].
3. For Laurent polynomials, the least and greatest nonzero exponents add under multiplication.
   If uv=1, their two widths add to zero, so both widths vanish. Thus each unit has a unique
   expression a*t^n, and its inverse is a^(-1)*t^(-n) [def-weil-laurent-polynomial-ring].
4. The polynomial ring is a PID [lem-pur-polynomial-field-pid]. For a Laurent ideal J, contract
   to k[T], choose its generator g, and write each x in J as f/T^n. Then f=T^n*x belongs to
   the contracted ideal, hence x belongs to gB; conversely gB is contained in J. The extreme
   coefficient computation proves the Laurent ring is a domain, so it too is a PID.
5. For any invertible module sheaf L on either affine scheme, its section module M has
   bijective evaluation Hom(M,R) tensor M -> R [lem-sc-affine-invertible-sections]. Over the
   PIDs in step 4 it is isomorphic to R [lem-pur-pid-invertible-module-trivial].
6. Invertible sheaves are quasi-coherent [def-sc-invertible-module]. Apply the affine tilde/
   Gamma functor and its quasi-coherent counit to the section-module isomorphism from step 5
   [lem-weil-pbc-affine-tilde-gamma-adjunction]. It gives L isomorphic to O_X, the identity
   Picard class [def-sc-picard-group]. This works over any field, without algebraic closure.
7. In the unique coordinates (a,n), the N-th power map is (a,n) -> (a^N,N*n). The map taking
   a*t^n to ([a],[n]) is surjective, with kernel precisely the N-th powers. The inverse on
   quotient classes sends ([a],[n]) to [a*t^n]; changing representatives multiplies this by
   an N-th power, so it is well defined. This gives the specified group isomorphism.
8. When every scalar unit is an N-th power, the scalar quotient vanishes. The remaining
   Z/N is generated by [1], hence by the class of t. The scalar assumption is precisely
   surjectivity of its power map. For algebraically closed k a root of X^N-a is nonzero
   whenever a is nonzero. For N=1 the quotient and its distinguished generator are trivial.
   The characteristic restriction is retained, though the algebra works without it. -/
theorem affine_punctured_line_algebra (k : Type u) [Field k] :
    Function.Bijective (fun a : kˣ ↦
      specUnitSection (Polynomial k) (Units.map Polynomial.C.toMonoidHom a)) ∧
    Function.Bijective (fun p : kˣ × ℤ ↦
      specUnitSection (LaurentPolynomial k) (laurentUnit k p.1 p.2)) ∧
    Subsingleton (Spec (CommRingCat.of (Polynomial k))).Pic ∧
    Subsingleton (Spec (CommRingCat.of (LaurentPolynomial k))).Pic ∧
    (∀ (N : ℕ), 1 ≤ N → IsUnit (N : k) →
      (∃ e :
          (specUnits (LaurentPolynomial k) ⧸ (powMonoidHom N).range) ≃*
            ((kˣ ⧸ (powMonoidHom N).range) × Multiplicative (ZMod N)),
        ∀ (a : kˣ) (n : ℤ),
          e (QuotientGroup.mk (specUnitSection (LaurentPolynomial k) (laurentUnit k a n))) =
            (QuotientGroup.mk a, Multiplicative.ofAdd (n : ZMod N))) ∧
      ((∀ a : kˣ, ∃ b : kˣ, b ^ N = a) →
        (∀ x : specUnits (LaurentPolynomial k) ⧸ (powMonoidHom N).range,
          ∃ n : ℤ, x =
            (QuotientGroup.mk
              (specUnitSection (LaurentPolynomial k) (laurentUnit k 1 1))) ^ n) ∧
        Function.Surjective (fun a : kˣ ↦ a ^ N)) ∧
      (IsAlgClosed k → ∀ a : kˣ, ∃ b : kˣ, b ^ N = a)) := by
  refine ⟨(specUnitEquiv _).bijective.comp (polyUnits k), ?_, picPID _, ?_, ?_⟩
  · exact (specUnitEquiv _).bijective.comp ⟨laurentInj k, laurentSurj k⟩
  · have := laurentPID k
    exact picPID _
  · intro N hN _
    refine ⟨⟨quotientEquiv k N, quotientEquiv_apply k N⟩, ?_, ?_⟩
    · intro h
      exact ⟨quotientCyclic k N h, h⟩
    · intro h
      have := h
      exact scalarRoots k N hN

end AlgebraicGeometry.AffinePuncturedLine
