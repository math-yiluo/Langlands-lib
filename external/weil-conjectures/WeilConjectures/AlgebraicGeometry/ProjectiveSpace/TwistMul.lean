/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor

/-!
# Multiplication of Laurent monomial sections of the twisting sheaves

Let `Uᵢ = D₊(xᵢ)` be the standard opens of `ℙ(n; S)` and, for a set `s` of coordinates,
`U_s = ⋂_{i ∈ s} Uᵢ`. Through the canonical isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`
(`AlgebraicGeometry.ProjectiveSpace.twistTensorIso`), the product of the Laurent monomial
sections `xᵉ` of `𝒪(a)` and `xᵉ'` of `𝒪(b)` over `U_s` is the Laurent monomial section
`x^{e + e'}` of `𝒪(a + b)`
(`AlgebraicGeometry.ProjectiveSpace.twistTensorIso_hom_app_twistMonomialSection`). This is the
computation behind the Serre pairing: the product of sections corresponds to the product of
Laurent polynomials.

We also define the multiplication `𝒪(b) ⟶ 𝒪(a + b)` by a global section of `𝒪(a)`
(`AlgebraicGeometry.ProjectiveSpace.twistMulHom`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Proj

open ProjectiveSpectrum.Twist HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] {R : Type u} [CommRing R]

omit [Fintype n] in
/-- A nonnegative exponent vector supported on one coordinate. -/
lemma single_natCast_nonneg [DecidableEq n] (i : n) (k : ℕ) : 0 ≤ (Pi.single i (k : ℤ) : n → ℤ) :=
  Pi.single_nonneg.2 (Int.natCast_nonneg k)

/-- The monomial with exponent vector `k eᵢ` is `Xᵢ ^ k`. -/
lemma monomialToNat_single [DecidableEq n] (i : n) (k : ℕ) :
    monomialToNat R (Pi.single i (k : ℤ)) = X i ^ k := by
  rw [monomialToNat_eq_prod, Finset.prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

/-- `D₊(∏_{j ∈ s} Xⱼ) ⊆ D₊(Xᵢ)` for `i ∈ s`. -/
lemma basicOpen_monomialToNat_indicator_le {s : Set n} {i : n} (hi : i ∈ s) :
    Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)) ≤
      Proj.basicOpen (homogeneousSubmodule n R) (X i) := fun _ hx ↦
  mem_basicOpen_monomialToNat_indicator.1 hx i hi

/-- **The generator `Xᵢᵐ` of `𝒪(m)` on `D₊(Xᵢ)` restricts to the Laurent monomial `Xᵢᵐ`** on
`D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma twist_presheaf_map_twistPowSection {s : Set n} {i : n} (hi : i ∈ s) (m : ℤ) :
    (twist (homogeneousSubmodule n R) m).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_le hi)).op
        (twistPowSection m (X_mem_homogeneousSubmodule_one R i)) =
      twistMonomial R s (singleExponent (s := s) (m := m) hi) := by
  classical
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  rw [twist_presheaf_map_apply, val_twistPowSection_apply, coe_twistMonomial_apply]
  have h0 := indicator_one_nonneg s
  refine mk_eq_mk_of_monomialToNat (single_natCast_nonneg i m.toNat)
    (single_natCast_nonneg i (-m).toNat)
    (add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
      (neg_le_negExponentSum _)) (nsmul_nonneg h0 _) (monomialToNat_single i _).symm
    (monomialToNat_single i _).symm rfl rfl ?_
  ext j
  simp only [singleExponent, Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

variable {s : Set n} {a b : ℤ}

variable (a b) in
/-- The sum `e + e'` of exponent vectors of Laurent monomials of degrees `a` and `b` regular on
`D₊(∏_{i ∈ s} Xᵢ)`. -/
def addExponent (e : laurentExponents s a) (e' : laurentExponents s b) :
    laurentExponents s (a + b) :=
  ⟨e.1 + e'.1, by simp [Finset.sum_add_distrib, e.2.1, e'.2.1],
    fun i hi ↦ add_nonneg (e.2.2 i hi) (e'.2.2 i hi)⟩

/-- `(xᵉ / xᵢᵃ) (xᵉ' / xᵢᵇ) = x^{e + e'} / xᵢ^{a + b}`. -/
lemma awayMonomial_shiftExponent_mul {i : n} (hi : i ∈ s) (e : laurentExponents s a)
    (e' : laurentExponents s b) :
    awayMonomial R s (shiftExponent a hi e) * awayMonomial R s (shiftExponent b hi e') =
      awayMonomial R s (shiftExponent (a + b) hi (addExponent a b e e')) := by
  classical
  refine awayMonomial_mul _ _ _ ?_
  ext j
  simp only [shiftExponent, addExponent, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> ring

end Proj

namespace ProjectiveSpace

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type u} [Fintype n] (S : Scheme.{u})

/-- **The generator `e_i^{(m)}` restricts to the Laurent monomial `xᵢᵐ`** on `U_s ⊆ Uᵢ`, for
`i ∈ s`. -/
lemma twist_presheaf_map_twistGenerator {s : Set n} {i : n} (hi : i ∈ s) (m : ℤ) :
    (twist n S m).presheaf.map (homOfLE (preimage_basicOpenInt_le_standardOpen S hi)).op
        (twistGenerator n S m i) =
      twistMonomialSection S s (Proj.singleExponent (s := s) (m := m) hi) := by
  have h := pullbackSection_map (toProjInt n S)
    (Proj.basicOpen_monomialToNat_indicator_le (R := ULift.{u} ℤ) hi)
    (Proj.twistPowSection m (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i))
  rw [Proj.twist_presheaf_map_twistPowSection hi] at h
  exact h.symm

/-- **The product of Laurent monomial sections**: over `U_s` (`s` nonempty), the canonical
isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` sends `xᵉ ⊗ xᵉ'` to `x^{e + e'}`. -/
lemma twistTensorIso_hom_app_twistMonomialSection {s : Set n} (hs : s.Nonempty) {a b : ℤ}
    (e : laurentExponents s a) (e' : laurentExponents s b) :
    (twistTensorIso n S a b).hom.app (toProjInt n S ⁻¹ᵁ basicOpenInt n s)
        (tmulSection (twistMonomialSection S s e) (twistMonomialSection S s e')) =
      twistMonomialSection S s (Proj.addExponent a b e e') := by
  obtain ⟨i, hi⟩ := hs
  rw [twistMonomialSection_eq_smul hi e, twistMonomialSection_eq_smul hi e',
    twistMonomialSection_eq_smul hi (Proj.addExponent a b e e'),
    ← twist_presheaf_map_twistGenerator S hi a, ← twist_presheaf_map_twistGenerator S hi b,
    ← twist_presheaf_map_twistGenerator S hi (a + b), smul_tmulSection, tmulSection_smul,
    smul_smul, ← tmulSection_map, twistTensorIso_hom_app_smul, ← map_mul,
    Proj.awayMonomial_shiftExponent_mul]

omit [Fintype n] in
variable {S} in
/-- **Multiplication by a global section** `t` of `𝒪(a)`: the morphism `𝒪(b) ⟶ 𝒪(c)`, for
`a + b = c`, given by `x ↦ t x`, i.e. `𝒪(b) ≅ 𝒪 ⊗ 𝒪(b) ⟶ 𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` through the
canonical isomorphism `twistTensorIso`. -/
def twistMulHom {a b c : ℤ} (h : a + b = c) (t : Γ(twist n S a, ⊤)) :
    twist n S b ⟶ twist n S c :=
  (λ_ (twist n S b)).inv ≫ (homOfGlobalSection _ t ▷ twist n S b) ≫
    (twistTensorIso n S a b).hom ≫ eqToHom (by rw [h])

omit [Fintype n] in
variable {S} in
/-- `twistMulHom t` sends a section `x` over `U` to `t|_U x`. -/
lemma twistMulHom_app {a b : ℤ} (t : Γ(twist n S a, ⊤)) (U : (ℙ(n; S)).Opens)
    (x : Γ(twist n S b, U)) :
    (twistMulHom rfl t).app U x = (twistTensorIso n S a b).hom.app U
      (tmulSection ((twist n S a).presheaf.map (homOfLE le_top).op t) x) := by
  simp only [twistMulHom, eqToHom_refl, Category.comp_id, Hom.comp_app,
    ConcreteCategory.comp_apply, leftUnitor_inv_app]
  refine congrArg ((twistTensorIso n S a b).hom.app U) ?_
  exact (whiskerRight_app_tmulSection (homOfGlobalSection (twist n S a) t)
    (unitSectionsEquiv U 1) x).trans
    (congrArg (tmulSection · x) (homOfGlobalSection_app_one _ t U))

omit [Fintype n] in
variable {S} in
/-- `twistMulHom t` is additive in `t`. -/
lemma twistMulHom_add {a b c : ℤ} (h : a + b = c) (t t' : Γ(twist n S a, ⊤)) :
    twistMulHom h (t + t') = twistMulHom h t + twistMulHom h t' := by
  subst h
  ext U x
  rw [Hom.add_app, AddCommGrpCat.hom_add_apply, twistMulHom_app, twistMulHom_app,
    twistMulHom_app, map_add, add_tmulSection, map_add]

omit [Fintype n] in
variable {S} in
/-- `twistMulHom (r • t)` is `twistMulHom t` followed by multiplication by the global function
`r`. -/
lemma twistMulHom_smul {a b c : ℤ} (h : a + b = c) (r : Γ(ℙ(n; S), ⊤)) (t : Γ(twist n S a, ⊤)) :
    twistMulHom h (r • t) = twistMulHom h t ≫ (twist n S c).smulHom r := by
  subst h
  ext U x
  rw [Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app_apply, twistMulHom_app,
    twistMulHom_app, map_smul, smul_tmulSection, Hom.app_smul]

end ProjectiveSpace

end AlgebraicGeometry
