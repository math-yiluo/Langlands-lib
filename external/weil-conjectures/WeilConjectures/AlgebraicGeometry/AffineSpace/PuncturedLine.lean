/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Polynomial.Basic
public import WeilConjectures.RingTheory.Kaehler.TraceDualityField
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.AlgebraicGeometry.Modules.PicardAffine
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Units and Picard groups of the affine line and the punctured line

Let `k` be a field, `𝔸¹_k = 𝔸(ULift (Fin 1); Spec k) = Spec k[t]` and `𝔾_{m,k}` the open
complement of the zero section, given by an open immersion `j : G ⟶ 𝔸¹_k` whose image is the
complement of the zero section (equivalently the basic open `D(t)`). We compute

* `Γ(𝔸¹_k, 𝒪)ˣ = kˣ` and `Γ(𝔾_{m,k}, 𝒪)ˣ = kˣ · tᶻ`;
* `Pic(𝔸¹_k) = Pic(𝔾_{m,k}) = 0`, the rings `k[t]` and `k[t, t⁻¹]` being principal;
* the cokernel of the `N`-th power map on `Γ(𝔾_{m,k}, 𝒪)ˣ`.

## Main statements

- `IsLocalization.Away.bijective_unitsProdZPowHom`: the units of `A[1/t]`, `t` prime in a domain
  `A`, are `Aˣ × tᶻ`.
- `AlgebraicGeometry.Scheme.Pic.subsingleton_of_isAffine`: the Picard group of an affine scheme
  whose ring of functions is a unique factorization domain vanishes.
- `AlgebraicGeometry.AffineSpace.unitLineCoord`: the coordinate `t` as a unit on `𝔾_{m,k}`.
- `AlgebraicGeometry.AffineSpace.units_pic_line_and_multiplicativeGroup`: the blueprint lemma
  `lem-pur-affine-punctured-line-algebra`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace IsLocalization.Away

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] (t : A)
  [IsLocalization.Away t B]

/-- The homomorphism `Aˣ × tᶻ → Bˣ`, `(a, m) ↦ a tᵐ`, for a localization `B = A[1/t]`. -/
noncomputable def unitsProdZPowHom : Aˣ × Multiplicative ℤ →* Bˣ :=
  (Units.map (algebraMap A B : A →* B)).coprod
    (zpowersHom Bˣ (IsLocalization.Away.algebraMap_isUnit (S := B) t).unit)

omit [IsDomain A] in
lemma val_unitsProdZPowHom_apply (a : Aˣ) (m : Multiplicative ℤ) :
    (unitsProdZPowHom (B := B) t (a, m) : B) =
      algebraMap A B a * ((IsLocalization.Away.algebraMap_isUnit (S := B) t).unit ^ m.toAdd :
        Bˣ) :=
  rfl

variable {t}

/-- The units of the localization `A[1/t]` of a domain at a prime element `t` are the products
`a tᵐ` with `a ∈ Aˣ` and `m ∈ ℤ`, uniquely. -/
theorem bijective_unitsProdZPowHom (ht : Prime t) :
    Function.Bijective (unitsProdZPowHom (B := B) t) := by
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B (M := Submonoid.powers t)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ht.ne_zero)
  have hτ := IsLocalization.Away.algebraMap_isUnit (S := B) t
  refine ⟨(injective_iff_map_eq_one _).2 ?_, fun u ↦ ?_⟩
  · rintro ⟨a, m⟩ h
    have h' := congrArg Units.val h
    rw [val_unitsProdZPowHom_apply, Units.val_one] at h'
    obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m.toAdd
    · rw [hk, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow,
        ← map_mul, ← map_one (algebraMap A B)] at h'
      have h1 : (a : A) * t ^ k = 1 := hinj h'
      have hk0 : k = 0 := by
        by_contra hk0
        exact ht.not_isUnit (isUnit_of_mul_isUnit_left (x := t) (y := t ^ (k - 1)) (by
          rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
          exact isUnit_of_mul_isUnit_right (x := (a : A)) (h1 ▸ isUnit_one)))
      subst hk0
      rw [pow_zero, mul_one] at h1
      refine Prod.ext (Units.ext h1) (Multiplicative.toAdd.injective ?_)
      rw [hk]
      rfl
    · have h2 : Units.map (algebraMap A B : A →* B) a = hτ.unit ^ k := by
        have := h
        rw [unitsProdZPowHom, MonoidHom.coprod_apply, zpowersHom_apply, hk, zpow_neg,
          zpow_natCast, mul_inv_eq_one] at this
        exact this
      have h' := congrArg Units.val h2
      rw [Units.coe_map, Units.val_pow_eq_pow_val, IsUnit.unit_spec, MonoidHom.coe_ofClass,
        ← map_pow] at h'
      have h1 : (a : A) = t ^ k := hinj h'
      rcases k with _ | k
      · refine Prod.ext (Units.ext (by simpa using h1)) (Multiplicative.toAdd.injective ?_)
        rw [hk]
        rfl
      · exact absurd (isUnit_of_dvd_unit (dvd_pow_self t (Nat.succ_ne_zero k))
          (h1 ▸ a.isUnit)) ht.not_isUnit
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj t (u : B)
    have hua : IsUnit (algebraMap A B a) := by
      rw [← ha]
      exact u.isUnit.mul (hτ.pow n)
    obtain ⟨m, hm⟩ := (IsLocalization.Away.algebraMap_isUnit_iff t).1 hua
    obtain ⟨i, -, v, hv⟩ := (dvd_prime_pow ht m).1 hm
    refine ⟨(v⁻¹, Multiplicative.ofAdd ((i : ℤ) - n)), ?_⟩
    rw [unitsProdZPowHom, MonoidHom.coprod_apply, zpowersHom_apply, toAdd_ofAdd, zpow_sub,
      zpow_natCast, zpow_natCast, ← mul_assoc, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec]
    rw [ha, ← map_pow, ← map_mul, ← hv, mul_comm, Units.mul_inv_cancel_right]

end IsLocalization.Away


/-- The cokernel of the `N`-th power map on `K × ℤ` (written additively) is
`K/N × ℤ/N`, through `(c, m) ↦ ([c], m mod N)`. -/
theorem AddMonoidHom.ker_prodMap_mk_intCast {K : Type*} [AddCommGroup K] (N : ℕ) :
    ((QuotientAddGroup.mk' (zsmulAddGroupHom (α := K) N).range).prodMap
        (Int.castAddHom (ZMod N))).ker =
      (zsmulAddGroupHom (α := K × ℤ) N).range := by
  ext ⟨c, m⟩
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  change ((QuotientAddGroup.mk c : K ⧸ _), ((m : ℤ) : ZMod N)) = 0 ↔ _
  rw [Prod.mk_eq_zero, QuotientAddGroup.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd,
    AddMonoidHom.mem_range]
  constructor
  · rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩
    refine ⟨(d, e), Prod.ext hd ?_⟩
    change (N : ℤ) • e = m
    rw [he, smul_eq_mul]
  · rintro ⟨⟨d, e⟩, h⟩
    exact ⟨⟨d, congrArg Prod.fst h⟩, ⟨e, (congrArg Prod.snd h).symm⟩⟩

namespace AlgebraicGeometry

open Scheme

/-- **The Picard group of an affine scheme with factorial ring of functions is trivial.** An
invertible module has a free generator over the whole (affine) scheme
(`AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_of_uniqueFactorizationMonoid`), hence
is isomorphic to the structure sheaf. -/
theorem Scheme.Pic.subsingleton_of_isAffine (X : Scheme.{u}) [IsAffine X] [IsDomain Γ(X, ⊤)]
    [UniqueFactorizationMonoid Γ(X, ⊤)] : Subsingleton X.Pic := by
  suffices h : ∀ L : X.Pic, L = 1 from ⟨fun L L' ↦ (h L).trans (h L').symm⟩
  intro L
  have := L.isInvertible
  obtain ⟨e, he⟩ := Modules.exists_isFreeGenerator_of_uniqueFactorizationMonoid
    ((fromSkeleton X.Modules).obj L.val) (isAffineOpen_top X)
  obtain ⟨φ⟩ := Modules.nonempty_iso_of_isFreeGenerator (ι := Unit) (U := fun _ ↦ ⊤)
    (N := Modules.unit X) (by simp) (fun _ ↦ he) (f := fun _ ↦ (1 : Γ(X, ⊤)))
    (fun _ _ W hi hj a b hab ↦ by
      obtain rfl : hi = hj := rfl
      rw [(he.map hi).smul_left_injective hab]) (fun _ ↦ Modules.isFreeGenerator_one ⊤)
  exact Pic.eq_iff_nonempty_iso.2 ⟨φ ≪≫ Pic.oneIso.symm⟩

namespace AffineSpace

variable (S : Scheme.{u})

/-- The coordinate `t` of the affine line `𝔸¹_S = 𝔸(ULift (Fin 1); S)`. -/
noncomputable abbrev lineCoord : Γ(𝔸(ULift.{u} (Fin 1); S), ⊤) :=
  coord S (ULift.up 0)

lemma range_coord_line : Set.range (coord (n := ULift.{u} (Fin 1)) S) = {lineCoord S} := by
  rw [Set.range_unique]
  rfl

/-- The zero section of the affine line is the zero locus `V(t)` of the coordinate: its range is
the complement of the basic open `D(t)`. -/
lemma range_zeroSection_line :
    Set.range (zeroSection (ULift.{u} (Fin 1)) S).base =
      ((𝔸(ULift.{u} (Fin 1); S).basicOpen (lineCoord S) : Set 𝔸(ULift.{u} (Fin 1); S)))ᶜ := by
  let e := zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) S (range_coord_line S)
  have he : e.hom ≫ _ = _ :=
    zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι (ULift.{u} (Fin 1)) S
      (range_coord_line S)
  rw [← Scheme.zeroLocus_singleton, ← range_zeroLocusSubschemeι, ← he]
  ext x
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨e.hom.base y, by rw [← hy]; rfl⟩, fun ⟨z, hz⟩ ↦ ⟨e.inv.base z, ?_⟩⟩
  rw [← hz, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]

section General

variable {S} {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); S)) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ)

include hj

/-- An open immersion onto the complement of the zero section has image the basic open `D(t)`
of the coordinate. -/
lemma opensRange_eq_basicOpen_lineCoord :
    j.opensRange = 𝔸(ULift.{u} (Fin 1); S).basicOpen (lineCoord S) := by
  ext x
  change x ∈ Set.range j.base ↔ _
  rw [hj, range_zeroSection_line, compl_compl]

lemma preimage_basicOpen_lineCoord :
    j ⁻¹ᵁ 𝔸(ULift.{u} (Fin 1); S).basicOpen (lineCoord S) = ⊤ := by
  rw [← opensRange_eq_basicOpen_lineCoord j hj, Scheme.Hom.preimage_opensRange]

/-- The sections of `𝒪` over `D(t) ⊆ 𝔸¹_S` are the global sections of the complement `G` of the
zero section. -/
noncomputable def basicOpenLineCoordRingEquiv :
    Γ(𝔸(ULift.{u} (Fin 1); S), 𝔸(ULift.{u} (Fin 1); S).basicOpen (lineCoord S)) ≃+* Γ(G, ⊤) :=
  have := j.isIso_app _ (opensRange_eq_basicOpen_lineCoord j hj).ge
  (asIso (j.app _)).commRingCatIsoToRingEquiv.trans
    (G.presheaf.mapIso
      (eqToIso (preimage_basicOpen_lineCoord j hj)).op).symm.commRingCatIsoToRingEquiv

lemma basicOpenLineCoordRingEquiv_apply (x) :
    basicOpenLineCoordRingEquiv j hj x =
      j.appLE _ ⊤ (preimage_basicOpen_lineCoord j hj).ge x :=
  rfl

lemma basicOpenLineCoordRingEquiv_res (x : Γ(𝔸(ULift.{u} (Fin 1); S), ⊤)) :
    basicOpenLineCoordRingEquiv j hj
      (𝔸(ULift.{u} (Fin 1); S).presheaf.map (homOfLE le_top).op x) = j.appTop x := by
  rw [basicOpenLineCoordRingEquiv_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact congrArg (fun φ ↦ φ.hom x) (Scheme.Hom.appLE_eq_app j (U := ⊤))

/-- The coordinate `t` is a unit on the complement of the zero section. -/
lemma isUnit_appTop_lineCoord : IsUnit (j.appTop (lineCoord S)) := by
  rw [← basicOpenLineCoordRingEquiv_res j hj]
  exact (RingedSpace.isUnit_res_basicOpen _ _).map _

/-- The coordinate `t`, as a global unit of the complement `G` of the zero section. -/
noncomputable def unitLineCoord : Γ(G, ⊤)ˣ :=
  (isUnit_appTop_lineCoord j hj).unit

@[simp]
lemma val_unitLineCoord : (unitLineCoord j hj : Γ(G, ⊤)) = j.appTop (lineCoord S) :=
  IsUnit.unit_spec _

end General

section Field

variable (k : Type u) [Field k]

/-- The ring of functions of the affine line `𝔸¹_k` is the polynomial ring `k[T]`, the
coordinate `t` corresponding to `T`. -/
noncomputable def lineRingEquiv :
    Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤) ≃+* Polynomial k :=
  ((Scheme.Γ.mapIso (SpecIso (ULift.{u} (Fin 1)) (.of k)).symm.op ≪≫
      Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv).trans
    (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv

lemma lineRingEquiv_apply (x : Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤)) :
    lineRingEquiv k x = MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))
      ((Scheme.ΓSpecIso _).hom ((SpecIso (ULift.{u} (Fin 1)) (.of k)).inv.appTop x)) :=
  rfl

@[simp]
lemma lineRingEquiv_lineCoord : lineRingEquiv k (lineCoord (Spec (.of k))) = Polynomial.X := by
  rw [lineRingEquiv_apply, SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]
  simp

/-- The structure map `k → Γ(X, 𝒪_X)` of a `k`-scheme `X`. -/
noncomputable abbrev _root_.AlgebraicGeometry.Scheme.Hom.structureRingHom {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

@[simp]
lemma lineRingEquiv_structureRingHom (c : k) :
    lineRingEquiv k ((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)).structureRingHom k c) =
      Polynomial.C c := by
  rw [lineRingEquiv_apply, Scheme.Hom.structureRingHom, CommRingCat.hom_comp, RingHom.comp_apply,
    ← CommRingCat.comp_apply ((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)).appTop),
    ← Scheme.Hom.comp_appTop, SpecIso_inv_over, ← CommRingCat.comp_apply,
    Scheme.ΓSpecIso_naturality]
  change MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))
    (MvPolynomial.C ((Scheme.ΓSpecIso (.of k)).hom ((Scheme.ΓSpecIso (.of k)).inv c))) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  simp

instance : IsDomain Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤) :=
  (lineRingEquiv k).toMulEquiv.isDomain

instance : IsPrincipalIdealRing Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤) :=
  IsPrincipalIdealRing.of_surjective (lineRingEquiv k).symm.toRingHom
    (lineRingEquiv k).symm.surjective

lemma prime_lineCoord : Prime (lineCoord (Spec (.of k))) := by
  rw [← MulEquiv.prime_iff (lineRingEquiv k)]
  exact (lineRingEquiv_lineCoord k).symm ▸ Polynomial.prime_X

/-- **Units of the affine line.** The units of `Γ(𝔸¹_k, 𝒪) = k[T]` are the nonzero constants. -/
theorem bijective_units_map_structureRingHom :
    Function.Bijective (Units.map
      ((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)).structureRingHom k).toMonoidHom) := by
  refine ⟨fun c d h ↦ Units.ext ((Scheme.Hom.structureRingHom _ _).injective
    (congrArg Units.val h)), fun u ↦ ?_⟩
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.1 ((u.isUnit).map (lineRingEquiv k))
  refine ⟨hc.unit, Units.ext ((lineRingEquiv k).injective ?_)⟩
  change lineRingEquiv k (Scheme.Hom.structureRingHom k _ c) = _
  rw [lineRingEquiv_structureRingHom, hcu]

variable {k} {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range (zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ)

include hj

lemma basicOpenLineCoordRingEquiv_algebraMap (x : Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤)) :
    basicOpenLineCoordRingEquiv j hj (algebraMap _ _ x) = j.appTop x :=
  basicOpenLineCoordRingEquiv_res j hj x

/-- The homomorphism `kˣ × tᶻ → Γ(G, 𝒪)ˣ`, `(c, m) ↦ c tᵐ`, on the complement `G = 𝔾_{m,k}` of
the zero section of `𝔸¹_k`. -/
noncomputable def unitsProdZPowHomLine : kˣ × Multiplicative ℤ →* Γ(G, ⊤)ˣ :=
  (Units.map ((j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)).structureRingHom
    k).toMonoidHom).coprod (zpowersHom _ (unitLineCoord j hj))

lemma unitsProdZPowHomLine_apply (c : kˣ) (m : Multiplicative ℤ) :
    unitsProdZPowHomLine j hj (c, m) =
      Units.map ((j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)).structureRingHom
        k).toMonoidHom c * unitLineCoord j hj ^ m.toAdd :=
  rfl

/-- **Units of `𝔾_{m,k}`.** The units of `Γ(𝔾_{m,k}, 𝒪) = k[t, t⁻¹]` are the products `c tᵐ`
with `c ∈ kˣ` and `m ∈ ℤ`, uniquely. -/
theorem bijective_unitsProdZPowHomLine : Function.Bijective (unitsProdZPowHomLine j hj) := by
  let B := Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), 𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen
    (lineCoord (Spec (.of k))))
  let e := basicOpenLineCoordRingEquiv j hj
  have h1 := bijective_units_map_structureRingHom k
  have h2 := IsLocalization.Away.bijective_unitsProdZPowHom (B := B) (prime_lineCoord k)
  have h3 : Function.Bijective (Units.map (e : B →* Γ(G, ⊤))) :=
    (Units.mapEquiv e.toMulEquiv).bijective
  have key : unitsProdZPowHomLine j hj = (Units.map (e : B →* Γ(G, ⊤))).comp
      ((IsLocalization.Away.unitsProdZPowHom (B := B) (lineCoord (Spec (.of k)))).comp
        (MonoidHom.prodMap (Units.map ((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘
          Spec (.of k)).structureRingHom k).toMonoidHom) (MonoidHom.id _))) := by
    refine MonoidHom.ext fun ⟨c, m⟩ ↦ Units.ext ?_
    rw [unitsProdZPowHomLine_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.coe_prodMap, Prod.map_apply, MonoidHom.id_apply, Units.coe_map,
      IsLocalization.Away.val_unitsProdZPowHom_apply, MonoidHom.coe_ofClass, map_mul, Units.val_mul]
    congr 1
    · change _ = e (algebraMap _ _ (Scheme.Hom.structureRingHom k _ c))
      rw [basicOpenLineCoordRingEquiv_algebraMap, Scheme.Hom.structureRingHom,
        Scheme.Hom.structureRingHom, Scheme.Hom.comp_appTop]
      rfl
    · rw [show e ((IsLocalization.Away.algebraMap_isUnit (S := B)
          (lineCoord (Spec (.of k)))).unit ^ m.toAdd : Bˣ) = ((Units.map (e : B →* Γ(G, ⊤)))
          ((IsLocalization.Away.algebraMap_isUnit (S := B)
          (lineCoord (Spec (.of k)))).unit ^ m.toAdd) : Γ(G, ⊤)) from rfl, map_zpow]
      congr 2
      refine Units.ext ?_
      rw [Units.coe_map, IsUnit.unit_spec, val_unitLineCoord, MonoidHom.coe_ofClass,
        basicOpenLineCoordRingEquiv_algebraMap]
  rw [key]
  exact h3.comp (h2.comp (Prod.map_bijective.2 ⟨h1, Function.bijective_id⟩))

/-- The complement of the zero section of `𝔸¹_k` is affine: it is the basic open `D(t)`. -/
lemma isAffine_of_range_eq_compl_zeroSection : IsAffine G := by
  have : IsAffine (𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen (lineCoord (Spec (.of k)))) :=
    (isAffineOpen_top _).basicOpen _
  exact .of_isIso (IsOpenImmersion.isoOfRangeEq j
    (𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen (lineCoord (Spec (.of k)))).ι (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe
        (opensRange_eq_basicOpen_lineCoord j hj))).hom

lemma isDomain_of_range_eq_compl_zeroSection : IsDomain Γ(G, ⊤) :=
  have := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers
      (lineCoord (Spec (.of k))))
    Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), 𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen
      (lineCoord (Spec (.of k))))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (prime_lineCoord k).ne_zero)
  (basicOpenLineCoordRingEquiv j hj).symm.toMulEquiv.isDomain

lemma isPrincipalIdealRing_of_range_eq_compl_zeroSection : IsPrincipalIdealRing Γ(G, ⊤) :=
  have := IsLocalization.isPrincipalIdealRing (M := Submonoid.powers
      (lineCoord (Spec (.of k))))
    (S := Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), 𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen
      (lineCoord (Spec (.of k)))))
  IsPrincipalIdealRing.of_surjective (basicOpenLineCoordRingEquiv j hj).toRingHom
    (basicOpenLineCoordRingEquiv j hj).surjective

/-- **The Picard group of `𝔾_{m,k}` is trivial**: `k[t, t⁻¹]` is a principal ideal domain. -/
theorem subsingleton_pic_of_range_eq_compl_zeroSection : Subsingleton G.Pic :=
  have := isAffine_of_range_eq_compl_zeroSection j hj
  have := isDomain_of_range_eq_compl_zeroSection j hj
  have := isPrincipalIdealRing_of_range_eq_compl_zeroSection j hj
  Scheme.Pic.subsingleton_of_isAffine G

/-- The units of `𝔾_{m,k}` as `kˣ × tᶻ`. -/
noncomputable def unitsMulEquivLine : kˣ × Multiplicative ℤ ≃* Γ(G, ⊤)ˣ :=
  MulEquiv.ofBijective _ (bijective_unitsProdZPowHomLine j hj)

lemma unitsMulEquivLine_apply (c : kˣ) (m : Multiplicative ℤ) :
    unitsMulEquivLine j hj (c, m) =
      Units.map ((j ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)).structureRingHom
        k).toMonoidHom c * unitLineCoord j hj ^ m.toAdd :=
  rfl

/-- The cokernel map `Γ(𝔾_m, 𝒪)ˣ → k^×/(k^×)^N × ℤ/N`, `c tᵐ ↦ ([c], m mod N)`. -/
noncomputable def unitsCokernelHomLine (N : ℕ) :
    Additive Γ(G, ⊤)ˣ →+ (Additive kˣ ⧸ (zsmulAddGroupHom (α := Additive kˣ) N).range) ×
      ZMod N where
  toFun x := (QuotientAddGroup.mk (Additive.ofMul ((unitsMulEquivLine j hj).symm x.toMul).1),
    (((unitsMulEquivLine j hj).symm x.toMul).2.toAdd : ZMod N))
  map_zero' := by simp
  map_add' x y := by
    simp only [toMul_add, map_mul, Prod.fst_mul, Prod.snd_mul, ofMul_mul, toAdd_mul,
      QuotientAddGroup.mk_add, Int.cast_add, Prod.mk_add_mk]

lemma unitsCokernelHomLine_apply (N : ℕ) (c : kˣ) (m : ℤ) :
    unitsCokernelHomLine j hj N (Additive.ofMul (unitsMulEquivLine j hj
      (c, Multiplicative.ofAdd m))) = (QuotientAddGroup.mk (Additive.ofMul c), (m : ZMod N)) := by
  simp [unitsCokernelHomLine]

lemma surjective_unitsCokernelHomLine (N : ℕ) :
    Function.Surjective (unitsCokernelHomLine j hj N) := by
  rintro ⟨c, z⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨_, unitsCokernelHomLine_apply j hj N c.toMul m⟩

lemma ker_unitsCokernelHomLine (N : ℕ) :
    (unitsCokernelHomLine j hj N).ker = (zsmulAddGroupHom (α := Additive Γ(G, ⊤)ˣ) N).range := by
  ext x
  obtain ⟨⟨c, m⟩, hx⟩ := (unitsMulEquivLine j hj).surjective x.toMul
  obtain rfl : x = Additive.ofMul (unitsMulEquivLine j hj (c, m)) := by rw [hx]; rfl
  rw [AddMonoidHom.mem_ker, ← ofAdd_toAdd m, unitsCokernelHomLine_apply, Prod.mk_eq_zero,
    QuotientAddGroup.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd, AddMonoidHom.mem_range,
    AddMonoidHom.mem_range]
  constructor
  · rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩
    refine ⟨Additive.ofMul (unitsMulEquivLine j hj (d.toMul, Multiplicative.ofAdd e)), ?_⟩
    rw [zsmulAddGroupHom_apply, ← ofMul_zpow, ← map_zpow]
    congr 2
    refine Prod.ext ?_ ?_
    · exact congrArg Additive.toMul hd
    · rw [Prod.pow_snd, he, ← ofAdd_zsmul, smul_eq_mul]
  · rintro ⟨y, hy⟩
    obtain ⟨⟨d, e⟩, hy'⟩ := (unitsMulEquivLine j hj).surjective y.toMul
    obtain rfl : y = Additive.ofMul (unitsMulEquivLine j hj (d, e)) := by rw [hy']; rfl
    rw [zsmulAddGroupHom_apply, ← ofMul_zpow, ← map_zpow] at hy
    have h := (unitsMulEquivLine j hj).injective (Additive.ofMul.injective hy)
    refine ⟨⟨Additive.ofMul d, congrArg (fun p ↦ Additive.ofMul p.1) h⟩, ⟨e.toAdd, ?_⟩⟩
    have h2 := congrArg (fun p ↦ p.2.toAdd) h
    simp only [Prod.pow_snd, toAdd_zpow, smul_eq_mul, toAdd_ofAdd] at h2
    rw [← h2]

/-- The cokernel of the `N`-th power map on the units of `𝔾_{m,k}` is `k^×/(k^×)^N × ℤ/N`, the
class of `c tᵐ` going to `([c], m mod N)`. -/
noncomputable def unitsCokernelAddEquivLine (N : ℕ) :
    Additive Γ(G, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(G, ⊤)ˣ) N).range ≃+
      (Additive kˣ ⧸ (zsmulAddGroupHom (α := Additive kˣ) N).range) × ZMod N :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_unitsCokernelHomLine j hj N).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_unitsCokernelHomLine j hj N))

lemma unitsCokernelAddEquivLine_mk (N : ℕ) (x : Additive Γ(G, ⊤)ˣ) :
    unitsCokernelAddEquivLine j hj N (QuotientAddGroup.mk x) = unitsCokernelHomLine j hj N x :=
  rfl

lemma unitsCokernelHomLine_unitLineCoord (N : ℕ) :
    unitsCokernelHomLine j hj N (Additive.ofMul (unitLineCoord j hj)) = (0, 1) := by
  have : unitLineCoord j hj = unitsMulEquivLine j hj (1, Multiplicative.ofAdd 1) := by
    rw [unitsMulEquivLine_apply, map_one, one_mul, toAdd_ofAdd, zpow_one]
  rw [this, unitsCokernelHomLine_apply]
  simp

/-- If every element of `kˣ` is an `N`-th power, the cokernel of the `N`-th power map on the units
of `𝔾_{m,k}` is `ℤ/N`, generated by the class of the coordinate `t`. -/
theorem exists_unitsCokernelAddEquiv_zmod (N : ℕ) (hk : ∀ c : kˣ, ∃ d : kˣ, d ^ N = c) :
    ∃ e : Additive Γ(G, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(G, ⊤)ˣ) N).range ≃+ ZMod N,
      e (QuotientAddGroup.mk (Additive.ofMul (unitLineCoord j hj))) = 1 := by
  have hsub : ∀ x : Additive kˣ ⧸ (zsmulAddGroupHom (α := Additive kˣ) N).range, x = 0 := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    obtain ⟨d, hd⟩ := hk c.toMul
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨Additive.ofMul d, by rw [zsmulAddGroupHom_apply, ← ofMul_zpow, zpow_natCast, hd]; rfl⟩
  let p : ((Additive kˣ ⧸ (zsmulAddGroupHom (α := Additive kˣ) N).range) × ZMod N) ≃+ ZMod N :=
    AddEquiv.ofBijective (AddMonoidHom.snd _ _)
      ⟨fun x y h ↦ Prod.ext ((hsub _).trans (hsub _).symm) h, fun z ↦ ⟨(0, z), rfl⟩⟩
  refine ⟨(unitsCokernelAddEquivLine j hj N).trans p, ?_⟩
  rw [AddEquiv.trans_apply, unitsCokernelAddEquivLine_mk, unitsCokernelHomLine_unitLineCoord]
  rfl

omit hj in
variable (k) in
/-- **The Picard group of `𝔸¹_k` is trivial**: `k[t]` is a principal ideal domain. -/
theorem subsingleton_pic_line : Subsingleton (𝔸(ULift.{u} (Fin 1); Spec (.of k))).Pic :=
  Scheme.Pic.subsingleton_of_isAffine _

omit hj in
/-- If every element of `kˣ` is an `N`-th power, so is every unit of the affine line. -/
lemma exists_pow_eq_units_line (N : ℕ) (hk : ∀ c : kˣ, ∃ d : kˣ, d ^ N = c)
    (u : Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤)ˣ) : ∃ v, v ^ N = u := by
  obtain ⟨c, rfl⟩ := (bijective_units_map_structureRingHom k).2 u
  obtain ⟨d, rfl⟩ := hk c
  exact ⟨_, (map_pow _ d N).symm⟩

/-- Blueprint `lem-pur-affine-punctured-line-algebra`: Units and Picard groups of the line and
the punctured line.

Let `k` be a field, `𝔸¹_k = Spec k[t]`, and `G = 𝔾_{m,k}` the complement of the zero section,
given by an open immersion `j : G ⟶ 𝔸¹_k` with image `D(t)`. Then

* `Γ(𝔸¹_k, 𝒪)ˣ = kˣ`, and `Γ(G, 𝒪)ˣ = kˣ · tᶻ` (`(c, m) ↦ c tᵐ` is an isomorphism);
* `Pic(𝔸¹_k) = 0` and `Pic(G) = 0`;
* for every `N`, the cokernel of the `N`-th power map on `Γ(G, 𝒪)ˣ` is `k^×/(k^×)^N ⊕ ℤ/N`,
  the class of `c tᵐ` going to `([c], m mod N)`;
* if every element of `kˣ` is an `N`-th power, this cokernel is `ℤ/N`, generated by the class of
  `t`, and every unit of `𝔸¹_k` is an `N`-th power.

No hypothesis on `N` and `char k` is needed. The rings `k[t]` and `k[t, t⁻¹]` are principal ideal
domains, whence the vanishing of the Picard groups
(`AlgebraicGeometry.Scheme.Pic.subsingleton_of_isAffine`). -/
theorem units_pic_line_and_multiplicativeGroup :
    Function.Bijective (Units.map ((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘
        Spec (.of k)).structureRingHom k).toMonoidHom) ∧
      Function.Bijective (unitsProdZPowHomLine j hj) ∧
      Subsingleton (𝔸(ULift.{u} (Fin 1); Spec (.of k))).Pic ∧ Subsingleton G.Pic ∧
      (∀ N : ℕ, ∀ (c : kˣ) (m : ℤ), unitsCokernelAddEquivLine j hj N
          (QuotientAddGroup.mk (Additive.ofMul (unitsProdZPowHomLine j hj
            (c, Multiplicative.ofAdd m)))) =
        (QuotientAddGroup.mk (Additive.ofMul c), (m : ZMod N))) ∧
      ∀ N : ℕ, (∀ c : kˣ, ∃ d : kˣ, d ^ N = c) →
        (∃ e : Additive Γ(G, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(G, ⊤)ˣ) N).range ≃+
          ZMod N, e (QuotientAddGroup.mk (Additive.ofMul (unitLineCoord j hj))) = 1) ∧
        ∀ u : Γ(𝔸(ULift.{u} (Fin 1); Spec (.of k)), ⊤)ˣ, ∃ v, v ^ N = u :=
  ⟨bijective_units_map_structureRingHom k, bijective_unitsProdZPowHomLine j hj,
    subsingleton_pic_line k, subsingleton_pic_of_range_eq_compl_zeroSection j hj,
    fun N c m ↦ unitsCokernelHomLine_apply j hj N c m,
    fun N hk ↦ ⟨exists_unitsCokernelAddEquiv_zmod j hj N hk, exists_pow_eq_units_line N hk⟩⟩

end Field

end AffineSpace

end AlgebraicGeometry
