/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Frobenius equivariance of the residue sequence

Let `U ⊆ C` be a nonempty open of an integral scheme over a field `k`, and let `E` be an
automorphism of `C` restricting to an automorphism of `U` and semilinear over an automorphism
`σ₀` of `k`. Transport along `E` acts on torsors over `U` (in the torsor model of `H¹`), and the
residues of the transported torsor are those of the torsor, moved along `E` and twisted by `σ₀`
on the roots of unity (`AlgebraicGeometry.Scheme.EtaleTorsor.residue_mapIso`). This is the
Frobenius equivariance of the residue map of blueprint `proposition-no-fixed-class-degree-one--1`.

For a power `Φ ^ m` of the geometric Frobenius fixing a boundary point `z`, `σ₀ = φ ^ m` with
`σ₀(x) ^ Q = x`, `Q = q ^ m`, so the pullback along `Φ ^ m` (transport along its inverse) acts on
the residues at `z` as multiplication by `Q`
(`AlgebraicGeometry.Scheme.EtaleTorsor.residue_mapIso_symm_eq_smul`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

/-- The order of vanishing is invariant under automorphisms: for an automorphism `E` of a locally
noetherian integral scheme, inducing `e` on the function field, `ord_z(e f) = ord_{E z}(f)`. -/
lemma ord_functionFieldAut {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (E : X ≅ X)
    (f : X.functionField) (z : X) :
    X.ord ((functionFieldAut E).hom f) z = X.ord f (E.hom z) :=
  Scheme.ord_functionFieldIso E.hom z f

/-- The automorphism of the function field induced by an automorphism `E` of a `k`-scheme,
semilinear over `σ₀`, acts on the constants through `σ₀`. -/
lemma functionFieldAut_functionFieldConstants {X : Scheme.{u}} [IsIntegral X] {k : Type u}
    [Field k] (p : X ⟶ Spec (.of k)) (E : X ≅ X) (σ₀ : k ≃+* k)
    (hσ₀ : E.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k))) (b : k) :
    (functionFieldAut E).hom (p.functionFieldConstants b) = p.functionFieldConstants (σ₀ b) := by
  change (functionFieldAut E).hom (X.presheaf.germ ⊤ (genericPoint X) trivial
    (p.appTop ((Scheme.ΓSpecIso (.of k)).inv b))) = _
  rw [functionFieldAut_germ]
  change _ = X.presheaf.germ ⊤ (genericPoint X) trivial
    (p.appTop ((Scheme.ΓSpecIso (.of k)).inv (σ₀ b)))
  congr 1
  have h1 := congrArg (fun h ↦ (Scheme.Hom.appTop h).hom ((Scheme.ΓSpecIso (.of k)).inv b)) hσ₀
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ₀ : k →+* k))) b).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleTorsor

section Transport

variable {C U : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] (j : U ⟶ C)
  [IsOpenImmersion j] [Nonempty U] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) {N : ℕ}
  [NeZero N] [NeZero (N : k)] [HasEnoughRootsOfUnity k N]

open FiniteEtale

local notation "Ω" => SeparableClosure (Scheme.functionField C)

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: Frobenius equivariance of the residue map.

Let `E_C` be an automorphism of `C`, semilinear over an automorphism `σ₀` of `k`, restricting to
an automorphism `E_U` of `U`. The residue at `E_C z` against `ξ` of the transport of a torsor `T`
along `E_U` is the residue of `T` at `z` against `σ₀ ξ`. -/
theorem residue_mapIso (EC : C ≅ C) (EU : U ≅ U) (hE : EU.hom ≫ j = j ≫ EC.hom)
    (σ₀ : k ≃+* k) (hσ₀ : EC.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k)))
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C) (ξ ξ' : rootsOfUnity N k)
    (hξ : ((ξ' : kˣ) : k) = σ₀ ((ξ : kˣ) : k)) :
    (T.mapIso EU).residue j p (EC.hom z) (Additive.ofMul ξ) =
      T.residue j p z (Additive.ofMul ξ') := by
  obtain ⟨φ, hφF, hφη⟩ := exists_ringEquiv_separableClosure EC Ω
  set F := C.functionField
  let ι : F →+* Ω := algebraMap F Ω
  let e := functionFieldAut EC
  let η := (Etale.genericGeometricPoint (C := C) j : Spec (.of Ω) ⟶ _)
  have hηj : η ≫ j = Spec.map (CommRingCat.ofHom ι) ≫ C.fromSpecFunctionField := by
    simp only [η, Etale.genericGeometricPoint, pointOfAlgebra, Category.assoc,
      genericPointLift_comp]
    rfl
  have hyU : Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) ≫ η = η ≫ EU.hom := by
    rw [← cancel_mono j, Category.assoc, hηj, hφη, Category.assoc, hE, ← Category.assoc η, hηj,
      Category.assoc]
  have hFinv (f : F) : φ.symm (ι f) = ι (e.inv f) := by
    rw [RingEquiv.symm_apply_eq, hφF, ← ConcreteCategory.comp_apply, e.inv_hom_id,
      CommRingCat.id_apply]
  have hspec (a b : Ω ≃+* Ω) : Spec.map (CommRingCat.ofHom ((a.trans b : Ω ≃+* Ω) : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (b : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom (a : Ω →+* Ω)) := by
    rw [← Spec.map_comp]
    rfl
  have hφφ : Spec.map (CommRingCat.ofHom (φ.symm : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) = 𝟙 _ := by
    rw [← hspec, RingEquiv.self_trans_symm]
    exact Spec.map_id _
  -- a point of the transported torsor over the generic geometric point
  let t := T.genericFiberPoint j
  have ht : t ≫ T.π = η := T.genericFiberPoint_comp j
  let t' : Spec (.of Ω) ⟶ (T.mapIso EU).P := Spec.map (CommRingCat.ofHom (φ.symm : Ω →+* Ω)) ≫ t
  have ht' : t' ≫ (T.mapIso EU).π = η := by
    simp only [t', mapIso_π, Category.assoc]
    rw [reassoc_of% ht, ← hyU, ← Category.assoc, hφφ, Category.id_comp]
  -- the Galois character of the transported torsor is that of `T` conjugated by `φ`
  let conj (σ : Gal(Ω/F)) : Gal(Ω/F) :=
    AlgEquiv.ofRingEquiv (f := φ.symm.trans (σ.toRingEquiv.trans φ)) fun f ↦ by
      change φ (σ (φ.symm (ι f))) = ι f
      rw [hFinv, σ.commutes, ← hFinv, RingEquiv.apply_symm_apply]
  have hconj (σ : Gal(Ω/F)) (w : Ω) : φ.symm (conj σ w) = σ (φ.symm w) := by
    change φ.symm (φ (σ (φ.symm w))) = _
    rw [RingEquiv.symm_apply_apply]
  have hχ (σ : Gal(Ω/F)) :
      (T.mapIso EU).galoisCharacter j σ = T.galoisCharacter j (conj σ) := by
    refine galoisCharacter_eq_of_specMap_comp_eq j _ σ t' ht' ?_
    have h1 : (φ.symm.trans σ.toRingEquiv : Ω ≃+* Ω) =
        ((conj σ).toRingEquiv.trans φ.symm : Ω ≃+* Ω) := by
      refine RingEquiv.ext fun w ↦ ?_
      exact (hconj σ w).symm
    have h2 : Spec.map (CommRingCat.ofHom ((conj σ).toRingEquiv : Ω →+* Ω)) ≫ t =
        t ≫ T.vadd ⟨T.galoisCharacter j (conj σ)⟩ :=
      T.specMap_comp_eq_comp_vadd_galoisCharacter j (conj σ) t ht
    change Spec.map (CommRingCat.ofHom (σ.toRingEquiv : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (φ.symm : Ω →+* Ω)) ≫ t = _
    rw [← Category.assoc, ← hspec, h1, hspec, Category.assoc, h2]
    simp only [t', Category.assoc, mapIso_vadd]
  -- a Kummer element of `T` against `σ₀ ξ` gives one of the transported torsor against `ξ`
  have hξ'N : ((ξ' : kˣ) : k) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N _).1 ξ'.2, Units.val_one]
  obtain ⟨x, f, hx, hf, hxσ⟩ := T.exists_kummerElement j p hξ'N
  have hκ : φ.symm (ι (p.functionFieldConstants ((ξ' : kˣ) : k))) =
      ι (p.functionFieldConstants ((ξ : kˣ) : k)) := by
    rw [hFinv, hξ, ← functionFieldAut_functionFieldConstants p EC σ₀ hσ₀]
    change ι ((e.hom ≫ e.inv) _) = _
    rw [e.hom_inv_id]
    rfl
  rw [T.residue_eq_ord j p z (Additive.ofMul ξ') hx hf hxσ]
  rw [(T.mapIso EU).residue_eq_ord j p (EC.hom z) (Additive.ofMul ξ) (x := φ.symm x)
    (f := e.inv f) ((map_ne_zero_iff _ φ.symm.injective).2 hx)
    (by rw [← hFinv, hf, map_pow]) fun σ ↦ ?_]
  · rw [← ord_functionFieldAut EC (e.inv f) z]
    change ((C.ord ((e.inv ≫ e.hom) f) z : ℤ) : ZMod N) = _
    rw [e.inv_hom_id]
    rfl
  · rw [← hconj, hxσ, map_mul, map_pow, hκ, hχ]
    rfl

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: a Frobenius power fixing a boundary point
acts on the residues there as multiplication by `Q`.

Let `E_C` be an automorphism of `C` fixing `z`, semilinear over `σ₀` with `σ₀(x) ^ Q = x` (for a
power `Φ ^ m` of the geometric Frobenius over `𝔽_q`, `Q = q ^ m`), and restricting to `E_U` on `U`.
Then the residue at `z` of the pullback of a torsor `T` along `E_U`, i.e. its transport along
`E_U⁻¹`, is `Q` times the residue of `T`: `Φ_Q` acts on `ℤ / N (-1)` as multiplication by `Q`. -/
theorem residue_mapIso_symm_eq_smul (EC : C ≅ C) (EU : U ≅ U) (hE : EU.hom ≫ j = j ≫ EC.hom)
    (σ₀ : k ≃+* k) (hσ₀ : EC.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k)))
    (Q : ℕ) (hQ : ∀ x : k, σ₀ x ^ Q = x) (z : C) (hz : EC.hom z = z)
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    (T.mapIso EU.symm).residue j p z = Q • T.residue j p z := by
  have hT : ((T.mapIso EU.symm).mapIso EU).IsIsomorphic T :=
    ⟨Iso.refl _, by simp, fun _ ↦ by simp⟩
  refine AddMonoidHom.ext fun ξ ↦ ?_
  -- `ξ = σ₀ (ξ ^ Q)`
  have hξ : ((ξ.toMul : kˣ) : k) = σ₀ (((ξ.toMul ^ Q : rootsOfUnity N k) : kˣ) : k) := by
    simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, map_pow, hQ]
  have h := residue_mapIso j p EC EU hE σ₀ hσ₀ (T.mapIso EU.symm) z (ξ.toMul ^ Q) ξ.toMul hξ
  rw [hz, residue_eq_of_isIsomorphic j p hT, ofMul_pow, map_nsmul, ofMul_toMul] at h
  rw [AddMonoidHom.smul_apply, ← h]

end Transport

end AlgebraicGeometry.Scheme.EtaleTorsor

namespace AlgebraicGeometry.Scheme.EtaleTorsor

section BoundaryModule

variable {k : Type u} [Field k] [IsAlgClosed k] {l : ℕ}

omit [IsAlgClosed k] in
/-- Iterating the transition maps `Hom(μ_{lⁿ⁺¹}, ℤ / lⁿ⁺¹) → Hom(μ_{lⁿ}, ℤ / lⁿ)` of a
compatible system. -/
lemma castHom_eq_of_compatible (hl : l.Prime)
    (r : ∀ n : ℕ, Additive (rootsOfUnity (l ^ n) k) →+ ZMod (l ^ n))
    (hr : ∀ n (ξ : rootsOfUnity (l ^ (n + 1)) k) (ξ' : rootsOfUnity (l ^ n) k),
      ((ξ' : kˣ) : k) = ((ξ : kˣ) : k) ^ l →
        r n (Additive.ofMul ξ') = ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1))
          (ZMod (l ^ n)) (r (n + 1) (Additive.ofMul ξ)))
    (n v : ℕ) (ξ : rootsOfUnity (l ^ (n + v)) k) (ξ' : rootsOfUnity (l ^ n) k)
    (h : ((ξ' : kˣ) : k) = ((ξ : kˣ) : k) ^ (l ^ v)) :
    r n (Additive.ofMul ξ') = ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n v))
      (ZMod (l ^ n)) (r (n + v) (Additive.ofMul ξ)) := by
  induction v with
  | zero =>
    rw [pow_zero, pow_one] at h
    have : ξ' = ξ := Subtype.ext (Units.ext h)
    subst this
    rw [ZMod.castHom_apply]
    exact (ZMod.cast_id _ _).symm
  | succ v ih =>
    have : NeZero (l ^ (n + v)) := ⟨pow_ne_zero _ hl.ne_zero⟩
    have hξ1 : (ξ : kˣ) ^ (l ^ (n + v + 1)) = 1 := (mem_rootsOfUnity _ _).1 ξ.2
    have hη : (((ξ : kˣ) : k) ^ l) ^ (l ^ (n + v)) = 1 := by
      rw [← pow_mul, ← pow_succ', ← Units.val_pow_eq_pow_val, hξ1, Units.val_one]
    let η : rootsOfUnity (l ^ (n + v)) k := rootsOfUnity.mkOfPowEq _ hη
    have hηk : ((η : kˣ) : k) = ((ξ : kˣ) : k) ^ l := rootsOfUnity.coe_mkOfPowEq hη
    rw [ih η (by rw [hηk, ← pow_mul, ← pow_succ', h]), hr (n + v) ξ η hηk,
      ← RingHom.comp_apply, ZMod.castHom_comp]
    rfl

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the inverse-limit boundary module
`lim_n Hom(μ_{lⁿ}, ℤ / lⁿ) = ℤ_l(-1)` has no nonzero element fixed by `Φ_Q`, which acts on it as
multiplication by `Q ≥ 2`: a compatible system `(r_n)` with `Q r_n = r_n` for all `n` is zero. -/
theorem eq_zero_of_compatible_of_smul_eq_self (hl : l.Prime) {Q : ℕ} (hQ : 2 ≤ Q)
    (r : ∀ n : ℕ, Additive (rootsOfUnity (l ^ n) k) →+ ZMod (l ^ n))
    (hr : ∀ n (ξ : rootsOfUnity (l ^ (n + 1)) k) (ξ' : rootsOfUnity (l ^ n) k),
      ((ξ' : kˣ) : k) = ((ξ : kˣ) : k) ^ l →
        r n (Additive.ofMul ξ') = ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1))
          (ZMod (l ^ n)) (r (n + 1) (Additive.ofMul ξ)))
    (hfix : ∀ n, Q • r n = r n) (n : ℕ) : r n = 0 := by
  obtain ⟨v, hv⟩ := ZMod.exists_natCast_pow_mul_eq_zero_of_natCast_sub_one_mul_eq_zero hl hQ
  refine AddMonoidHom.ext fun ξ' ↦ ?_
  have : NeZero (l ^ (n + v)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((ξ'.toMul : kˣ) : k)
    (pow_pos hl.pos v)
  have hyN : y ^ (l ^ (n + v)) = 1 := by
    rw [pow_add, mul_comm, pow_mul, hy, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity _ _).1 ξ'.toMul.2, Units.val_one]
  let ξ : rootsOfUnity (l ^ (n + v)) k := rootsOfUnity.mkOfPowEq _ hyN
  have h := castHom_eq_of_compatible hl r hr n v ξ ξ'.toMul
    (by rw [rootsOfUnity.coe_mkOfPowEq hyN, hy])
  rw [ofMul_toMul] at h
  rw [h, AddMonoidHom.zero_apply]
  refine ZMod.castHom_eq_zero_of_pow_mul_eq_zero hl (hv _ _ ?_)
  have := DFunLike.congr_fun (hfix (n + v)) (Additive.ofMul ξ)
  rw [AddMonoidHom.smul_apply, nsmul_eq_mul] at this
  rw [sub_mul, one_mul, this, sub_self]

end BoundaryModule

end AlgebraicGeometry.Scheme.EtaleTorsor

namespace AlgebraicGeometry.Scheme.EtaleTorsor

section FixedSystems

variable {C U : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] (j : U ⟶ C)
  [IsOpenImmersion j] [Nonempty U] {k : Type u} [Field k] [IsAlgClosed k]
  (p : C ⟶ Spec (.of k))

/-- Blueprint `proposition-no-fixed-class-degree-one--1` (as used in
`proposition-no-fixed-class-degree-one--1`): the residues of a compatible Frobenius-fixed system
vanish.

Let `E_C` be an automorphism of `C` fixing `z`, semilinear over `σ₀` with `σ₀(x) ^ Q = x` for some
`Q ≥ 2` (a power `Φ_Q` of the geometric Frobenius), restricting to `E_U` on `U`. Let `(t_n)` be
`ℤ / lⁿ`-torsors on `U` whose Galois characters are compatible under reduction and which are all
fixed by `E_U`. Then the residues `r_n = res_z(t_n)` form a compatible element of
`lim_n ℤ / lⁿ(-1)` fixed by `Φ_Q`, which acts there as `Q`; hence they vanish. -/
theorem residue_eq_zero_of_compatible_of_isIsomorphic_mapIso (EC : C ≅ C) (EU : U ≅ U)
    (hE : EU.hom ≫ j = j ≫ EC.hom) (σ₀ : k ≃+* k)
    (hσ₀ : EC.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k)))
    {Q : ℕ} (hQ2 : 2 ≤ Q) (hQ : ∀ x : k, σ₀ x ^ Q = x) (z : C) (hz : EC.hom z = z)
    {l : ℕ} (hl : l.Prime) [∀ n, NeZero (l ^ n)] [∀ n, NeZero ((l ^ n : ℕ) : k)]
    (t : ∀ n : ℕ, EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) U)
    (ht : ∀ n σ, (t n).galoisCharacter j σ = ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1))
      (ZMod (l ^ n)) ((t (n + 1)).galoisCharacter j σ))
    (hfix : ∀ n, ((t n).mapIso EU).IsIsomorphic (t n)) (n : ℕ) :
    (t n).residue j p z = 0 := by
  refine eq_zero_of_compatible_of_smul_eq_self hl hQ2 (fun n ↦ (t n).residue j p z)
    (fun m ξ ξ' hξ ↦ ?_) (fun m ↦ ?_) n
  · have : NeZero (l ^ m * l) := inferInstanceAs (NeZero (l ^ (m + 1)))
    have : NeZero ((l ^ m * l : ℕ) : k) := inferInstanceAs (NeZero ((l ^ (m + 1) : ℕ) : k))
    exact residue_eq_castHom_of_galoisCharacter (N := l ^ m) (d := l) j p (ht m) z ξ ξ' hξ
  · have h : ((t m).mapIso EU.symm).IsIsomorphic (t m) :=
      (((hfix m).mapIso EU.symm).symm.trans ⟨Iso.refl _, by simp, fun _ ↦ by simp⟩)
    rw [← residue_mapIso_symm_eq_smul j p EC EU hE σ₀ hσ₀ Q hQ z hz,
      residue_eq_of_isIsomorphic j p h]

end FixedSystems

end AlgebraicGeometry.Scheme.EtaleTorsor
