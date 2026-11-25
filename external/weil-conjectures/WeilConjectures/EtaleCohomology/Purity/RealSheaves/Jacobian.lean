/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GaloisGroupLaw
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.RationalTateModule
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Picard.GaloisTwist
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.GroupTheory.TateModule
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic

/-!
# Jacobian torsion data

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K = 𝔽_q` and let
`C = C₀ ×_K K̄` be its geometric fiber (`AlgebraicGeometry.Scheme.Hom.geometricFiber`), with
`Γ = Gal(K̄ / K)` acting on the Picard group `Pic(C)` by pulling back line bundles along the
automorphisms `𝟙 × Spec σ` of `C` (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap`).

A *Jacobian torsion datum* records the outcome of the theory of the Jacobian in exactly the
amount needed by the purity argument for real lisse sheaves: an abelian variety `J₀` over `K`
(`AlgebraicGeometry.IsAbelianVariety`, which by `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`
is automatically commutative) representing the degree-zero Picard functor `Pic⁰_{C₀/K}`,
together with `Γ`-equivariant isomorphisms `J₀(K̄)[ℓⁿ] ≃ Pic(C)[ℓⁿ]` matching multiplication by
`ℓ` on the torsion of `J₀` with the `ℓ`-th tensor power of line bundles. Here `J₀(K̄)` is the
group `Additive (Spec K̄ ⟶ J₀)` of geometric points of `J₀`, with `Γ` acting by coordinates
(`AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv`), and `Pic(C)` is
`AlgebraicGeometry.Scheme.Pic` with the tensor product as group law, written additively. From
the datum one reads off the Tate module `T_ℓ J = lim_n J[ℓⁿ]`
(`AlgebraicGeometry.IsAbelianVariety.tateModule`) and its identification with the Tate module of
`Pic(C)` (`AlgebraicGeometry.JacobianTorsionDatum.nonempty_tateModuleEquiv`).

The Kummer half of blueprint `proposition-kummer-duality-integral-tate-module` — the system
`(μ_{lⁿ}, z ↦ z ^ l)` defining `ℤ_l(1)` — consists of the transition maps
`AlgebraicGeometry.Scheme.rootsOfUnityPowMap`; the resulting identification
`H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` is `AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv`. The Tate twist
itself is `AlgebraicGeometry.WeilGroup.tateLine`.

## Main definitions

- `AlgebraicGeometry.JacobianTorsionDatum`
- `AlgebraicGeometry.JacobianTorsionDatum.tateModule`

## Main statements

- `AlgebraicGeometry.JacobianTorsionDatum.nonempty_tateModuleEquiv`
- `AlgebraicGeometry.exists_jacobian_galoisAction`: the semilinear Galois action on the geometric
  Jacobian, preserving the group law (blueprint `proposition-jacobian-over-ground-field--5`).
- `AlgebraicGeometry.JacobianTorsionDatum.exists_equivTorsion_eq_restrict`: a Jacobian torsion
  datum whose comparison isomorphisms are induced by the representing isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {C : Scheme.{u}}

/-- Blueprint `proposition-kummer-duality-integral-tate-module`: Jacobian torsion data and Kummer
coefficients.

A Jacobian torsion datum for a proper smooth geometrically integral curve `p : C₀ ⟶ Spec K`
over a finite field and a prime `l` consists of an abelian variety `J₀` over `K` representing the
degree-zero relative Picard functor `Pic⁰_{C₀/K}` (blueprint
`theorem-picard-scheme-jacobian-over-separably--3`), together with a compatible system of
isomorphisms

`J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]`

between the `lⁿ`-torsion of the group of geometric points of `J₀` and that of the Picard group of
the geometric curve `C = C₀ ×_K K̄`, which are equivariant for `Gal(K̄ / K)` (acting on points
by coordinates and on line bundles by pullback along `𝟙 × Spec σ`) and carry multiplication by
`l` on `J₀(K̄)[l ^ (n + 1)] → J₀(K̄)[lⁿ]` to the `l`-th tensor power of line bundles. -/
structure JacobianTorsionDatum [Finite K] (p : C ⟶ Spec (.of K)) [IsCurve p] [Smooth p]
    [IsProper p] [GeometricallyIntegral p] (l : ℕ) [Fact l.Prime] where
  /-- The abelian variety `J₀`, as a scheme over `Spec K`. -/
  J : Over (Spec (.of K))
  /-- `J₀` is a group scheme over `K`. -/
  [grpObj : GrpObj J]
  /-- `J₀` is an abelian variety over `K`; commutativity of its group law is then automatic
  by `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`. -/
  [isAbelianVariety : IsAbelianVariety J]
  /-- `J₀` represents the degree-zero Picard functor `Pic⁰_{C₀/K}`: it is the Jacobian of
  `C₀`. -/
  representableBy : (picardFunctorDegree p 0).obj.RepresentableBy J
  /-- The comparison isomorphism `J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]` with the `lⁿ`-torsion of the Picard
  group of the geometric curve. -/
  equivTorsion (n : ℕ) :
    AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J)) ((l : ℤ) ^ n) ≃+
      AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n)
  /-- The comparison isomorphisms are Galois-equivariant: `σ ∈ Gal(K̄ / K)` acts on geometric
  points by coordinates and on line bundles by pullback along `𝟙 × Spec σ`. -/
  equivTorsion_galois (n : ℕ) (σ : Gal(AlgebraicClosure K/K))
    (x : AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J)) ((l : ℤ) ^ n)) :
    (equivTorsion n ⟨IsAbelianVariety.geometricPointsAddEquiv σ x,
        AddSubgroup.apply_mem_torsionBy (IsAbelianVariety.geometricPointsAddEquiv σ) x.2⟩ :
          Additive p.geometricFiber.Pic) =
      Additive.ofMul (Scheme.Pic.map (p.geometricFiberGaloisMap σ.toAlgHom)
        (equivTorsion n x : Additive p.geometricFiber.Pic).toMul)
  /-- The comparison isomorphisms match multiplication by `l` on the torsion of `J₀` with the
  `l`-th tensor power of line bundles, i.e. the square

  ```
      J[lⁿ⁺¹] ──equivTorsion (n+1)──▶ Pic[lⁿ⁺¹]
         │                                │
       l • ─                            l • ─
         ▼                                ▼
       J[lⁿ] ───equivTorsion n───────▶ Pic[lⁿ]
  ```

  commutes. -/
  equivTorsion_zsmul (n : ℕ)
    (x : AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J)) ((l : ℤ) ^ (n + 1))) :
    (equivTorsion n ⟨(l : ℤ) • (x : Additive (Scheme.specAlgebraicClosure K ⟶ J)),
        AddSubgroup.zsmul_mem_torsionBy_pow x.2⟩ : Additive p.geometricFiber.Pic) =
      (l : ℤ) • (equivTorsion (n + 1) x : Additive p.geometricFiber.Pic)

attribute [instance] JacobianTorsionDatum.grpObj JacobianTorsionDatum.isAbelianVariety

namespace JacobianTorsionDatum

variable [Finite K] {p : C ⟶ Spec (.of K)} [IsCurve p] [Smooth p] [IsProper p]
  [GeometricallyIntegral p] {l : ℕ} [Fact l.Prime]

variable (l) in
/-- Blueprint `proposition-kummer-duality-integral-tate-module`: Jacobian torsion data and Kummer
coefficients.

The Tate module `T_l J = lim_n J₀(K̄)[lⁿ]` of the abelian variety of a Jacobian torsion datum,
the compatible systems of `lⁿ`-torsion geometric points under multiplication by `l`
(`AlgebraicGeometry.IsAbelianVariety.tateModule`).

Inverting `l` gives `V_l J = T_l J ⊗ ℚ_l`, the `l`-adic homology of the curve. -/
noncomputable abbrev tateModule (d : JacobianTorsionDatum p l) :
    AddSubgroup (∀ _ : ℕ, Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) :=
  IsAbelianVariety.tateModule l d.J

/-- The comparison isomorphisms of a Jacobian torsion datum, inverted, are also compatible with
multiplication by `l`. -/
theorem equivTorsion_symm_zsmul (d : JacobianTorsionDatum p l) (n : ℕ)
    (y : AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ (n + 1))) :
    ((d.equivTorsion n).symm ⟨(l : ℤ) • (y : Additive p.geometricFiber.Pic),
        AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ :
          Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) =
      (l : ℤ) • ((d.equivTorsion (n + 1)).symm y :
        Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) := by
  set x := (d.equivTorsion (n + 1)).symm y
  have h := d.equivTorsion_zsmul n x
  rw [show d.equivTorsion (n + 1) x = y from (d.equivTorsion (n + 1)).apply_symm_apply y] at h
  have h' : (⟨(l : ℤ) • (y : Additive p.geometricFiber.Pic),
      AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ :
        AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n)) =
      d.equivTorsion n ⟨_, AddSubgroup.zsmul_mem_torsionBy_pow x.2⟩ :=
    Subtype.ext h.symm
  rw [h', AddEquiv.symm_apply_apply]

/-- Blueprint `proposition-kummer-duality-integral-tate-module`: Jacobian torsion data and Kummer
coefficients.

The comparison isomorphisms `J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]` are compatible with the transition maps,
so they identify the Tate module `T_l J` of the datum with the Tate module
`AddCommGroup.tateModule` of the Picard group of the geometric curve. This is the form in which
`T_l J` enters `theorem-rank-one-sheaves-have-finite`. -/
theorem nonempty_tateModuleEquiv (d : JacobianTorsionDatum p l) :
    Nonempty (d.tateModule l ≃+ AddCommGroup.tateModule l (Additive p.geometricFiber.Pic)) := by
  let M := Additive (Scheme.specAlgebraicClosure K ⟶ d.J)
  let N := Additive p.geometricFiber.Pic
  have hM (t : AddCommGroup.tateModule l M) (n : ℕ) :
      (t : ∀ _ : ℕ, M) n ∈ AddSubgroup.torsionBy M ((l : ℤ) ^ n) :=
    AddCommGroup.tateModule.pow_zsmul_coe t n
  have hN (t : AddCommGroup.tateModule l N) (n : ℕ) :
      (t : ∀ _ : ℕ, N) n ∈ AddSubgroup.torsionBy N ((l : ℤ) ^ n) :=
    AddCommGroup.tateModule.pow_zsmul_coe t n
  refine ⟨
    { toFun t := ⟨fun n ↦ (d.equivTorsion n ⟨_, hM t n⟩ : N),
        fun n ↦ (d.equivTorsion n _).2, fun n ↦ ?_⟩
      invFun t := ⟨fun n ↦ ((d.equivTorsion n).symm ⟨_, hN t n⟩ : M),
        fun n ↦ ((d.equivTorsion n).symm _).2, fun n ↦ ?_⟩
      left_inv t := Subtype.ext <| funext fun n ↦ by simp
      right_inv t := Subtype.ext <| funext fun n ↦ by simp
      map_add' s t := Subtype.ext <| funext fun n ↦ by
        change (d.equivTorsion n ⟨_, hM (s + t) n⟩ : N) =
          (d.equivTorsion n ⟨_, hM s n⟩ : N) + (d.equivTorsion n ⟨_, hM t n⟩ : N)
        rw [← AddSubgroup.coe_add, ← map_add]
        rfl }⟩
  · rw [← d.equivTorsion_zsmul n ⟨_, hM t (n + 1)⟩]
    congr 2
    exact Subtype.ext (AddCommGroup.tateModule.zsmul_coe_succ t n)
  · rw [← d.equivTorsion_symm_zsmul n ⟨_, hN t (n + 1)⟩]
    congr 2
    exact Subtype.ext (AddCommGroup.tateModule.zsmul_coe_succ t n)

variable (p l) in
/-- Blueprint `proposition-jacobian-over-ground-field`: The Jacobian over a general base field, by
Galois descent.

Every proper smooth geometrically connected curve over a finite field admits a Jacobian torsion
datum: the descended Jacobian `J₀` of `AlgebraicGeometry.exists_jacobian_descent` with its
Galois-equivariant identification `J₀(K̄) ≅ Pic⁰(C)`, restricted to `lⁿ`-torsion, which lies in
`Pic⁰(C)`. -/
theorem nonempty [SmoothOfRelativeDimension 1 p] : Nonempty (JacobianTorsionDatum p l) := by
  let _ : C.Over (Spec (.of K)) := ⟨p⟩
  let _ : p.geometricFiber.Over (Spec (.of (AlgebraicClosure K))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  have : SmoothOfRelativeDimension 1 (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd p _))
  have : IsProper (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (IsProper (pullback.snd p _))
  have : GeometricallyConnected (C ↘ Spec (.of K)) := .of_geometricallyIrreducible p
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of K)) := ‹SmoothOfRelativeDimension 1 p›
  have : IsProper (C ↘ Spec (.of K)) := ‹IsProper p›
  obtain ⟨J₀, _, r, hP, hS, hG, -, -, e₀, -, he⟩ := exists_jacobian_descent K (AlgebraicClosure K)
    (AlgebraicClosure K) C _ rfl p.geometricFiber p.geometricFiberProj
    (IsPullback.of_hasPullback _ _)
  have : Smooth J₀.hom := SmoothOfRelativeDimension.smooth (Scheme.arithmeticGenus K C) _
  have : IrreducibleSpace J₀.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := J₀.hom)
  have hJ : IsAbelianVariety J₀ := ⟨⟩
  let e : picardZero (AlgebraicClosure K) p.geometricFiber ≃*
      (Scheme.specAlgebraicClosure K ⟶ J₀) := e₀
  -- the torsion of `Pic(C)` lies in `Pic⁰(C)`
  have hdeg (n : ℕ) (y : Additive p.geometricFiber.Pic) (hy : ((l : ℤ) ^ n) • y = 0) :
      y.toMul ∈ picardZero (AlgebraicClosure K) p.geometricFiber := by
    rw [MonoidHom.mem_ker]
    have h := congrArg
      (fun z ↦ (Scheme.picDegreeHom (AlgebraicClosure K) p.geometricFiber z.toMul).toAdd) hy
    simp only [toMul_zsmul, map_zpow, toAdd_zpow, toMul_zero, map_one, toAdd_one] at h
    rw [← ofAdd_toAdd (Scheme.picDegreeHom _ _ _), ofAdd_eq_one]
    exact (mul_eq_zero.1 h).resolve_left
      (pow_ne_zero n (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  -- `e⁻¹ : J₀(K̄) ≃ Pic⁰(C) ⊆ Pic(C)` commutes with integer multiples
  have hzsmul (x : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) (k : ℤ) :
      (k • Additive.ofMul ((e.symm (Additive.toMul x) :
        picardZero (AlgebraicClosure K) p.geometricFiber) : p.geometricFiber.Pic)) =
      Additive.ofMul ((e.symm (Additive.toMul (k • x)) :
        picardZero (AlgebraicClosure K) p.geometricFiber) : p.geometricFiber.Pic) := by
    simp [toMul_zsmul, map_zpow]
  let eT (n : ℕ) :
      AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) ((l : ℤ) ^ n) ≃+
        AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) ((l : ℤ) ^ n) :=
    { toFun x := ⟨.ofMul (e.symm x.1.toMul : p.geometricFiber.Pic), by
        change ((l : ℤ) ^ n) • (Additive.ofMul _ : Additive p.geometricFiber.Pic) = 0
        rw [hzsmul,
          show ((l : ℤ) ^ n) • (x : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) = 0 from x.2]
        simp⟩
      invFun y := ⟨.ofMul (e ⟨y.1.toMul, hdeg n y.1 y.2⟩), by
        change ((l : ℤ) ^ n) •
          (Additive.ofMul _ : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) = 0
        rw [← ofMul_zpow, ← map_zpow]
        have : (⟨y.1.toMul, hdeg n y.1 y.2⟩ :
            picardZero (AlgebraicClosure K) p.geometricFiber) ^ ((l : ℤ) ^ n) = 1 :=
          Subtype.ext (by
            have h := congrArg Additive.toMul
              (show ((l : ℤ) ^ n) • (y : Additive p.geometricFiber.Pic) = 0 from y.2)
            rw [toMul_zsmul, toMul_zero] at h
            simpa only [SubgroupClass.coe_zpow, OneMemClass.coe_one] using h)
        rw [this, map_one, ofMul_one]⟩
      left_inv x := Subtype.ext (by simp)
      right_inv y := Subtype.ext (by simp)
      map_add' x y := Subtype.ext (by simp) }
  refine ⟨@JacobianTorsionDatum.mk _ _ _ _ p _ _ _ _ l _ J₀ _ hJ r eT ?_ ?_⟩
  · intro n σ x
    obtain ⟨γ, hγ₁, hγ₂, act, hact₁, hact₂⟩ := he σ
    have hγ : γ = p.geometricFiberGaloisMap σ.toAlgHom :=
      Scheme.Hom.geometricFiber_hom_ext p (by simpa using hγ₁) (by
        rw [Scheme.Hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure]
        exact hγ₂)
    have hx : e (act (e.symm x.1.toMul)) = specAlgEquivOver σ ≫ e (e.symm x.1.toMul) :=
      hact₂ (e.symm x.1.toMul)
    rw [MulEquiv.apply_symm_apply, ← MulEquiv.eq_symm_apply] at hx
    change Additive.ofMul (e.symm (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x.1.toMul) :
      p.geometricFiber.Pic) = _
    rw [show Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x.1.toMul =
      specAlgEquivOver σ ≫ x.1.toMul from rfl, ← hx, hact₁, hγ]
    rfl
  · intro n x
    change Additive.ofMul (e.symm (Additive.toMul ((l : ℤ) •
        (x : Additive (Scheme.specAlgebraicClosure K ⟶ J₀)))) : p.geometricFiber.Pic) =
      (l : ℤ) • Additive.ofMul (e.symm x.1.toMul : p.geometricFiber.Pic)
    rw [hzsmul]


/-- Blueprint `proposition-no-frobenius-fixed-vector`: arithmetic Frobenius has no fixed vector on
the Jacobian Tate module, on the rational Tate module.

Let `d` be a Jacobian torsion datum of a proper smooth geometrically integral curve `C₀` over a
finite field `K`, with abelian variety `J₀`. The arithmetic Frobenius `σ : z ↦ z ^ q` of
`Gal(K̄ / K)`, acting on `J₀(K̄)` by coordinates, fixes no nonzero vector of `V_l J`: its fixed
points on `J₀(K̄)` are the finitely many rational points `J₀(K)`
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_frobenius_fixed`), so this is
`AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self`. In other words `σ - 1` is injective
on `V_l J`. -/
theorem eq_zero_of_map_frobenius_eq_self [Fintype K] (d : JacobianTorsionDatum p l)
    {v : IsAbelianVariety.rationalTateModule l d.J}
    (hv : AddCommGroup.rationalTateModule.map (IsAbelianVariety.geometricPointsAddEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))).toAddMonoidHom v = v) :
    v = 0 :=
  AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self _
    (IsAbelianVariety.finite_setOf_frobenius_fixed d.J) hv

/-- Blueprint `proposition-no-frobenius-fixed-vector`: arithmetic Frobenius has no fixed vector on
the Jacobian Tate module, `(T_l J)^{σ = 1} = 0`.

The arithmetic Frobenius `σ : z ↦ z ^ q` of `Gal(K̄ / K)` acts on `T_l J` through the Galois
representation of the abelian variety `J₀` of a Jacobian torsion datum, i.e. by coordinates on
the geometric points; its fixed vectors vanish
(`AlgebraicGeometry.IsAbelianVariety.eq_zero_of_galoisRepresentation_frobenius_eq_self`). -/
theorem eq_zero_of_galoisRepresentation_frobenius_eq_self [Fintype K]
    (d : JacobianTorsionDatum p l) {t : d.tateModule l}
    (ht : IsAbelianVariety.galoisRepresentation l d.J
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) t = t) :
    t = 0 :=
  IsAbelianVariety.eq_zero_of_galoisRepresentation_frobenius_eq_self l d.J ht

/-- Blueprint `proposition-no-frobenius-fixed-vector`: for `l` invertible in `K`, `σ - 1` is an
automorphism of the rational Tate module `V_l J`, `σ` the arithmetic Frobenius.

`V_l J` is finite dimensional, of dimension `2 dim J₀`
(`AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_rationalTateModule_of_natCast_ne_zero`)
and `σ - 1` is injective
(`AlgebraicGeometry.JacobianTorsionDatum.eq_zero_of_map_frobenius_eq_self`),
hence bijective. -/
theorem bijective_rationalTateModuleGaloisMap_frobenius_sub_id [Fintype K]
    (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0) :
    Function.Bijective (IsAbelianVariety.rationalTateModuleGaloisMap l d.J
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) -
        LinearMap.id (R := ℚ_[l]) (M := IsAbelianVariety.rationalTateModule l d.J)) :=
  IsAbelianVariety.bijective_rationalTateModuleGaloisMap_frobenius_sub_id l d.J hl

/-- Blueprint `proposition-no-frobenius-fixed-vector`: for `l` invertible in `K`, `σ - 1` as a
linear automorphism of the rational Tate module `V_l J`, `σ` the arithmetic Frobenius
(`AlgebraicGeometry.IsAbelianVariety.frobeniusSubOneLinearEquiv`). -/
noncomputable def frobeniusSubOneLinearEquiv [Fintype K] (d : JacobianTorsionDatum p l)
    (hl : (l : K) ≠ 0) :
    IsAbelianVariety.rationalTateModule l d.J ≃ₗ[ℚ_[l]]
      IsAbelianVariety.rationalTateModule l d.J :=
  IsAbelianVariety.frobeniusSubOneLinearEquiv l d.J hl

/-- Blueprint `proposition-no-frobenius-fixed-vector`: arithmetic Frobenius has no fixed vector on
the Jacobian Tate module.

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K`, `C` its
geometric fibre and `l` a prime. The arithmetic Frobenius `σ : z ↦ z ^ q` of `Gal(K̄ / K)` acts
on `Pic(C)` by pullback of line bundles along `𝟙 × Spec σ`; on the Tate module
`T_l Pic(C) = T_l J` it has no nonzero fixed vector. Indeed a Jacobian torsion datum
(`AlgebraicGeometry.JacobianTorsionDatum.nonempty`) identifies `Pic(C)[lⁿ]` with `J₀(K̄)[lⁿ]`
compatibly with `σ` (`AlgebraicGeometry.JacobianTorsionDatum.equivTorsion_galois`) and with the
transition maps, and `σ` has only the finitely many fixed points `J₀(K)` on `J₀(K̄)`
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_frobenius_fixed`), so this is
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.eq_zero_of_mem_tateModule_pic_of_forall_frobenius
    [Fintype K] [SmoothOfRelativeDimension 1 p] {t : ℕ → Additive p.geometricFiber.Pic}
    (ht : t ∈ AddCommGroup.tateModule l (Additive p.geometricFiber.Pic))
    (hfix : ∀ n, Additive.ofMul (Scheme.Pic.map (p.geometricFiberGaloisMap
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom)
        (t n).toMul) = t n) :
    t = 0 := by
  obtain ⟨d⟩ := JacobianTorsionDatum.nonempty p l
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)
  let M := Additive (Scheme.specAlgebraicClosure K ⟶ d.J)
  let N := Additive p.geometricFiber.Pic
  let t' : AddCommGroup.tateModule l N := ⟨t, ht⟩
  have hN (n : ℕ) : t n ∈ AddSubgroup.torsionBy N ((l : ℤ) ^ n) :=
    AddCommGroup.tateModule.pow_zsmul_coe t' n
  let s (n : ℕ) : M := (d.equivTorsion n).symm ⟨t n, hN n⟩
  have hs (n : ℕ) : s n ∈ AddSubgroup.torsionBy M ((l : ℤ) ^ n) :=
    ((d.equivTorsion n).symm ⟨t n, hN n⟩).2
  have hsT : s ∈ AddCommGroup.tateModule l M := ⟨hs, fun n ↦ by
    have h := d.equivTorsion_symm_zsmul n ⟨t (n + 1), hN (n + 1)⟩
    rw [show (⟨(l : ℤ) • t (n + 1), AddSubgroup.zsmul_mem_torsionBy_pow (hN (n + 1))⟩ :
        AddSubgroup.torsionBy N ((l : ℤ) ^ n)) = ⟨t n, hN n⟩ from
      Subtype.ext (AddCommGroup.tateModule.zsmul_coe_succ t' n)] at h
    exact h.symm⟩
  have hsfix (n : ℕ) : IsAbelianVariety.geometricPointsAddEquiv σ (s n) = s n := by
    have h := d.equivTorsion_galois n σ ⟨s n, hs n⟩
    have h' : d.equivTorsion n ⟨IsAbelianVariety.geometricPointsAddEquiv σ (s n),
        AddSubgroup.apply_mem_torsionBy (IsAbelianVariety.geometricPointsAddEquiv σ) (hs n)⟩ =
          d.equivTorsion n ⟨s n, hs n⟩ := by
      have hst : d.equivTorsion n ⟨s n, hs n⟩ = ⟨t n, hN n⟩ :=
        (d.equivTorsion n).apply_symm_apply ⟨t n, hN n⟩
      refine Subtype.ext ?_
      rw [h, hst]
      exact hfix n
    exact congrArg Subtype.val ((d.equivTorsion n).injective h')
  have h0 := AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed _
    (IsAbelianVariety.finite_setOf_frobenius_fixed d.J) hsT hsfix
  funext n
  have hsn : s n = 0 := congrFun h0 n
  have := (d.equivTorsion n).apply_symm_apply ⟨t n, hN n⟩
  rw [show (d.equivTorsion n).symm ⟨t n, hN n⟩ = 0 from Subtype.ext hsn, map_zero] at this
  exact (congrArg Subtype.val this).symm
end JacobianTorsionDatum

/-! ### The Galois action on the geometric Jacobian -/

namespace Scheme.Hom

variable {Y₀ : Scheme.{u}} (g : Y₀ ⟶ Spec (.of K))

/-- The Galois action `σ ↦ 𝟙 × Spec σ` on a geometric fiber is contravariant, like
`σ ↦ Spec σ`. -/
lemma geometricFiberGaloisMap_comp (σ τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    g.geometricFiberGaloisMap (σ.comp τ) =
      g.geometricFiberGaloisMap σ ≫ g.geometricFiberGaloisMap τ :=
  geometricFiber_hom_ext g (by simp) (by simp [Scheme.specAlgebraicClosureMap_comp])

@[simp]
lemma geometricFiberGaloisMap_id :
    g.geometricFiberGaloisMap (AlgHom.id K (AlgebraicClosure K)) = 𝟙 _ :=
  geometricFiber_hom_ext g (by simp) (by
    rw [geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure,
      Scheme.specAlgebraicClosureMap_id, Over.id_left]
    exact Category.comp_id _)

end Scheme.Hom

namespace Scheme

/-- On the unit object of `Over (Spec K̄)`, the endomorphism `Spec σ⁻¹` lies over a section of
`Spec σ`, for `σ ∈ Gal(K̄ / K)`. This is the condition needed to transport points along
semilinear maps over `Spec σ` (`AlgebraicGeometry.SemilinearGrpHom.mapPoints`). -/
lemma specAlgebraicClosureMap_inv_left_comp (σ : Gal(AlgebraicClosure K/K)) :
    (specAlgebraicClosureMap σ⁻¹.toAlgHom).left ≫
        (𝟙_ (Over (Spec (.of (AlgebraicClosure K))))).hom ≫
          (specAlgebraicClosureMap σ.toAlgHom).left =
      (𝟙_ (Over (Spec (.of (AlgebraicClosure K))))).hom := by
  rw [Over.tensorUnit_hom]
  exact (Category.id_comp _).trans
    (congrArg Over.Hom.left (specAlgebraicClosureMap_symm_comp_self σ))

variable (A : Over (Spec (.of K))) [GrpObj A]

/-- Blueprint `proposition-jacobian-over-ground-field--5` (Galois module of points): for a group
scheme `A` over `K` and `σ ∈ Gal(K̄ / K)`, transporting a `K̄`-point `P` of `A_{K̄}` along the
semilinear automorphism `σ_A = 𝟙 × Spec σ`
(`AlgebraicGeometry.Scheme.geometricFiberGaloisGrpHom`), `P ↦ σ_A ∘ P ∘ Spec σ⁻¹`, is the
action of `σ⁻¹` by coordinates on `A(K̄) = A_{K̄}(K̄)`
(`AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv`). -/
theorem geometricPointsAddEquivBaseChangePoints_symm_mapPoints (σ : Gal(AlgebraicClosure K/K))
    (x : Additive (Scheme.specAlgebraicClosure K ⟶ A)) :
    (geometricPointsAddEquivBaseChangePoints A).symm
        ((geometricFiberGaloisGrpHom A σ.toAlgHom).mapPoints
          (specAlgebraicClosureMap σ⁻¹.toAlgHom).left
          (specAlgebraicClosureMap_inv_left_comp σ)
          (geometricPointsAddEquivBaseChangePoints A x)) =
      IsAbelianVariety.geometricPointsAddEquiv σ⁻¹ x := by
  refine Additive.toMul.injective (Over.OverMorphism.ext ?_)
  have h1 (y : Additive (𝟙_ (Over (Spec (.of (AlgebraicClosure K)))) ⟶
      baseChangeAlgebraicClosure A)) :
      ((geometricPointsAddEquivBaseChangePoints A).symm y).toMul.left =
        y.toMul.left ≫ pullback.fst _ _ := rfl
  have h2 : ((geometricPointsAddEquivBaseChangePoints A) x).toMul.left ≫ pullback.fst _ _ =
      x.toMul.left :=
    congrArg (fun z ↦ z.toMul.left)
      ((geometricPointsAddEquivBaseChangePoints A).symm_apply_apply x)
  have h3 (y : Additive (𝟙_ (Over (Spec (.of (AlgebraicClosure K)))) ⟶
      baseChangeAlgebraicClosure A)) :
      ((geometricFiberGaloisGrpHom A σ.toAlgHom).mapPoints
          (specAlgebraicClosureMap σ⁻¹.toAlgHom).left
          (specAlgebraicClosureMap_inv_left_comp σ) y).toMul.left =
        (specAlgebraicClosureMap σ⁻¹.toAlgHom).left ≫ y.toMul.left ≫
          A.hom.geometricFiberGaloisMap σ.toAlgHom := rfl
  rw [h1, h3]
  erw [Category.assoc, Category.assoc, Hom.geometricFiberGaloisMap_comp_geometricFiberProj, h2]
  rfl

end Scheme

/-- An injective homomorphism `f : M →+ N` whose image contains the `n`-torsion of `N` restricts
to an isomorphism `M[n] ≃+ N[n]` of `n`-torsion subgroups. -/
theorem _root_.AddSubgroup.exists_addEquiv_torsionBy_of_injective {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (hf : Function.Injective f) {n : ℤ}
    (hn : ∀ y ∈ AddSubgroup.torsionBy N n, y ∈ f.range) :
    ∃ e : AddSubgroup.torsionBy M n ≃+ AddSubgroup.torsionBy N n, ∀ x, (e x : N) = f x := by
  let g : AddSubgroup.torsionBy M n →+ AddSubgroup.torsionBy N n :=
    { toFun x := ⟨f x.1, AddSubgroup.apply_mem_torsionBy f x.2⟩
      map_zero' := Subtype.ext (map_zero f)
      map_add' x y := Subtype.ext (map_add f x.1 y.1) }
  refine ⟨AddEquiv.ofBijective g ⟨fun x y h ↦ Subtype.ext (hf (congrArg Subtype.val h)),
    fun y ↦ ?_⟩, fun x ↦ rfl⟩
  obtain ⟨x, hx⟩ := hn y y.2
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change n • x = 0
  apply hf
  rw [map_zsmul, hx, map_zero]
  exact y.2

variable (K) in
/-- Blueprint `proposition-jacobian-over-ground-field--5`: Canonical semilinear Galois action on
the geometric Jacobian.

Let `C₀` be a smooth proper geometrically connected curve over a field `K` (given by
`p : C₀ ⟶ Spec K`) and `C = C₀ ×_K K̄` its geometric fiber. There is an abelian variety (a
commutative group scheme) `J₀` over `K` representing `Pic⁰_{C₀/K}` by `r` (the Jacobian of
`C₀`), whose base change `J = J₀ ×_K K̄` (`J₀.hom.geometricFiber`) represents `Pic⁰_{C/K̄}`
by the base change `rK` of `r`, i.e. is the Jacobian of `C`. Moreover:

* the identification `φ : J₀(K̄) ≅ Pic⁰(C) ⊆ Pic(C)` is induced by the representing data: a
  geometric point `x` of `J₀` is the point which `r` attaches to the class of `φ x`; `φ` is an
  injective group homomorphism whose image contains all torsion line bundles;
* for `σ ∈ Gal(K̄ / K)`, the automorphism `σ_J = 𝟙 × Spec σ` of `J`
  (`J₀.hom.geometricFiberGaloisMap σ`), which lies over `Spec σ`, is the unique endomorphism of
  `J` over `Spec σ` inducing the Galois action `σ_C^*` on the represented functor
  `Pic⁰_{C/K̄}` (`AlgebraicGeometry.Scheme.Hom.geometricFiberPicardGaloisMap`), by Yoneda;
* `σ ↦ σ_J` is an action: `σ_J` for `σ τ` is `σ_J ≫ τ_J` (`Spec` is contravariant);
* `σ_J` preserves the group laws: it underlies a homomorphism of group schemes semilinear over
  `Spec σ` (`AlgebraicGeometry.SemilinearGrpHom`, for the base-changed group law on `J`). The
  induced action on `K̄`-points, `P ↦ σ_J ∘ P ∘ Spec σ⁻¹`, is the coordinate action of `σ⁻¹` on
  `J(K̄) = J₀(K̄)`, so that `J₀(K̄)` is a Galois module, and componentwise it is the
  `ℤ_l`-linear Galois action on the Tate module `T_l J`
  (`AlgebraicGeometry.IsAbelianVariety.galoisRepresentation`), making `T_l J` a
  `ℤ_l[Gal(K̄ / K)]`-module;
* `φ` is Galois equivariant: `φ (Spec σ ≫ x) = σ_C^* (φ x)` for the action `σ_C = 𝟙 × Spec σ` of
  `σ` on `C`, and so are its restrictions `J₀[n](K̄) ≅ Pic⁰(C)[n]` to `n`-torsion, `n ≠ 0`. -/
theorem exists_jacobian_galoisAction (p : C ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    [IsProper p] [GeometricallyConnected p] :
    ∃ (J₀ : Over (Spec (.of K))) (_ : CommGrpObj J₀) (_ : IsAbelianVariety J₀)
      (r : (picardFunctorDegree p 0).obj.RepresentableBy J₀)
      (rK : (picardFunctorDegree p.geometricFiberToAlgebraicClosure 0).obj.RepresentableBy
        (Over.mk J₀.hom.geometricFiberToAlgebraicClosure))
      (φ : (Scheme.specAlgebraicClosure K ⟶ J₀) →* p.geometricFiber.Pic),
      -- `rK` is the base change of `r`
      (∀ (T : Over (Spec (.of (AlgebraicClosure K))))
        (y : (picardFunctorDegree p 0).obj.obj
          (.op ((Over.map (Spec.map (CommRingCat.ofHom
            (algebraMap K (AlgebraicClosure K))))).obj T))),
        rK.homEquiv.symm ((p.geometricFiberPicardIso 0).hom.app (.op T) y) =
          (Over.mapPullbackAdj _).homEquiv T J₀ (r.homEquiv.symm y)) ∧
      -- `φ` is induced by `r`
      (∀ x, ∃ h, x = r.homEquiv.symm ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree p 0).toFunctor).app _
            ⟨Scheme.Pic.map (IsPullback.of_hasPullback p
              (Scheme.specAlgebraicClosure K).hom).isoPullback.inv (φ x), h⟩)) ∧
      Function.Injective φ ∧
      (∀ (n : ℕ) (L : p.geometricFiber.Pic), n ≠ 0 → L ^ n = 1 → L ∈ φ.range) ∧
      -- `σ_J` is the unique endomorphism over `Spec σ` inducing `σ_C^*`
      (∀ (σ : Gal(AlgebraicClosure K/K)) (f : J₀.hom.geometricFiber ⟶ J₀.hom.geometricFiber)
        (hf : f ≫ J₀.hom.geometricFiberToAlgebraicClosure =
          J₀.hom.geometricFiberToAlgebraicClosure ≫
            (Scheme.specAlgebraicClosureMap σ.toAlgHom).left),
        (∀ (T : Over (Spec (.of (AlgebraicClosure K))))
          (x : T ⟶ Over.mk J₀.hom.geometricFiberToAlgebraicClosure),
          rK.homEquiv (galoisTwistHom (J := Over.mk J₀.hom.geometricFiberToAlgebraicClosure)
            f hf x) = p.geometricFiberPicardGaloisMap 0 σ.toAlgHom T (rK.homEquiv x)) ↔
        f = J₀.hom.geometricFiberGaloisMap σ.toAlgHom) ∧
      -- `σ ↦ σ_J` is an action
      (∀ σ τ : Gal(AlgebraicClosure K/K),
        J₀.hom.geometricFiberGaloisMap (σ * τ).toAlgHom =
          J₀.hom.geometricFiberGaloisMap σ.toAlgHom ≫ J₀.hom.geometricFiberGaloisMap τ.toAlgHom) ∧
      -- `σ_J` preserves the group law: it is a homomorphism of group schemes over `Spec σ`;
      -- transporting `K̄`-points along it is the coordinate action of `σ⁻¹` on `J₀(K̄)`, and so
      -- `σ_J` induces the `ℤ_l`-linear Galois action on the Tate module `T_l J`
      (∀ σ : Gal(AlgebraicClosure K/K), ∃ g : SemilinearGrpHom
          (S := Spec (.of (AlgebraicClosure K))) (Scheme.specAlgebraicClosureMap σ.toAlgHom).left
          (Scheme.baseChangeAlgebraicClosure J₀) (Scheme.baseChangeAlgebraicClosure J₀),
        g.hom = J₀.hom.geometricFiberGaloisMap σ.toAlgHom ∧
        (∀ x, (Scheme.geometricPointsAddEquivBaseChangePoints J₀).symm
            (g.mapPoints (Scheme.specAlgebraicClosureMap σ⁻¹.toAlgHom).left
              (Scheme.specAlgebraicClosureMap_inv_left_comp σ)
              (Scheme.geometricPointsAddEquivBaseChangePoints J₀ x)) =
          IsAbelianVariety.geometricPointsAddEquiv σ⁻¹ x) ∧
        ∀ (l : ℕ) [Fact l.Prime] (t : IsAbelianVariety.tateModule l J₀) (n : ℕ),
          ((IsAbelianVariety.galoisRepresentation l J₀ σ⁻¹ t : IsAbelianVariety.tateModule l J₀) :
              ∀ _ : ℕ, Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) n =
            (Scheme.geometricPointsAddEquivBaseChangePoints J₀).symm
              (g.mapPoints (Scheme.specAlgebraicClosureMap σ⁻¹.toAlgHom).left
                (Scheme.specAlgebraicClosureMap_inv_left_comp σ)
                (Scheme.geometricPointsAddEquivBaseChangePoints J₀
                  ((t : ∀ _ : ℕ, Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) n)))) ∧
      -- `φ` is Galois equivariant
      (∀ (σ : Gal(AlgebraicClosure K/K)) (x : Scheme.specAlgebraicClosure K ⟶ J₀),
        φ (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x) =
          Scheme.Pic.map (p.geometricFiberGaloisMap σ.toAlgHom) (φ x)) ∧
      -- and so are its restrictions to torsion
      ∀ n : ℕ, n ≠ 0 → ∃ eₙ : AddSubgroup.torsionBy
          (Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) (n : ℤ) ≃+
            AddSubgroup.torsionBy (Additive p.geometricFiber.Pic) (n : ℤ),
        (∀ x, (eₙ x : Additive p.geometricFiber.Pic) = Additive.ofMul (φ x.1.toMul)) ∧
        ∀ (σ : Gal(AlgebraicClosure K/K))
          (x : AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ J₀)) (n : ℤ)),
          (eₙ ⟨IsAbelianVariety.geometricPointsAddEquiv σ x,
              AddSubgroup.apply_mem_torsionBy (IsAbelianVariety.geometricPointsAddEquiv σ) x.2⟩ :
            Additive p.geometricFiber.Pic) =
            Additive.ofMul (Scheme.Pic.map (p.geometricFiberGaloisMap σ.toAlgHom)
              (eₙ x : Additive p.geometricFiber.Pic).toMul) := by
  let _ : C.Over (Spec (.of K)) := ⟨p⟩
  let _ : p.geometricFiber.Over (Spec (.of (AlgebraicClosure K))) :=
    ⟨p.geometricFiberToAlgebraicClosure⟩
  have : SmoothOfRelativeDimension 1 (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd p _))
  have : IsProper (p.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
    inferInstanceAs (IsProper (pullback.snd p _))
  have : GeometricallyConnected (C ↘ Spec (.of K)) := ‹GeometricallyConnected p›
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of K)) := ‹SmoothOfRelativeDimension 1 p›
  have : IsProper (C ↘ Spec (.of K)) := ‹IsProper p›
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  obtain ⟨J₀, _, r, hP, hS, hG, -, ⟨rK, hrK⟩, e, he, hσ⟩ := exists_jacobian_descent K
    (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K) C _ rfl p.geometricFiber
    p.geometricFiberProj (IsPullback.of_hasPullback _ _)
  have : Smooth J₀.hom := SmoothOfRelativeDimension.smooth (Scheme.arithmeticGenus K C) _
  have : IrreducibleSpace J₀.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    (f := J₀.hom)
  have hJ : IsAbelianVariety J₀ := ⟨⟩
  let φ : (Scheme.specAlgebraicClosure K ⟶ J₀) →* p.geometricFiber.Pic :=
    (picardZero (AlgebraicClosure K) p.geometricFiber).subtype.comp e.symm.toMonoidHom
  have hinj : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  -- a torsion line bundle has degree zero
  have htors (n : ℕ) (L : p.geometricFiber.Pic) (hn : n ≠ 0) (hL : L ^ n = 1) : L ∈ φ.range := by
    have hL0 : L ∈ picardZero (AlgebraicClosure K) p.geometricFiber := by
      rw [MonoidHom.mem_ker]
      have h := congrArg (fun z ↦ (Scheme.picDegreeHom (AlgebraicClosure K)
        p.geometricFiber z).toAdd) hL
      simp only [map_pow, toAdd_pow, map_one, toAdd_one] at h
      rw [← ofAdd_toAdd (Scheme.picDegreeHom _ _ _), ofAdd_eq_one]
      exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hn)
    exact ⟨e ⟨L, hL0⟩, by
      change ((e.symm (e ⟨L, hL0⟩) : picardZero (AlgebraicClosure K) p.geometricFiber) :
        p.geometricFiber.Pic) = L
      rw [MulEquiv.symm_apply_apply]⟩
  -- equivariance of `φ`
  have hφσ (σ : Gal(AlgebraicClosure K/K)) (x : Scheme.specAlgebraicClosure K ⟶ J₀) :
      φ (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x) =
        Scheme.Pic.map (p.geometricFiberGaloisMap σ.toAlgHom) (φ x) := by
    obtain ⟨γ, hγ₁, hγ₂, act, hact₁, hact₂⟩ := hσ σ
    have hγ : γ = p.geometricFiberGaloisMap σ.toAlgHom :=
      Scheme.Hom.geometricFiber_hom_ext p (by simpa using hγ₁) (by
        rw [Scheme.Hom.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure]
        exact hγ₂)
    have hx : e (act (e.symm x)) = specAlgEquivOver σ ≫ e (e.symm x) := hact₂ (e.symm x)
    rw [MulEquiv.apply_symm_apply, ← MulEquiv.eq_symm_apply] at hx
    change ((e.symm (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x) :
      picardZero (AlgebraicClosure K) p.geometricFiber) : p.geometricFiber.Pic) = _
    rw [show Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ x = specAlgEquivOver σ ≫ x from rfl,
      ← hx, hact₁, hγ]
    rfl
  refine ⟨J₀, inferInstance, hJ, r, rK, φ, hrK, fun x ↦ ?_, hinj, htors,
    fun σ f hf ↦ Scheme.Hom.homEquiv_galoisTwistHom_iff hrK σ.toAlgHom f hf,
    fun σ τ ↦ ?_, fun σ ↦ ⟨Scheme.geometricFiberGaloisGrpHom J₀ σ.toAlgHom, rfl,
      Scheme.geometricPointsAddEquivBaseChangePoints_symm_mapPoints J₀ σ,
      fun l _ t n ↦ (Scheme.geometricPointsAddEquivBaseChangePoints_symm_mapPoints J₀ σ _).symm⟩,
    hφσ, fun n hn ↦ ?_⟩
  · obtain ⟨h, hx⟩ := he (e.symm x)
    exact ⟨h, (e.apply_symm_apply x).symm.trans hx⟩
  · rw [show (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom from AlgHom.ext fun _ ↦ rfl]
    exact Scheme.Hom.geometricFiberGaloisMap_comp _ _ _
  · obtain ⟨eₙ, heₙ⟩ := AddSubgroup.exists_addEquiv_torsionBy_of_injective φ.toAdditive hinj
      fun y hy ↦ by
        have h2 : ((n : ℤ) • y) = 0 := hy
        have h3 := congrArg Additive.toMul h2
        rw [toMul_zsmul, toMul_zero, zpow_natCast] at h3
        obtain ⟨x, hx⟩ := htors n _ hn h3
        exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
    refine ⟨eₙ, heₙ, fun σ x ↦ ?_⟩
    rw [heₙ, heₙ]
    exact congrArg Additive.ofMul (hφσ σ x.1.toMul)

namespace JacobianTorsionDatum

variable [Finite K] {p : C ⟶ Spec (.of K)} [IsCurve p] [Smooth p] [IsProper p]
  [GeometricallyIntegral p] {l : ℕ} [Fact l.Prime]

variable (p l) in
/-- Blueprint `proposition-jacobian-over-ground-field--5` (torsion clause), as used in
`proposition-h-1-curve-tate-module--1`: the comparison isomorphisms of a Jacobian torsion
datum can be taken to be induced by the representing isomorphism.

There is a Jacobian torsion datum `d` together with an injective homomorphism
`φ : J₀(K̄) → Pic(C)` determined by the representing isomorphism `d.representableBy` of `J₀`
(a geometric point `x` is the point which it attaches to the class of `φ x`), such that every
comparison isomorphism `J₀(K̄)[lⁿ] ≃ Pic(C)[lⁿ]` of `d` is the restriction of `φ`. This is the
datum obtained from `AlgebraicGeometry.exists_jacobian_galoisAction`. -/
theorem exists_equivTorsion_eq_restrict [SmoothOfRelativeDimension 1 p] :
    ∃ (d : JacobianTorsionDatum p l)
      (φ : (Scheme.specAlgebraicClosure K ⟶ d.J) →* p.geometricFiber.Pic),
      (∀ x, ∃ h, x = d.representableBy.homEquiv.symm
        ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree p 0).toFunctor).app _
            ⟨Scheme.Pic.map (IsPullback.of_hasPullback p
              (Scheme.specAlgebraicClosure K).hom).isoPullback.inv (φ x), h⟩)) ∧
      Function.Injective φ ∧
      ∀ (n : ℕ) (x : AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ d.J))
          ((l : ℤ) ^ n)),
        (d.equivTorsion n x : Additive p.geometricFiber.Pic) = Additive.ofMul (φ x.1.toMul) := by
  have : GeometricallyConnected p := .of_geometricallyIrreducible p
  obtain ⟨J₀, _, hJ, r, -, φ, -, hφr, hinj, htors, -, -, -, hφσ, -⟩ :=
    exists_jacobian_galoisAction K p
  choose eT heT using fun n : ℕ ↦
    AddSubgroup.exists_addEquiv_torsionBy_of_injective φ.toAdditive hinj (n := (l : ℤ) ^ n)
      fun y hy ↦ by
        have h3 := congrArg Additive.toMul (show ((l : ℤ) ^ n) • y = 0 from hy)
        rw [toMul_zsmul, toMul_zero, ← Nat.cast_pow, zpow_natCast] at h3
        obtain ⟨x, hx⟩ := htors (l ^ n) _ (pow_ne_zero n (Fact.out : l.Prime).ne_zero) h3
        exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  refine ⟨@JacobianTorsionDatum.mk _ _ _ _ p _ _ _ _ l _ J₀ _ hJ r eT (fun n σ x ↦ ?_)
    (fun n x ↦ ?_), φ, hφr, hinj, heT⟩
  · rw [heT, heT]
    exact congrArg Additive.ofMul (hφσ σ x.1.toMul)
  · rw [heT, heT]
    exact map_zsmul φ.toAdditive _ _

end JacobianTorsionDatum

end AlgebraicGeometry
