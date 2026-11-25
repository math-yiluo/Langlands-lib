/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.KummerTransition
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PicTorsionPairingTransport
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian

/-!
# Kummer theory and the Jacobian Tate module

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K`, `C` its
geometric fiber and `l` a prime different from the characteristic. Composing the Kummer
identification `H¹(C, μ_{lⁿ}) ≅ Pic(C)[lⁿ]` (`AlgebraicGeometry.Scheme.kummerTorsionEquiv`) with
the comparison isomorphisms `Pic(C)[lⁿ] ≅ J₀(K̄)[lⁿ]` of a Jacobian torsion datum gives
isomorphisms `H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` which are Galois-equivariant and compatible with the
transition maps `μ_{lⁿ⁺¹} ⟶ μ_{lⁿ}`, `z ↦ z ^ l`, and multiplication by `l`.

## Main definitions

- `AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv`: `H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]`.

## Main statements

- `AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv_restrictMuH`: Galois equivariance.
- `AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv_map_rootsOfUnityPowMap`: compatibility
  with the transition maps.
- `AlgebraicGeometry.JacobianTorsionDatum.exists_kummerEquiv_eq`: for a datum whose comparison
  maps are induced by the representing isomorphism of the Jacobian, `kummerEquiv` is the Kummer
  identification followed by that representing isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

namespace Scheme.Hom

variable {Y₀ : Scheme.{u}} (g : Y₀ ⟶ Spec (.of K))

/-- The geometric fiber `Y₀ ×_K K̄` as a scheme over `Spec K̄`. -/
noncomputable instance geometricFiberOver :
    g.geometricFiber.Over (Spec (.of (AlgebraicClosure K))) :=
  ⟨g.geometricFiberToAlgebraicClosure⟩

instance [IsProper g] : IsProper (g.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
  inferInstanceAs (IsProper (pullback.snd g _))

instance [SmoothOfRelativeDimension 1 g] :
    SmoothOfRelativeDimension 1 (g.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) :=
  inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd g _))

/-- The Galois action `𝟙 × Spec σ` of an automorphism `σ` of `K̄` is an isomorphism, with
inverse the action of `σ⁻¹`. -/
instance isIso_geometricFiberGaloisMap (σ : Gal(AlgebraicClosure K/K)) :
    IsIso (g.geometricFiberGaloisMap σ.toAlgHom) :=
  ⟨g.geometricFiberGaloisMap σ⁻¹.toAlgHom, by
    rw [← geometricFiberGaloisMap_comp]
    convert g.geometricFiberGaloisMap_id
    ext
    simp, by
    rw [← geometricFiberGaloisMap_comp]
    convert g.geometricFiberGaloisMap_id
    ext
    simp⟩

/-- The Galois action `𝟙 × Spec σ` lies over the automorphism `Spec σ` of `Spec K̄`. -/
lemma geometricFiberGaloisMap_over (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) :
    g.geometricFiberGaloisMap σ ≫ (g.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) =
      (g.geometricFiber ↘ Spec (.of (AlgebraicClosure K))) ≫
        (Scheme.specAlgebraicClosureMap σ).left :=
  g.geometricFiberGaloisMap_comp_geometricFiberToAlgebraicClosure σ

end Scheme.Hom

namespace JacobianTorsionDatum

variable [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p] [Smooth p] [IsProper p]
  [GeometricallyIntegral p] {l : ℕ} [Fact l.Prime]

omit [Finite K] [Fact l.Prime] in
/-- A prime different from the characteristic of `K` is invertible in `K̄`, as are its
powers. -/
lemma natCast_pow_ne_zero (hl : (l : K) ≠ 0) (n : ℕ) :
    ((l ^ n : ℕ) : AlgebraicClosure K) ≠ 0 := by
  rw [Nat.cast_pow, ← map_natCast (algebraMap K (AlgebraicClosure K))]
  exact pow_ne_zero _ ((map_ne_zero _).2 hl)

/-- Blueprint `proposition-h-1-curve-tate-module--1`: Kummer identifies curve cohomology
with the Jacobian torsion.

For a Jacobian torsion datum `d` of `C₀` and a prime `l` invertible in `K`, the isomorphism
`H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]`: the Kummer identification `H¹(C, μ_{lⁿ}) ≅ Pic(C)[lⁿ]`
(`AlgebraicGeometry.Scheme.kummerTorsionEquiv`) followed by the inverse of the comparison
isomorphism `J₀(K̄)[lⁿ] ≅ Pic(C)[lⁿ]` of the datum. It is Galois-equivariant
(`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv_restrictMuH`) and compatible with the
transition maps (`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv_map_rootsOfUnityPowMap`). -/
noncomputable def kummerEquiv (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0) (n : ℕ) :
    Sheaf.H (p.geometricFiber.rootsOfUnitySheaf (l ^ n)) 1 ≃+
      AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) ((l : ℤ) ^ n) :=
  ((Scheme.kummerTorsionEquiv (l ^ n) (natCast_pow_ne_zero hl n)).trans
    (AddEquiv.addSubgroupCongr (by rw [Nat.cast_pow]))).trans (d.equivTorsion n).symm

lemma equivTorsion_kummerEquiv (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0) (n : ℕ)
    (x : Sheaf.H (p.geometricFiber.rootsOfUnitySheaf (l ^ n)) 1) :
    (d.equivTorsion n (d.kummerEquiv hl n x) : Additive p.geometricFiber.Pic) =
      Scheme.kummerTorsionEquiv (l ^ n) (natCast_pow_ne_zero hl n) x := by
  simp [kummerEquiv]

/-- Blueprint `proposition-h-1-curve-tate-module--1`: the isomorphism
`H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` is Galois-equivariant: restriction along the automorphism
`σ_C = 𝟙 × Spec σ` of `C` corresponds to the action of `σ` on geometric points by
coordinates. -/
theorem kummerEquiv_restrictMuH (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0) (n : ℕ)
    (σ : Gal(AlgebraicClosure K/K))
    (x : Sheaf.H (p.geometricFiber.rootsOfUnitySheaf (l ^ n)) 1) :
    (d.kummerEquiv hl n (Scheme.restrictMuH (p.geometricFiberGaloisMap σ.toAlgHom) (l ^ n) 1 x) :
        Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) =
      IsAbelianVariety.geometricPointsAddEquiv σ (d.kummerEquiv hl n x) := by
  have key : d.kummerEquiv hl n
      (Scheme.restrictMuH (p.geometricFiberGaloisMap σ.toAlgHom) (l ^ n) 1 x) =
      ⟨IsAbelianVariety.geometricPointsAddEquiv σ (d.kummerEquiv hl n x),
        AddSubgroup.apply_mem_torsionBy _ (d.kummerEquiv hl n x).2⟩ := by
    apply (d.equivTorsion n).injective
    apply Subtype.ext
    rw [equivTorsion_kummerEquiv, d.equivTorsion_galois, equivTorsion_kummerEquiv,
      Scheme.coe_kummerTorsionEquiv_restrictMuH]
    rfl
  rw [key]

/-- Blueprint `proposition-h-1-curve-tate-module--1`: the isomorphisms
`H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` are compatible with the transition maps: the map induced by
`μ_{lⁿ⁺¹} ⟶ μ_{lⁿ}`, `z ↦ z ^ l`, corresponds to multiplication by `l`. Hence they form a
compatible system identifying `lim_n H¹(C, μ_{lⁿ})` with the Tate module `T_l J`. -/
theorem kummerEquiv_map_rootsOfUnityPowMap (d : JacobianTorsionDatum p l) (hl : (l : K) ≠ 0)
    (n : ℕ) (x : Sheaf.H (p.geometricFiber.rootsOfUnitySheaf (l ^ (n + 1))) 1) :
    (d.kummerEquiv hl n
        (Sheaf.H.map (p.geometricFiber.rootsOfUnityPowMap l (pow_succ l n).symm) 1 x) :
        Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) =
      (l : ℤ) • (d.kummerEquiv hl (n + 1) x : Additive (Scheme.specAlgebraicClosure K ⟶ d.J)) := by
  have key : d.kummerEquiv hl n
      (Sheaf.H.map (p.geometricFiber.rootsOfUnityPowMap l (pow_succ l n).symm) 1 x) =
      (d.equivTorsion n).symm ⟨(l : ℤ) •
        (d.equivTorsion (n + 1) (d.kummerEquiv hl (n + 1) x) : Additive p.geometricFiber.Pic),
        AddSubgroup.zsmul_mem_torsionBy_pow (d.equivTorsion (n + 1) _).2⟩ := by
    rw [AddEquiv.eq_symm_apply]
    apply Subtype.ext
    rw [equivTorsion_kummerEquiv, Scheme.coe_kummerTorsionEquiv_map_rootsOfUnityPowMap l _ _
      (natCast_pow_ne_zero hl _), ← natCast_zsmul]
    simp [equivTorsion_kummerEquiv]
  rw [key, d.equivTorsion_symm_zsmul, AddEquiv.symm_apply_apply]

variable (p l) in
/-- Blueprint `proposition-h-1-curve-tate-module--1`: Kummer identifies curve cohomology
with the Jacobian torsion, through the representing isomorphism of the Jacobian.

There is a Jacobian torsion datum `d` and an injective homomorphism `φ : J₀(K̄) → Pic(C)`
determined by the representing isomorphism `d.representableBy` of the Jacobian (a geometric
point `x` of `J₀` is the point which it attaches to the class of `φ x`), such that the
isomorphism `H¹(C, μ_{lⁿ}) ≅ J₀(K̄)[lⁿ]` of `d`
(`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv`, Galois-equivariant by
`AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv_restrictMuH` and compatible with the
transition maps by `AlgebraicGeometry.JacobianTorsionDatum.kummerEquiv_map_rootsOfUnityPowMap`)
is the Kummer identification `H¹(C, μ_{lⁿ}) ≅ Pic(C)[lⁿ]`
(`AlgebraicGeometry.Scheme.kummerTorsionEquiv`) followed by the inverse of `φ`. -/
theorem exists_kummerEquiv_eq [SmoothOfRelativeDimension 1 p] (hl : (l : K) ≠ 0) :
    ∃ (d : JacobianTorsionDatum p l)
      (φ : (Scheme.specAlgebraicClosure K ⟶ d.J) →* p.geometricFiber.Pic),
      (∀ x, ∃ h, x = d.representableBy.homEquiv.symm
        ((toSheafify (Scheme.fppfTopology.over (Spec (.of K)))
          (picardSubfunctorDegree p 0).toFunctor).app _
            ⟨Scheme.Pic.map (IsPullback.of_hasPullback p
              (Scheme.specAlgebraicClosure K).hom).isoPullback.inv (φ x), h⟩)) ∧
      Function.Injective φ ∧
      ∀ (n : ℕ) (x : Sheaf.H (p.geometricFiber.rootsOfUnitySheaf (l ^ n)) 1),
        Additive.ofMul (φ (d.kummerEquiv hl n x :
            Additive (Scheme.specAlgebraicClosure K ⟶ d.J)).toMul) =
          Scheme.kummerTorsionEquiv (l ^ n) (natCast_pow_ne_zero hl n) x := by
  obtain ⟨d, φ, hφr, hinj, hφ⟩ := exists_equivTorsion_eq_restrict p l
  exact ⟨d, φ, hφr, hinj, fun n x ↦ by rw [← equivTorsion_kummerEquiv d hl, hφ]⟩

end JacobianTorsionDatum

end AlgebraicGeometry
