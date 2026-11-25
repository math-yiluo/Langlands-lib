/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusLift
public import WeilConjectures.Evaluation
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Local Frobenius elements in the étale fundamental group

Let `p : X₀ ⟶ Spec k₀` be a connected scheme over a finite field with `q` elements, `s` a
geometric point and `G = π₁(X₀, s)`. For a point `x` of `X₀` with finite residue field, any two
fibre functors of `FÉt(X₀)` being isomorphic, there is a path from the geometric point `x̄` over
`x` to `s`, and transporting the geometric Frobenius `F_x` along it gives a Frobenius element at
`x` (`AlgebraicGeometry.Scheme.FiniteEtale.exists_isFrobeniusElement`).

On the geometric fibre of a constant cover `X₀ ×_{k₀} Spec A`, the geometric Frobenius `F_x`
acts as the `e_x`-th power of the geometric Frobenius of `k₀`, where `e_x = [κ(x) : k₀]`, since
`#κ(x) = q ^ e_x`. Hence a Frobenius element at `x` lies in the Weil group with degree `e_x`
(`AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement.mem_weilGroup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {K : Type u} [Field K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

/-- Precomposition with `Spec σ` acts on the embeddings `A → Ω` by postcomposition with `σ`. -/
lemma fiberConstantCoverEquiv_fiberPrecompIso (σ : Ω ≃+* Ω)
    (he : (specMapIso σ).hom ≫ s = s) (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover p A)) :
    (fiberConstantCoverEquiv p s A ((fiberPrecompIso s (specMapIso σ) he).hom.app _ y)).1 =
      σ.toRingHom.comp (fiberConstantCoverEquiv p s A y).1 := by
  rw [fiberConstantCoverEquiv_apply, fiberConstantCoverEquiv_apply,
    fiberPrecompIso_hom_app_left]
  change _ = (Spec.preimage (y.left ≫ pullback.snd p A.specHom) ≫
    CommRingCat.ofHom σ.toRingHom).hom
  congr 1
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Category.assoc]
  rfl

variable [Finite K]

lemma geometricFrobenius_inv_apply (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover p A)) :
    (geometricFrobenius p s A)⁻¹ y = (fiber s).map (arithmeticFrobenius p A).hom y :=
  rfl

/-- The arithmetic Frobenius raises the embeddings `A → Ω` to the `q`-th power. -/
lemma fiberConstantCoverEquiv_arithmeticFrobenius (A : FiniteEtaleAlgebra K)
    (y : (fiber s).obj (constantCover p A)) (a : A.1) :
    (fiberConstantCoverEquiv p s A ((fiber s).map (arithmeticFrobenius p A).hom y)).1 a =
      (fiberConstantCoverEquiv p s A y).1 a ^ Nat.card K := by
  rw [show (arithmeticFrobenius p A).hom = constantCoverHom p A.frobenius.toAlgHom from rfl,
    fiberConstantCoverEquiv_fiber_map]
  simp [FiniteEtaleAlgebra.frobenius_apply, map_pow]

lemma fiberConstantCoverEquiv_geometricFrobenius_inv_pow (A : FiniteEtaleAlgebra K) (n : ℕ)
    (y : (fiber s).obj (constantCover p A)) (a : A.1) :
    (fiberConstantCoverEquiv p s A (((geometricFrobenius p s A)⁻¹ ^ n) y)).1 a =
      (fiberConstantCoverEquiv p s A y).1 a ^ (Nat.card K ^ n) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, geometricFrobenius_inv_apply,
      fiberConstantCoverEquiv_arithmeticFrobenius, ih, ← pow_mul, pow_succ, mul_comm]

/-- Precomposition with `Spec ρ`, for a ring automorphism `ρ` of `Ω` with `ρ(z) ^ (q ^ n) = z`,
acts on the geometric fibres of the constant covers as the `n`-th power of the geometric
Frobenius. -/
lemma fiberPrecompIso_hom_app_eq_geometricFrobenius_zpow (n : ℕ) (ρ : Ω ≃+* Ω)
    (hρ : ∀ z, ρ z ^ (Nat.card K ^ n) = z) (he : (specMapIso ρ).hom ≫ s = s)
    (A : FiniteEtaleAlgebra K) (y : (fiber s).obj (constantCover p A)) :
    (fiberPrecompIso s (specMapIso ρ) he).hom.app _ y =
      (geometricFrobenius p s A ^ (n : ℤ)) y := by
  rw [zpow_natCast, ← inv_inv (geometricFrobenius p s A), inv_pow, Equiv.Perm.eq_inv_iff_eq]
  apply (fiberConstantCoverEquiv p s A).injective
  ext a
  rw [fiberConstantCoverEquiv_geometricFrobenius_inv_pow,
    fiberConstantCoverEquiv_fiberPrecompIso]
  exact hρ _

/-- The geometric Frobenius `F_x` at a point `x` with finite residue field acts on the geometric
fibres at `x̄` of the constant covers as the `e_x`-th power of the geometric Frobenius of `k₀`,
`e_x = [κ(x) : k₀]`. -/
lemma geometricFrobeniusAt_hom_app_eq (x : X₀) [Finite (X₀.residueField x)]
    (A : FiniteEtaleAlgebra K) (y : (fiber (residueFieldPoint X₀ x)).obj (constantCover p A)) :
    (geometricFrobeniusAt x).hom.app _ y =
      (geometricFrobenius p (residueFieldPoint X₀ x) A ^ (p.degreeOver x : ℤ)) y := by
  refine fiberPrecompIso_hom_app_eq_geometricFrobenius_zpow p _ _ _ (fun z ↦ ?_) _ A y
  rw [← p.pointNorm_eq_pow_degreeOver (X₀.mem_finitePoints.2 inferInstance), pointNorm]
  rw [← arithmeticFrobeniusAt_apply x]
  exact (arithmeticFrobeniusAt x).apply_symm_apply z

/-- A path `τ` between fibre functors commutes with the integral powers of the geometric
Frobenius on the geometric fibres of the constant covers. -/
lemma app_geometricFrobenius_zpow {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    {t : Spec (.of Ω') ⟶ X₀} (τ : fiber t ≅ fiber s) (A : FiniteEtaleAlgebra K) (n : ℤ)
    (y : (fiber t).obj (constantCover p A)) :
    τ.hom.app _ ((geometricFrobenius p t A ^ n) y) =
      (geometricFrobenius p s A ^ n) (τ.hom.app _ y) := by
  refine Equiv.Perm.zpow_apply_eq_of_comm _ _ _ (fun y ↦ ?_) n y
  have hinj : Function.Injective ((fiber s).map (arithmeticFrobenius p A).hom) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  apply hinj
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius, ← ConcreteCategory.comp_apply,
    ← τ.hom.naturality, ConcreteCategory.comp_apply,
    fiber_map_arithmeticFrobenius_geometricFrobenius]

variable (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)]

/-- A Frobenius element at a point `x` lies in the Weil group, with degree `e_x = [κ(x) : k₀]`:
it acts on the geometric fibres of the constant covers as the `e_x`-th power of the geometric
Frobenius. -/
theorem IsFrobeniusElement.mem_weilGroup [GeometricallyConnected p] {x : X₀}
    [Finite (X₀.residueField x)] {g : G}
    (hg : IsFrobeniusElement s G x g) :
    (g, Multiplicative.ofAdd (p.degreeOver x : ℤ)) ∈ weilGroup p s G := by
  obtain ⟨τ, hτ⟩ := hg
  refine (mem_weilGroup_iff p s G).2 fun A z ↦ ?_
  obtain ⟨y, rfl⟩ : ∃ y, τ.hom.app _ y = z :=
    ⟨τ.inv.app _ z, ConcreteCategory.congr_hom (τ.inv_hom_id_app _) z⟩
  rw [hτ, geometricFrobeniusAt_hom_app_eq, app_geometricFrobenius_zpow]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace X₀]
  [IsFundamentalGroup (fiber s) G]

/-- **Existence of Frobenius elements.** Every point `x` with finite residue field has a
Frobenius element in `π₁(X₀, s)`: transport the geometric Frobenius `F_x` along a path from
`x̄` to `s`, which exists since any two fibre functors are isomorphic. -/
theorem exists_isFrobeniusElement (x : X₀) [Finite (X₀.residueField x)] :
    ∃ g : G, IsFrobeniusElement s G x g := by
  obtain ⟨τ⟩ := nonempty_iso_of_fiberFunctor (fiber (residueFieldPoint X₀ x)) (fiber s)
  obtain ⟨g, hg⟩ := (toAut_bijective (fiber s) G).2 (.of (τ.symm ≪≫ geometricFrobeniusAt x ≪≫ τ))
  refine ⟨g, τ, fun P y ↦ ?_⟩
  rw [← toAut_hom_app_apply, hg]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply (τ.hom.app P) (τ.inv.app P), τ.hom_inv_id_app]
  rfl

end AlgebraicGeometry.Scheme.FiniteEtale
