/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Weil groups after a finite constant field extension

Let `p : X₀ ⟶ Spec K` be a scheme over a finite field `K` with `q` elements, let `L / K` be a
finite field extension of degree `m`, and let `X₀' = X₀ ×_K Spec L`, the constant cover of `X₀`
attached to `L`, regarded as an `L`-scheme through the second projection `p'`. Base change along
the projection `π : X₀' ⟶ X₀` and a path `τ` induce an injective map
`ρ : π₁(X₀', s') → π₁(X₀, s)` (`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap`).

This file shows that `ρ` identifies the Weil group of `X₀'` over `L` with the elements of degree
divisible by `m` of the Weil group of `X₀` over `K`, the degree being divided by `m`
(blueprint `lemma-geometric-constituents-after-constant-extension`):

* `(g, n) ∈ W(X₀', s')` if and only if `(ρ g, m n) ∈ W(X₀, s)`
  (`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_constantExtension_iff`);
* if `(ρ g, n) ∈ W(X₀, s)` then `m ∣ n`
  (`AlgebraicGeometry.Scheme.FiniteEtale.dvd_of_mem_weilGroup_constantExtension`);
* if `(h, n) ∈ W(X₀, s)` and `m ∣ n`, then `h` is in the image of `ρ`
  (`AlgebraicGeometry.Scheme.FiniteEtale.mem_range_of_mem_weilGroup_constantExtension`).

The comparison of the Frobenius actions rests on the constant covers: for a finite étale
`K`-algebra `A`, the base change to `X₀'` of `X₀ ×_K Spec A` is `X₀' ×_L Spec (L ⊗_K A)`, on
whose geometric fibre the `q ^ m`-power Frobenius of `L ⊗_K A` acts as the `m`-th power of the
`q`-power Frobenius of `A`. Conversely the constant cover `X₀' ×_L Spec B` of a finite étale
`L`-algebra `B` embeds into the base change of `X₀ ×_K Spec B`. Both are instances of the map of
geometric fibres induced by a ring homomorphism `φ : A → B` over `K → L`
(`AlgebraicGeometry.Scheme.FiniteEtale.constantExtensionFiberMap`), which on the descriptions of
the fibres as sets of ring homomorphisms is precomposition with `φ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

namespace FiniteEtaleAlgebra

variable {k₀ : Type u} [Field k₀]

/-- A finite étale `k₀`-algebra `A`, as an object of `FiniteEtaleAlgebra k₀`. -/
noncomputable abbrev of (A : Type u) [CommRing A] [Algebra k₀ A] [Module.Finite k₀ A]
    [Algebra.Etale k₀ A] : FiniteEtaleAlgebra k₀ :=
  ⟨CommAlgCat.of k₀ A, inferInstanceAs (Module.Finite k₀ A), inferInstanceAs (Algebra.Etale k₀ A)⟩

variable {L : Type u} [Field L]

/-- A finite étale `L`-algebra, for a finite étale field extension `L / k₀`, regarded as a finite
étale `k₀`-algebra. -/
noncomputable def restrictScalars (k₀ : Type u) [Field k₀] [Algebra k₀ L] [Module.Finite k₀ L]
    [Algebra.Etale k₀ L] (B : FiniteEtaleAlgebra L) : FiniteEtaleAlgebra k₀ :=
  letI : Algebra k₀ B.1 := ((algebraMap L B.1).comp (algebraMap k₀ L)).toAlgebra
  haveI : IsScalarTower k₀ L B.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  ⟨CommAlgCat.of k₀ B.1, Module.Finite.trans L B.1, Algebra.Etale.comp k₀ L B.1⟩

lemma restrictScalars_algebraMap [Algebra k₀ L] [Module.Finite k₀ L] [Algebra.Etale k₀ L]
    (B : FiniteEtaleAlgebra L) :
    algebraMap k₀ (restrictScalars k₀ B).1 = (algebraMap L B.1).comp (algebraMap k₀ L) :=
  rfl

/-- The base change `L ⊗_{k₀} A` of a finite étale `k₀`-algebra `A`, a finite étale
`L`-algebra. -/
noncomputable def baseChange [Algebra k₀ L] (A : FiniteEtaleAlgebra k₀) : FiniteEtaleAlgebra L :=
  of (TensorProduct k₀ L A.1)

/-- The ring homomorphism `a ↦ 1 ⊗ a : A → L ⊗_{k₀} A`. -/
noncomputable def includeRight [Algebra k₀ L] (A : FiniteEtaleAlgebra k₀) :
    A.1 →+* (baseChange (L := L) A).1 :=
  Algebra.TensorProduct.includeRight.toRingHom

end FiniteEtaleAlgebra

section Frobenius

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of k₀))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀) (A : FiniteEtaleAlgebra k₀)

/-- The arithmetic Frobenius acts on the embeddings `A → Ω` by precomposition with the
`q`-power map. -/
lemma fiberConstantCoverEquiv_geometricFrobenius_inv (z : (fiber s).obj (constantCover p A))
    (x : A.1) :
    (fiberConstantCoverEquiv p s A ((geometricFrobenius p s A)⁻¹ z)).1 x =
      (fiberConstantCoverEquiv p s A z).1 (x ^ Nat.card k₀) := by
  rw [geometricFrobenius_inv_apply]
  change (fiberConstantCoverEquiv p s A
    ((fiber s).map (constantCoverHom p A.frobenius.toAlgHom) z)).1 x = _
  rw [fiberConstantCoverEquiv_fiber_map]
  simp [FiniteEtaleAlgebra.frobenius_apply]

/-- On the geometric fibre of the constant cover attached to a finite field extension `L` of
degree `m`, the `m`-th power of the geometric Frobenius is the identity. -/
lemma geometricFrobenius_pow_finrank_apply (L : Type u) [Field L] [Algebra k₀ L]
    [Module.Finite k₀ L] [Algebra.Etale k₀ L]
    (z : (fiber s).obj (constantCover p (FiniteEtaleAlgebra.of L))) :
    (geometricFrobenius p s (FiniteEtaleAlgebra.of L) ^ Module.finrank k₀ L) z = z := by
  have : Finite L := Module.finite_of_finite k₀
  have h : ((geometricFrobenius p s (FiniteEtaleAlgebra.of L))⁻¹ ^ Module.finrank k₀ L) z = z := by
    apply (fiberConstantCoverEquiv p s _).injective
    refine Subtype.ext (RingHom.ext fun x ↦ ?_)
    have := Fintype.ofFinite L
    rw [fiberConstantCoverEquiv_geometricFrobenius_inv_pow, ← map_pow,
      ← Module.natCard_eq_pow_finrank (K := k₀) (V := L),
      Nat.card_eq_fintype_card, FiniteField.pow_card x]
  rw [inv_pow] at h
  exact (Equiv.Perm.inv_eq_iff_eq.1 h).symm

/-- If an integral power `Φ ^ n` of the geometric Frobenius fixes a point of the geometric fibre
of the constant cover attached to a finite field extension `L` of degree `m`, then `m ∣ n`. -/
lemma dvd_of_geometricFrobenius_zpow_apply (L : Type u) [Field L] [Algebra k₀ L]
    [Module.Finite k₀ L] [Algebra.Etale k₀ L]
    (z : (fiber s).obj (constantCover p (FiniteEtaleAlgebra.of L))) (n : ℤ)
    (h : (geometricFrobenius p s (FiniteEtaleAlgebra.of L) ^ n) z = z) :
    (Module.finrank k₀ L : ℤ) ∣ n := by
  have : Finite L := Module.finite_of_finite k₀
  have := Fintype.ofFinite k₀
  set Φ := geometricFrobenius p s (FiniteEtaleAlgebra.of L)
  have h' : (Φ⁻¹ ^ n.natAbs) z = z := by
    rcases Int.natAbs_eq n with hn | hn
    · rw [hn, zpow_natCast] at h
      rw [inv_pow]
      exact Equiv.Perm.inv_eq_iff_eq.2 h.symm
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow] at h
      exact h
  rw [Int.natCast_dvd, ← FiniteField.orderOf_frobeniusAlgHom k₀ L,
    orderOf_dvd_iff_pow_eq_one]
  refine AlgHom.ext fun x ↦ ?_
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
    ← Nat.card_eq_fintype_card]
  have hx : (fiberConstantCoverEquiv p s _ ((Φ⁻¹ ^ n.natAbs) z)).1 x =
      (fiberConstantCoverEquiv p s _ z).1 x := by rw [h']
  rw [fiberConstantCoverEquiv_geometricFrobenius_inv_pow] at hx
  apply (fiberConstantCoverEquiv p s _ z).1.injective
  rw [map_pow]
  exact hx

end Frobenius

variable {K : Type u} [Field K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.Etale K L]

/-- The constant field extension `X₀ ×_K Spec L` of a `K`-scheme `X₀` along a finite field
extension `L / K`: the underlying scheme of the constant cover attached to `L`. -/
noncomputable abbrev constantExtension : Scheme.{u} :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.left

/-- The structure morphism `X₀ ×_K Spec L ⟶ Spec L` of the constant field extension. -/
noncomputable abbrev constantExtensionHom : constantExtension p L ⟶ Spec (.of L) :=
  pullback.snd p (FiniteEtaleAlgebra.of (k₀ := K) L).specHom

/-- The projection `π : X₀ ×_K Spec L ⟶ X₀` of the constant field extension. -/
noncomputable abbrev constantExtensionProj : constantExtension p L ⟶ X₀ :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.hom

lemma constantExtensionProj_comp :
    constantExtensionProj p L ≫ p =
      constantExtensionHom p L ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
  pullback.condition

instance : IsFinite (constantExtensionProj p L) :=
  (constantCover p (FiniteEtaleAlgebra.of L)).property

instance : Etale (constantExtensionProj p L) :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.prop

variable {L} {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s' : Spec (.of Ω') ⟶ constantExtension p L)

omit [IsSepClosed Ω'] in
lemma baseRingHom_constantExtensionProj :
    baseRingHom p (s' ≫ constantExtensionProj p L) =
      (baseRingHom (constantExtensionHom p L) s').comp (algebraMap K L) := by
  change (Spec.preimage _).hom = ((CommRingCat.ofHom (algebraMap K L)) ≫
    Spec.preimage (s' ≫ constantExtensionHom p L)).hom
  congr 1
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Category.assoc, Category.assoc,
    constantExtensionProj_comp]

section FiberMap

variable {A : FiniteEtaleAlgebra K} {B : FiniteEtaleAlgebra L} (φ : A.1 →+* B.1)
  (hφ : φ.comp (algebraMap K A.1) = (algebraMap L B.1).comp (algebraMap K L))

include hφ

/-- The morphism `X₀' ×_L Spec B ⟶ X₀ ×_K Spec A` induced by a ring homomorphism `φ : A → B`
over `K → L`. -/
noncomputable def constantExtensionLeftMap :
    (constantCover (constantExtensionHom p L) B).obj.left ⟶ (constantCover p A).obj.left :=
  pullback.lift (pullback.fst _ _ ≫ constantExtensionProj p L)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ)) (by
      rw [Category.assoc, constantExtensionProj_comp, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
      exact hφ.symm)

@[reassoc (attr := simp)]
lemma constantExtensionLeftMap_fst :
    constantExtensionLeftMap p φ hφ ≫ pullback.fst p A.specHom =
      pullback.fst _ _ ≫ constantExtensionProj p L :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma constantExtensionLeftMap_snd :
    constantExtensionLeftMap p φ hφ ≫ pullback.snd p A.specHom =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

/-- The map `y ↦ y ≫ (π ×_φ 1)` from the geometric fibre of `X₀' ×_L Spec B` at `s'` to that of
`X₀ ×_K Spec A` at `s' ≫ π`. -/
noncomputable def constantExtensionFiberMap
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    (fiber (s' ≫ constantExtensionProj p L)).obj (constantCover p A) :=
  fiberMk _ (constantCover p A) (y.left ≫ constantExtensionLeftMap p φ hφ) (by
    change (y.left ≫ constantExtensionLeftMap p φ hφ) ≫ pullback.fst p A.specHom = _
    rw [Category.assoc, constantExtensionLeftMap_fst, ← Category.assoc]
    exact congrArg (· ≫ constantExtensionProj p L) (fiber_left_comp s' y))

/-- On the descriptions of the geometric fibres as sets of ring homomorphisms, the map
`AlgebraicGeometry.Scheme.FiniteEtale.constantExtensionFiberMap` is precomposition with `φ`. -/
lemma fiberConstantCoverEquiv_constantExtensionFiberMap
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    (fiberConstantCoverEquiv p _ A (constantExtensionFiberMap p s' φ hφ y)).1 =
      (fiberConstantCoverEquiv (constantExtensionHom p L) s' B y).1.comp φ := by
  rw [fiberConstantCoverEquiv_apply, fiberConstantCoverEquiv_apply]
  change (Spec.preimage ((y.left ≫ constantExtensionLeftMap p φ hφ) ≫
    pullback.snd p A.specHom)).hom = (CommRingCat.ofHom φ ≫
      Spec.preimage (y.left ≫ pullback.snd (constantExtensionHom p L) B.specHom)).hom
  congr 1
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Category.assoc,
    constantExtensionLeftMap_snd, Category.assoc]

/-- The morphism `X₀' ×_L Spec B ⟶ π^* (X₀ ×_K Spec A)` of finite étale `X₀'`-schemes. -/
noncomputable def constantExtensionToPullback :
    constantCover (constantExtensionHom p L) B ⟶
      (pullback (constantExtensionProj p L)).obj (constantCover p A) :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.lift (constantExtensionLeftMap p φ hφ) (pullback.fst _ _)
      (constantExtensionLeftMap_fst p φ hφ))
    (pullback.lift_snd _ _ _))

lemma pullbackFiberIso_constantExtensionToPullback
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    (pullbackFiberIso _ s').hom.app _ ((fiber s').map (constantExtensionToPullback p φ hφ) y) =
      constantExtensionFiberMap p s' φ hφ y := by
  apply fiber_ext
  change (y.left ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ = _
  simp [constantExtensionFiberMap]

variable [Finite K] [Finite L]

/-- The `q ^ m`-power Frobenius of `B` restricts along `φ` to the `m`-th power of the `q`-power
Frobenius of `A`: on geometric fibres the arithmetic Frobenius of `X₀' ×_L Spec B` corresponds to
the `m`-th power of that of `X₀ ×_K Spec A`. -/
lemma constantExtensionFiberMap_geometricFrobenius_inv
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    constantExtensionFiberMap p s' φ hφ
        ((geometricFrobenius (constantExtensionHom p L) s' B)⁻¹ y) =
      ((geometricFrobenius p _ A)⁻¹ ^ Module.finrank K L)
        (constantExtensionFiberMap p s' φ hφ y) := by
  apply (fiberConstantCoverEquiv p _ A).injective
  refine Subtype.ext (RingHom.ext fun x ↦ ?_)
  rw [fiberConstantCoverEquiv_geometricFrobenius_inv_pow,
    fiberConstantCoverEquiv_constantExtensionFiberMap,
    fiberConstantCoverEquiv_constantExtensionFiberMap, RingHom.comp_apply, RingHom.comp_apply,
    fiberConstantCoverEquiv_geometricFrobenius_inv, Module.natCard_eq_pow_finrank (K := K) (V := L),
    map_pow]

/-- The integral powers of the geometric Frobenius: `Φ_B ^ n` corresponds to `Φ_A ^ (m n)`. -/
lemma constantExtensionFiberMap_geometricFrobenius_zpow (n : ℤ)
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    constantExtensionFiberMap p s' φ hφ
        ((geometricFrobenius (constantExtensionHom p L) s' B ^ n) y) =
      (geometricFrobenius p _ A ^ ((Module.finrank K L : ℤ) * n))
        (constantExtensionFiberMap p s' φ hφ y) := by
  have := Equiv.Perm.zpow_apply_eq_of_comm _ _ _
    (constantExtensionFiberMap_geometricFrobenius_inv p s' φ hφ) (-n) y
  simpa only [inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul, mul_neg, neg_mul] using this

end FiberMap

section WeilGroup

variable [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X₀}
  (τ : pullback (constantExtensionProj p L) ⋙ fiber s' ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

omit [Module.Finite K L] [Algebra.Etale K L] [Finite K] [Finite L] [GeometricallyConnected p]
  [ConnectedSpace X₀] in
/-- `φ = 1 ⊗ id : A → L ⊗_K A` lies over `K → L`. -/
lemma includeRight_comp_algebraMap (A : FiniteEtaleAlgebra K) :
    (FiniteEtaleAlgebra.includeRight (L := L) A).comp (algebraMap K A.1) =
      (algebraMap L (FiniteEtaleAlgebra.baseChange (L := L) A).1).comp (algebraMap K L) := by
  ext x
  change (1 : L) ⊗ₜ[K] algebraMap K A.1 x = algebraMap K L x ⊗ₜ[K] (1 : A.1)
  rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]

omit [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀] in
/-- The geometric fibre of `X₀' ×_L Spec (L ⊗_K A)` at `s'` maps onto that of `X₀ ×_K Spec A` at
`s' ≫ π`: an embedding `χ : A → Ω'` over `K` extends to `L ⊗_K A` by the embedding of `L`
through which `s'` lies over `Spec L`. -/
lemma constantExtensionFiberMap_surjective (A : FiniteEtaleAlgebra K) :
    Function.Surjective (constantExtensionFiberMap p s' (FiniteEtaleAlgebra.includeRight A)
      (includeRight_comp_algebraMap (L := L) A)) := by
  intro z
  let χ := fiberConstantCoverEquiv p _ A z
  let κ := baseRingHom (constantExtensionHom p L) s'
  let : Algebra K Ω' := (κ.comp (algebraMap K L)).toAlgebra
  let f : L →ₐ[K] Ω' := { κ with commutes' := fun _ ↦ rfl }
  have hg (k : K) : χ.1 (algebraMap K A.1 k) = algebraMap K Ω' k := by
    exact (RingHom.congr_fun χ.2 k).trans
      (RingHom.congr_fun (baseRingHom_constantExtensionProj p s') k)
  let g : A.1 →ₐ[K] Ω' := { χ.1 with commutes' := hg }
  let ψ : (FiniteEtaleAlgebra.baseChange (L := L) A).1 →+* Ω' :=
    (Algebra.TensorProduct.productMap f g).toRingHom
  have hψ : ψ.comp (algebraMap L (FiniteEtaleAlgebra.baseChange (L := L) A).1) = κ := by
    ext l
    change f l * g 1 = κ l
    simp [f]
  refine ⟨(fiberConstantCoverEquiv (constantExtensionHom p L) s' _).symm ⟨ψ, hψ⟩, ?_⟩
  apply (fiberConstantCoverEquiv p _ A).injective
  refine Subtype.ext ?_
  rw [fiberConstantCoverEquiv_constantExtensionFiberMap, Equiv.apply_symm_apply]
  ext a
  change f 1 * g a = χ.1 a
  simp [g]

omit [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀] in
/-- For `φ = id : B → B`, from a finite étale `L`-algebra regarded as a `K`-algebra, the map of
geometric fibres is injective. -/
lemma constantExtensionFiberMap_injective (B : FiniteEtaleAlgebra L) :
    Function.Injective (constantExtensionFiberMap p s'
      (A := FiniteEtaleAlgebra.restrictScalars K B) (B := B) (RingHom.id B.1) rfl) := by
  intro y₁ y₂ e
  apply (fiberConstantCoverEquiv (constantExtensionHom p L) s' B).injective
  refine Subtype.ext ?_
  have := congrArg (fun w ↦ (fiberConstantCoverEquiv p _ _ w).1) e
  simp only [fiberConstantCoverEquiv_constantExtensionFiberMap] at this
  ext b
  exact RingHom.congr_fun this b

variable (G' : Type u) [Group G'] [∀ P, MulAction G' ((fiber s').obj P)]
  [IsNaturalSMul (fiber s') G']

omit [Finite K] [Finite L] [GeometricallyConnected p] in
lemma fundamentalGroupMap_smul_constantExtensionFiberMap {A : FiniteEtaleAlgebra K}
    {B : FiniteEtaleAlgebra L} (φ : A.1 →+* B.1)
    (hφ : φ.comp (algebraMap K A.1) = (algebraMap L B.1).comp (algebraMap K L)) (g : G')
    (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
    fundamentalGroupMap τ G' G g •
        ((pullbackFiberIso _ s').symm ≪≫ τ).hom.app _ (constantExtensionFiberMap p s' φ hφ y) =
      ((pullbackFiberIso _ s').symm ≪≫ τ).hom.app _
        (constantExtensionFiberMap p s' φ hφ (g • y)) := by
  have key (y : (fiber s').obj (constantCover (constantExtensionHom p L) B)) :
      ((pullbackFiberIso _ s').symm ≪≫ τ).hom.app _ (constantExtensionFiberMap p s' φ hφ y) =
        τ.hom.app _ ((fiber s').map (constantExtensionToPullback p φ hφ) y) := by
    rw [← pullbackFiberIso_constantExtensionToPullback]
    change τ.hom.app _ ((pullbackFiberIso _ s').inv.app _ ((pullbackFiberIso _ s').hom.app _ _)) = _
    congr 1
    exact ConcreteCategory.congr_hom ((pullbackFiberIso _ s').hom_inv_id_app _) _
  rw [key, key, fundamentalGroupMap_smul, IsNaturalSMul.naturality]

/-- Blueprint `lemma-geometric-constituents-after-constant-extension`: Weil group after a finite
constant-field extension.

The map `ρ : π₁(X₀', s') → π₁(X₀, s)` induced by the projection `π : X₀ ×_K Spec L ⟶ X₀` carries
the Weil group of `X₀'` over `L` into that of `X₀` over `K`, multiplying the degree by
`m = [L : K]`: an element acting on the constant covers of `X₀'` as the `n`-th power of the
geometric Frobenius over `L` acts on those of `X₀` as the `m n`-th power of the geometric
Frobenius over `K`, and conversely. -/
theorem mem_weilGroup_constantExtension_iff (g : G') (n : Multiplicative ℤ) :
    (g, n) ∈ weilGroup (constantExtensionHom p L) s' G' ↔
      (fundamentalGroupMap τ G' G g, n ^ Module.finrank K L) ∈ weilGroup p s G := by
  rw [mem_weilGroup_iff, mem_weilGroup_iff]
  have hn : (n ^ Module.finrank K L).toAdd = (Module.finrank K L : ℤ) * n.toAdd := by
    rw [toAdd_pow, nsmul_eq_mul]
  constructor
  · intro h A z
    obtain ⟨w, rfl⟩ : ∃ w, ((pullbackFiberIso _ s').symm ≪≫ τ).hom.app _ w = z :=
      ⟨((pullbackFiberIso _ s').symm ≪≫ τ).inv.app _ z,
        ConcreteCategory.congr_hom (((pullbackFiberIso _ s').symm ≪≫ τ).inv_hom_id_app _) z⟩
    obtain ⟨y, rfl⟩ := constantExtensionFiberMap_surjective p s' A w
    rw [fundamentalGroupMap_smul_constantExtensionFiberMap p s' τ G G', h,
      constantExtensionFiberMap_geometricFrobenius_zpow, app_geometricFrobenius_zpow, hn]
  · intro h B y
    apply constantExtensionFiberMap_injective p s' B
    apply ((ConcreteCategory.isIso_iff_bijective
      (((pullbackFiberIso _ s').symm ≪≫ τ).hom.app _)).1 inferInstance).1
    rw [← fundamentalGroupMap_smul_constantExtensionFiberMap p s' τ G G', h,
      constantExtensionFiberMap_geometricFrobenius_zpow, app_geometricFrobenius_zpow, hn]

/-- The diagonal point of the geometric fibre at `s'` of `π^* (X₀ ×_K Spec L)`, the point on the
diagonal section `X₀' ⟶ X₀' ×_{X₀} X₀'`. -/
noncomputable def diagonalPoint :
    (fiber s').obj ((pullback (constantExtensionProj p L)).obj
      (constantCover p (FiniteEtaleAlgebra.of L))) :=
  fiberMk s' _ (s' ≫ pullback.lift (𝟙 _) (𝟙 _) rfl) (by
    change (s' ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ = s'
    simp)

omit [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀] in
lemma smul_diagonalPoint (g : G') : g • diagonalPoint p s' = diagonalPoint p s' :=
  smul_eq_self_of_section s' G' _ (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _) _ rfl g

omit [Finite L] in
/-- Blueprint `lemma-geometric-constituents-after-constant-extension`: Weil group after a finite
constant-field extension.

The image under `ρ` of an element of `π₁(X₀', s')` has degree divisible by `m = [L : K]`: it
fixes the image of the diagonal point of `π^* (X₀ ×_K Spec L)`, on which the geometric Frobenius
over `K` has order `m`. -/
theorem dvd_of_mem_weilGroup_constantExtension (g : G') (n : Multiplicative ℤ)
    (h : (fundamentalGroupMap τ G' G g, n) ∈ weilGroup p s G) :
    (Module.finrank K L : ℤ) ∣ n.toAdd := by
  have hv := fundamentalGroupMap_smul τ G' G g _ (diagonalPoint p s')
  rw [smul_diagonalPoint, (mem_weilGroup_iff p s G).1 h] at hv
  exact dvd_of_geometricFrobenius_zpow_apply p s L _ _ hv

end WeilGroup

section Range

variable [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀]
  [ConnectedSpace (constantExtension p L)]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X₀}
  (τ : pullback (constantExtensionProj p L) ⋙ fiber s' ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [∀ P, MulAction G' ((fiber s').obj P)] [IsFundamentalGroup (fiber s') G']

omit [Finite L] in
/-- Blueprint `lemma-geometric-constituents-after-constant-extension`: Weil group after a finite
constant-field extension.

An element of the Weil group of `X₀` whose degree is divisible by `m = [L : K]` lies in the image
of `ρ : π₁(X₀', s') → π₁(X₀, s)`. The image of `ρ` is closed, and a point `u` of a geometric fibre
fixed by it comes, through a section of the base change to `X₀'`, from a point of the geometric
fibre of `X₀ ×_K Spec L ≅ X₀'`, on which the `m`-th power of the geometric Frobenius is trivial. -/
theorem mem_range_of_mem_weilGroup_constantExtension (h : G) (n : Multiplicative ℤ)
    (hmem : (h, n) ∈ weilGroup p s G) (hdvd : (Module.finrank K L : ℤ) ∣ n.toAdd) :
    h ∈ (fundamentalGroupMap τ G' G).range := by
  have : T2Space G := (toAutHomeo (fiber s) G).isEmbedding.t2Space
  have : ∀ P, ContinuousSMul G' ((fiber s').obj P) := fun P ↦ IsFundamentalGroup.continuous_smul P
  have hcl : IsClosed ((fundamentalGroupMap τ G' G).range : Set G) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_fundamentalGroupMap τ G' G)).isClosed
  refine mem_of_forall_smul_eq_self s G _ hcl h fun U u hu ↦ ?_
  -- the point of the fibre over `X₀'` corresponding to `u` is fixed by `π₁(X₀')`
  let z : (fiber s').obj ((pullback (constantExtensionProj p L)).obj U) := τ.inv.app U u
  have hτz : τ.hom.app U z = u := ConcreteCategory.congr_hom (τ.inv_hom_id_app U) u
  have hz (k : G') : k • z = z := by
    apply ((ConcreteCategory.isIso_iff_bijective (τ.hom.app U)).1 inferInstance).1
    rw [← fundamentalGroupMap_smul τ G' G, hτz]
    exact hu _ ⟨k, rfl⟩
  -- a fixed point lies on a section
  let E := equivalenceContAction s' G'
  let T₀ : (constantExtension p L).FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (𝟙 _) inferInstance, inferInstanceAs (IsFinite (𝟙 _))⟩
  let x₀ : (fiber s').obj T₀ := Over.homMk s' (Category.comp_id s')
  let m : E.functor.obj T₀ ⟶ E.functor.obj ((pullback (constantExtensionProj p L)).obj U) :=
    ObjectProperty.homMk
      { hom := FintypeCat.homMk fun _ ↦ z
        comm k := FintypeCat.hom_ext _ _ fun _ ↦ (hz k).symm }
  let S := E.fullyFaithfulFunctor.preimage m
  have hS : (fiber s').map S x₀ = z :=
    congrArg (fun f ↦ f.hom.hom x₀) (E.fullyFaithfulFunctor.map_preimage m)
  have hσb : S.hom.left ≫ pullback.snd U.obj.hom (constantExtensionProj p L) = 𝟙 _ :=
    hom_left_comp S
  let σ := S.hom.left ≫ pullback.fst U.obj.hom (constantExtensionProj p L)
  have hσ : σ ≫ U.obj.hom = constantExtensionProj p L := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσb, Category.id_comp]
  -- the section is a morphism `X₀ ×_K Spec L ⟶ U` of finite étale `X₀`-schemes
  let ψ : constantCover p (FiniteEtaleAlgebra.of L) ⟶ U :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk σ hσ)
  have hx :
      (fiber s').map ((pullback (constantExtensionProj p L)).map ψ) (diagonalPoint p s') = z := by
    apply fiber_ext
    rw [fiber_map_left, ← hS, fiber_map_left]
    change (s' ≫ pullback.lift _ _ _) ≫ _ = x₀.left ≫ S.hom.left
    rw [Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [pullback_map_hom_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.id_comp]
      rfl
    · simp only [pullback_map_hom_left, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact hσb.symm
  have hu' : (fiber s).map ψ (τ.hom.app _ (diagonalPoint p s')) = u := by
    rw [← hτz, ← hx]
    exact (ConcreteCategory.congr_hom (τ.hom.naturality ψ) _).symm
  rw [← hu', ← IsNaturalSMul.naturality, (mem_weilGroup_iff p s G).1 hmem]
  congr 1
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, zpow_mul, zpow_natCast]
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
    (geometricFrobenius_pow_finrank_apply p s L _) k

end Range

section Exact

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

omit [Finite K] in
/-- Every finite subset of `K̄` lies in a finite subextension of `K̄ / K`. -/
lemma FiniteSubfield.exists_forall_mem (T : Finset (AlgebraicClosure K)) :
    ∃ L : FiniteSubfield K, ∀ x ∈ T, x ∈ L.1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, by simp⟩
  | insert a T _ ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨L', h₁, h₂⟩ := FiniteSubfield.exists_ge L (FiniteSubfield.adjoin a)
    refine ⟨L', fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h₂ (FiniteSubfield.mem_adjoin x)
    · exact h₁ (hL x hx)

/-- There are finite subextensions of `K̄ / K` of arbitrarily large degree. -/
lemma FiniteSubfield.exists_lt_finrank (N : ℕ) :
    ∃ L : FiniteSubfield K, N < Module.finrank K L.1 := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (AlgebraicClosure K) (Nat.card K ^ N + 1)
  obtain ⟨L, hL⟩ := FiniteSubfield.exists_forall_mem S
  refine ⟨L, ?_⟩
  have := L.2
  have : Finite L.1 := Module.finite_of_finite K
  have hcard : S.card ≤ Nat.card L.1 := by
    change S.card ≤ Nat.card (L.1 : Set (AlgebraicClosure K))
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard (fun x hx ↦ hL x hx) (Set.toFinite _)
  rw [hS, Module.natCard_eq_pow_finrank (K := K) (V := L.1)] at hcard
  exact (Nat.pow_lt_pow_iff_right Finite.one_lt_card).1 (Nat.lt_of_succ_le hcard)

/-- The geometric Frobenius has infinite order: on the geometric fibre of the constant cover
attached to a finite field extension of degree `m`, it has order `m`, and there are such
extensions of every degree. -/
theorem not_isOfFinOrder_geometricFrobenius : ¬IsOfFinOrder (geometricFrobenius p s) := by
  intro hfin
  obtain ⟨d, hd, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨L, hL⟩ := FiniteSubfield.exists_lt_finrank (K := K) d
  have := L.2
  have : Algebra.Etale K L.1 := L.toFiniteEtaleAlgebra.2.2
  let : Algebra K Ω := (baseRingHom p s).toAlgebra
  let φ : L.1 →ₐ[K] Ω := IsSepClosed.lift
  let z := (fiberConstantCoverEquiv p s (FiniteEtaleAlgebra.of L.1)).symm
    ⟨φ.toRingHom, φ.comp_algebraMap⟩
  have hz : (geometricFrobenius p s (FiniteEtaleAlgebra.of L.1) ^ (d : ℤ)) z = z := by
    rw [zpow_natCast, ← Pi.pow_apply, hpow]
    rfl
  have hdvd := dvd_of_geometricFrobenius_zpow_apply p s L.1 z d hz
  have := Int.le_of_dvd (by exact_mod_cast hd) hdvd
  omega

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [ConnectedSpace X₀] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- Blueprint `situation-weil`: Pointer to the properties of `situation-weil`.

The exact sequence of `situation-weil` for the Weil group of a connected,
geometrically connected scheme over a finite field: the degree map is surjective, the elements of
degree zero are those of `π₁(X₀, s)` acting trivially on the constant covers, and every lift of
the geometric Frobenius has degree one. -/
theorem exact_weilGroupDeg [GeometricallyConnected p] :
    Function.Surjective (weilGroupDeg p s G) ∧
      Function.Injective ((constantCoverAction p s G).kerToWeilGroup (geometricFrobenius p s)) ∧
      ((constantCoverAction p s G).kerToWeilGroup (geometricFrobenius p s)).range =
        (weilGroupDeg p s G).ker ∧
      ∀ w : weilGroup p s G, constantCoverAction p s G (w : G × Multiplicative ℤ).1 =
        geometricFrobenius p s → weilGroupDeg p s G w = Multiplicative.ofAdd 1 := by
  obtain ⟨g, hg⟩ := exists_smul_eq_geometricFrobenius p s G
  refine (constantCoverAction p s G).exact_weilGroupDeg (geometricFrobenius p s)
    ⟨g, funext fun A ↦ Equiv.ext fun y ↦ hg A y⟩ (not_isOfFinOrder_geometricFrobenius p s)

end Exact

end AlgebraicGeometry.Scheme.FiniteEtale
