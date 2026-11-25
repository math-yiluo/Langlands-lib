/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.Regular

/-!
# Functoriality of the arithmetic monodromy extension

Let `(W, deg, γ)` be a degree datum represented by `ρ : W → GL n k`, with geometric monodromy
group `H` and arithmetic monodromy extension `G_arith(ρ)(k) = H(k) ⋊ ℤ`. Let `S ≤ GL n k` be a
subgroup containing `ρ(W)` and `H(k)`, for instance the stabilizer of a flag of subspaces stable
under `ρ(W)`, and let `R : S →* GL m k` be a regular homomorphism (its entries are polynomials in
the entries of the matrix and the inverse of its determinant), for instance the action on a
subquotient, a tensor product, an exterior power or the determinant. Then `ρ_Q = R ∘ ρ` is again a
represented degree datum, and `(h, m) ↦ (R(h), m)` is a homomorphism
`Φ_Q : G_arith(ρ) → G_arith(ρ_Q)` which preserves the degree, is regular on every degree component,
has Zariski-dense image in every degree component and maps central elements to central elements.

For the determinant `ρ ↦ det ρ` this is the determinant morphism of arithmetic monodromy.

## Main definitions

- `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.mapOn`: the represented degree datum `R ∘ ρ`.
- `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.extensionMap`: the homomorphism
  `(h, m) ↦ (R(h), m)` of arithmetic monodromy extensions.
- `AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.det`: the determinant line `det ρ`.

## Main results

- `RepresentedDegreeDatum.rightHom_extensionMap`: `Φ_Q` preserves the degree.
- `RepresentedDegreeDatum.arithmeticMonodromyExtensionHom_extensionMap`: on matrices `Φ_Q` is `R`.
- `RepresentedDegreeDatum.vanishingIdeal_image_degreeComponent`: the image of every degree
  component is Zariski dense in the corresponding degree component.
- `RepresentedDegreeDatum.extensionMap_mem_center`: `Φ_Q` maps central elements to central
  elements.
-/

@[expose] public section

open Matrix.GeneralLinearGroup
open scoped Pointwise

namespace AlgebraicGeometry.Monodromy.RepresentedDegreeDatum

variable {W : Type*} [Group W] {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
  (D : RepresentedDegreeDatum W n k) {m : Type*} [Fintype m] [DecidableEq m]
  (S : Subgroup (GL n k)) (hS : ∀ w, D.rep w ∈ S) (R : S →* GL m k)

/-- The represented degree datum `ρ_Q = R ∘ ρ` obtained from a homomorphism `R: S →* GL m k`
defined on a subgroup `S` containing the image of `ρ`. -/
def mapOn : RepresentedDegreeDatum W m k :=
  { D.toDegreeDatum with rep := R.comp (D.rep.codRestrict S hS) }

theorem mapOn_rep (w : W) : (D.mapOn S hS R).rep w = R ⟨D.rep w, hS w⟩ :=
  rfl

theorem mapOn_frobenius : (D.mapOn S hS R).frobenius = R ⟨D.frobenius, hS _⟩ :=
  rfl

variable {S} (hH : (zeroLocus D.geometricMonodromy k : Set (GL n k)) ⊆ S) {R}

include hH in
/-- A regular `R` maps the geometric monodromy group `H` into the geometric monodromy group of
`R ∘ ρ`: the closure of `ρ(P)` into the closure of `R(ρ(P))`. -/
theorem mem_zeroLocus_geometricMonodromy_mapOn (hR : IsRegularOn S R) {h : GL n k}
    (hh : h ∈ zeroLocus D.geometricMonodromy k) :
    R ⟨h, hH hh⟩ ∈ zeroLocus (D.mapOn S hS R).geometricMonodromy k := by
  refine hR.mem_zeroLocus_vanishingIdeal (Γ := (D.degreeZero.map D.rep : Set (GL n k)))
    (fun _ hg ↦ hH (D.map_rep_degreeZero_le_zeroLocus_geometricMonodromy hg)) ?_ ⟨h, hH hh⟩ hh
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, hw, rfl⟩

/-- The action of `R` on the geometric monodromy group, as a homomorphism `H(k) →* H_Q(k)`. -/
noncomputable def geometricMap (hR : IsRegularOn S R) :
    zeroLocus D.geometricMonodromy k →* zeroLocus (D.mapOn S hS R).geometricMonodromy k where
  toFun h := ⟨R ⟨h, hH h.2⟩, D.mem_zeroLocus_geometricMonodromy_mapOn hS hH hR h.2⟩
  map_one' := Subtype.ext (by
    change R ⟨1, _⟩ = 1
    exact map_one R)
  map_mul' g h := Subtype.ext (by
    change R ⟨g * h, _⟩ = R ⟨g, _⟩ * R ⟨h, _⟩
    rw [← map_mul]
    rfl)

theorem coe_geometricMap_apply (hR : IsRegularOn S R) (h : zeroLocus D.geometricMonodromy k) :
    (D.geometricMap hS hH hR h : GL m k) = R ⟨h, hH h.2⟩ :=
  rfl

/-- **Functoriality of the arithmetic monodromy extension.** The homomorphism
`Φ_Q: G_arith(ρ) → G_arith(R ∘ ρ)`, `(h, m) ↦ (R(h), m)`. -/
noncomputable def extensionMap (hR : IsRegularOn S R) :
    D.ArithmeticMonodromyExtension →* (D.mapOn S hS R).ArithmeticMonodromyExtension :=
  SemidirectProduct.map (D.geometricMap hS hH hR) (MonoidHom.id _) fun t ↦ by
    ext h : 2
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MonoidHom.id_apply]
    simp only [coe_frobeniusAction_apply, coe_geometricMap_apply, mapOn_frobenius]
    rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg R (Subtype.ext (by simp))

@[simp]
theorem extensionMap_left (hR : IsRegularOn S R) (x : D.ArithmeticMonodromyExtension) :
    ((D.extensionMap hS hH hR x).left : GL m k) = R ⟨x.left, hH x.left.2⟩ :=
  rfl

@[simp]
theorem extensionMap_right (hR : IsRegularOn S R) (x : D.ArithmeticMonodromyExtension) :
    (D.extensionMap hS hH hR x).right = x.right :=
  rfl

/-- `Φ_Q` preserves the degree. -/
theorem rightHom_extensionMap (hR : IsRegularOn S R) (x : D.ArithmeticMonodromyExtension) :
    SemidirectProduct.rightHom (D.extensionMap hS hH hR x) = SemidirectProduct.rightHom x :=
  rfl

/-- `Φ_Q` maps the degree component `G^[m]` into the degree component `G_Q^[m]`. -/
theorem extensionMap_mem_degreeComponent (hR : IsRegularOn S R) {t : ℤ}
    {x : D.ArithmeticMonodromyExtension} (hx : x ∈ D.degreeComponent t) :
    D.extensionMap hS hH hR x ∈ (D.mapOn S hS R).degreeComponent t :=
  hx

/-- On matrices, `Φ_Q` is `R`: `j_Q ∘ Φ_Q = R ∘ j`. In particular `Φ_Q` is regular on every degree
component. -/
theorem arithmeticMonodromyExtensionHom_extensionMap (hR : IsRegularOn S R)
    (x : D.ArithmeticMonodromyExtension) :
    (D.mapOn S hS R).arithmeticMonodromyExtensionHom (D.extensionMap hS hH hR x) =
      R ⟨D.arithmeticMonodromyExtensionHom x,
        mul_mem (hH x.left.2) (zpow_mem (hS _) _)⟩ := by
  rw [arithmeticMonodromyExtensionHom_apply, extensionMap_left, extensionMap_right,
    mapOn_frobenius, ← map_zpow, ← map_mul]
  congr 1

/-- The image under `R` of the geometric monodromy group is Zariski dense in the geometric
monodromy group of `R ∘ ρ`: both have the vanishing ideal `H_Q`. -/
theorem vanishingIdeal_image_geometricMap (hR : IsRegularOn S R) :
    vanishingIdeal (Set.range fun h ↦ (D.geometricMap hS hH hR h : GL m k)) =
      (D.mapOn S hS R).geometricMonodromy := by
  apply le_antisymm
  · refine vanishingIdeal_anti ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨D.rep w, D.map_rep_degreeZero_le_zeroLocus_geometricMonodromy ⟨w, hw, rfl⟩⟩, rfl⟩
  · intro f hf
    exact mem_vanishingIdeal.2 fun _ ⟨h, hh⟩ ↦ hh ▸ (D.geometricMap hS hH hR h).2 f hf

/-- **Density.** For every degree `t`, the matrix image of `Φ_Q(G^[t])` is Zariski dense in the
matrix image of the degree component `G_Q^[t]`: both have the same vanishing ideal. -/
theorem vanishingIdeal_image_degreeComponent (hR : IsRegularOn S R) (t : ℤ) :
    vanishingIdeal ((D.mapOn S hS R).arithmeticMonodromyExtensionHom ''
        (D.extensionMap hS hH hR '' D.degreeComponent t)) =
      vanishingIdeal ((D.mapOn S hS R).arithmeticMonodromyExtensionHom ''
        (D.mapOn S hS R).degreeComponent t) := by
  have e₁ : (D.mapOn S hS R).arithmeticMonodromyExtensionHom ''
      (D.extensionMap hS hH hR '' D.degreeComponent t) =
      (Set.range fun h ↦ (D.geometricMap hS hH hR h : GL m k)) *
        ({(D.mapOn S hS R).frobenius ^ t} : Set (GL m k)) := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨_, ⟨x.left, rfl⟩, _, rfl, ?_⟩
      rw [arithmeticMonodromyExtensionHom_apply, extensionMap_right, (mem_degreeComponent D).1 hx,
        toAdd_ofAdd]
      rfl
    · rintro ⟨_, ⟨h, rfl⟩, _, rfl, rfl⟩
      refine ⟨_, ⟨⟨h, Multiplicative.ofAdd t⟩, rfl, rfl⟩, ?_⟩
      rw [arithmeticMonodromyExtensionHom_apply]
      rfl
  rw [e₁, image_degreeComponent]
  have hsub : Set.range (fun h ↦ (D.geometricMap hS hH hR h : GL m k)) ⊆
      zeroLocus (D.mapOn S hS R).geometricMonodromy k := by
    rintro _ ⟨h, rfl⟩
    exact (D.geometricMap hS hH hR h).2
  apply le_antisymm
  · intro f hf
    refine mem_vanishingIdeal.2 fun g ⟨h', hh', c, hc, hg⟩ ↦ ?_
    rw [Set.mem_singleton_iff] at hc
    subst hc hg
    have hf' : translate 1 ((D.mapOn S hS R).frobenius ^ t) f ∈
        vanishingIdeal (Set.range fun h ↦ (D.geometricMap hS hH hR h : GL m k)) :=
      mem_vanishingIdeal.2 fun y hy ↦ by
        rw [evalAlgHom_translate_apply, one_mul]
        exact mem_vanishingIdeal.1 hf _ ⟨y, hy, _, rfl, rfl⟩
    rw [vanishingIdeal_image_geometricMap] at hf'
    have := hh' _ hf'
    rwa [evalAlgHom_translate_apply, one_mul] at this
  · exact vanishingIdeal_anti (Set.mul_subset_mul_right hsub)

/-- An element commuting with a set `Γ` of matrices commutes with the `k`-points of its Zariski
closure. -/
private theorem commute_of_mem_vanishingIdeal {Γ : Set (GL m k)} {z : GL m k}
    (hz : ∀ g ∈ Γ, z * g = g * z) {g : GL m k}
    (hg : ∀ a ∈ vanishingIdeal Γ, evalAlgHom g a = 0) : z * g = g * z := by
  ext i j
  have h := hg (commutatorEquation z i j) <| mem_vanishingIdeal.2 fun h hh ↦ by
    rw [evalAlgHom_commutatorEquation, ← Units.val_mul, ← Units.val_mul, hz h hh, sub_self]
  rw [evalAlgHom_commutatorEquation, sub_eq_zero] at h
  exact h.symm

/-- Two elements of `G_arith(ρ)` commute as soon as their matrix images commute. -/
theorem commute_of_arithmeticMonodromyExtensionHom (x y : D.ArithmeticMonodromyExtension)
    (h : D.arithmeticMonodromyExtensionHom x * D.arithmeticMonodromyExtensionHom y =
      D.arithmeticMonodromyExtensionHom y * D.arithmeticMonodromyExtensionHom x) :
    x * y = y * x := by
  have hr : (x * y).right = (y * x).right := mul_comm _ _
  rw [← map_mul, ← map_mul, arithmeticMonodromyExtensionHom_apply,
    arithmeticMonodromyExtensionHom_apply, hr, mul_left_inj] at h
  exact SemidirectProduct.ext (Subtype.ext h) hr

/-- **Centrality.** `Φ_Q` maps central elements of `G_arith(ρ)` to central elements of
`G_arith(ρ_Q)`. -/
theorem extensionMap_mem_center (hR : IsRegularOn S R) {x : D.ArithmeticMonodromyExtension}
    (hx : x ∈ Subgroup.center D.ArithmeticMonodromyExtension) :
    D.extensionMap hS hH hR x ∈ Subgroup.center (D.mapOn S hS R).ArithmeticMonodromyExtension := by
  set Q := D.mapOn S hS R
  set Φ := D.extensionMap hS hH hR
  refine Subgroup.mem_center_iff.2 fun y ↦ (Q.commute_of_arithmeticMonodromyExtensionHom _ _ ?_)
  have hy : y ∈ Q.degreeComponent (Multiplicative.toAdd y.right) := rfl
  have hg : ∀ a ∈ vanishingIdeal (Q.arithmeticMonodromyExtensionHom ''
      (Φ '' D.degreeComponent (Multiplicative.toAdd y.right))),
      evalAlgHom (Q.arithmeticMonodromyExtensionHom y) a = 0 := by
    rw [D.vanishingIdeal_image_degreeComponent hS hH hR]
    exact fun a ha ↦ mem_vanishingIdeal.1 ha _ ⟨y, hy, rfl⟩
  refine (commute_of_mem_vanishingIdeal ?_ hg).symm
  rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx w]


section Determinant

/-- The **determinant line** `det ρ`, the rank-one represented degree datum `g ↦ det (ρ g)`. -/
noncomputable def det : RepresentedDegreeDatum W (Fin 1) k :=
  D.mapOn ⊤ (fun _ ↦ trivial) ((detGL n k).comp (⊤ : Subgroup (GL n k)).subtype)

theorem det_rep (w : W) : D.det.rep w = detGL n k (D.rep w) :=
  rfl

theorem isRegularOn_detGL :
    IsRegularOn ⊤ ((detGL n k).comp (⊤ : Subgroup (GL n k)).subtype) :=
  let ⟨φ, hφ⟩ := exists_algHom_comp_eq_evalAlgHom_detGL (n := n) (k := k)
  isRegularOn_top _ φ hφ

/-- **The determinant morphism of arithmetic monodromy** `Δ_ρ: G_arith(ρ) → G_arith(det ρ)`,
`(h, m) ↦ (det h, m)`. It preserves the degree (`rightHom_extensionMap`), is given by the
determinant on matrices (`arithmeticMonodromyExtensionHom_detExtensionMap`), has dense image on
every degree component (`vanishingIdeal_image_degreeComponent`) and maps central elements to
central elements (`extensionMap_mem_center`). -/
noncomputable def detExtensionMap :
    D.ArithmeticMonodromyExtension →* D.det.ArithmeticMonodromyExtension :=
  D.extensionMap (S := ⊤) (fun _ ↦ trivial) (fun _ _ ↦ trivial) isRegularOn_detGL

theorem rightHom_detExtensionMap (x : D.ArithmeticMonodromyExtension) :
    SemidirectProduct.rightHom (D.detExtensionMap x) = SemidirectProduct.rightHom x :=
  rfl

theorem arithmeticMonodromyExtensionHom_detExtensionMap (x : D.ArithmeticMonodromyExtension) :
    D.det.arithmeticMonodromyExtensionHom (D.detExtensionMap x) =
      detGL n k (D.arithmeticMonodromyExtensionHom x) :=
  D.arithmeticMonodromyExtensionHom_extensionMap _ _ _ x

theorem vanishingIdeal_image_detExtensionMap (t : ℤ) :
    vanishingIdeal (D.det.arithmeticMonodromyExtensionHom ''
        (D.detExtensionMap '' D.degreeComponent t)) =
      vanishingIdeal (D.det.arithmeticMonodromyExtensionHom '' D.det.degreeComponent t) :=
  D.vanishingIdeal_image_degreeComponent _ _ _ t

theorem detExtensionMap_mem_center {x : D.ArithmeticMonodromyExtension}
    (hx : x ∈ Subgroup.center D.ArithmeticMonodromyExtension) :
    D.detExtensionMap x ∈ Subgroup.center D.det.ArithmeticMonodromyExtension :=
  D.extensionMap_mem_center _ _ _ hx

end Determinant

end AlgebraicGeometry.Monodromy.RepresentedDegreeDatum
