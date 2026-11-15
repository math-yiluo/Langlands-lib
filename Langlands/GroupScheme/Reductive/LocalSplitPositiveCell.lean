import Langlands.GroupScheme.Reductive.LocalSplitGeneratorRelations
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Localization.Integer

/-! # Products of positive root points over local rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Cocharacter

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]

/-- The pairing `∑ⱼ ch j * ν j` of an exponent vector `ch` with a cocharacter vector `ν`. -/
def coPairing (ch ν : I → ℤ) : ℤ := ∑ j, ch j * ν j

/-- The torus point `ν(t)` whose coordinates are the powers `t ^ ν j` of a global unit `t`. -/
def cocharPoint (ν : I → ℤ) (Z : Over (Spec (CommRingCat.of R))) (t : (Γ(Z.left, ⊤))ˣ) :
    Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X :=
  (splitTorus.pointsEquiv I Z).symm fun j => t ^ ν j

private theorem zpow_finset_sum {α M : Type*} [CommGroup M] (t : M) (s : Finset α)
    (f : α → ℤ) : t ^ (∑ j ∈ s, f j) = ∏ j ∈ s, t ^ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

/-- An exponent character takes the value `t ^ ⟨ch, ν⟩` at `ν(t)`. -/
theorem torusChar_cocharPoint (ch ν : I → ℤ) (Z : Over (Spec (CommRingCat.of R)))
    (t : (Γ(Z.left, ⊤))ˣ) :
    torusChar ch Z (cocharPoint ν Z t) =
      ((t ^ coPairing ch ν : (Γ(Z.left, ⊤))ˣ) : Γ(Z.left, ⊤)) := by
  rw [torusChar, Corepresented.charValue_exponentCharacter, cocharPoint,
    MulEquiv.apply_symm_apply]
  congr 1
  change (∏ j, (t ^ ν j) ^ ch j) = t ^ coPairing ch ν
  rw [coPairing, zpow_finset_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← zpow_mul, mul_comm]

/-- The value at `ν(t)` of an exponent character with positive pairing `d`. -/
theorem torusChar_cocharPoint_of_eq {ch ν : I → ℤ} {d : ℕ} (hd : coPairing ch ν = d)
    (Z : Over (Spec (CommRingCat.of R))) (t : (Γ(Z.left, ⊤))ˣ) :
    torusChar ch Z (cocharPoint ν Z t) = (t : Γ(Z.left, ⊤)) ^ d := by
  rw [torusChar_cocharPoint, hd, zpow_natCast, Units.val_pow_eq_pow_val]

/-- The inverse of the value at `ν(t)` of an exponent character with negative pairing
`-d`. -/
theorem inverse_torusChar_cocharPoint_of_eq {ch ν : I → ℤ} {d : ℕ} (hd : coPairing ch ν = -d)
    (Z : Over (Spec (CommRingCat.of R))) (t : (Γ(Z.left, ⊤))ˣ) :
    Ring.inverse (torusChar ch Z (cocharPoint ν Z t)) = (t : Γ(Z.left, ⊤)) ^ d := by
  rw [torusChar_cocharPoint, hd, Ring.inverse_unit, zpow_neg, inv_inv, zpow_natCast,
    Units.val_pow_eq_pow_val]

end Cocharacter

section Conjugation

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}

/-- Torus points of `G` commute. -/
theorem torus_comp_mul_comm (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {Z : Over (Spec (CommRingCat.of R))}
    (t τ : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (τ ≫ i.hom.hom) * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * (τ ≫ i.hom.hom) := by
  have h : τ * t = t * τ :=
    (splitTorus.pointsEquiv I Z).injective (by rw [map_mul, map_mul, mul_comm])
  rw [← MonObj.mul_comp, h, MonObj.mul_comp]

/-- Conjugating an ordered product of root points by a torus point scales each coordinate by
its character. -/
theorem torus_mul_orderedProduct_mul_inv (hu : TorusEquivariant i ch u) {r : ℕ}
    (e : Fin r → J) {Z : Over (Spec (CommRingCat.of R))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Fin r → Γ(Z.left, ⊤)) :
    (t ≫ i.hom.hom) * orderedProduct u e Z c * (t ≫ i.hom.hom)⁻¹ =
      orderedProduct u e Z (fun k => torusChar (ch (e k)) Z t * c k) := by
  rw [mul_inv_eq_iff_eq_mul, orderedProduct_mul_torus hu e t]
  congr 2
  funext k
  rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_torusChar _ _ _), one_mul]

variable {m n : ℕ}

/-- The identity is the cell point with zero root coordinates and trivial torus
coordinate. -/
theorem mkCellPoint_one_comp_cellMap (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) :
    mkCellPoint Z 0 1 0 ≫ cellMap i u neg pos = 1 := by
  have ht : torusCoord (mkCellPoint (I := I) Z (0 : Fin m → Γ(Z.left, ⊤)) 1
      (0 : Fin n → Γ(Z.left, ⊤))) = 1 :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint, map_one])
  rw [comp_cellMap, cellPoint, negCoord_mkCellPoint, posCoord_mkCellPoint, ht,
    orderedProduct_zero, orderedProduct_zero, MonObj.one_comp, one_mul, one_mul]

/-- Conjugating a cell point by the inverse of a torus point divides its root coordinates by
their characters and keeps its torus coordinate. -/
theorem torus_inv_mul_cellMap_mul (hu : TorusEquivariant i ch u) (neg : Fin m → J)
    (pos : Fin n → J) {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n)
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    (t ≫ i.hom.hom)⁻¹ * (x ≫ cellMap i u neg pos) * (t ≫ i.hom.hom) =
      mkCellPoint Z (fun k => Ring.inverse (torusChar (ch (neg k)) Z t) * negCoord x k)
          (splitTorus.pointsEquiv I Z (torusCoord x))
          (fun k => Ring.inverse (torusChar (ch (pos k)) Z t) * posCoord x k) ≫
        cellMap i u neg pos := by
  have ht : torusCoord (mkCellPoint Z
      (fun k => Ring.inverse (torusChar (ch (neg k)) Z t) * negCoord x k)
      (splitTorus.pointsEquiv I Z (torusCoord x))
      (fun k => Ring.inverse (torusChar (ch (pos k)) Z t) * posCoord x k)) = torusCoord x :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint])
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, negCoord_mkCellPoint,
    posCoord_mkCellPoint, ht]
  have hA := orderedProduct_mul_torus hu neg t (negCoord x)
  have hB := orderedProduct_mul_torus hu pos t (posCoord x)
  have hc := torus_comp_mul_comm i t (torusCoord x)
  set T := t ≫ i.hom.hom
  set τ := torusCoord x ≫ i.hom.hom
  set A := orderedProduct u neg Z (negCoord x)
  set B := orderedProduct u pos Z (posCoord x)
  set A' := orderedProduct u neg Z
    (fun k => Ring.inverse (torusChar (ch (neg k)) Z t) * negCoord x k)
  set B' := orderedProduct u pos Z
    (fun k => Ring.inverse (torusChar (ch (pos k)) Z t) * posCoord x k)
  calc T⁻¹ * (A * τ * B) * T = T⁻¹ * A * τ * (B * T) := by group
    _ = T⁻¹ * A * (τ * T) * B' := by rw [hB]; group
    _ = T⁻¹ * (A * T) * τ * B' := by rw [hc]; group
    _ = A' * τ * B' := by rw [hA]; group

end Conjugation

section PositiveProducts

open Polynomial GenericLine

/-- Restriction of global functions along `Spec` of an injective ring map is injective. -/
theorem specMap_appTop_injective {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    (hκ : Function.Injective κ) :
    Function.Injective (Spec.map (CommRingCat.ofHom κ)).appTop := by
  have key : ∀ x, (Spec.map (CommRingCat.ofHom κ)).appTop x =
      (Scheme.ΓSpecIso (CommRingCat.of L')).inv
        (κ ((Scheme.ΓSpecIso (CommRingCat.of L)).hom x)) := by
    intro x
    conv_lhs => rw [← (Scheme.ΓSpecIso (CommRingCat.of L)).hom_inv_id_apply x]
    exact specMap_appTop_ΓSpecIso_inv κ _
  intro a b h
  rw [key, key] at h
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of L')).hom h
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at h2
  have h3 := congrArg (Scheme.ΓSpecIso (CommRingCat.of L)).inv (hκ h2)
  rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at h3

/-- The structure map `B → B[X]_{𝔪[X]}` to the local ring of the generic point of the closed
fibre of the affine line is local. -/
theorem isLocalHom_algebraMap_generic_comp_C (B : Type u) [CommRing B] [IsLocalRing B] :
    IsLocalHom ((algebraMap B[X] (Generic B)).comp C) := by
  refine ⟨fun b hb => ?_⟩
  rw [RingHom.comp_apply,
    IsLocalization.AtPrime.isUnit_to_map_iff (Generic B) (genericIdeal B)] at hb
  by_contra hnb
  apply hb
  show C b ∈ genericIdeal B
  rw [mem_genericIdeal_iff, Polynomial.map_C, Polynomial.C_eq_zero,
    IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal b).mpr hnb

theorem X_notMem_genericIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    (X : B[X]) ∉ genericIdeal B := by
  rw [mem_genericIdeal_iff, Polynomial.map_X]
  exact Polynomial.X_ne_zero

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

/-- **Products of positive root points lie in the positive cell.** Let `ν` be a cocharacter
pairing negatively with the characters of the negative cell factors. Over every local test
ring, a finite product of root points whose characters pair positively with `ν` is a
product of the positive cell factors. The proof contracts the product along `ν`: the
contraction over the line lands in the open cell near `X = 0`, at the generic point of the
closed fibre it is a torus conjugate of the product, and comparing cell coordinates kills
the negative and torus coordinates. -/
theorem exists_orderedProduct_eq_pos [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    {r : ℕ} (e : Fin r → J) (he : ∀ k, 0 < coPairing (ch (e k)) ν)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (c : Fin r → Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u e (Over.mk s) c = orderedProduct u pos (Over.mk s) z := by
  classical
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  -- exponents
  have hd : ∀ k, ∃ d : ℕ, 0 < d ∧ coPairing (ch (e k)) ν = d := fun k =>
    ⟨(coPairing (ch (e k)) ν).toNat, by have := he k; omega,
      (Int.toNat_of_nonneg (he k).le).symm⟩
  choose d hd0 hdeq using hd
  -- the contraction of the product along `ν`
  let S : ∀ {W : Over (Spec (CommRingCat.of R))}, (W ⟶ Over.mk s) → Γ(W.left, ⊤) →
      (W ⟶ G.X) := fun f t =>
    orderedProduct u e _ (fun k => t ^ d k * f.left.appTop (c k))
  have hS_comp : ∀ {W W' : Over (Spec (CommRingCat.of R))} (k : W' ⟶ W) (f : W ⟶ Over.mk s)
      (t : Γ(W.left, ⊤)), k ≫ S f t = S (k ≫ f) (k.left.appTop t) := by
    intro W W' k f t
    simp only [S, comp_orderedProduct, map_mul, map_pow, Over.comp_left,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hS_zero : ∀ {W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Over.mk s), S f 0 = 1 := by
    intro W f
    simp only [S, zero_pow (hd0 _).ne', zero_mul]
    exact orderedProduct_zero u e W
  have hS_unit : ∀ {W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Over.mk s)
      (t : (Γ(W.left, ⊤))ˣ), S f t =
        (cocharPoint ν W t ≫ i.hom.hom) * (f ≫ orderedProduct u e (Over.mk s) c) *
          (cocharPoint ν W t ≫ i.hom.hom)⁻¹ := by
    intro W f t
    rw [comp_orderedProduct, torus_mul_orderedProduct_mul_inv hu]
    simp only [S, torusChar_cocharPoint_of_eq (hdeq _)]
  -- the local ring of the line at `X = 0`
  let ι₀ : B →+* AtPoint B 0 := (algebraMap B[X] (AtPoint B 0)).comp C
  let s₀ := Spec.map (CommRingCat.ofHom ι₀) ≫ s
  let f₀ : Over.mk s₀ ⟶ Over.mk s := specHom ι₀ rfl
  let t₀ : Γ((Over.mk s₀).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (AtPoint B 0))).inv (algebraMap B[X] (AtPoint B 0) X)
  let E₀ := S f₀ t₀
  let Ev : Over.mk s ⟶ Over.mk s₀ := specHom (evalAt 0) (specMap_evalAt_comp 0 s)
  have hEv : Ev ≫ f₀ = 𝟙 _ :=
    (specHom_comp_eq (by rw [← RingHom.comp_assoc, evalAt_comp_C]) _ _).trans (specHom_id _)
  have hEvt : Ev.left.appTop t₀ = 0 := by
    change (Spec.map (CommRingCat.ofHom (evalAt (0 : B)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (AtPoint B 0))).inv _) = 0
    rw [specMap_appTop_ΓSpecIso_inv, evalAt_algebraMap, Polynomial.eval_X, map_zero]
  have hEvE : Ev ≫ E₀ = 1 := by
    rw [hS_comp, hEv, hEvt, hS_zero]
  have hk₀ : E₀.left (IsLocalRing.closedPoint (AtPoint B 0)) ∈
      Set.range (cellMap i u neg pos).left := by
    have hcl : Ev.left (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint (AtPoint B 0) :=
      IsLocalRing.comap_closedPoint (evalAt (0 : B))
    rw [← hcl]
    change (Ev ≫ E₀).left (IsLocalRing.closedPoint B) ∈ _
    rw [hEvE, ← mkCellPoint_one_comp_cellMap (i := i) (u := u) neg pos]
    exact ⟨_, rfl⟩
  obtain ⟨Y₀, hY₀⟩ := exists_lift_of_localPoint_closedPoint_mem (cellMap i u neg pos) E₀ hk₀
  have hEvY : Ev ≫ Y₀ = mkCellPoint _ 0 1 0 := by
    apply (cancel_mono (cellMap i u neg pos)).mp
    rw [Category.assoc, hY₀, hEvE, mkCellPoint_one_comp_cellMap]
  -- the generic point of the closed fibre
  let κ : AtPoint B 0 →+* Generic B := toGeneric 0
  let sG := Spec.map (CommRingCat.ofHom κ) ≫ s₀
  let fG : Over.mk sG ⟶ Over.mk s₀ := specHom κ rfl
  have hX : IsUnit (κ (algebraMap B[X] (AtPoint B 0) X)) := by
    rw [toGeneric_algebraMap]
    exact IsLocalization.map_units (Generic B)
      (⟨X, X_notMem_genericIdeal B⟩ : (genericIdeal B).primeCompl)
  let uG : (Γ((Over.mk sG).left, ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (Generic B))).inv.hom.toMonoidHom hX.unit
  have huG : (uG : Γ((Over.mk sG).left, ⊤)) = fG.left.appTop t₀ := by
    change (Scheme.ΓSpecIso (CommRingCat.of (Generic B))).inv (κ _) =
      (Spec.map (CommRingCat.ofHom κ)).appTop ((Scheme.ΓSpecIso (CommRingCat.of _)).inv _)
    rw [specMap_appTop_ΓSpecIso_inv]
  let g := orderedProduct u e (Over.mk s) c
  let Y' := mkCellPoint (Over.mk sG)
    (fun k => Ring.inverse (torusChar (ch (neg k)) _ (cocharPoint ν (Over.mk sG) uG)) *
      negCoord (fG ≫ Y₀) k)
    (splitTorus.pointsEquiv I _ (torusCoord (fG ≫ Y₀)))
    (fun k => Ring.inverse (torusChar (ch (pos k)) _ (cocharPoint ν (Over.mk sG) uG)) *
      posCoord (fG ≫ Y₀) k)
  have hG : (fG ≫ f₀) ≫ g = Y' ≫ cellMap i u neg pos := by
    have h1 : fG ≫ E₀ = (cocharPoint ν (Over.mk sG) uG ≫ i.hom.hom) * ((fG ≫ f₀) ≫ g) *
        (cocharPoint ν (Over.mk sG) uG ≫ i.hom.hom)⁻¹ := by
      rw [hS_comp, ← huG, hS_unit]
    rw [← hY₀, ← Category.assoc] at h1
    rw [← torus_inv_mul_cellMap_mul hu neg pos (fG ≫ Y₀), h1]
    group
  -- the product lies in the cell
  have hloc := isLocalHom_algebraMap_generic_comp_C B
  have hfG : (fG ≫ f₀).left = Spec.map (CommRingCat.ofHom ((algebraMap B[X] (Generic B)).comp C)) := by
    rw [Over.comp_left, specHom_left, specHom_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← RingHom.comp_assoc, toGeneric_comp]
  have hkB : g.left (IsLocalRing.closedPoint B) ∈ Set.range (cellMap i u neg pos).left := by
    have hcl : (fG ≫ f₀).left (IsLocalRing.closedPoint (Generic B)) =
        IsLocalRing.closedPoint B := by
      rw [hfG]
      exact IsLocalRing.comap_closedPoint ((algebraMap B[X] (Generic B)).comp C)
    rw [← hcl]
    change ((fG ≫ f₀) ≫ g).left (IsLocalRing.closedPoint (Generic B)) ∈ _
    rw [hG]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := exists_lift_of_localPoint_closedPoint_mem (cellMap i u neg pos) g hkB
  let y₀ := f₀ ≫ y
  have hy₀ : fG ≫ y₀ = Y' := by
    apply (cancel_mono (cellMap i u neg pos)).mp
    rw [Category.assoc, Category.assoc, hy, ← Category.assoc, hG]
  have hEvy : Ev ≫ y₀ = y := by
    rw [← Category.assoc, hEv, Category.id_comp]
  have hinj := specMap_appTop_injective κ (toGeneric_injective 0)
  -- the negative coordinates vanish
  have hneg0 : negCoord y = 0 := by
    funext k
    obtain ⟨q, hq⟩ : ∃ q : ℕ, coPairing (ch (neg k)) ν = -q :=
      ⟨(-coPairing (ch (neg k)) ν).toNat, by have := hneg k; omega⟩
    have hq0 : q ≠ 0 := by have := hneg k; omega
    have h1 : negCoord (fG ≫ y₀) k = negCoord Y' k := by rw [hy₀]
    simp only [Y', negCoord_comp, negCoord_mkCellPoint] at h1
    rw [inverse_torusChar_cocharPoint_of_eq hq, huG, ← map_pow, ← map_mul] at h1
    have h2 : negCoord y₀ k = t₀ ^ q * negCoord Y₀ k := hinj h1
    have h3 := congrArg Ev.left.appTop h2
    rw [map_mul, map_pow, hEvt, zero_pow hq0, zero_mul] at h3
    have h4 : negCoord (Ev ≫ y₀) k = 0 := by rw [negCoord_comp]; exact h3
    rw [hEvy] at h4
    exact h4
  -- the torus coordinate is trivial
  have htor : torusCoord y = 1 := by
    apply (splitTorus.pointsEquiv I _).injective
    have hunits : Function.Injective (splitTorus.unitsRestrict I fG) := by
      intro a b hab
      funext j
      apply Units.ext
      exact hinj (congrArg (fun w => ((w j : (Γ((Over.mk sG).left, ⊤))ˣ) : Γ((Over.mk sG).left, ⊤))) hab)
    have h1 : splitTorus.pointsEquiv I _ (torusCoord y₀) =
        splitTorus.pointsEquiv I _ (torusCoord Y₀) := by
      apply hunits
      rw [← splitTorus.pointsEquiv_naturality, ← splitTorus.pointsEquiv_naturality,
        ← torusCoord_comp, ← torusCoord_comp, hy₀]
      simp only [Y', torusCoord_mkCellPoint]
    rw [← hEvy, torusCoord_comp, splitTorus.pointsEquiv_naturality, h1,
      ← splitTorus.pointsEquiv_naturality, ← torusCoord_comp, hEvY, torusCoord_mkCellPoint,
      map_one]
  refine ⟨posCoord y, ?_⟩
  change g = _
  rw [← hy, comp_cellMap, cellPoint, hneg0, htor, orderedProduct_zero, MonObj.one_comp,
    one_mul, one_mul]

/-- Appending one root point to an ordered product. -/
theorem orderedProduct_snoc (u : J → (Ga R ⟶ G)) {r : ℕ} (e : Fin r → J) (α : J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) (a : Γ(Z.left, ⊤)) :
    orderedProduct u (Fin.snoc e α : Fin (r + 1) → J) Z (Fin.snoc c a) =
      orderedProduct u e Z c * rootPoint (u α) Z a := by
  simp only [orderedProduct, List.ofFn_succ', List.concat_eq_append, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one, Fin.snoc_castSucc, Fin.snoc_last]

/-- **Right translation of the positive cell factor by a positive root point.** -/
theorem exists_orderedProduct_mul_rootPoint_eq_pos
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) {α : J} (hα : 0 < coPairing (ch α) ν)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (w : Fin n → Γ((Over.mk s).left, ⊤)) (a : Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u pos (Over.mk s) w * rootPoint (u α) (Over.mk s) a =
        orderedProduct u pos (Over.mk s) z := by
  have he : ∀ k, 0 < coPairing (ch ((Fin.snoc pos α : Fin (n + 1) → J) k)) ν := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [Fin.snoc_last]; exact hα
    · rw [Fin.snoc_castSucc]; exact hpos k
  obtain ⟨z, hz⟩ := exists_orderedProduct_eq_pos (pos := pos) hu ν hneg _ he s (Fin.snoc w a)
  exact ⟨z, by rw [← orderedProduct_snoc, hz]⟩

/-- **Right translation of a cell point by a positive root point** stays in the cell and
changes only the positive coordinates. -/
theorem exists_comp_cellMap_mul_rootPoint
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) {α : J} (hα : 0 < coPairing (ch α) ν)
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk s ⟶ cellObj R I m n) (a : Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      (x ≫ cellMap i u neg pos) * rootPoint (u α) (Over.mk s) a =
        mkCellPoint (Over.mk s) (negCoord x) (splitTorus.pointsEquiv I _ (torusCoord x)) z ≫
          cellMap i u neg pos := by
  obtain ⟨z, hz⟩ :=
    exists_orderedProduct_mul_rootPoint_eq_pos hu ν hneg hpos hα s (posCoord x) a
  refine ⟨z, ?_⟩
  have ht : torusCoord (mkCellPoint (Over.mk s) (negCoord x)
      (splitTorus.pointsEquiv I _ (torusCoord x)) z) = torusCoord x :=
    (splitTorus.pointsEquiv I _).injective (by rw [torusCoord_mkCellPoint])
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, negCoord_mkCellPoint,
    posCoord_mkCellPoint, ht, mul_assoc, hz]

end PositiveProducts

section RootDatum

variable {I : Type u} [Fintype I] {J : Type u}

/-- Some cocharacter pairs with every root as a fixed positive multiple of its height relative
to a base. -/
theorem exists_coPairing_eq_height (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) :
    ∃ d : ℤ, 0 < d ∧ ∃ ν : I → ℤ, ∀ j, coPairing (P.root j) ν = d * b.height j := by
  classical
  let castL : (I → ℤ) →ₗ[ℤ] (I → ℚ) := (Int.castAddHom ℚ).toIntLinearMap.compLeft I
  have hcast : Function.Injective castL := fun x y h => funext fun j => by
    have h' := congrFun h j
    simpa [castL] using h'
  have hZ : LinearIndependent ℤ (fun a : b.support => P.root a) := b.linearIndepOn_root
  have hZQ : LinearIndependent ℤ (fun a : b.support => castL (P.root a)) :=
    hZ.map' castL (LinearMap.ker_eq_bot.mpr hcast)
  have hQ : LinearIndependent ℚ (fun a : b.support => castL (P.root a)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZQ
  let Wsp : Submodule ℚ (I → ℚ) :=
    Submodule.span ℚ (Set.range fun a : b.support => castL (P.root a))
  let f : (I → ℚ) →ₗ[ℚ] ℚ :=
    Subspace.dualLift Wsp ((Module.Basis.span hQ).constr ℚ (fun _ => (1 : ℚ)))
  have hf (a : b.support) : f (castL (P.root a)) = 1 := by
    dsimp only [f]
    rw [← Module.Basis.coe_span_apply hQ a, Subspace.dualLift_of_subtype,
      Module.Basis.constr_basis]
  -- clear the denominators of `f`
  let q : I → ℚ := fun j => f (Pi.single j 1)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose a ha using hc
  have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.ne_zero c.property
  have ha' (j : I) : (a j : ℚ) = (c : ℤ) * q j := by
    simpa [Algebra.smul_def, algebraMap_int_eq] using ha j
  have hpair (x : I → ℤ) :
      (coPairing x (fun j => (c : ℤ) * a j) : ℚ) = ((c : ℤ) ^ 2 : ℤ) * f (castL x) := by
    have hfx : f (castL x) = ∑ j, (x j : ℚ) * q j := by
      have hx : castL x = ∑ j, (x j : ℚ) • Pi.single j (1 : ℚ) := by
        funext j
        simp [castL, Finset.sum_apply, Pi.single_apply]
      rw [hx, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hfx, coPairing, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [ha']
    ring
  refine ⟨(c : ℤ) ^ 2, sq_pos_of_ne_zero hc0, fun j => (c : ℤ) * a j, fun j => ?_⟩
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hroot : f (castL (P.root j)) = ∑ k ∈ b.support, (g k : ℚ) := by
    rw [hg, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_zsmul, map_zsmul, hf ⟨k, hk⟩, zsmul_eq_mul, mul_one]
  have h := hpair (P.root j)
  rw [hroot] at h
  rw [RootPairing.Base.height_eq_sum hg]
  exact_mod_cast h

/-- A cocharacter pairing positively with the positive roots of a base and negatively with
the other roots. -/
theorem exists_cocharacter_of_base (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) :
    ∃ ν : I → ℤ, (∀ j, b.IsPos j → 0 < coPairing (P.root j) ν) ∧
      ∀ j, ¬ b.IsPos j → coPairing (P.root j) ν < 0 := by
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  refine ⟨ν, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hν]
    exact mul_pos hd hj
  · rw [hν]
    have h0 := b.height_ne_zero j
    rw [RootPairing.Base.isPos_iff] at hj
    exact mul_neg_of_pos_of_neg hd (by omega)

end RootDatum

section RootFamilies

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- **Products of positive root points over local rings.** For a reductive group with a
fibrewise maximal coordinate split torus, a fibrewise root datum, a base and actual root
parametrizations of all roots, every finite product of positive root points over a local
test ring is a product of the positive cell factors. -/
theorem exists_orderedProduct_eq_pos_of_isPos (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base) {u : J → (Ga R ⟶ G)}
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) {r : ℕ} (e : Fin r → J)
    (he : ∀ k, b.IsPos (e k)) (c : Fin r → Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u e (Over.mk s) c = orderedProduct u (fun k => (pos k : J)) (Over.mk s) z := by
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b u hu neg pos
  obtain ⟨ν, hνpos, hνneg⟩ := exists_cocharacter_of_base P b
  exact exists_orderedProduct_eq_pos (ch := fun α => P.root α) (neg := fun k => (neg k : J))
    (fun α Z t c => (hu α).equivariant Z t c) ν (fun k => hνneg _ (neg k).2) e
    (fun k => hνpos _ (he k)) s c

/-- **Right translation of a big-cell point by a positive root point** over a local test
ring changes only its positive coordinates. -/
theorem exists_comp_cellMap_mul_rootPoint_of_isPos (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base) {u : J → (Ga R ⟶ G)}
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    {B : Type u} [CommRing B] [IsLocalRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk s ⟶ cellObj R I m n) {α : J} (hα : b.IsPos α) (a : Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      (x ≫ cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))) *
          rootPoint (u α) (Over.mk s) a =
        mkCellPoint (Over.mk s) (negCoord x) (splitTorus.pointsEquiv I _ (torusCoord x)) z ≫
          cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J)) := by
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b u hu neg pos
  obtain ⟨ν, hνpos, hνneg⟩ := exists_cocharacter_of_base P b
  exact exists_comp_cellMap_mul_rootPoint (ch := fun α => P.root α)
    (fun α Z t c => (hu α).equivariant Z t c) ν (fun k => hνneg _ (neg k).2)
    (fun k => hνpos _ (pos k).2) (hνpos _ hα) s x a

end RootFamilies

end LocalSplitCell

open LocalSplitCell in
/-- **Products of positive root points lie in the positive cell factor**, over every local
ring. Let `G` be reductive over a commutative ring `R`, with a fibrewise maximal coordinate
split torus `i`, a fibrewise root datum `P`, a base `b` and actual root parametrizations `u`
of all roots. Enumerate the non-positive and the positive roots by `neg` and `pos`. Then for
every local ring `B` with a morphism `Spec B ⟶ Spec R` and every finite list of positive roots
with coordinates in `B`, the product of the corresponding root points equals
`∏ₖ u_{pos k}(z k)` for some coordinates `z`. -/
def LocalSplitPositiveProductStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom], IsReductive G →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
      ∀ (b : P.Base) (u : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (u α)) →
      ∀ (m n : ℕ) (_neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
        (B : Type u) [CommRing B] [IsLocalRing B]
        (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (r : ℕ) (e : Fin r → J),
        (∀ k, b.IsPos (e k)) → ∀ c : Fin r → Γ((Over.mk s).left, ⊤),
        ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
          orderedProduct u e (Over.mk s) c =
            orderedProduct u (fun k => (pos k : J)) (Over.mk s) z

/-- Products of positive root points lie in the positive cell factor over local rings. -/
theorem localSplitPositiveProduct : LocalSplitPositiveProductStatement.{u} := by
  intro R _ I _ J G _ hG i hmax P hP b u hu m n neg pos B _ _ s r e he c
  exact LocalSplitCell.exists_orderedProduct_eq_pos_of_isPos hG hmax hP b hu neg pos s e he c

end Langlands.GroupScheme
