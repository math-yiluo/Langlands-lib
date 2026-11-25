/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistGenerator
public import WeilConjectures.LinearAlgebra.ExteriorPower.ChartTransition
public import WeilConjectures.RingTheory.Kaehler.LocalizationPolynomial

/-!
# The canonical sheaf of projective space

Let `A` be a commutative ring and `ℙ = ℙ(n; Spec A)` with `Nat.card n = d + 1`. The canonical
sheaf `ω_ℙ = ⋀ᵈ Ω¹_{ℙ/A}` is invertible, with free generator
`ηᵢ = (-1)ⁱ ⋀_{k ≠ i} d(x_k / xᵢ)` on the standard open `Uᵢ = D₊(xᵢ)`, and `ω_ℙ ≅ 𝒪(-d-1)`,
`ηᵢ ↦ eᵢ^{(-d-1)}`. The signs and the order of the wedge products refer to an enumeration
`e: n ≃ Fin (d + 1)`.

## Main declarations

- `AlgebraicGeometry.ProjectiveSpace.canonicalModule`: `ω_ℙ = ⋀ᵈ Ω¹_{ℙ/S}`.
- `AlgebraicGeometry.ProjectiveSpace.canonicalGenerator`: the local generator `ηᵢ` on `Uᵢ`, a
  free generator by `isFreeGenerator_canonicalGenerator`.
- `AlgebraicGeometry.ProjectiveSpace.map_canonicalGenerator_eq_transitionUnit_smul`: the
  transition rule `ηᵢ = (xᵢ / xⱼ)^{-(d+1)} ηⱼ` on `Uᵢ ∩ Uⱼ`.
- `AlgebraicGeometry.ProjectiveSpace.canonicalModuleIsoTwist`: `ω_ℙ ≅ 𝒪(-d-1)`, `ηᵢ ↦ eᵢ^{(-d-1)}`.

## Implementation details

The generators `ηᵢ` and `eᵢ^{(-d-1)}` have the same transition units `(xᵢ / xⱼ)^{-d-1}`, so the
local isomorphisms glue via `Scheme.Modules.isoOfIsFreeGenerator`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MvPolynomial Module

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable (n : Type u) (A : Type u) [CommRing A]

/-- **The differentials on a basic open of a standard chart.** On a basic open `W = D(f)` of the
standard open `Uᵢ = D₊(xᵢ)` of `ℙ(n; Spec A)`, the sections of `Ω¹_{ℙ/A}` are free with basis
the differentials `d(x_k / xᵢ)`, `k ≠ i`. -/
theorem exists_basis_relativeDifferentials_basicOpen (i : n)
    (f : Γ(ℙ(n; Spec (.of A)), standardOpen n _ i)) :
    ∃ b : Basis {k : n // k ≠ i} Γ(ℙ(n; Spec (.of A)), ℙ(n; Spec (.of A)).basicOpen f)
        Γ((ℙ(n; Spec (.of A)) ↘ Spec (.of A)).relativeDifferentials,
          ℙ(n; Spec (.of A)).basicOpen f),
      ∀ k, b k = (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).relativeDifferentials.presheaf.map
        (homOfLE (ℙ(n; Spec (.of A)).basicOpen_le f)).op
        ((ℙ(n; Spec (.of A)) ↘ Spec (.of A)).sectionsD _ (coordRatio n _ i k)) := by
  set X := ℙ(n; Spec (.of A))
  set g := X ↘ Spec (.of A)
  set W := X.basicOpen f
  have hU := isAffineOpen_standardOpen n (Spec (.of A)) i
  let : Algebra A Γ(X, W) := (g.specStructureMap W).hom.toAlgebra
  let : Algebra (MvPolynomial {k : n // k ≠ i} A) Γ(X, W) :=
    ((algebraMap Γ(X, standardOpen n _ i) Γ(X, W)).comp
      (chartRingEquiv n A i).symm.symm.toRingHom).toAlgebra
  have : IsLocalization ((Submonoid.powers f).map (chartRingEquiv n A i).symm) Γ(X, W) :=
    have := hU.isLocalization_basicOpen f
    IsLocalization.isLocalization_of_base_ringEquiv _ _ (chartRingEquiv n A i).symm
  have : IsScalarTower A (MvPolynomial {k : n // k ≠ i} A) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
        RingEquiv.symm_symm, RingEquiv.toRingHom_eq_coe]
      erw [chartRingEquiv_C]
      rw [← g.specStructureMap_map (X.basicOpen_le f), CommRingCat.comp_apply]
  refine ⟨(KaehlerDifferential.basisOfIsLocalizationMvPolynomial A {k : n // k ≠ i} Γ(X, W)
    ((Submonoid.powers f).map (chartRingEquiv n A i).symm)).map
      (g.kaehlerSectionsEquiv W rfl (hU.basicOpen f)), fun k ↦ ?_⟩
  rw [Basis.map_apply, KaehlerDifferential.basisOfIsLocalizationMvPolynomial_apply,
    Scheme.Hom.kaehlerSectionsEquiv_D, ← Scheme.Hom.sectionsD_map]
  congr 1
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingEquiv.symm_symm,
    RingEquiv.toRingHom_eq_coe]
  erw [chartRingEquiv_X]

/-! ### The ratios of homogeneous coordinates on the overlaps of the standard opens -/

section Ratio

open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n} {S : Scheme.{u}}

lemma val_awayMap_awayXRatio {i k : n} {e : ℕ} {g : MvPolynomial n (ULift.{u} ℤ)}
    (hg : g ∈ homogeneousSubmodule n (ULift.{u} ℤ) e) {x : MvPolynomial n (ULift.{u} ℤ)}
    (hx : x = X i * g) :
    (awayMap _ hg hx (awayXRatio (ULift.{u} ℤ) i k)).val =
      Localization.mk (X k * g) ⟨x, Submonoid.mem_powers x⟩ := by
  rw [awayXRatio, awayMap_mk, Away.val_mk]
  simp

/-- The restriction of `x_k / xᵢ` to an open contained in the preimage of `D₊(x)`, for a
multiple `x = Tᵢ g` of `Tᵢ`, computed in the degree-zero part of `ℤ[T]ₓ`. -/
lemma map_coordRatio {i k : n} {e : ℕ} {g : MvPolynomial n (ULift.{u} ℤ)}
    (hg : g ∈ homogeneousSubmodule n (ULift.{u} ℤ) e) {x : MvPolynomial n (ULift.{u} ℤ)}
    (hx : x = X i * g) {W : ℙ(n; S).Opens}
    (hW : W ≤ toProjInt n S ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule n (ULift.{u} ℤ)) x)
    (hW' : W ≤ standardOpen n S i) :
    ℙ(n; S).presheaf.map (homOfLE hW').op (coordRatio n S i k) =
      (Proj.awayToSection _ x ≫ (toProjInt n S).appLE _ W hW)
        (awayMap _ hg hx (awayXRatio (ULift.{u} ℤ) i k)) := by
  have key : Proj.awayToSection _ (X i) ≫ (toProjInt n S).app _ ≫
      ℙ(n; S).presheaf.map (homOfLE hW').op =
      CommRingCat.ofHom (awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        (toProjInt n S).appLE _ W hW := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Proj.awayMap_awayToSection_assoc,
      Scheme.Hom.map_appLE]
  have := ConcreteCategory.congr_hom key (awayXRatio (ULift.{u} ℤ) i k)
  simp only [CategoryTheory.comp_apply] at this ⊢
  exact this

@[simp]
lemma coordRatio_self (i : n) : coordRatio n S i i = 1 := by
  rw [coordRatio, awayXRatio_self, map_one, map_one]

/-- **The change of affine coordinates** `x_k / xᵢ = (x_k / xⱼ) (xⱼ / xᵢ)` on an open contained
in `Uᵢ ∩ Uⱼ`. -/
lemma map_coordRatio_eq_mul {i j : n} {W : ℙ(n; S).Opens} (hi : W ≤ standardOpen n S i)
    (hj : W ≤ standardOpen n S j) (k : n) :
    ℙ(n; S).presheaf.map (homOfLE hi).op (coordRatio n S i k) =
      ℙ(n; S).presheaf.map (homOfLE hj).op (coordRatio n S j k) *
        ℙ(n; S).presheaf.map (homOfLE hi).op (coordRatio n S i j) := by
  have hXi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i
  have hXj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) j
  have hW := (le_inf hi hj).trans (standardOpen_inf_le (S := S) i j)
  rw [map_coordRatio hXj (x := X i * X j) rfl hW,
    map_coordRatio hXi (x := X i * X j) (by ring) hW,
    map_coordRatio hXj (x := X i * X j) rfl hW, ← map_mul]
  refine appLE_awayToSection_congr _ ?_
  rw [val_mul, val_awayMap_awayXRatio, val_awayMap_awayXRatio, val_awayMap_awayXRatio,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- `(xⱼ / xᵢ) (xᵢ / xⱼ) = 1` on `Uᵢ ∩ Uⱼ`: the restriction of the coordinate `xⱼ / xᵢ` of `Uᵢ`
is the inverse of the unit `ratioUnit n S i j = xᵢ / xⱼ`. -/
lemma map_coordRatio_eq_ratioUnit_inv (i j : n) :
    ℙ(n; S).presheaf.map (homOfLE (inf_le_left :
        standardOpen n S i ⊓ standardOpen n S j ≤ _)).op (coordRatio n S i j) =
      ((ratioUnit n S i j)⁻¹ : Γ(ℙ(n; S), standardOpen n S i ⊓ standardOpen n S j)ˣ) := by
  refine Units.eq_inv_of_mul_eq_one_left ?_
  have hXi := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i
  have hXj := X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (σ := n) j
  change ratio n S i j * _ = 1
  rw [← (show ℙ(n; S).presheaf.map (homOfLE le_rfl).op (ratio n S i j) = ratio n S i j from
      by simp),
    map_coordRatio hXj (x := X i * X j) rfl (standardOpen_inf_le i j),
    map_ratio hXi (x := X i * X j) (by ring) (standardOpen_inf_le i j), ← map_mul,
    ← map_one (Proj.awayToSection _ (X i * X j) ≫
      (toProjInt n S).appLE _ _ (standardOpen_inf_le i j)).hom]
  refine appLE_awayToSection_congr _ ?_
  rw [val_mul, val_awayMap_awayRatio, val_awayMap_awayXRatio, val_one, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

end Ratio

/-! ### The canonical module and its local generators -/

variable (S : Scheme.{u}) (d : ℕ)

/-- **The canonical module of projective space**: `ω_ℙ = ⋀ᵈ Ω¹_{ℙ/S}` for `ℙ = ℙ(n; S)`, where
`Nat.card n = d + 1`. -/
def canonicalModule : ℙ(n; S).Modules :=
  (ℙ(n; S) ↘ S).relativeDifferentials.exteriorPower d

variable {n S d} (e : n ≃ Fin (d + 1))

/-- The increasing enumeration `Fin d ≃ {k // k ≠ i}` of the indices other than `i`, for the
order on `n` transported from `Fin (d + 1)` along `e`. -/
def chartIndexEquiv (i : n) : Fin d ≃ {k : n // k ≠ i} :=
  (finSuccAboveEquiv (e i)).trans
    (e.symm.subtypeEquiv fun x ↦ by rw [ne_eq, ne_eq, Equiv.symm_apply_eq])

@[simp]
lemma coe_chartIndexEquiv (i : n) (m : Fin d) :
    (chartIndexEquiv e i m : n) = e.symm ((e i).succAbove m) := by
  simp [chartIndexEquiv, finSuccAboveEquiv_apply]

/-- **The local generator `ηᵢ` of the canonical module** on the standard open `Uᵢ = D₊(xᵢ)` of
`ℙ(n; Spec A)`: `ηᵢ = (-1)ⁱ ⋀_{k ≠ i} d(x_k / xᵢ)`, the wedge product being taken in increasing
order of `k`, for the order on `n` given by `e: n ≃ Fin (d + 1)` (and `i` read as `e i`). -/
def canonicalGenerator (i : n) : Γ(canonicalModule n (Spec (.of A)) d, standardOpen n _ i) :=
  ((-1 : Γ(ℙ(n; Spec (.of A)), standardOpen n _ i)) ^ (e i : ℕ)) •
    wedge fun m ↦ (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).sectionsD _
      (coordRatio n _ i (chartIndexEquiv e i m))

/-- The wedge product `⋀_{k ≠ i} d(x_k / xᵢ)` is a free generator of `ω_ℙ` on `Uᵢ`, since the
differentials `d(x_k / xᵢ)` form a basis of `Ω¹_{ℙ/A}` on the basic opens of `Uᵢ`. -/
lemma isFreeGenerator_wedge_sectionsD_coordRatio (i : n) :
    IsFreeGenerator (M := canonicalModule n (Spec (.of A)) d)
      (wedge fun m ↦ (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).sectionsD _
        (coordRatio n _ i (chartIndexEquiv e i m))) := by
  refine isFreeGenerator_wedge _ fun V hV x hx ↦ ?_
  obtain ⟨f, hfV, hxf⟩ := (isAffineOpen_standardOpen n _ i).exists_basicOpen_le ⟨x, hx⟩ (hV hx)
  obtain ⟨b, hb⟩ := exists_basis_relativeDifferentials_basicOpen n A i f
  refine ⟨_, hfV, hxf, b.reindex (chartIndexEquiv e i).symm, fun k ↦ ?_⟩
  rw [Basis.reindex_apply, Equiv.symm_symm, hb]

/-- **`ηᵢ` is a free generator of `ω_ℙ` on `Uᵢ`**; in particular `ω_ℙ` is invertible. -/
lemma isFreeGenerator_canonicalGenerator (i : n) :
    IsFreeGenerator (canonicalGenerator A e i) := by
  have h := (isFreeGenerator_wedge_sectionsD_coordRatio A e i).units_smul ((-1) ^ (e i : ℕ))
  rwa [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h


/-- **The transition rule for the local generators of `ω_ℙ`**: on the overlap `Uᵢ ∩ Uⱼ` of two
distinct standard opens of `ℙ(n; Spec A)`, `ηᵢ = (xᵢ / xⱼ)^{-(d+1)} • ηⱼ`, where
`(xᵢ / xⱼ)^{-(d+1)} = transitionUnit n _ (-d-1) i j`. -/
theorem map_canonicalGenerator_eq_transitionUnit_smul {i j : n} (hij : i ≠ j) :
    (canonicalModule n (Spec (.of A)) d).presheaf.map (homOfLE (inf_le_left :
        standardOpen n _ i ⊓ standardOpen n _ j ≤ _)).op
        (canonicalGenerator A e i) =
      (transitionUnit n (Spec (.of A)) (-(d : ℤ) - 1) i j).1 •
        (canonicalModule n (Spec (.of A)) d).presheaf.map (homOfLE inf_le_right).op
          (canonicalGenerator A e j) := by
  set X := ℙ(n; Spec (.of A))
  set g := X ↘ Spec (.of A)
  set V := standardOpen n (Spec (.of A)) i ⊓ standardOpen n (Spec (.of A)) j
  have hi : V ≤ standardOpen n _ i := inf_le_left
  have hj : V ≤ standardOpen n _ j := inf_le_right
  let y (k : Fin (d + 1)) : Γ(X, V) := X.presheaf.map (homOfLE hi).op (coordRatio n _ i (e.symm k))
  let z (k : Fin (d + 1)) : Γ(X, V) := X.presheaf.map (homOfLE hj).op (coordRatio n _ j (e.symm k))
  have hy (k : Fin (d + 1)) (_ : k ≠ e i) (_ : k ≠ e j) : y k = z k * y (e j) := by
    simp only [y, z, Equiv.symm_apply_apply]
    exact map_coordRatio_eq_mul hi hj _
  have hinv : z (e i) * y (e j) = 1 := by
    have h := map_coordRatio_eq_mul hi hj i
    rw [coordRatio_self, map_one] at h
    simp only [y, z, Equiv.symm_apply_apply]
    exact h.symm
  have key := exteriorPower.ιMulti_chart_transition (g.sectionsD V) (g.sectionsD_mul V) y z
    (e.injective.ne hij) hy hinv
  have hyq : y (e j) ^ (d + 1) = (transitionUnit n _ (-(d : ℤ) - 1) i j).1 := by
    have h : -(d : ℤ) - 1 = -((d + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [y, Equiv.symm_apply_apply]
    rw [map_coordRatio_eq_ratioUnit_inv, transitionUnit, h, zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val]
  have hmap (k : n) (W : X.Opens) (hW : W ≤ standardOpen n _ k) :
      (canonicalModule n (Spec (.of A)) d).presheaf.map (homOfLE hW).op
          (canonicalGenerator A e k) =
        (-1 : Γ(X, W)) ^ (e k : ℕ) • wedge fun m ↦ g.sectionsD W
          (X.presheaf.map (homOfLE hW).op (coordRatio n _ k (e.symm ((e k).succAbove m)))) := by
    rw [canonicalGenerator, Scheme.Modules.map_smul, map_pow, map_neg, map_one]
    congr 1
    erw [wedge_map]
    congr 1
    funext m
    rw [g.sectionsD_map, coe_chartIndexEquiv]
  rw [hmap, hmap, ← hyq, smul_smul, wedge, wedge, ← toSheafificationObj_app_smul,
    ← toSheafificationObj_app_smul]
  exact congrArg _ key

/-- **Families of free generators with the same transition units.** Let `e i`, `f i` be free
generators of `M`, `N` on `U i`, and suppose that on each overlap `U i ⊓ U j` (`i ≠ j`) both
satisfy `e i = c i j • e j` and `f i = c i j • f j` for the same functions `c i j`. Then they have
the same transition functions on every open of `U i ⊓ U j`, as required by
`Scheme.Modules.isoOfIsFreeGenerator`. -/
lemma _root_.AlgebraicGeometry.Scheme.Modules.transition_of_eq_smul {X : Scheme.{u}}
    {M N : X.Modules} {ι : Type*} {U : ι → X.Opens} {e : ∀ i, Γ(M, U i)} {f : ∀ i, Γ(N, U i)}
    (he : ∀ i, IsFreeGenerator (e i)) (c : ∀ i j, Γ(X, U i ⊓ U j))
    (hce : ∀ i j, i ≠ j → M.presheaf.map (homOfLE inf_le_left).op (e i) =
      c i j • M.presheaf.map (homOfLE inf_le_right).op (e j))
    (hcf : ∀ i j, i ≠ j → N.presheaf.map (homOfLE inf_le_left).op (f i) =
      c i j • N.presheaf.map (homOfLE inf_le_right).op (f j))
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W))
    (hab : a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j)) :
    a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j) := by
  by_cases hij : i = j
  · subst hij
    rw [((he i).map hi).smul_left_injective hab]
  · have hW : W ≤ U i ⊓ U j := le_inf hi hj
    have key {P : X.Modules} {s : ∀ i, Γ(P, U i)}
        (hs : P.presheaf.map (homOfLE inf_le_left).op (s i) =
          c i j • P.presheaf.map (homOfLE inf_le_right).op (s j)) :
        P.presheaf.map (homOfLE hi).op (s i) =
          X.presheaf.map (homOfLE hW).op (c i j) • P.presheaf.map (homOfLE hj).op (s j) := by
      rw [← presheaf_map_homOfLE_map_homOfLE inf_le_left hW, hs, map_smul,
        presheaf_map_homOfLE_map_homOfLE]
    have hb : a * X.presheaf.map (homOfLE hW).op (c i j) = b := by
      refine ((he j).map hj).smul_left_injective ?_
      dsimp only
      rw [mul_smul, ← key (hce i j hij), hab]
    rw [key (hcf i j hij), smul_smul, hb]

/-- **The canonical module of projective space is a twisting sheaf**: `ω_ℙ ≅ 𝒪(-d-1)` on
`ℙ = ℙ(n; Spec A)`, `Nat.card n = d + 1`, sending the local generator
`ηᵢ = (-1)ⁱ ⋀_{k ≠ i} d(x_k / xᵢ)` of `ω_ℙ` to the generator `eᵢ^{(-d-1)}` of `𝒪(-d-1)` on each
standard open `Uᵢ`. The signs `(-1)ⁱ` refer to the order on `n` given by `e: n ≃ Fin (d + 1)`. -/
def canonicalModuleIsoTwist :
    canonicalModule n (Spec (.of A)) d ≅ twist n (Spec (.of A)) (-(d : ℤ) - 1) :=
  isoOfIsFreeGenerator (iSup_standardOpen n _) (isFreeGenerator_canonicalGenerator A e)
    (isFreeGenerator_twistGenerator n _ _)
    (transition_of_eq_smul (isFreeGenerator_canonicalGenerator A e)
      (fun i j ↦ (transitionUnit n _ (-(d : ℤ) - 1) i j).1)
      (fun _ _ hij ↦ map_canonicalGenerator_eq_transitionUnit_smul A e hij)
      (fun i j _ ↦ map_twistGenerator_eq_transitionUnit_smul n _ _ i j))

/-- **`ω_ℙ ≅ 𝒪(-d-1)` sends `ηᵢ` to `eᵢ^{(-d-1)}`** on the standard open `Uᵢ`. -/
lemma canonicalModuleIsoTwist_hom_app (i : n) :
    (canonicalModuleIsoTwist A e).hom.app (standardOpen n _ i) (canonicalGenerator A e i) =
      twistGenerator n _ (-(d : ℤ) - 1) i :=
  isoOfIsFreeGenerator_hom_app _ _ _ _ i

/-- **Local description of `canonicalModuleIsoTwist`**: on an open `W ⊆ Uᵢ`, it sends
`r • ηᵢ|_W` to `r • eᵢ^{(-d-1)}|_W`. -/
lemma canonicalModuleIsoTwist_hom_app_smul (i : n) {W : ℙ(n; Spec (.of A)).Opens}
    (hW : W ≤ standardOpen n _ i) (r : Γ(ℙ(n; Spec (.of A)), W)) :
    (canonicalModuleIsoTwist A e).hom.app W
        (r • (canonicalModule n (Spec (.of A)) d).presheaf.map (homOfLE hW).op
          (canonicalGenerator A e i)) =
      r • (twist n (Spec (.of A)) (-(d : ℤ) - 1)).presheaf.map (homOfLE hW).op
        (twistGenerator n _ (-(d : ℤ) - 1) i) :=
  isoOfIsFreeGenerator_hom_app_smul _ _ _ _ i hW r

end AlgebraicGeometry.ProjectiveSpace
