/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
public import WeilConjectures.AlgebraicGeometry.Curve.Jacobian
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Kummer
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Smooth affine curves over an algebraically closed field

Let `C` be a smooth affine connected curve over an algebraically closed field `k`. This file
collects the inputs of the computation of the étale cohomology of `C`
(`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth`):

* the normalization of `C` in a finite extension of its function field is again a smooth affine
  connected curve, finite over `C`;
* the group `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite;
* `Pic(C)` is a quotient of the `k`-points of the Jacobian of the smooth compactification of `C`
  by a finitely generated subgroup; hence it is `n`-divisible with finite `n`-torsion for `n`
  prime to `char k`;
* `H²(C, ℤ/ℓ) = 0` for every prime `ℓ`; the vanishing of `H²(C, η_* M)` for torsion sheaves `M`
  on the generic point `η` of `C` is in `WeilConjectures.AlgebraicGeometry.Curve.AffineGeneric`.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.normalizationIn`: the normalization in a finite extension.
- `AlgebraicGeometry.IsConnectedCurve.finite_units_quotient`: `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite.
- `AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`: `Pic(C)` is
  `n`-divisible with finite `n`-torsion.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_constantZMod`: `H²(C, ℤ/ℓ) = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **An affine curve model for a finite extension.** Let `C` be a smooth integral affine
connected curve over an algebraically closed field `k`, and `L` a finite extension of its function
field. Then the normalization `h : C' ⟶ C` of `C` in `L`
(`AlgebraicGeometry.Scheme.normalizationIn`) is finite, `C'` is a smooth affine connected curve
over `k` (it is integral, `AlgebraicGeometry.Scheme.Hom.normalization` of an integral scheme), and
the morphism `Spec L ⟶ C'` is the generic point of `C'`, identifying `L` with the function field
of `C'`.

Finiteness is `AlgebraicGeometry.Scheme.isFinite_fromNormalizationIn`, so `C'` is affine and has
dimension one. Its local rings are integrally closed, hence `C'` is regular, hence smooth over the
perfect field `k` (`AlgebraicGeometry.smooth_of_isRegular`).
(blueprint: `theorem-cohomology-curves--2`) -/
theorem normalizationIn (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    [IsIntegral C] (L : Type u) [Field L] [Algebra C.functionField L]
    [FiniteDimensional C.functionField L] :
    IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
      IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧ Smooth (C.fromNormalizationIn L ≫ f) ∧
      ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
        e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
          (C.fromSpecOfAlgebraFunctionField L).toNormalization := by
  set h := C.fromNormalizationIn L
  have : IsFinite h := C.isFinite_fromNormalizationIn L f
  have : IsAffine (C.normalizationIn L) := isAffine_of_isAffineHom h
  -- `h` is surjective: it is closed, and dominant since `Spec L ⟶ C` is.
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap C.functionField L))) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y⟩ : Nonempty (Spec (.of L)) := inferInstance
    exact subset_closure ⟨y, Subsingleton.elim _ _⟩
  have : IsDominant ((C.fromSpecOfAlgebraFunctionField L).toNormalization ≫ h) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
  have : IsDominant h := .of_comp (C.fromSpecOfAlgebraFunctionField L).toNormalization _
  have hdim : topologicalKrullDim (C.normalizationIn L) = 1 := by
    rw [h.topologicalKrullDim_eq_of_surjective]
    exact IsConnectedCurve.krullDim_eq_one (f := f)
  have : IsLocallyNoetherian (C.normalizationIn L) :=
    LocallyOfFiniteType.isLocallyNoetherian (h ≫ f)
  -- The local rings of `Spec L` are integrally closed, hence so are those of `C'`.
  have hK (x : Spec (.of L)) : IsIntegrallyClosed ((Spec (.of L)).presheaf.stalk x) := by
    let := TopCat.Presheaf.algebra_section_stalk (Spec (.of L)).presheaf
      (⟨x, trivial⟩ : (⊤ : (Spec (.of L)).Opens))
    have := (isAffineOpen_top (Spec (.of L))).isLocalization_stalk ⟨x, trivial⟩
    have : IsIntegrallyClosed Γ(Spec (.of L), ⊤) :=
      .of_equiv (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.symm
    exact isIntegrallyClosed_of_isLocalization _ _
      ((isAffineOpen_top _).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
  have : IsRegular (C.normalizationIn L) := IsRegular.of_isIntegrallyClosed_stalk
    (fun y ↦ ⟨inferInstance,
      (C.fromSpecOfAlgebraFunctionField L).isIntegrallyClosed_stalk_normalization hK y⟩) hdim.le
  have : Smooth (h ≫ f) := smooth_of_isRegular _
  exact ⟨inferInstance, inferInstance,
    { krullDim_le_one := hdim.le
      connectedSpace := inferInstance
      krullDim_eq_one := hdim }, inferInstance,
    C.exists_iso_toNormalization_normalizationIn L⟩

/-- **Units modulo `n`-th powers on an affine curve.** Let `C` be a smooth affine connected curve
over an algebraically closed field `k` and `n ≥ 1`. Then `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite.

Let `C ⊆ C̄` be the smooth compactification, with finite complement `S`. The divisor of a unit
of `𝒪(C)` is supported on `S`, and it vanishes only for the units which extend to `C̄`, i.e. for
`k^×` (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isAlgClosed`). So `𝒪(C)ˣ / k^×` is a
subgroup `Λ` of the free abelian group `ℤ^S`, and `𝒪(C)ˣ / 𝒪(C)ˣⁿ ≅ Λ / nΛ` since every element of
`k^×` is an `n`-th power.
(blueprint: `proposition-cohomology-smooth-affine-curve--2`) -/
theorem finite_units_quotient (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsAffine C] (n : ℕ) (hn : 0 < n) :
    Finite (Additive Γ(C, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) n).range) := by
  obtain ⟨c, hZ, hsm, hfin, hcl⟩ := IsConnectedCurve.exists_smooth_properCompactification f
  have := c.isProper
  have := c.isOpenImmersion
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have := IsConnectedCurve.nonempty f
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IrreducibleSpace c.Z := IsRegular.irreducibleSpace c.Z
  have : IsReduced c.Z := isReduced_of_isReduced_stalk c.Z
  have : IsIntegral c.Z := isIntegral_of_irreducibleSpace_of_isReduced c.Z
  have : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := c.g))
  set V : c.Z.Opens := c.i ''ᵁ ⊤
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have : Nonempty V := ⟨⟨c.i x₀, x₀, trivial, rfl⟩⟩
  have : Nonempty (⊤ : c.Z.Opens) := ⟨⟨c.i x₀, trivial⟩⟩
  -- the inclusion `ρ : Γ(C, 𝒪) ⟶ k(C̄)`
  let ρ : Γ(C, ⊤) ⟶ c.Z.functionField := (c.i.appIso ⊤).inv ≫ c.Z.germToFunctionField V
  have hρ : Function.Injective ρ := by
    intro a b h
    exact (c.i.appIso ⊤).commRingCatIsoToRingEquiv.symm.injective
      (c.Z.germToFunctionField_injective V h)
  have hρ0 (u : Γ(C, ⊤)ˣ) : ρ u ≠ 0 := (u.isUnit.map ρ.hom).ne_zero
  -- sections over `C` lie in the local rings of `C̄` at points of `C`
  have hρV (a : Γ(C, ⊤)) (x : c.Z) (hx : x ∈ V) :
      ρ a ∈ Set.range (algebraMap (c.Z.presheaf.stalk x) c.Z.functionField) :=
    ⟨c.Z.presheaf.germ V x hx ((c.i.appIso ⊤).inv a),
      Scheme.algebraMap_germ_eq_germToFunctionField _ hx _⟩
  -- the points of the boundary
  set S := {x : c.Z // x ∉ V}
  have : Finite S := by
    refine Set.Finite.to_subtype (s := {x | x ∉ V}) (hfin.subset fun x hx hr ↦ hx ?_)
    obtain ⟨y, hy⟩ := hr
    exact ⟨y, trivial, hy⟩
  have hS (P : S) : IsClosed {P.1} := hcl P.1 fun ⟨y, hy⟩ ↦ P.2 ⟨y, trivial, hy⟩
  have hS1 (P : S) : Order.coheight P.1 = 1 := by
    have h := ringKrullDim_stalk_eq_coheight P.1
    rw [Scheme.ringKrullDim_stalk_eq_one_of_isClosed c.g (hS P)] at h
    exact_mod_cast h.symm
  -- the divisor map `Γ(C, 𝒪)ˣ ⟶ ℤ^S`
  let D : Additive Γ(C, ⊤)ˣ →+ (S → ℤ) :=
    { toFun u P := c.Z.ord (ρ u.toMul) P.1
      map_zero' := by
        ext P
        simp only [toMul_zero, Units.val_one, map_one, Pi.zero_apply]
        have h := Scheme.ord_mul (X := c.Z) (x := P.1) (one_ne_zero (α := c.Z.functionField))
          one_ne_zero
        rw [_root_.mul_one] at h
        omega
      map_add' u v := by
        ext P
        simp only [toMul_add, Units.val_mul, map_mul, Pi.add_apply]
        exact Scheme.ord_mul (hρ0 _) (hρ0 _) }
  -- the constants
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have : IsProper (c.Z ↘ Spec (.of k)) := c.isProper
  let κ : k →+* Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hκ (b : k) : ρ (κ b) =
      c.Z.germToFunctionField ⊤ (Scheme.globalSectionsRingHom k (X := c.Z) b) := by
    have e : c.Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (c.i.appIso ⊤).hom =
        c.i.appTop := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE]
      rfl
    have e' : (c.i.appIso ⊤).inv (κ b) =
        c.Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          (Scheme.globalSectionsRingHom k (X := c.Z) b) := by
      rw [← Iso.eq_comp_inv] at e
      change (c.i.appIso ⊤).inv (f.appTop _) = _
      rw [congrArg Scheme.Hom.appTop c.comm, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← CommRingCat.comp_apply _ (c.i.appIso ⊤).inv, ← e]
      rfl
    change c.Z.germToFunctionField V ((c.i.appIso ⊤).inv (κ b)) = _
    rw [e']
    exact c.Z.presheaf.germ_res_apply _ _ _ _
  -- the kernel of `D` consists of constants, which are `n`-th powers
  have hker : D.ker ≤ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) n).range := by
    intro u hu
    rw [AddMonoidHom.mem_ker] at hu
    have hg (x : c.Z) (_ : x ∈ (⊤ : c.Z.Opens)) :
        ρ u.toMul ∈ Set.range (algebraMap (c.Z.presheaf.stalk x) c.Z.functionField) := by
      by_cases hx : x ∈ V
      · exact hρV _ x hx
      · let P : S := ⟨x, hx⟩
        have h0 : c.Z.ord (ρ u.toMul) x = 0 := congr_fun hu P
        obtain ⟨_, _⟩ := Scheme.isDiscreteValuationRing_stalk_of_isClosed c.g (hS P)
        rw [Scheme.ord_eq_iff (hS1 P) (hρ0 _)] at h0
        have hmem : ρ u.toMul ∈ MonoidHom.mker (Ring.ordFrac (c.Z.presheaf.stalk x)) := h0
        rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
        obtain ⟨r, -, hr⟩ := hmem
        exact ⟨r, hr⟩
    obtain ⟨s, hs⟩ := Scheme.exists_germToFunctionField_eq ⊤ _ hg
    obtain ⟨a, rfl⟩ := (Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom
      (k := k) (X := c.Z)).2 s
    have hu' : (u.toMul : Γ(C, ⊤)) = κ a := hρ (hs.symm.trans (hκ a).symm)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a hn
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hρ0 u.toMul
      rw [hu', ← hb, zero_pow hn.ne', map_zero, map_zero]
    refine ⟨.ofMul (hb0.isUnit.map κ).unit, ?_⟩
    rw [zsmulAddGroupHom_apply, natCast_zsmul, ← ofMul_pow]
    change Additive.ofMul _ = Additive.ofMul u.toMul
    congr 1
    ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hb, hu']
  exact AddMonoidHom.finite_quotient_range_zsmul_of_ker_le D hn.ne' hker

/-- **`Pic` of an affine curve as a quotient of the Jacobian.** Let `C` be a smooth affine
connected curve over an algebraically closed field `k`. Then there are a smooth proper connected
compactification `C̄` of `C`, an abelian variety `J` over `k` representing the degree zero part
`Pic⁰_{C̄/k}` of the Picard functor of `C̄` compatibly with the group laws (the Jacobian of `C̄`),
and a finitely generated subgroup `Λ ⊆ J(k)` with `Pic(C) ≅ J(k) / Λ`.

The restriction `Pic(C̄) ⟶ Pic(C)` is surjective with kernel generated by the classes of the
points of `S = C̄ ∖ C` (`AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic`). Fixing
`P₀ ∈ S`, the splitting `Pic(C̄) = ℤ ⊕ Pic⁰(C̄)` of the degree
(`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`) identifies `Pic(C)` with
`Pic⁰(C̄) / Λ` for `Λ` generated by the classes `[P] - [P₀]`, `P ∈ S`, and
`Pic⁰(C̄) = J(k)` (`AlgebraicGeometry.exists_jacobian`). The group `Λ` is finitely generated
since `S` is finite.
(blueprint: `proposition-cohomology-smooth-affine-curve--3`, the presentation) -/
theorem exists_addEquiv_pic_quotient (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsAffine C] :
    ∃ (c : Compactification f) (J : Over (Spec (.of k))) (_ : GrpObj J) (_ : IsAbelianVariety J)
      (Λ : AddSubgroup (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J))),
      IsConnectedCurve c.g ∧ Smooth c.g ∧
        (∃ e : (picardFunctorDegree c.g 0).obj.RepresentableBy J, IsPicardZeroMul c.g e) ∧
        Λ.FG ∧
        Nonempty (Additive C.Pic ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ J) ⧸ Λ) := by
  classical
  obtain ⟨c, hconn, hsm, hfin, hcl⟩ := IsConnectedCurve.exists_smooth_properCompactification f
  have := c.isProper
  have := c.isOpenImmersion
  -- `C̄ = c.Z` and `C` are noetherian integral curves
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have := IsConnectedCurve.connectedSpace (f := f)
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one c.g
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one f
  have : IsProper (c.Z ↘ Spec (.of k)) := c.isProper
  have : IsCurve (c.Z ↘ Spec (.of k)) := inferInstanceAs (IsCurve c.g)
  have : IsCurve (C ↘ Spec (.of k)) := inferInstanceAs (IsCurve f)
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IrreducibleSpace c.Z := IsRegular.irreducibleSpace c.Z
  have : IsReduced c.Z := isReduced_of_isReduced_stalk c.Z
  have : IsIntegral c.Z := isIntegral_of_irreducibleSpace_of_isReduced c.Z
  have : CompactSpace c.Z := (quasiCompact_iff_compactSpace c.g).mp inferInstance
  have : IsNoetherian c.Z := ⟨⟩
  have : JacobsonSpace c.Z := LocallyOfFiniteType.jacobsonSpace c.g
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  have : IsNoetherian C := ⟨⟩
  -- the Jacobian of `C̄` and `Pic(C̄) ≅ ℤ × J(k)`
  obtain ⟨J, _, e, _, he, -, -, E, hE⟩ := Scheme.exists_jacobian_addEquiv_prod k c.Z
  set G := Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)
  obtain ⟨eC, -⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := C)
  obtain ⟨eX, heX⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := c.Z)
  -- `T : Div(C̄) → Pic(C̄) ≅ ℤ × J(k)`
  let T : c.Z.Divisor →+ ℤ × G := E.toAddMonoidHom.comp (Scheme.Divisor.toPic k c.Z)
  have hT (D : c.Z.Divisor) : T D = E (Scheme.Divisor.toPic k c.Z D) := rfl
  have hTker (D : c.Z.Divisor) : T D = 0 ↔ D ∈ c.Z.principalDivisors := by
    rw [hT, AddEquiv.map_eq_zero_iff]
    rw [← heX, AddEquiv.map_eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  have hTsurj : Function.Surjective T := by
    intro y
    obtain ⟨D, hD⟩ := QuotientAddGroup.mk_surjective (eX.symm (E.symm y))
    refine ⟨D, ?_⟩
    rw [hT, ← heX, hD, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hT1 (P : closedPoints c.Z) : (T (Finsupp.single P 1)).1 = 1 := by
    rw [hT, hE]
    simp only [Scheme.Divisor.toPic_single, one_smul, toMul_ofMul,
      Scheme.picDegreeHom_ofClosedPoint, toAdd_ofAdd]
  -- the boundary `S = C̄ ∖ C`, a finite nonempty set of closed points
  let S := {P : closedPoints c.Z // P.1 ∉ Set.range c.i}
  have : Finite S := by
    have := hfin.to_subtype
    exact Finite.of_injective (fun P : S ↦ (⟨P.1.1, P.2⟩ : ((Set.range c.i.base)ᶜ : Set c.Z)))
      fun P Q h ↦ Subtype.ext (Subtype.ext (by simpa using h))
  obtain ⟨x, hx⟩ : ∃ x, x ∉ Set.range c.i := by
    by_contra! h
    have : Surjective c.i := ⟨h⟩
    have : IsIso c.i := (isIso_iff_isOpenImmersion_and_surjective c.i).mpr ⟨inferInstance, ‹_›⟩
    have : IsProper f := c.comm ▸ inferInstance
    have h0 := (isFinite_of_isProper_of_isAffine f).2
    rw [IsConnectedCurve.krullDim_eq_one (f := f)] at h0
    exact absurd h0 (by decide)
  let P₀ : S := ⟨⟨x, hcl x hx⟩, hx⟩
  -- `ψ(a, g) = g - a • x₀` with `x₀` the class of `[P₀]` in `J(k)`, and `Λ = ⟨ψ [P] : P ∈ S⟩`
  let x₀ : G := (T (Finsupp.single P₀.1 1)).2
  let ψ : ℤ × G →+ G := AddMonoidHom.snd ℤ G - (zmultiplesHom G x₀).comp (AddMonoidHom.fst ℤ G)
  have hψ (y : ℤ × G) : ψ y = y.2 - y.1 • x₀ := rfl
  let v : S → G := fun P ↦ ψ (T (Finsupp.single P.1 1))
  let Λ : AddSubgroup G := AddSubgroup.closure (Set.range v)
  have hΛ : Λ.FG := AddSubgroup.isAddFG_iff.mpr ⟨(Set.finite_range v).toFinset, by simp [Λ]⟩
  let Θ : c.Z.Divisor →+ G ⧸ Λ := (QuotientAddGroup.mk' Λ).comp (ψ.comp T)
  -- `Θ` kills principal divisors and divisors supported on `S`
  have hΘS (D : c.Z.Divisor) (hD : Scheme.Divisor.comap c.i D = 0) : Θ D = 0 := by
    rw [Scheme.Divisor.comap_eq_zero_iff] at hD
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [map_finsuppSum]
    refine Finset.sum_eq_zero fun P hP ↦ ?_
    dsimp only
    rw [← Finsupp.smul_single_one, map_zsmul]
    have hP' : P.1 ∉ Set.range c.i := hD P (Finsupp.mem_support_iff.mp hP)
    have : Θ (Finsupp.single P 1) = 0 := by
      simp only [Θ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact AddSubgroup.subset_closure ⟨⟨P, hP'⟩, rfl⟩
    rw [this, smul_zero]
  have hΘker (D : c.Z.Divisor) (hD : Θ D = 0) :
      ∃ D₁ ∈ c.Z.principalDivisors, Scheme.Divisor.comap c.i (D - D₁) = 0 := by
    simp only [Θ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff] at hD
    obtain ⟨a, ha⟩ := AddSubgroup.mem_closure_range_iff.mp hD
    let DS : c.Z.Divisor := Finsupp.mapDomain Subtype.val a
    have hDS : ψ (T DS) = ψ (T D) := by
      have hDS' : DS = a.sum fun P n ↦ Finsupp.single P.1 n := rfl
      rw [hDS', map_finsuppSum, map_finsuppSum, ha]
      refine Finsupp.sum_congr fun P _ ↦ ?_
      rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul]
    set b := (T (D - DS)).1
    have hb : T (D - DS - Finsupp.single P₀.1 b) = 0 := by
      have h1 : ψ (T (D - DS)) = 0 := by
        calc ψ (T (D - DS)) = ψ (T D) - ψ (T DS) := by rw [map_sub, map_sub]
          _ = 0 := by rw [hDS, sub_self]
      rw [hψ, sub_eq_zero] at h1
      have h2 : T (Finsupp.single P₀.1 b) = (b, b • x₀) := by
        rw [← Finsupp.smul_single_one, map_zsmul]
        exact Prod.ext (by simp [hT1]) rfl
      rw [map_sub, h2]
      refine Prod.ext ?_ ?_
      · change (T (D - DS)).1 - b = 0
        exact sub_self _
      · change (T (D - DS)).2 - b • x₀ = 0
        rw [h1, sub_self]
    refine ⟨D - DS - Finsupp.single P₀.1 b, (hTker _).1 hb, ?_⟩
    rw [Scheme.Divisor.comap_eq_zero_iff]
    intro P hP hPr
    rw [show D - (D - DS - Finsupp.single P₀.1 b) = DS + Finsupp.single P₀.1 b by abel] at hP
    by_cases h₀ : P = P₀.1
    · exact P₀.2 (h₀ ▸ hPr)
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h₀, add_zero] at hP
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (f := Subtype.val)
        (s := a) (Finsupp.mem_support_iff.mpr hP))
      exact Q.2 hPr
  -- `Ξ : Div(C) → J(k) / Λ`, through the extension by zero `Div(C) → Div(C̄)`
  let ext : C.Divisor →+ c.Z.Divisor := Finsupp.mapDomain.addMonoidHom c.i.closedPointsMap
  have hext (D : C.Divisor) : Scheme.Divisor.comap c.i (ext D) = D := by
    ext P
    rw [Scheme.Divisor.comap_apply]
    exact Finsupp.mapDomain_apply_of_injective c.i.closedPointsMap_injective D P
  have hΘext (D : c.Z.Divisor) : Θ (ext (Scheme.Divisor.comap c.i D)) = Θ D := by
    rw [← sub_eq_zero, ← map_sub]
    exact hΘS _ (by rw [map_sub, hext, sub_self])
  let Ξ : C.Divisor →+ G ⧸ Λ := Θ.comp ext
  have hΞ : Function.Surjective Ξ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective Λ y
    obtain ⟨D, hD⟩ := hTsurj (0, g)
    refine ⟨Scheme.Divisor.comap c.i D, ?_⟩
    change Θ (ext _) = _
    rw [hΘext]
    simp [Θ, hD, hψ]
  let Φ := (c.i.functionFieldIso.commRingCatIsoToRingEquiv : c.Z.functionField ≃+* _)
  have hker : C.principalDivisors = Ξ.ker := by
    ext D
    rw [AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨h, rfl⟩
      let g : Additive c.Z.functionFieldˣ := .ofMul (Units.map Φ.symm.toMonoidHom h.toMul)
      have hg : Scheme.Divisor.comap c.i (c.Z.div g) = C.div h := by
        rw [Scheme.Divisor.comap_div]
        congr 1
        ext
        exact Φ.apply_symm_apply _
      change Θ (ext _) = 0
      rw [← hg, hΘext]
      simp [Θ, (hTker _).2 ⟨g, rfl⟩]
    · intro hD
      obtain ⟨D₁, ⟨g, rfl⟩, hD₁⟩ := hΘker (ext D) hD
      rw [map_sub, hext, sub_eq_zero, Scheme.Divisor.comap_div] at hD₁
      exact ⟨_, hD₁.symm⟩
  exact ⟨c, J, inferInstance, inferInstance, Λ, hconn, hsm, ⟨e, he⟩, hΛ,
    ⟨eC.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Ξ hΞ))⟩⟩

/-- **`Pic` of an affine curve is divisible with finite torsion.** Let `C` be a smooth affine
connected curve over an algebraically closed field `k` and `n` prime to `char k`. Then `Pic(C)`
is `n`-divisible and `Pic(C)[n]` is finite.

By `AlgebraicGeometry.IsConnectedCurve.exists_addEquiv_pic_quotient`, `Pic(C) ≅ J(k) / Λ` for an
abelian variety `J` and a finitely generated subgroup `Λ`. The group `J(k)` is divisible with
finite `n`-torsion (`AlgebraicGeometry.abelianVariety_estimate_of_isAlgClosed`), hence so is its
quotient by `Λ` (`AddSubgroup.finite_torsionBy_quotient`).
(blueprint: `proposition-cohomology-smooth-affine-curve--3`) -/
theorem surjective_zsmul_pic_and_finite_torsionBy (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Surjective (zsmulAddGroupHom (α := Additive C.Pic) n) ∧
      Finite (AddSubgroup.torsionBy (Additive C.Pic) n) := by
  obtain ⟨c, J, _, _, Λ, -, -, -, hΛ, ⟨e⟩⟩ := exists_addEquiv_pic_quotient f
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hp : ¬ ringChar k ∣ n := fun h ↦ hn ((ringChar.spec k n).2 h)
  obtain ⟨hfin, -, hdiv, -, -⟩ := abelianVariety_estimate_of_isAlgClosed (ringChar k) J
  set G := Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)
  have hG : Function.Surjective (zsmulAddGroupHom (α := G) n) := by
    intro x
    obtain ⟨a, ha⟩ := hdiv n (Nat.pos_of_ne_zero hn0) x.toMul
    refine ⟨.ofMul a, ?_⟩
    rw [zsmulAddGroupHom_apply, natCast_zsmul, ← ofMul_pow, show a ^ n = x.toMul from ha]
    rfl
  have : NeZero n := ⟨hn0⟩
  obtain ⟨eJ⟩ := hfin n (Nat.pos_of_ne_zero hn0) hp
  have : Finite (AddSubgroup.torsionBy G n) := .of_equiv _ eJ.toEquiv.symm
  have hQ := AddSubgroup.finite_torsionBy_quotient Λ hn0 hG hΛ
  refine ⟨fun y ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (QuotientAddGroup.mk'_surjective Λ).comp hG (e y)
    refine ⟨e.symm (QuotientAddGroup.mk' Λ x), ?_⟩
    simp only [zsmulAddGroupHom_apply, Function.comp_apply] at hx ⊢
    rw [← map_zsmul, ← map_zsmul, hx, AddEquiv.symm_apply_apply]
  · refine Finite.of_injective (β := AddSubgroup.torsionBy (G ⧸ Λ) n)
      (fun x ↦ ⟨e x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩) fun x y hxy ↦ ?_
    · rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero]
    · exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

/-- **Second cohomology of `ℤ/ℓ` on an affine curve.** Let `C` be a smooth affine connected curve
over an algebraically closed field `k` and `ℓ` a prime. Then `H²(C_ét, ℤ/ℓ) = 0`.

If `ℓ ≠ char k`, a primitive `ℓ`-th root of unity identifies `ℤ/ℓ` with `μ_ℓ`
(`AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`), and the Kummer sequence gives
`H²(C, μ_ℓ) ≅ Pic(C) / ℓ`
(`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth`), which
vanishes as `Pic(C)` is `ℓ`-divisible
(`AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`). If
`ℓ = char k`, this is the Artin–Schreier vanishing
`AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`.
(blueprint: `theorem-cohomology-curves--2`) -/
theorem subsingleton_sheafH_two_constantZMod (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (Sheaf.H (C.constantZMod ℓ) 2) := by
  by_cases hℓ : (ℓ : k) = 0
  · refine C.subsingleton_sheafH_constantZMod_of_isAffine ℓ ?_ 2 le_rfl
    simpa using congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom hℓ
  have : NeZero (ℓ : k) := ⟨hℓ⟩
  have : NeZero ℓ := .of_neZero_natCast k
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k ℓ
  obtain ⟨e⟩ := IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two_of_smooth f ℓ hℓ
  obtain ⟨ePic⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  have hdiv := (surjective_zsmul_pic_and_finite_torsionBy f hℓ).1
  have htop : (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (ℓ : ℤ)).range = ⊤ := by
    refine AddMonoidHom.range_eq_top.2 fun y ↦ ?_
    obtain ⟨x, hx⟩ := hdiv (ePic.symm y)
    refine ⟨ePic x, ?_⟩
    simp only [zsmulAddGroupHom_apply] at hx ⊢
    rw [← map_zsmul, hx, AddEquiv.apply_symm_apply]
  have : Subsingleton (C.CohomologicalPicardGroup ⧸
      (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (ℓ : ℤ)).range) := by
    rw [htop]
    exact QuotientAddGroup.subsingleton_quotient_top
  have e' := ((Sheaf.functorH _ 2).mapIso
    (C.constantZModIsoRootsOfUnitySheaf ℓ f hζ)).addCommGroupIsoToAddEquiv
  exact (e'.trans e).subsingleton

end AlgebraicGeometry.IsConnectedCurve
