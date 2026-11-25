/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate

/-!
# The order of `H¹(C, ℤ/n)` for a smooth affine curve

Let `C` be a smooth affine connected curve over an algebraically closed field `k`, with a smooth
proper connected compactification `C ⊆ C̄` of genus `g` whose boundary `S = C̄ ∖ C` has `r`
points, and let `n` be prime to `char k`. Then `|H¹(C_ét, ℤ/n)| = n ^ (2g + r - 1)`.

The Kummer sequence gives `|H¹(C, ℤ/n)| = |𝒪(C)ˣ / n| · |Pic(C)[n]|`, and the divisor map gives
an exact sequence `0 → 𝒪(C)ˣ / kˣ → ℤ^S → Pic(C̄) → Pic(C) → 0`. Since `kˣ` is divisible,
`Pic(C̄)[n] ≅ (ℤ/n)^{2g}` and `Pic(C̄) / n ≅ ℤ/n`, the formula follows from the multiplicativity of
`|A / nA| / |A[n]|` in short exact sequences
(`AddSubgroup.natCard_quotient_range_zsmul_mul_eq`).

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.exists_units_pic_presentation`: the exact sequence
  `0 → 𝒪(C)ˣ / kˣ → ℤ^S → Pic(C̄) → Pic(C) → 0`.
- `AlgebraicGeometry.IsConnectedCurve.natCard_sheafH_one_constantZMod_mul`:
  `|H¹(C, ℤ/n)| · n = n ^ (r + 2g)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Units and `Pic` of an affine curve.** Let `C` be a smooth affine connected curve over an
algebraically closed field `k`, and `C ⊆ C̄` a smooth proper connected compactification with
boundary `S` (as a set of closed points). Then there are homomorphisms
`D : 𝒪(C)ˣ ⟶ ℤ^S` (the orders of a unit at the points of `S`) and `a : ℤ^S ⟶ Pic(C̄)` (the
class of a divisor supported on `S`) such that the image of `D` is the kernel of `a`, the kernel
of `D` (the constants `kˣ`) consists of `n`-th powers for every `n ≥ 1`, and
`Pic(C) ≅ Pic(C̄) / a(ℤ^S)`.
(blueprint: `proposition-cohomology-smooth-affine-curve--3`,
`proposition-cohomology-smooth-affine-curve--2`) -/
theorem exists_units_pic_presentation (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    [IsAffine C] (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g] :
    ∃ (D : Additive Γ(C, ⊤)ˣ →+ ({P : closedPoints c.Z // P.1 ∉ Set.range c.i} → ℤ))
      (a : ({P : closedPoints c.Z // P.1 ∉ Set.range c.i} → ℤ) →+ Additive c.Z.Pic),
      D.range = a.ker ∧
        (∀ n : ℕ, 0 < n → D.ker ≤ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) n).range) ∧
        Nonempty (Additive C.Pic ≃+ Additive c.Z.Pic ⧸ a.range) ∧
        Finite {P : closedPoints c.Z // P.1 ∉ Set.range c.i} := by
  classical
  have := c.isProper
  have := c.isOpenImmersion
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have := IsConnectedCurve.connectedSpace (f := f)
  have := IsConnectedCurve.nonempty f
  have : SmoothOfRelativeDimension 1 c.g := IsConnectedCurve.smoothOfRelativeDimension_one c.g
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
  have : Scheme.GlobalSectionsBijective k c.Z := Scheme.GlobalSectionsBijective.of_isAlgClosed
  have hdim : topologicalKrullDim c.Z = 1 := IsConnectedCurve.krullDim_eq_one (f := c.g)
  set V : c.Z.Opens := c.i ''ᵁ ⊤
  obtain ⟨x₀⟩ := ‹Nonempty C›
  have : Nonempty V := ⟨⟨c.i x₀, x₀, trivial, rfl⟩⟩
  have hV (x : c.Z) : x ∈ V ↔ x ∈ Set.range c.i :=
    ⟨fun ⟨y, _, hy⟩ ↦ ⟨y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, trivial, hy⟩⟩
  -- the boundary `S`
  set S := {P : closedPoints c.Z // P.1 ∉ Set.range c.i}
  -- the inclusion `ρ : Γ(C, 𝒪) ⟶ k(C̄)`
  let ρ : Γ(C, ⊤) ⟶ c.Z.functionField := (c.i.appIso ⊤).inv ≫ c.Z.germToFunctionField V
  have hρ : Function.Injective ρ := by
    intro a b h
    exact (c.i.appIso ⊤).commRingCatIsoToRingEquiv.symm.injective
      (c.Z.germToFunctionField_injective V h)
  have hρ0 (u : Γ(C, ⊤)ˣ) : ρ u ≠ 0 := (u.isUnit.map ρ.hom).ne_zero
  let ρU : Additive Γ(C, ⊤)ˣ →+ Additive c.Z.functionFieldˣ :=
    (Units.map ρ.hom.toMonoidHom).toAdditive
  have hρU (u : Additive Γ(C, ⊤)ˣ) : ((ρU u).toMul : c.Z.functionField) = ρ u.toMul := rfl
  -- the divisor map `D : Γ(C, 𝒪)ˣ ⟶ ℤ^S`
  let D : Additive Γ(C, ⊤)ˣ →+ (S → ℤ) :=
    (AddMonoidHom.pi fun P : S ↦ Finsupp.applyAddHom P.1).comp (c.Z.div.comp ρU)
  have hD (u : Additive Γ(C, ⊤)ˣ) (P : S) : D u P = c.Z.ord (ρ u.toMul) P.1.1 := rfl
  -- the divisors supported on `S`
  have hSfin : Finite S := by
    have hfin := V.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim.le
      ⟨c.i x₀, x₀, trivial, rfl⟩
    have := hfin.to_subtype
    exact Finite.of_injective (fun P : S ↦ (⟨P.1.1, fun h ↦ P.2 ((hV _).1 h)⟩ :
      ((V : Set c.Z)ᶜ : Set c.Z))) fun P Q h ↦ Subtype.ext (Subtype.ext (by simpa using h))
  let divS : (S → ℤ) →+ c.Z.Divisor :=
    (Finsupp.mapDomain.addMonoidHom Subtype.val).comp
      (Finsupp.linearEquivFunOnFinite ℤ ℤ S).symm.toAddMonoidHom
  have hdivS (v : S → ℤ) (Q : closedPoints c.Z) :
      divS v Q = if h : Q.1 ∈ Set.range c.i then 0 else v ⟨Q, h⟩ := by
    split_ifs with h
    · refine Finsupp.mapDomain_of_notMem_range _ _ fun ⟨P, hP⟩ ↦ ?_
      exact P.2 (hP ▸ h)
    · change Finsupp.mapDomain Subtype.val _ (Subtype.val (⟨Q, h⟩ : S)) = _
      rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
      rfl
  let ext : C.Divisor →+ c.Z.Divisor := Finsupp.mapDomain.addMonoidHom c.i.closedPointsMap
  have hext (E : C.Divisor) : Scheme.Divisor.comap c.i (ext E) = E := by
    ext P
    rw [Scheme.Divisor.comap_apply]
    exact Finsupp.mapDomain_apply_of_injective c.i.closedPointsMap_injective E P
  have hsplit (E : c.Z.Divisor) :
      E = ext (Scheme.Divisor.comap c.i E) + divS fun P ↦ E P.1 := by
    ext Q
    rw [Finsupp.add_apply, hdivS]
    split_ifs with h
    · obtain ⟨y, hy⟩ := h
      have hy' : y ∈ c.i ⁻¹' closedPoints c.Z := by rw [Set.mem_preimage, hy]; exact Q.2
      rw [c.i.isOpenEmbedding.preimage_closedPoints] at hy'
      have hQ : c.i.closedPointsMap ⟨y, hy'⟩ = Q := Subtype.ext hy
      rw [add_zero, ← hQ]
      change _ = Finsupp.mapDomain _ _ _
      rw [Finsupp.mapDomain_apply_of_injective c.i.closedPointsMap_injective,
        Scheme.Divisor.comap_apply]
    · suffices hz : ext (Scheme.Divisor.comap c.i E) Q = 0 by rw [hz, zero_add]
      refine Finsupp.mapDomain_of_notMem_range _ _ fun ⟨P, hP⟩ ↦ h ⟨P.1, congrArg Subtype.val hP⟩
  have hcomap_divS (v : S → ℤ) : Scheme.Divisor.comap c.i (divS v) = 0 := by
    rw [Scheme.Divisor.comap_eq_zero_iff]
    intro P hP
    rw [hdivS] at hP
    split_ifs at hP with h
    · exact absurd rfl hP
    · exact h
  -- the class map `a : ℤ^S ⟶ Pic(C̄)`
  obtain ⟨eX, heX⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := c.Z)
  obtain ⟨eC, heC⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := C)
  have htoPic (E : c.Z.Divisor) :
      Scheme.Divisor.toPic k c.Z E = 0 ↔ E ∈ c.Z.principalDivisors := by
    rw [← heX, AddEquiv.map_eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  let a : (S → ℤ) →+ Additive c.Z.Pic := (Scheme.Divisor.toPic k c.Z).comp divS
  -- the divisor of a unit of `𝒪(C)` is supported on `S`
  have hdivρ (u : Additive Γ(C, ⊤)ˣ) : c.Z.div (ρU u) = divS (D u) := by
    ext Q
    rw [Scheme.div_apply, hdivS, hρU]
    split_ifs with h
    · have hu : IsUnit ((c.i.appIso ⊤).inv u.toMul) := u.toMul.isUnit.map _
      exact Scheme.ord_of_isUnit hu ((hV _).2 h)
    · rfl
  refine ⟨D, a, ?_, fun n hn ↦ ?_, ?_, hSfin⟩
  · ext v
    rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨u, rfl⟩
      change Scheme.Divisor.toPic k c.Z (divS (D u)) = 0
      rw [← hdivρ, htoPic]
      exact ⟨_, rfl⟩
    · intro hv
      obtain ⟨h, hh⟩ := (htoPic _).1 hv
      have hord (y : c.Z) (hy : y ∈ V) : c.Z.ord (h.toMul : c.Z.functionField) y = 0 := by
        by_contra hne
        have hcl := Scheme.isClosed_of_ord_ne_zero k hne
        have := congrArg (fun E : c.Z.Divisor ↦ E ⟨y, hcl⟩) hh
        simp only [Scheme.div_apply, hdivS, dite_eq_left ((hV y).1 hy)] at this
        exact hne this
      obtain ⟨s, hs, hsh⟩ := Scheme.exists_isUnit_germToFunctionField_eq_of_ord_eq_zero c.g
        h.toMul.ne_zero hord
      let u : Γ(C, ⊤)ˣ := (hs.map (c.i.appIso ⊤).hom.hom).unit
      have hu : ρ u = h.toMul := by
        rw [← hsh]
        simp only [ρ, u, IsUnit.unit_spec, CommRingCat.comp_apply]
        congr 1
        exact congrArg (fun φ : Γ(c.Z, V) ⟶ Γ(c.Z, V) ↦ φ.hom s) (c.i.appIso ⊤).hom_inv_id
      refine ⟨.ofMul u, funext fun P ↦ ?_⟩
      rw [hD, toMul_ofMul, hu]
      have := congrArg (fun E : c.Z.Divisor ↦ E P.1) hh
      simp only [Scheme.div_apply, hdivS, dite_eq_right P.2] at this
      exact this
  · -- the kernel of `D` consists of constants, which are `n`-th powers
    intro u hu
    rw [AddMonoidHom.mem_ker] at hu
    have : Nonempty (⊤ : c.Z.Opens) := ⟨⟨c.i x₀, trivial⟩⟩
    have hord (y : c.Z) (_ : y ∈ (⊤ : c.Z.Opens)) : 0 ≤ c.Z.ord (ρ u.toMul) y := by
      by_cases hy : y ∈ V
      · have hu' : IsUnit ((c.i.appIso ⊤).inv u.toMul) := u.toMul.isUnit.map _
        exact (Scheme.ord_of_isUnit hu' hy).ge
      by_cases hcl : IsClosed ({y} : Set c.Z)
      · exact (congr_fun hu ⟨⟨y, hcl⟩, fun h ↦ hy ((hV y).2 h)⟩).ge
      · exact (not_not.1 fun hne ↦ hcl (Scheme.isClosed_of_ord_ne_zero k hne)).ge
    obtain ⟨s, hs⟩ := Scheme.exists_germToFunctionField_eq_of_ord_nonneg c.g hord
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
  · -- `Pic(C) ≅ Pic(C̄) / a(ℤ^S)`
    let Ξ : C.Divisor →+ Additive c.Z.Pic ⧸ a.range :=
      (QuotientAddGroup.mk' a.range).comp ((Scheme.Divisor.toPic k c.Z).comp ext)
    have hΞ' (E : c.Z.Divisor) :
        Ξ (Scheme.Divisor.comap c.i E) = QuotientAddGroup.mk (Scheme.Divisor.toPic k c.Z E) := by
      have h0 : (QuotientAddGroup.mk (Scheme.Divisor.toPic k c.Z (divS fun P ↦ E P.1)) :
          Additive c.Z.Pic ⧸ a.range) = 0 := (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
      conv_rhs => rw [hsplit E, map_add, QuotientAddGroup.mk_add, h0, add_zero]
      rfl
    have hΞ : Function.Surjective Ξ := by
      intro y
      obtain ⟨L, rfl⟩ := QuotientAddGroup.mk'_surjective a.range y
      obtain ⟨E, hE⟩ := QuotientAddGroup.mk_surjective (eX.symm L)
      refine ⟨Scheme.Divisor.comap c.i E, ?_⟩
      rw [hΞ', ← heX, hE, AddEquiv.apply_symm_apply]
      rfl
    let Φ := (c.i.functionFieldIso.commRingCatIsoToRingEquiv : c.Z.functionField ≃+* _)
    have hker : C.principalDivisors = Ξ.ker := by
      ext E
      rw [AddMonoidHom.mem_ker]
      constructor
      · rintro ⟨h, rfl⟩
        let g : Additive c.Z.functionFieldˣ := .ofMul (Units.map Φ.symm.toMonoidHom h.toMul)
        have hg : Scheme.Divisor.comap c.i (c.Z.div g) = C.div h := by
          rw [Scheme.Divisor.comap_div]
          congr 1
          ext
          exact Φ.apply_symm_apply _
        rw [← hg, hΞ', (htoPic _).2 ⟨g, rfl⟩]
        rfl
      · intro hE
        obtain ⟨v, hv⟩ := (QuotientAddGroup.eq_zero_iff _).1 hE
        have h0 : Scheme.Divisor.toPic k c.Z (ext E - divS v) = 0 := by
          rw [map_sub, sub_eq_zero]
          exact hv.symm
        obtain ⟨g, hg⟩ := (htoPic _).1 h0
        refine ⟨.ofMul (Units.map Φ.toMonoidHom g.toMul), ?_⟩
        rw [← Scheme.Divisor.comap_div, hg, map_sub, hext, hcomap_divS, sub_zero]
    exact ⟨eC.symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Ξ hΞ))⟩

/-- **The order of `H¹` of a smooth affine curve.** Let `C` be a smooth affine connected curve
over an algebraically closed field `k`, `C ⊆ C̄` a smooth proper connected compactification of
genus `g` whose boundary consists of `r` closed points, and `n` prime to `char k`. Then
`|H¹(C_ét, ℤ/n)| · n = n ^ (r + 2g)`, i.e. `|H¹(C_ét, ℤ/n)| = n ^ (2g + r - 1)`.

By the Kummer sequence (`AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isAffine`),
`|H¹(C, ℤ/n)| = |𝒪(C)ˣ / n| · |Pic(C)[n]|`. By
`AlgebraicGeometry.IsConnectedCurve.exists_units_pic_presentation`, `𝒪(C)ˣ / n ≅ M / n` for the
kernel `M` of `a : ℤ^S ⟶ Pic(C̄)` and `Pic(C) ≅ Pic(C̄) / Λ` for its image `Λ`. The
multiplicativity of `|A / nA| / |A[n]|` (`AddSubgroup.natCard_quotient_range_zsmul_mul_eq`)
applied to `0 → M → ℤ^S → Λ → 0` and `0 → Λ → Pic(C̄) → Pic(C) → 0`, together with
`Pic(C̄)[n] ≅ (ℤ/n)^{2g}`, `Pic(C̄) / n ≅ ℤ/n`
(`AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`) and the divisibility of
`Pic(C)` (`AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`), gives
the formula.
(blueprint: `proposition-cohomology-smooth-affine-curve`, affine case) -/
theorem natCard_sheafH_one_constantZMod_mul (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    Nat.card (Sheaf.H (C.constantZMod n) 1) * n =
      n ^ (Nat.card {P : closedPoints c.Z // P.1 ∉ Set.range c.i} + 2 * c.g.genus) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  set S := {P : closedPoints c.Z // P.1 ∉ Set.range c.i}
  obtain ⟨D, a, hDa, hDker, ⟨ePic⟩, hSfin⟩ := exists_units_pic_presentation f c
  obtain ⟨-, -, ⟨α, β, hα, hαβ, hβ⟩, -, -⟩ := sheafH_constantZMod_of_isAffine f n hn
  obtain ⟨ePicC⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  obtain ⟨hdivC, hfinC⟩ := surjective_zsmul_pic_and_finite_torsionBy f hn
  have := c.isProper
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) :=
    IsConnectedCurve.smoothOfRelativeDimension_one c.g
  have : IsProper (c.Z ↘ Spec (.of k)) := c.isProper
  obtain ⟨⟨eT⟩, ⟨eQ⟩, -⟩ := Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient (C := c.Z) hn
  -- `|H¹| = |𝒪(C)ˣ / n| · |Pic(C)[n]|`
  have h1 : Nat.card (Sheaf.H (C.constantZMod n) 1) =
      Nat.card (a.ker ⧸ (zsmulAddGroupHom (α := a.ker) n).range) *
        Nat.card (AddSubgroup.torsionBy (Additive c.Z.Pic ⧸ a.range) n) := by
    rw [AddSubgroup.natCard_eq_of_exact hαβ, hα, hβ,
      AddSubgroup.natCard_quotient_range_zsmul_eq_of_ker_le D _ (hDker n (Nat.pos_of_ne_zero hn0)),
      hDa, Nat.card_congr (AddSubgroup.torsionByCongr (ePicC.symm.trans ePic) n).toEquiv]
  -- the sequence `0 → M → ℤ^S → Λ → 0`
  have e1 := AddSubgroup.natCard_quotient_range_zsmul_mul_eq a.ker n
  rw [Nat.card_congr (AddSubgroup.quotientRangeZsmulCongr
      (QuotientAddGroup.quotientKerEquivRange a) n).toEquiv,
    Nat.card_congr (AddSubgroup.torsionByCongr (QuotientAddGroup.quotientKerEquivRange a)
      n).toEquiv, AddSubgroup.natCard_quotient_range_zsmul_pi,
    AddSubgroup.natCard_torsionBy_eq_one_of_le_pi _ (by exact_mod_cast hn0),
    ← Nat.card_congr (AddSubgroup.torsionByCongr AddSubgroup.topEquiv n).toEquiv,
    AddSubgroup.natCard_torsionBy_eq_one_of_le_pi _ (by exact_mod_cast hn0)] at e1
  -- the sequence `0 → Λ → Pic(C̄) → Pic(C) → 0`
  have e2 := AddSubgroup.natCard_quotient_range_zsmul_mul_eq a.range n
  have hQ : Nat.card ((Additive c.Z.Pic ⧸ a.range) ⧸
      (zsmulAddGroupHom (α := Additive c.Z.Pic ⧸ a.range) n).range) = 1 := by
    rw [← Nat.card_congr (AddSubgroup.quotientRangeZsmulCongr ePic n).toEquiv,
      AddMonoidHom.range_eq_top.2 hdivC]
    exact Nat.card_eq_one_iff_unique.2 ⟨QuotientAddGroup.subsingleton_quotient_top, ⟨0⟩⟩
  rw [hQ, Nat.card_congr eT.toEquiv, Nat.card_congr eQ.toEquiv, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at e2
  -- finiteness
  have : NeZero n := ⟨hn0⟩
  have hT : Nat.card (AddSubgroup.torsionBy a.range n) ≠ 0 := by
    have : Finite (AddSubgroup.torsionBy (Additive c.Z.Pic) n) := Finite.of_equiv _ eT.symm.toEquiv
    have : Finite (AddSubgroup.torsionBy a.range n) :=
      Finite.of_injective (fun x : AddSubgroup.torsionBy a.range n ↦
        (⟨x.1.1, congrArg Subtype.val (show (n : ℤ) • x.1 = 0 from x.2)⟩ :
          AddSubgroup.torsionBy (Additive c.Z.Pic) n))
        fun x y h ↦ by
          have := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext this)
    exact Nat.card_pos.ne'
  have hQn : Nat.card (AddSubgroup.torsionBy (Additive c.Z.Pic ⧸ a.range) n) ≠ 0 := by
    have : Finite (AddSubgroup.torsionBy (Additive c.Z.Pic ⧸ a.range) n) :=
      Finite.of_equiv _ (AddSubgroup.torsionByCongr ePic n).toEquiv
    exact Nat.card_pos.ne'
  set m := Nat.card (a.ker ⧸ (zsmulAddGroupHom (α := a.ker) n).range)
  set l := Nat.card (a.range ⧸ (zsmulAddGroupHom (α := a.range) n).range)
  set t := Nat.card (AddSubgroup.torsionBy a.range n)
  set q := Nat.card (AddSubgroup.torsionBy (Additive c.Z.Pic ⧸ a.range) n)
  have hl : l ≠ 0 := by
    intro hl
    rw [hl, zero_mul, zero_mul, eq_comm] at e2
    simp only [mul_eq_zero, hn0, hT, hQn, or_self] at e2
  rw [h1]
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (mul_ne_zero hl hT)) ?_
  calc m * q * n * (l * t) = (m * l * 1) * (n * t * q) := by ring
    _ = (n ^ Nat.card S * 1 * t) * (l * 1 * n ^ (2 * c.g.genus)) := by rw [e1, ← e2]; rfl
    _ = n ^ (Nat.card S + 2 * c.g.genus) * (l * t) := by ring

end AlgebraicGeometry.IsConnectedCurve
