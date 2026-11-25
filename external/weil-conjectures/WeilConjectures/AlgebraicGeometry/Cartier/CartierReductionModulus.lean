/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass

/-! # Naturality of the normalized Cartier reduction

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Etale

private theorem kummer_modulus (Z : Scheme.{u}) (m n : ℕ) (hdiv : n ∣ m)
    (hZm : IsUnit (m : Γ(Z, ⊤))) (hZn : IsUnit (n : Γ(Z, ⊤)))
    (q : Z.rootsOfUnitySheaf m ⟶ Z.rootsOfUnitySheaf n)
    (hq : q ≫ kernel.ι (n • 𝟙 Z.gmSheaf) = (m / n) • kernel.ι (m • 𝟙 Z.gmSheaf)) :
    (Z.kummerSequence_shortExact m hZm).extClass.comp (Ext.mk₀ q) (add_zero 1) =
      (Z.kummerSequence_shortExact n hZn).extClass := by
  let f : Z.kummerSequence m ⟶ Z.kummerSequence n :=
    { τ₁ := q
      τ₂ := (m / n) • 𝟙 Z.gmSheaf
      τ₃ := 𝟙 Z.gmSheaf
      comm₁₂ := by simpa only [Scheme.kummerSequence, Preadditive.comp_nsmul,
        Category.comp_id] using hq
      comm₂₃ := by
        simp only [Scheme.kummerSequence, Preadditive.comp_nsmul, Category.comp_id, smul_smul]
        rw [Nat.mul_div_cancel' hdiv] }
  have hh := ShortComplex.ShortExact.extClass_naturality
    (Z.kummerSequence_shortExact m hZm) (Z.kummerSequence_shortExact n hZn) f
  change (Z.kummerSequence_shortExact m hZm).extClass.comp (Ext.mk₀ q) (add_zero 1) =
    (Ext.mk₀ (𝟙 Z.gmSheaf)).comp (Z.kummerSequence_shortExact n hZn).extClass
      (zero_add 1) at hh
  rw [Ext.mk₀_id_comp] at hh
  exact hh

private theorem root_map_modulus (A : Type (u + 1)) [CommRing A]
    (m n : ℕ) (hAm : (m : A) = 0) (hAn : (n : A) = 0) (Z : Scheme.{u})
    (q : Z.rootsOfUnitySheaf m ⟶ Z.rootsOfUnitySheaf n)
    (e : Scheme.finiteEtaleTateLine Z m A hAm ≅ Scheme.finiteEtaleTateLine Z n A hAn)
    (he : ∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf m).obj.obj W),
      e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A m Z hAm W a z) =
        Scheme.finiteEtaleTateOneGenerator A n Z hAn W a (q.hom.app W z)) :
    ordinaryFiniteRootMap A m hAm Z ≫ (RawModuleScalarComparison.forget A Z).map e.hom =
      q ≫ ordinaryFiniteRootMap A n hAn Z := by
  ext W z
  exact he W 1 z

private theorem yoneda_modulus {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {P B M N L L' : C} (β : Ext P B 1) (δm : Ext B M 1) (δn : Ext B N 1)
    (g : M ⟶ L) (e : L ⟶ L') (q : M ⟶ N) (h : N ⟶ L')
    (hk : δm.comp (Ext.mk₀ q) (add_zero 1) = δn) (hr : g ≫ e = q ≫ h) :
    ((β.comp δm rfl).comp (Ext.mk₀ g) (add_zero 2)).comp (Ext.mk₀ e) (add_zero 2) =
      (β.comp δn rfl).comp (Ext.mk₀ h) (add_zero 2) := by
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hr, ← Ext.mk₀_comp_mk₀]
  rw [Ext.comp_assoc_of_third_deg_zero β δm,
    ← Ext.comp_assoc_of_third_deg_zero δm (Ext.mk₀ q), hk,
    Ext.comp_assoc_of_third_deg_zero]

private theorem boundary_modulus (A : Type (u + 1)) [CommRing A]
    (m n : ℕ) (hdiv : n ∣ m) (hAm : (m : A) = 0) (hAn : (n : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZm : IsUnit (m : Γ(Z, ⊤))) (hZn : IsUnit (n : Γ(Z, ⊤)))
    (q : Z.rootsOfUnitySheaf m ⟶ Z.rootsOfUnitySheaf n)
    (e : Scheme.finiteEtaleTateLine Z m A hAm ≅ Scheme.finiteEtaleTateLine Z n A hAn)
    (hq : q ≫ kernel.ι (n • 𝟙 Z.gmSheaf) = (m / n) • kernel.ι (m • 𝟙 Z.gmSheaf))
    (he : ∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf m).obj.obj W),
      e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A m Z hAm W a z) =
        Scheme.finiteEtaleTateOneGenerator A n Z hAn W a (q.hom.app W z))
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine Z m A hAm) 2)
    (hκ : SupportedKummerBoundary A m hAm i hI hZm κ) :
    SupportedKummerBoundary A n hAn i hI hZn
      (κ.comp (Ext.mk₀ e.hom) (add_zero 2)) := by
  unfold SupportedKummerBoundary at hκ ⊢
  intro W hW
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hclass⟩ := hκ W hW
  refine ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, ?_⟩
  have hk := kummer_modulus Z m n hdiv hZm hZn q hq
  have hr := root_map_modulus A m n hAm hAn Z q e he
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc, hclass]
  · exact yoneda_modulus hE.extClass _ _ _ _ q _ hk hr
  · rfl
  · rfl

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Compatibility of normalized reduction with a specified modulus projection.
This lemma constructs neither a root projection nor a Tate-line isomorphism: those
are the existing finite-twist comparisons. It identifies their action on the reduced
boundary of the same integral pole extension.
Source: blueprint sk-lem-geo-cartier.proof.md, paragraph 4, exponent sentence;
(blueprint: lem-sfb-cartier-reduction-modulus).
Proof: write m = dn. The morphism from the m-Kummer sequence to the n-Kummer sequence
has components q on the kernels, multiplication by d on the middle units, and the
identity on the right units. The equation q followed by the kernel inclusion equals
d times the m-kernel inclusion is precisely its left square; nd=m gives its right
square. Naturality of the short exact triangle thus identifies the two positive
Kummer connecting maps. The pure-tensor equation identifies their further A-linear
root maps. Both relative boundaries use the same integral pole extension followed
by these connecting maps. Uniqueness of the normalized relative boundary identifies
the resulting A-linear Ext classes. Exact comparison inverse image preserves this
equality and its specified source mate. For m=n the kernel equation forces q to be
the identity and the generator equation forces e to be the identity. For n=1 the
coefficient ring is zero, and both Ext classes vanish. Empty support also gives zero. -/
theorem geoCartierCanonicalClass_modulus (ℓ : ℕ) (hℓ : ℓ.Prime)
    (r s : ℕ) (_hr : 0 < r) (_hs : 0 < s) (hrs : r ≤ s)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hAm : ((ℓ ^ s : ℕ) : A) = 0) (hAn : ((ℓ ^ r : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZm : IsUnit ((ℓ ^ s : ℕ) : Γ(Z, ⊤)))
    (hZn : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤)))
    (q : Z.rootsOfUnitySheaf (ℓ ^ s) ⟶ Z.rootsOfUnitySheaf (ℓ ^ r))
    (e : Scheme.finiteEtaleTateLine Z (ℓ ^ s) A hAm ≅
      Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hAn)
    (hq : q ≫ kernel.ι ((ℓ ^ r) • 𝟙 Z.gmSheaf) =
      (ℓ ^ s / ℓ ^ r) • kernel.ι ((ℓ ^ s) • 𝟙 Z.gmSheaf))
    (he : ∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf (ℓ ^ s)).obj.obj W),
      e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A (ℓ ^ s) Z hAm W a z) =
        Scheme.finiteEtaleTateOneGenerator A (ℓ ^ r) Z hAn W a (q.hom.app W z)) :
    (geoCartierCanonicalClass A (ℓ ^ s) (pow_pos hℓ.pos s) hAm i hI hZm).comp
        (Ext.mk₀ ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).map e.hom)) (add_zero 2) =
      geoCartierCanonicalClass A (ℓ ^ r) (pow_pos hℓ.pos r) hAn i hI hZn := by
  have hm := (Etale.geoCartierEtaleClass_spec A (ℓ ^ s) (pow_pos hℓ.pos s)
    hAm i hI hZm).1
  have heq := (Etale.geoCartierEtaleClass_spec A (ℓ ^ r) (pow_pos hℓ.pos r)
    hAn i hI hZn).2 _
      (Etale.boundary_modulus A (ℓ ^ s) (ℓ ^ r) (pow_dvd_pow ℓ hrs) hAm hAn
        i hI hZm hZn q e hq he _ hm)
  have hmap := congrArg
    (fun κ ↦ κ.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)) heq
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at hmap
  unfold geoCartierCanonicalClass
  rw [Ext.comp_assoc_of_third_deg_zero, hmap]

end AlgebraicGeometry.ProEtale
