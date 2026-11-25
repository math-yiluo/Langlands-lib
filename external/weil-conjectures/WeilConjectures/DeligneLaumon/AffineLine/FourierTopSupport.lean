/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters
public import WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform
public import WeilConjectures.WeilSheaf.SupportSubobject

/-!
# The top cohomology sheaf of the Fourier transform has finite support

Let `K` be a Weil complex on the affine line concentrated in degrees `≤ m`. Then `FT_ψ(K)` is
concentrated in degrees `≤ m + 1`, and its top cohomology sheaf `H = 𝓗^{m+1} FT_ψ(K)` has finite
support (`AlgebraicGeometry.support_homologySheaf_fourierTransform_finite`, the key step 1(a) of
blueprint `proposition-fourier-transform-perverse-heart--1`).

The blueprint computes the stalk of `H` at a geometric point `ξ` as
`H²_c(U, F ⊗ ℒ_{ψ(ξ x)})`, the coinvariants of `F ⊗ ℒ_{ψ(ξ x)}`, and counts the linear
characters which are quotients of `F`. We argue by Fourier inversion instead, which avoids the
stalks at points which are not `k₀`-rational:

- for a closed point `x` in the support of `H`, the closed complement `i : Z₀ ↪ 𝔸¹` of
  `V₀ = 𝔸¹ ∖ {x}` gives a nonzero morphism `H ⟶ i_* i^* H`, from the open–closed triangle and
  the vanishing of the stalk of `j_! j^* H` at `x`;
- the composite `FT_ψ(K) ⟶ H[-m-1] ⟶ (i_* i^* H)[-m-1]` is nonzero; applying `FT_{ψ⁻¹}` and
  Fourier inversion, it becomes a nonzero morphism `N ⟶ B` from `N = 𝓗^m(K(-1))` to the lisse
  sheaf `B[1] = FT_{ψ⁻¹}(i_* i^* H)`, which is geometrically a sum of linear characters
  `ℒ_{ψ(a x)}` with `-a` the coordinate of a geometric point over `x`
  (`AlgebraicGeometry.WeilSheaf.exists_iso_carrier_lowerStar_tensorObj_fourierKernel_inv`);
- the restriction of `N ⟶ B` to a dense open `U` stays nonzero: its image `I` vanishing on `U`
  would have `FT_ψ(I) ≤ -1`, while `FT_ψ(B) ≥ 1` by Fourier inversion
  (`AlgebraicGeometry.WeilSheaf.eq_zero_of_upperStar_map_eq_zero`);
- on the geometric fibre `Ū` of a dense open on which `N` is lisse, `N` therefore has a nonzero
  morphism to some `ℒ_{ψ(a x)}|_Ū` with `a` over `x`
  (`AlgebraicGeometry.exists_isNegCoordOver_ne_zero_of_mem_support`). These characters are
  irreducible and pairwise distinct
  (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isEmpty_iso_linearCharacter`),
  so there are at most `rank N|_U` of them
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.le_finrank_of_ne_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀) in
/-- `a ∈ k̄` is minus the coordinate of a geometric point of the affine line over the closed
point `x`. -/
def affineLine.IsNegCoordOver (a : AlgebraicClosure k₀) (x : (affineLine k₀).finitePoints) :
    Prop :=
  ∃ t : Spec (.of (AlgebraicClosure k₀)) ⟶ affineLine k₀,
    t ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = (Scheme.specAlgebraicClosure k₀).hom ∧
      t.base (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 ∧
        a = -affineLine.coordOfPoint t

omit [Finite k₀] in
/-- A geometric point of the affine line over `k̄` is determined by its coordinate, so an element
of `k̄` lies over at most one closed point. -/
theorem affineLine.IsNegCoordOver.eq {a : AlgebraicClosure k₀}
    {x y : (affineLine k₀).finitePoints} (hx : affineLine.IsNegCoordOver k₀ a x)
    (hy : affineLine.IsNegCoordOver k₀ a y) : x = y := by
  obtain ⟨t, ht, hxt, rfl⟩ := hx
  obtain ⟨t', ht', hyt, ha⟩ := hy
  have hc : affineLine.coordOfPoint t = affineLine.coordOfPoint t' := neg_injective ha
  have : t = t' := by
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · exact ht.trans ht'.symm
    · exact (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).commRingCatIsoToRingEquiv.injective hc
  subst this
  exact Subtype.ext (hxt.symm.trans hyt)

namespace WeilComplex

section Orthogonality

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- A morphism from a Weil complex `≤ a` to a Weil complex `≥ b` vanishes if `a < b`. -/
lemma eq_zero_of_isLE_of_isGE {K L : WeilComplex k₀ l X} (f : K ⟶ L) {a b : ℤ} (hab : a < b)
    (hK : K.obj.IsLE a) (hL : L.obj.IsGE b) : f = 0 :=
  (ObjectProperty.ι _).map_injective (by
    rw [Functor.map_zero]
    exact _root_.DerivedCategory.TStructure.t.zero (X := K.obj) (Y := L.obj) _ a b hab)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil sheaf placed in degree zero is `≥ 0`. -/
lemma isGE_toComplex_obj (G : WeilSheaf k₀ l X) : (WeilSheaf.toComplex.obj G).obj.IsGE 0 :=
  (isGE_iff_isZero_homologySheaf _ 0).2 fun _ ha ↦
    isZero_homologySheaf_singleComplex ha.ne G

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil sheaf placed in degree `n`, as the shift `G[-n]`, is `≥ n`. -/
lemma isGE_shift_toComplex_obj (G : WeilSheaf k₀ l X) (n : ℤ) :
    ((WeilSheaf.toComplex.obj G)⟦-n⟧).obj.IsGE n :=
  isGE_shift_obj _ 0 (-n) n (by lia) (isGE_toComplex_obj G)

/-- **The top truncation detects nonzero morphisms to sheaves.** Let
`F₁ ⟶ F ⟶ F₃ ⟶ F₁[1]` be a distinguished triangle with `F₁ ≤ n - 1` and `F₃ ≅ G[-n]` a Weil
sheaf placed in degree `n`. A nonzero morphism `β : G ⟶ C` to a complex `C ≥ 0` induces a nonzero
morphism `F ⟶ F₃ ≅ G[-n] ⟶ C[-n]`: a morphism `F₃ ⟶ C[-n]` vanishing on `F` factors through
`F₁[1] ≤ n - 2`, hence vanishes. -/
lemma mor₂_comp_shift_map_ne_zero {F₁ F F₃ C : WeilComplex k₀ l X} (f : F₁ ⟶ F) (g : F ⟶ F₃)
    (h : F₃ ⟶ F₁⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang _) (n : ℤ)
    (hF₁ : F₁.obj.IsLE (n - 1)) (hC : C.obj.IsGE 0) {G : WeilSheaf k₀ l X}
    (e : F₃ ≅ (WeilSheaf.toComplex.obj G)⟦-n⟧) (β : WeilSheaf.toComplex.obj G ⟶ C)
    (hβ : β ≠ 0) : g ≫ e.hom ≫ (shiftFunctor _ (-n)).map β ≠ 0 := by
  intro h0
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₃ _ hT (e.hom ≫ (shiftFunctor _ (-n)).map β) h0
  have hr0 : r = 0 := eq_zero_of_isLE_of_isGE r (a := n - 2) (b := n) (by lia)
    (isLE_shift_obj F₁ (n - 1) 1 (n - 2) (by lia) hF₁) (isGE_shift_obj C 0 (-n) n (by lia) hC)
  refine hβ ((shiftFunctor _ (-n)).map_injective ?_)
  rw [Functor.map_zero, ← cancel_epi e.hom, comp_zero]
  simpa [hr0] using hr

/-- **Morphisms from a complex `≤ n` to a sheaf placed in degree `n`.** Let
`K₁ ⟶ K ⟶ K₃ ⟶ K₁[1]` be a distinguished triangle with `K₁ ≤ n - 1` and `K₃ ≅ N[-n]` a Weil sheaf
placed in degree `n`. A nonzero morphism `K ⟶ B[-n]` to a Weil sheaf placed in degree `n` gives a
nonzero morphism of Weil sheaves `N ⟶ B`: it vanishes on `K₁`, so factors through `K₃`. -/
lemma exists_ne_zero_of_distTriang {K₁ K K₃ : WeilComplex k₀ l X} (f : K₁ ⟶ K) (g : K ⟶ K₃)
    (h : K₃ ⟶ K₁⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang _) (n : ℤ)
    (hK₁ : K₁.obj.IsLE (n - 1)) {N B : WeilSheaf k₀ l X}
    (e : K₃ ≅ (WeilSheaf.toComplex.obj N)⟦-n⟧)
    (φ : K ⟶ (WeilSheaf.toComplex.obj B)⟦-n⟧) (hφ : φ ≠ 0) : ∃ p : N ⟶ B, p ≠ 0 := by
  obtain ⟨φ₃, hφ₃⟩ := Triangle.yoneda_exact₂ _ hT φ
    (eq_zero_of_isLE_of_isGE _ (a := n - 1) (b := n) (by lia) hK₁ (isGE_shift_toComplex_obj B n))
  refine ⟨WeilSheaf.toComplex.preimage ((shiftFunctor _ (-n)).preimage (e.inv ≫ φ₃)),
    fun hp ↦ hφ ?_⟩
  have h₃ : e.inv ≫ φ₃ = 0 := by
    rw [← (shiftFunctor _ (-n)).map_preimage (e.inv ≫ φ₃),
      ← WeilSheaf.toComplex.map_preimage ((shiftFunctor _ (-n)).preimage (e.inv ≫ φ₃)), hp,
      Functor.map_zero, Functor.map_zero]
  rw [hφ₃, (cancel_epi e.inv).1 (h₃.trans comp_zero.symm)]
  exact comp_zero

end Orthogonality

/-- **The restriction to a closed point in the support is nonzero.** Let `j : V₀ ↪ 𝔸¹` be an open
immersion missing a closed point `x` in the support of a Weil sheaf `G`, and let
`j_!j^*G ⟶ G ⟶ C ⟶` be a distinguished triangle (for instance the open–closed triangle). Then
`G ⟶ C` is nonzero: otherwise `G` would be a direct summand of `j_!j^*G`, whose stalk at `x`
vanishes. -/
theorem mor₂_ne_zero_of_mem_support {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    (j : V ⟶ affineLine k₀) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l (affineLine k₀))
    (x : (affineLine k₀).finitePoints) (hxG : x ∈ G.support) (hxj : x.1 ∉ Set.range j.base)
    {C : WeilComplex k₀ l (affineLine k₀)}
    (α : (derivedLowerShriek k₀ l j).obj ((upperStar j).obj (WeilSheaf.toComplex.obj G)) ⟶
      (derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G))
    (β : (derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G) ⟶ C)
    (γ : C ⟶ ((derivedLowerShriek k₀ l j).obj
      ((upperStar j).obj (WeilSheaf.toComplex.obj G)))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α β γ ∈ distTriang _) : β ≠ 0 := by
  intro hβ
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ _ hT (𝟙 _) (by simp [hβ])
  obtain ⟨eId⟩ := nonempty_derivedLowerShriekIdIso (k₀ := k₀) (l := l) (affineLine k₀)
    (WeilSheaf.toComplex.obj G)
  obtain ⟨eZ⟩ := nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (l := l) j
    ((WeilSheaf.upperStar j).obj G)
  let H0 := homologySheaf (k₀ := k₀) (l := l) (X := affineLine k₀) 0
  let e₁ : H0.obj ((derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G)) ≅ G :=
    H0.mapIso eId ≪≫ WeilSheaf.toComplexCompHomologySheafIso.app G
  let e₂ : H0.obj ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj
      (WeilSheaf.toComplex.obj G))) ≅ (WeilSheaf.extensionByZero j).obj
        ((WeilSheaf.upperStar j).obj G) :=
    H0.mapIso ((derivedLowerShriek k₀ l j).mapIso
      ((WeilSheaf.toComplexCompUpperStarIso j).app G) ≪≫ eZ) ≪≫
      WeilSheaf.toComplexCompHomologySheafIso.app _
  let s : G ⟶ (WeilSheaf.extensionByZero j).obj ((WeilSheaf.upperStar j).obj G) :=
    e₁.inv ≫ H0.map r ≫ e₂.hom
  have hs : s ≫ (e₂.inv ≫ H0.map α ≫ e₁.hom) = 𝟙 _ := by
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    have hr' : r ≫ α = 𝟙 ((derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G)) :=
      hr.symm
    rw [← H0.map_comp_assoc, hr', H0.map_id, Category.id_comp, Iso.inv_hom_id]
  have : Mono s := mono_of_mono_fac hs
  have hx := WeilSheaf.support_subset_of_mono s hxG
  exact (not_subsingleton_iff_nontrivial.2 hx)
    (WeilSheaf.subsingleton_stalk_extensionByZero j _ x hxj)

end WeilComplex

namespace WeilSheaf

/-- **Morphisms which the transform carries across the t-structure vanish.** A morphism of Weil
sheaves `Q ⟶ B` on the affine line with `FT_ψ(Q) ≤ -1` and `FT_ψ(B) ≥ 0` vanishes, `FT_ψ` and
the inclusion of Weil sheaves into Weil complexes being faithful. -/
theorem eq_zero_of_isLE_fourierTransform_of_isGE (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {Q B : WeilSheaf k₀ l (affineLine k₀)} (f : Q ⟶ B)
    (hQ : ((fourierTransform ψ).obj (toComplex.obj Q)).obj.IsLE (-1))
    (hB : ((fourierTransform ψ).obj (toComplex.obj B)).obj.IsGE 0) : f = 0 := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  refine toComplex.map_injective ((fourierTransform ψ).map_injective ?_)
  rw [Functor.map_zero, Functor.map_zero]
  exact WeilComplex.eq_zero_of_isLE_of_isGE _ (by lia) hQ hB

/-- **Restriction to a dense open is faithful on morphisms to a sheaf with positive transform.**
Let `j : U ↪ 𝔸¹` be a dense quasi-compact open immersion and `f : Q ⟶ B` a morphism of Weil
sheaves with `FT_ψ(B) ≥ 0`. If `j^* f = 0`, then `f = 0`: the image of `f` vanishes on `U`, so
its transform is `≤ -1`
(`AlgebraicGeometry.WeilSheaf.exists_isLisse_iso_fourierTransform_of_isZero_upperStar`). -/
theorem eq_zero_of_upperStar_map_eq_zero (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀)
    [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    {Q B : WeilSheaf k₀ l (affineLine k₀)} (f : Q ⟶ B) (hf : (upperStar j).map f = 0)
    (hB : ((fourierTransform ψ).obj (toComplex.obj B)).obj.IsGE 0) : f = 0 := by
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over j]
    infer_instance
  have : (upperStar (k₀ := k₀) (l := l) j).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have : (upperStar (k₀ := k₀) (l := l) j).PreservesEpimorphisms :=
    preservesEpimorphisms_of_preservesColimitsOfShape _
  have : Mono ((upperStar j).map (image.ι f)) := Functor.map_mono _ _
  have : Epi ((upperStar j).map (factorThruImage f)) := Functor.map_epi _ _
  have hI : IsZero ((upperStar j).obj (image f)) := by
    refine IsZero.of_epi_eq_zero ((upperStar j).map (factorThruImage f))
      ((cancel_mono ((upperStar j).map (image.ι f))).1 ?_)
    rw [← Functor.map_comp, image.fac, hf, zero_comp]
  obtain ⟨B', -, ⟨e⟩⟩ := exists_isLisse_iso_fourierTransform_of_isZero_upperStar ψ j (image f) hI
  have hQ : ((fourierTransform ψ).obj (toComplex.obj (image f))).obj.IsLE (-1) := by
    rw [WeilComplex.isLE_iff_isZero_homologySheaf]
    intro a ha
    exact (isZero_homologySheaf_toShiftedComplex ha.ne' B').of_iso
      ((WeilComplex.homologySheaf a).mapIso e)
  have h0 := eq_zero_of_isLE_fourierTransform_of_isGE ψ hψ (image.ι f) hQ hB
  calc f = factorThruImage f ≫ image.ι f := (image.fac f).symm
    _ = 0 := by rw [h0, comp_zero]

/-- If `B[1] ≅ FT_{ψ⁻¹}(C)` for a Weil complex `C ≥ 0`, then `FT_ψ(B) ≥ 1`: by Fourier inversion,
`FT_ψ(B)[1] ≅ FT_ψ(FT_{ψ⁻¹}(C)) ≅ C(-1)`. -/
theorem isGE_fourierTransform_toComplex_of_iso (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {C : WeilComplex k₀ l (affineLine k₀)} (hC : C.obj.IsGE 0)
    {B : WeilSheaf k₀ l (affineLine k₀)}
    (e : (fourierTransform ψ⁻¹).obj C ≅ toShiftedComplex.obj B) :
    ((fourierTransform ψ).obj (toComplex.obj B)).obj.IsGE 1 := by
  obtain ⟨eI⟩ := nonempty_fourierTransform_comp_fourierTransform_inv_iso (l := l) ψ⁻¹
    (inv_ne_one.2 hψ)
  rw [inv_inv] at eI
  let e' : ((fourierTransform ψ).obj (toComplex.obj B))⟦(1 : ℤ)⟧ ≅
      (WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj C :=
    (((fourierTransform ψ).commShiftIso (1 : ℤ)).app _).symm ≪≫
      (fourierTransform ψ).mapIso e.symm ≪≫ eI.app C
  rw [WeilComplex.isGE_iff_isZero_homologySheaf] at hC ⊢
  intro a ha
  refine IsZero.of_iso ?_ ((WeilComplex.homologySheafShiftIso _ 1 (a - 1) a (by lia)).symm ≪≫
    (WeilComplex.homologySheaf (a - 1)).mapIso e')
  rw [WeilComplex.isZero_homologySheaf_tateTwist_iff]
  exact hC _ (by lia)

end WeilSheaf

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **A closed point in the support of the top cohomology sheaf of `FT_ψ(K)` gives a linear
character quotient**. Let `K ≤ m`, with truncation triangles `F₁ ⟶ FT_ψ(K) ⟶ G[-m-1] ⟶` and
`K₁ ⟶ K(-1) ⟶ N[-m] ⟶` (`F₁ ≤ m`, `K₁ ≤ m - 1`), and let `x` be a closed point in the support of
`G`. Then for every dense open `U ⊆ 𝔸¹` there are `a ∈ k̄` minus the coordinate of a geometric
point over `x` and a nonzero morphism `N|_Ū ⟶ ℒ_{ψ(a x)}|_Ū`.

Let `j : V ↪ 𝔸¹` be the complement of `x` and `i : Z ↪ 𝔸¹` the reduced point `x`. The open–closed
triangle `j_!j^*G ⟶ G ⟶ i_*i^*G ⟶` has nonzero second morphism, as `x` lies in the support of
`G`, so the composite `FT_ψ(K) ⟶ G[-m-1] ⟶ (i_*i^*G)[-m-1]` is nonzero. Applying `FT_{ψ⁻¹}` and
Fourier inversion gives a nonzero morphism `K(-1) ⟶ B[-m]`, where `B[1] = FT_{ψ⁻¹}(i_*i^*G)`, and
hence a nonzero morphism `N ⟶ B`, still nonzero on `U` since `FT_ψ(B) ≥ 0`. Geometrically `B` is
a sum of characters `ℒ_{ψ(a x)}` with `-a` the coordinate of a geometric point over `x`
(`AlgebraicGeometry.WeilSheaf.exists_iso_carrier_lowerStar_tensorObj_fourierKernel_inv`). -/
theorem exists_isNegCoordOver_ne_zero_of_mem_support (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) {K : WeilComplex k₀ l (affineLine k₀)} {m : ℤ}
    {F₁ F₃ : WeilComplex k₀ l (affineLine k₀)} (f : F₁ ⟶ (fourierTransform ψ).obj K)
    (g : (fourierTransform ψ).obj K ⟶ F₃) (h : F₃ ⟶ F₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _) (hF₁ : F₁.obj.IsLE m)
    {G : WeilSheaf k₀ l (affineLine k₀)} (eG : F₃ ≅ (WeilSheaf.toComplex.obj G)⟦-(m + 1)⟧)
    {K₁ K₃ : WeilComplex k₀ l (affineLine k₀)}
    (f' : K₁ ⟶ (WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj K)
    (g' : (WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj K ⟶ K₃)
    (h' : K₃ ⟶ K₁⟦(1 : ℤ)⟧) (hT' : Triangle.mk f' g' h' ∈ distTriang _)
    (hK₁ : K₁.obj.IsLE (m - 1)) {N : WeilSheaf k₀ l (affineLine k₀)}
    (eN : K₃ ≅ (WeilSheaf.toComplex.obj N)⟦-m⟧)
    {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (jU : U ⟶ affineLine k₀)
    [IsOpenImmersion jU] [QuasiCompact jU] [jU.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant jU] (x : (affineLine k₀).finitePoints) (hx : x ∈ G.support) :
    ∃ a : AlgebraicClosure k₀, affineLine.IsNegCoordOver k₀ a x ∧
      ∃ p : ((WeilSheaf.upperStar jU).obj N).obj.carrier ⟶
        (Scheme.Hom.geometricFiberMap jU (comp_over jU _))^*ᵃ[l].obj
          ((affineLine.geometricSMul k₀ a)^*ᵃ[l].obj (artinSchreier ψ 1).obj.carrier), p ≠ 0 := by
  -- the open complement `V` of `x`, and its reduced closed complement `Z = {x}`
  have hxc : IsClosed ({x.1} : Set (affineLine k₀)) :=
    (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
  let V : (affineLine k₀).Opens := ⟨{x.1}ᶜ, hxc.isOpen_compl⟩
  have hVd : Dense (V : Set (affineLine k₀)) := by
    obtain ⟨V', hV', hxV'⟩ :=
      affineLine.exists_opens_dense_compl_finite {x} (Set.finite_singleton x)
    exact hV'.mono fun y hy hyx ↦ hxV' x (Set.mem_singleton x) (Set.mem_singleton_iff.1 hyx ▸ hy)
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : TopologicalSpace.NoetherianSpace (affineLine k₀) := by
    have := LocallyOfFiniteType.isLocallyNoetherian (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
    have : IsNoetherian (affineLine k₀) := {}
    infer_instance
  have : TopologicalSpace.NoetherianSpace V :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨Z, _, i, _, _, _, _, hi⟩ := exists_isReduced_isClosedImmersion_range_eq_compl V.ι
  have hxj : x.1 ∉ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun h ↦ h (Set.mem_singleton _)
  -- the open–closed triangle of `G` has a nonzero second morphism `G ⟶ i_*i^*G`
  set KG := WeilSheaf.toComplex.obj G
  set C := (WeilComplex.derivedLowerShriek k₀ l i).obj ((WeilComplex.upperStar i).obj KG)
  obtain ⟨α, β, γ, hT₀⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_openClosed_comp V.ι
    i hi (𝟙 _) V.ι i (Category.comp_id _) (Category.comp_id _) KG
  have hβ := WeilComplex.mor₂_ne_zero_of_mem_support V.ι G x hx hxj α β γ hT₀
  obtain ⟨eId⟩ := WeilComplex.nonempty_derivedLowerShriekIdIso (k₀ := k₀) (l := l)
    (affineLine k₀) KG
  have hC : C.obj.IsGE 0 := WeilComplex.isGE_derivedLowerShriek_obj i
    (WeilComplex.isGE_upperStar_obj i (WeilComplex.isGE_toComplex_obj G))
  have hφ := WeilComplex.mor₂_comp_shift_map_ne_zero f g h hT (m + 1) (by simpa using hF₁) hC eG
    (eId.inv ≫ β) fun h0 ↦ hβ ((cancel_epi eId.inv).1 (h0.trans comp_zero.symm))
  -- the inverse transform of `i_*i^*G` is `B[1]`
  let X' := pullback i (affinePlane.fst k₀)
  let q : X' ⟶ Z := pullback.fst i (affinePlane.fst k₀)
  let i' : X' ⟶ affinePlane k₀ := pullback.snd i (affinePlane.fst k₀)
  let : X'.Over (Spec (CommRingCat.of k₀)) := ⟨i' ≫ affinePlane k₀ ↘ Spec (CommRingCat.of k₀)⟩
  have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change q ≫ Z ↘ Spec (CommRingCat.of k₀) = i' ≫ affinePlane.fst k₀ ≫ _
    rw [← comp_over i (Spec (CommRingCat.of k₀)), ← Category.assoc, pullback.condition,
      Category.assoc]⟩
  let π : X' ⟶ affineLine k₀ := i' ≫ affinePlane.snd k₀
  have hP : IsPullback q π (Z ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have := (IsPullback.of_hasPullback i (affinePlane.fst k₀)).paste_vert
      (IsPullback.of_hasPullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    rwa [comp_over] at this
  have : IsFinite π := MorphismProperty.of_isPullback hP inferInstance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (i' ≫ _))
  set E := (WeilSheaf.upperStar i).obj G
  obtain ⟨eB⟩ := WeilSheaf.nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback ψ⁻¹ i q
    i' π rfl (IsPullback.of_hasPullback i (affinePlane.fst k₀)) E
  set B := (WeilSheaf.lowerStar π).obj
    (((WeilSheaf.upperStar i').obj (fourierKernel ψ⁻¹)).tensorObj ((WeilSheaf.upperStar q).obj E)
      (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ⁻¹)))
  let eC : C ≅ (WeilComplex.derivedLowerShriek k₀ l i).obj (WeilSheaf.toComplex.obj E) :=
    (WeilComplex.derivedLowerShriek k₀ l i).mapIso
      ((WeilSheaf.toComplexCompUpperStarIso i).app G)
  -- applying `FT_{ψ⁻¹}` and Fourier inversion: a nonzero morphism `K(-1) ⟶ B[-m]`
  have := isEquivalence_fourierTransform (l := l) ψ⁻¹ (inv_ne_one.2 hψ)
  obtain ⟨eI⟩ := nonempty_fourierTransform_comp_fourierTransform_inv_iso (l := l) ψ hψ
  let ε : (fourierTransform ψ⁻¹).obj (C⟦-(m + 1)⟧) ≅ (WeilSheaf.toComplex.obj B)⟦-m⟧ :=
    ((fourierTransform ψ⁻¹).commShiftIso (-(m + 1))).app C ≪≫
      (shiftFunctor _ (-(m + 1))).mapIso ((fourierTransform ψ⁻¹).mapIso eC ≪≫ eB) ≪≫
      (shiftFunctorAdd' _ (1 : ℤ) (-(m + 1)) (-m) (by ring)).symm.app _
  set φ := g ≫ eG.hom ≫ (shiftFunctor _ (-(m + 1))).map (eId.inv ≫ β)
  have hφ' : (eI.app K).inv ≫ (fourierTransform ψ⁻¹).map φ ≫ ε.hom ≠ 0 := by
    intro h0
    refine hφ ((fourierTransform ψ⁻¹).map_injective ?_)
    have h₁ : (eI.app K).inv ≫ (fourierTransform ψ⁻¹).map φ = 0 := by
      rw [← cancel_mono ε.hom, Category.assoc, h0, zero_comp]
    rw [Functor.map_zero, ← cancel_epi (eI.app K).inv, h₁, comp_zero]
  obtain ⟨p, hp⟩ := WeilComplex.exists_ne_zero_of_distTriang f' g' h' hT' m hK₁ eN _ hφ'
  -- the restriction of `p : N ⟶ B` to `U` is nonzero
  have hB : ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj B)).obj.IsGE 0 := by
    have := WeilSheaf.isGE_fourierTransform_toComplex_of_iso ψ hψ
      (WeilComplex.isGE_derivedLowerShriek_obj i (WeilComplex.isGE_toComplex_obj E)) eB
    exact _root_.DerivedCategory.TStructure.t.isGE_of_ge _ 0 1 zero_le_one
  have hpU : (WeilSheaf.upperStar jU).map p ≠ 0 := fun h0 ↦
    hp (WeilSheaf.eq_zero_of_upperStar_map_eq_zero ψ hψ jU p h0 hB)
  let ΦU := (WeilSheaf.objectProperty k₀ l U).ι ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)
  have hpU' : ΦU.map ((WeilSheaf.upperStar jU).map p) ≠ 0 := fun h0 ↦
    hpU (ΦU.map_injective (by rw [h0, Functor.map_zero]))
  -- geometrically, `B` is a sum of linear characters over `x`
  obtain ⟨n, t, mt, ht, ⟨eS⟩⟩ := WeilSheaf.exists_iso_carrier_lowerStar_tensorObj_fourierKernel_inv
    ψ i q i' π rfl pullback.condition.symm hP E
  set jg := Scheme.Hom.geometricFiberMap jU (comp_over jU (Spec (CommRingCat.of k₀)))
  let eS' := (jg)^*ᵃ[l].mapIso eS ≪≫ (jg)^*ᵃ[l].mapBiproduct _ ≪≫
    biproduct.mapIso fun k ↦ (jg)^*ᵃ[l].mapBiproduct _
  set c := ΦU.map ((WeilSheaf.upperStar jU).map p) ≫ eS'.hom
  have hc : c ≠ 0 := fun h0 ↦ hpU' (by rw [← cancel_mono eS'.hom, zero_comp]; exact h0)
  obtain ⟨k, hk⟩ : ∃ k, c ≫ biproduct.π _ k ≠ 0 := by
    by_contra! hall
    exact hc (biproduct.hom_ext _ _ fun k ↦ by rw [hall k, zero_comp])
  obtain ⟨r, hr⟩ : ∃ r, (c ≫ biproduct.π _ k) ≫ biproduct.π _ r ≠ 0 := by
    by_contra! hall
    exact hk (biproduct.hom_ext _ _ fun r ↦ by rw [hall r, zero_comp])
  refine ⟨-affineLine.coordOfPoint (t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i),
    ⟨t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i, ?_, ?_, rfl⟩, _, hr⟩
  · rw [Category.assoc, Category.assoc, comp_over i, Scheme.Hom.geometricFiber_condition,
      ← Category.assoc, ht k, Category.id_comp]
  · have hmem : (t k ≫ (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ≫ i).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) ∈ Set.range i.base := ⟨_, rfl⟩
    rw [hi, Scheme.Opens.range_ι] at hmem
    simpa [V] using hmem

/-- **The top cohomology sheaf of the transform of a complex `≤ m` has finite support** (step 1(a)
of blueprint `proposition-fourier-transform-perverse-heart--1`). Let `K ≤ m`, so that
`FT_ψ(K) ≤ m + 1`, and let `N = 𝓗^m(K(-1))`, lisse on a dense open `U`. Each closed point `x` in the
support of `𝓗^{m+1} FT_ψ(K)` gives a nonzero morphism from `N|_Ū` to a linear character
`ℒ_{ψ(a x)}|_Ū`, with `-a` the coordinate of a geometric point over `x`
(`AlgebraicGeometry.exists_isNegCoordOver_ne_zero_of_mem_support`). Distinct points give distinct
irreducible characters, so there are at most `rank N|_U` of them
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.le_finrank_of_ne_zero`). -/
theorem support_homologySheaf_fourierTransform_finite (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) {m : ℤ} {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsLE m) :
    ((WeilComplex.homologySheaf (m + 1)).obj ((fourierTransform ψ).obj K)).support.Finite := by
  -- the top truncation of `FT_ψ(K) ≤ m + 1`
  obtain ⟨F₁, F₃, f, g, h, hT, hF₁, hF₃, hF₃', ⟨eH⟩⟩ :=
    WeilComplex.exists_distTriang_of_isLE _ (m + 1) (isLE_fourierTransform_obj ψ hψ hK)
  obtain ⟨G, ⟨eG⟩, ⟨eG'⟩⟩ := WeilComplex.exists_iso_singleComplex F₃ (m + 1)
  rw [WeilSheaf.support_congr (eH.symm ≪≫
    ObjectProperty.isoMk (X := (WeilComplex.homologySheaf (m + 1)).obj F₃) (Y := G) _ eG')]
  -- the top truncation of `K(-1) ≤ m`
  have hK' : ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj K).obj.IsLE m := by
    rw [WeilComplex.isLE_iff_isZero_homologySheaf] at hK ⊢
    intro a ha
    rw [WeilComplex.isZero_homologySheaf_tateTwist_iff]
    exact hK a ha
  obtain ⟨K₁, K₃, f', g', h', hT', hK₁, hK₃, hK₃', -⟩ :=
    WeilComplex.exists_distTriang_of_isLE _ m hK'
  obtain ⟨N, ⟨eN⟩, -⟩ := WeilComplex.exists_iso_singleComplex K₃ m
  -- a dense open `U` on which `N` is lisse
  obtain ⟨U, hU, hNU⟩ := WeilSheaf.exists_dense_isLisse_upperStar N
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : TopologicalSpace.NoetherianSpace (affineLine k₀) := by
    have := LocallyOfFiniteType.isLocallyNoetherian (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
    have : IsNoetherian (affineLine k₀) := {}
    infer_instance
  have : TopologicalSpace.NoetherianSpace U :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let D : WeilSheaf.LisseOnDenseOpen k₀ l :=
    { U := U, j := U.ι, sheaf := (WeilSheaf.upperStar U.ι).obj N, lisse := hNU }
  have key (x : (affineLine k₀).finitePoints) (hx : x ∈ G.support) :
      ∃ a : AlgebraicClosure k₀, affineLine.IsNegCoordOver k₀ a x ∧
        ∃ p : D.sheaf.obj.carrier ⟶ D.linearCharacter ψ a, p ≠ 0 :=
    exists_isNegCoordOver_ne_zero_of_mem_support ψ hψ f g h hT (by simpa using hF₁)
      (eG ≪≫ WeilComplex.singleComplexIsoShift (m + 1) G) f' g' h' hT' hK₁
      (eN ≪≫ WeilComplex.singleComplexIsoShift m N) U.ι x hx
  -- a geometric point of `Ū`, and the rank `r` of `N` there
  by_contra hinf
  have := D.irreducibleSpace_geometricFiber
  obtain ⟨y, hy⟩ := hU.nonempty
  obtain ⟨z, -⟩ :=
    Scheme.Hom.geometricFiberProj_surjective (D.U ↘ Spec (CommRingCat.of k₀)) ⟨y, hy⟩
  have : Nonempty (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber := ⟨z⟩
  obtain ⟨Ω, _, _, ⟨s⟩⟩ := exists_geometricPoint (D.U ↘ Spec (CommRingCat.of k₀)).geometricFiber
  set r := Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
    ((ProEtale.geometricStalkFunctor l s).obj D.sheaf.obj.carrier))
  -- `r + 1` distinct points of the support give `r + 1` distinct characters
  let xs : ℕ ↪ G.support := Set.Infinite.natEmbedding _ hinf
  choose a ha p hp using fun i : Fin (r + 1) ↦ key (xs i) (xs i).2
  have hle := ProEtale.IsAdicLisseSheaf.le_finrank_of_ne_zero s (r + 1)
    (fun i ↦ D.linearCharacter ψ (a i)) (fun i ↦ D.isIrreducibleAdicLocalSystem_linearCharacter ψ _)
    (fun i j ⟨e⟩ ↦ by
      by_contra hij
      have hne : a i ≠ a j := fun hae ↦ hij (Fin.ext (xs.injective (Subtype.ext
        ((ha i).eq (hae ▸ ha j)))))
      exact (D.isEmpty_iso_linearCharacter ψ hψ hne).false e)
    D.sheaf.obj.carrier D.lisse p hp
  exact Nat.not_succ_le_self r hle

end AlgebraicGeometry
