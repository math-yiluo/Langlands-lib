/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.GrothendieckLefschetz
public import WeilConjectures.WeilSheaf.StalkUpperStarCharpoly
public import WeilConjectures.ZetaLinearAlgebra.CharpolyRevExpand
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TracePow
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Local Frobenius of quasi-finite direct images

Let `f : X ⟶ Y` be a separated quasi-finite morphism of `k₀`-schemes and `F` a Weil sheaf on `X`.
At a closed point `y` of `Y` of degree `d`, the Frobenius `F_y` on `(f₀!F)_ȳ` satisfies

`det (1 - T F_y ∣ (f₀!F)_ȳ) = ∏_{x ↦ y} det (1 - T^{e_x} F_x ∣ F_x̄)`, `e_x = [κ(x) : κ(y)]`,

the product running over the closed points of `X` above `y`. Similarly, for a `k₀`-scheme `T`
quasi-finite over `k₀` and a Weil sheaf `G` on `T`,

`det (1 - T F ∣ H_c^0(T ⊗ k̄, G)) = ∏_t det (1 - T^{deg t} F_t ∣ G_t̄)`.

The second formula follows from the Grothendieck–Lefschetz trace formula, both sides being
determined by their traces of powers. The first one follows from the second, applied to the point
`Spec κ(y)` and to the fibre `X_y = X ×_Y Spec κ(y)`, whose compactly supported cohomologies in
degree zero are identified by compact support base change and composition.

## Main statements

- `AlgebraicGeometry.WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite`
- `AlgebraicGeometry.WeilSheaf.exists_charpolyRev_stalk_higherLowerShriek_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A scheme which is locally quasi-finite and quasi-compact over a field has finitely many
points. -/
theorem Scheme.Hom.finite_of_locallyQuasiFinite_toSpecField {K : Type u} [Field K]
    {T : Scheme.{u}} (p : T ⟶ Spec (CommRingCat.of K)) [LocallyQuasiFinite p]
    [QuasiCompact p] : Finite T := by
  have h1 := p.finite_preimage_singleton (IsLocalRing.closedPoint K)
  have h2 : p.base ⁻¹' {IsLocalRing.closedPoint K} = Set.univ :=
    Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  rw [h2] at h1
  exact Set.finite_univ_iff.1 h1

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section QuasiFiniteCohomology

variable {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (T ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [LocallyQuasiFinite (T ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology of a Weil sheaf on a `k₀`-scheme quasi-finite over `k₀`
is concentrated in degree zero. -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_of_locallyQuasiFinite
    (G : WeilSheaf k₀ l T) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (G.compactlySupportedCohomology i).carrier := by
  refine WeilSheaf.subsingleton_globalSections_of_isZero ?_
  rcases lt_or_gt_of_ne hi with h | h
  · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, (Int.toNat_of_nonneg h.le).symm⟩
    exact isZero_higherLowerShriek_of_quasiFinite (T ↘ Spec (CommRingCat.of k₀)) n
      (by exact_mod_cast h) G

/-- **The trace formula on a scheme quasi-finite over `k₀`**: the trace of `Fᵐ` on
`H_c^0(T ⊗ k̄, G)` is the sum over the closed points `x` of degree dividing `m` of
`deg x · tr (F_x^{m / deg x})`. -/
theorem WeilSheaf.trace_compactlySupportedCohomology_zero_of_locallyQuasiFinite
    (G : WeilSheaf k₀ l T) {m : ℕ} (hm : m ≠ 0) :
    LinearMap.trace (PadicAlgCl l) (G.compactlySupportedCohomology 0).carrier
        ((G.compactlySupportedCohomology 0).frobeniusEnd ^ m) =
      ∑ᶠ x : T.finitePoints, if (T ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ m then
        ((T ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : PadicAlgCl l) *
          LinearMap.trace (PadicAlgCl l) (G.stalk x).carrier ((G.stalk x).frobeniusEnd ^
            (m / (T ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))
      else 0 := by
  rw [← WeilSheaf.sum_trace_compactlySupportedCohomology G hm, finsum_eq_single _ 0]
  · simp
  · intro i hi
    have := G.subsingleton_compactlySupportedCohomology_of_locallyQuasiFinite hi
    rw [Subsingleton.elim ((G.compactlySupportedCohomology i).frobeniusEnd ^ m) 0, map_zero,
      smul_zero]


/-- **The local polynomial of `H_c^0` of a scheme quasi-finite over `k₀`**:
`det (1 - T F ∣ H_c^0(T ⊗ k̄, G)) = ∏_t det (1 - T^{deg t} F_t ∣ G_t̄)`, the product running over
the (finitely many) closed points `t` of `T`. Both sides are determined by the traces of the
powers of the Frobenius, which agree by the Grothendieck–Lefschetz trace formula. -/
theorem WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite
    (G : WeilSheaf k₀ l T) [Fintype T.finitePoints] :
    (G.compactlySupportedCohomology 0).frobeniusEnd.charpolyRev =
      ∏ t : T.finitePoints, Polynomial.expand _
        ((T ↘ Spec (CommRingCat.of k₀)).degreeOver t.1) (G.stalk t).frobeniusEnd.charpolyRev := by
  refine LinearMap.charpolyRev_eq_prod_expand_of_trace_pow_eq _ _ _ _
    (fun t ↦ Scheme.Hom.degreeOver_ne_zero _ t.2) fun m hm ↦ ?_
  rw [G.trace_compactlySupportedCohomology_zero_of_locallyQuasiFinite hm,
    finsum_eq_sum_of_fintype]

/-- **The local polynomial of `H_c^0` of a point**: if `T` has at most one point, then
`det (1 - T F ∣ H_c^0(T ⊗ k̄, G)) = det (1 - T^{deg t} F_t ∣ G_t̄)` for its closed point `t`. -/
theorem WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton [Subsingleton T]
    (G : WeilSheaf k₀ l T) (t : T.finitePoints) :
    (G.compactlySupportedCohomology 0).frobeniusEnd.charpolyRev =
      Polynomial.expand _ ((T ↘ Spec (CommRingCat.of k₀)).degreeOver t.1)
        (G.stalk t).frobeniusEnd.charpolyRev := by
  let : Fintype T.finitePoints := Fintype.ofFinite _
  rw [G.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite,
    Fintype.prod_subsingleton _ t]

end QuasiFiniteCohomology

section Helpers

/-- The trace bookkeeping behind the Frobenius at a point of a quasi-finite direct image: if the
traces of the powers of `H₁ ≃ H₂` are `d tr (A^{m / d})` (for `d ∣ m`) on the one hand and
`∑ₓ dₓ tr (Bₓ^{m / dₓ})` (for `dₓ ∣ m`) on the other, with `dₓ = d eₓ`, then
`tr (Aⁿ) = ∑_{eₓ ∣ n} eₓ tr (Bₓ^{n / eₓ})`. -/
theorem _root_.FrobeniusModule.trace_pow_eq_sum_of_equiv {K : Type} [Field K] [CharZero K]
    {H₁ H₂ A : FrobeniusModule.{u + 1, 0} K} (E : H₁.Equiv H₂) {ι : Type*} [Fintype ι]
    (B : ι → FrobeniusModule.{u + 1, 0} K) {d : ℕ} (hd : d ≠ 0) (e : ι → ℕ)
    (h₁ : ∀ m : ℕ, m ≠ 0 → LinearMap.trace K H₁.carrier (H₁.frobeniusEnd ^ m) =
      if d ∣ m then (d : K) * LinearMap.trace K A.carrier (A.frobeniusEnd ^ (m / d)) else 0)
    (h₂ : ∀ m : ℕ, m ≠ 0 → LinearMap.trace K H₂.carrier (H₂.frobeniusEnd ^ m) =
      ∑ x, if d * e x ∣ m then ((d * e x : ℕ) : K) *
        LinearMap.trace K (B x).carrier ((B x).frobeniusEnd ^ (m / (d * e x))) else 0)
    (n : ℕ) (hn : n ≠ 0) :
    LinearMap.trace K A.carrier (A.frobeniusEnd ^ n) =
      ∑ x, if e x ∣ n then (e x : K) *
        LinearMap.trace K (B x).carrier ((B x).frobeniusEnd ^ (n / e x)) else 0 := by
  have hdn : d * n ≠ 0 := mul_ne_zero hd hn
  have h := E.trace_frobeniusEnd_pow (d * n)
  rw [h₁ _ hdn, h₂ _ hdn, ite_eq_left (dvd_mul_right d n),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)] at h
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hd
  refine mul_left_cancel₀ hdK (h.symm.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hd)]
  simp only [Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd)]
  split_ifs <;> push_cast <;> ring

end Helpers

section ConcentratedInDegreeZero

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil complex whose cohomology sheaves vanish outside degree zero is its cohomology sheaf in
degree zero, placed in degree zero. -/
theorem WeilComplex.nonempty_iso_toComplex_homologySheaf_zero (K : WeilComplex k₀ l X)
    (h : ∀ b : ℤ, b ≠ 0 → IsZero ((WeilComplex.homologySheaf b).obj K)) :
    Nonempty (K ≅ WeilSheaf.toComplex.obj ((WeilComplex.homologySheaf 0).obj K)) := by
  have : K.obj.IsGE 0 := (_root_.DerivedCategory.isGE_iff _ 0).2 fun i hi ↦
    (WeilComplex.isZero_homologySheaf_obj_iff i K).1 (h i hi.ne)
  have : K.obj.IsLE 0 := (_root_.DerivedCategory.isLE_iff _ 0).2 fun i hi ↦
    (WeilComplex.isZero_homologySheaf_obj_iff i K).1 (h i hi.ne')
  obtain ⟨Y, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj 0
  let eY : (_root_.DerivedCategory.homologyFunctor _ 0).obj K.obj ≅ Y :=
    (_root_.DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y
  let G' : WeilSheaf k₀ l X := ⟨Y, (WeilSheaf.objectProperty k₀ l X).prop_of_iso eY (K.2.2 0)⟩
  let e' : K ≅ WeilSheaf.toComplex.obj G' := ObjectProperty.isoMk _ e
  exact ⟨e' ≪≫ WeilSheaf.toComplex.mapIso
    ((WeilSheaf.toComplexCompHomologySheafIso.app G').symm ≪≫
      (WeilComplex.homologySheaf 0).mapIso e'.symm)⟩

end ConcentratedInDegreeZero

section Fibre

/-- The direct image with compact support only depends on the morphism, not on the instance
arguments through which it is formed. -/
noncomputable def WeilComplex.derivedLowerShriekCongr {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f f' : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (h : f = f') :
    WeilComplex.derivedLowerShriek k₀ l f ≅ WeilComplex.derivedLowerShriek k₀ l f' := by
  subst h
  exact Iso.refl _

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyQuasiFinite f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f'] [LocallyOfFiniteType f']
  [QuasiCompact f'] [IsSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
  {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
  [h.IsOver (Spec (CommRingCat.of k₀))]

/-- **Compact support base change in degree zero for a quasi-finite morphism.** For a cartesian
square `X' = X ×_Y Y'` of `k₀`-schemes with `f : X ⟶ Y` separated and quasi-finite, the
compactly supported cohomology in degree zero of the restriction `h^*(f₀!F)` of the direct image
of a Weil sheaf `F` is that of the restriction `g^*F`: `Rf₀!F = f₀!F` is concentrated in degree
zero, `h^* Rf₀! ≅ Rf'₀! g^*`, and `R(f' ≫ a_{Y'})₀! ≅ R(a_{Y'})₀! ∘ Rf'₀!`. -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_upperStar_higherLowerShriek
    (hH : IsPullback g f' f h) (F : WeilSheaf k₀ l X) :
    Nonempty ((((WeilSheaf.upperStar h).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj
      F)).compactlySupportedCohomology 0).Equiv
        (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology 0)) := by
  -- `Rf₀!F` is `f₀!F` placed in degree zero
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_toComplex_homologySheaf_zero
    ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)) fun b hb ↦ by
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg F hb
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
        exact isZero_higherLowerShriek_of_quasiFinite f n (by exact_mod_cast hb) F
  obtain ⟨e₃⟩ := WeilComplex.nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) hH
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f'
    (Y' ↘ Spec (CommRingCat.of k₀))
  -- the identification of the complexes on `Y'`
  let E : WeilSheaf.toComplex.obj ((WeilSheaf.upperStar h).obj
      ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)) ≅
      (WeilComplex.derivedLowerShriek k₀ l f').obj
        (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar g).obj F)) :=
    (WeilComplex.upperStarToComplexIso h _).symm ≪≫
      (WeilComplex.upperStar h).mapIso e₂.symm ≪≫ e₃.app _ ≪≫
      (WeilComplex.derivedLowerShriek k₀ l f').mapIso (WeilComplex.upperStarToComplexIso g F)
  let E' := (WeilComplex.derivedLowerShriek k₀ l (Y' ↘ Spec (CommRingCat.of k₀))).mapIso E ≪≫
    (e₅.app _).symm ≪≫ (WeilComplex.derivedLowerShriekCongr (comp_over f' _)).app _
  exact ⟨WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf 0).mapIso E')⟩

omit [IsSeparated (X' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))] in
/-- **Base change for the degree-zero direct image with compact support of a quasi-finite
morphism.** For a cartesian square `X' = X ×_Y Y'` of `k₀`-schemes with `f : X ⟶ Y` separated and
quasi-finite, `h^*(f₀!F) ≅ f'₀!(g^*F)`: `Rf₀!F = f₀!F` is concentrated in degree zero and
`h^* Rf₀! ≅ Rf'₀! g^*`. -/
theorem WeilSheaf.nonempty_upperStar_higherLowerShriek_zero_iso
    (hH : IsPullback g f' f h) (F : WeilSheaf k₀ l X) :
    Nonempty ((WeilSheaf.upperStar h).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F) ≅
      (WeilSheaf.higherLowerShriek k₀ l f' 0).obj ((WeilSheaf.upperStar g).obj F)) := by
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_toComplex_homologySheaf_zero
    ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)) fun b hb ↦ by
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg F hb
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
        exact isZero_higherLowerShriek_of_quasiFinite f n (by exact_mod_cast hb) F
  obtain ⟨e₃⟩ := WeilComplex.nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) hH
  let E : WeilSheaf.toComplex.obj ((WeilSheaf.upperStar h).obj
      ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F)) ≅
      (WeilComplex.derivedLowerShriek k₀ l f').obj
        (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar g).obj F)) :=
    (WeilComplex.upperStarToComplexIso h _).symm ≪≫
      (WeilComplex.upperStar h).mapIso e₂.symm ≪≫ e₃.app _ ≪≫
      (WeilComplex.derivedLowerShriek k₀ l f').mapIso (WeilComplex.upperStarToComplexIso g F)
  exact ⟨(WeilSheaf.toComplexCompHomologySheafIso.app _).symm ≪≫
    (WeilComplex.homologySheaf 0).mapIso E⟩

end Fibre

section StalkFormula

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The degree over `k₀` of the image of a point with finite residue field divides the degree of
the point. -/
theorem Scheme.Hom.degreeOver_dvd_of_isOver {x : X} (hx : x ∈ X.finitePoints) :
    (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (f.base x) ∣
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver x := by
  have := Scheme.Hom.degreeOver_dvd_degreeOver_comp f (Y ↘ Spec (CommRingCat.of k₀)) hx
  rwa [comp_over] at this

variable [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The local Frobenius of a quasi-finite direct image** (blueprint:
`lemma-finite-quasi-finite-direct-images`). For `f : X ⟶ Y` separated and quasi-finite and a closed
point `y` of `Y`, there are finitely many closed points `x` of `X` above `y`, and
`det (1 - T F_y ∣ (f₀!F)_ȳ) = ∏_{x ↦ y} det (1 - T^{e_x} F_x ∣ F_x̄)`, with
`e_x = deg x / deg y = [κ(x) : κ(y)]` (see `Scheme.Hom.degreeOver_dvd_of_isOver`). -/
theorem WeilSheaf.exists_charpolyRev_stalk_higherLowerShriek_zero (F : WeilSheaf k₀ l X)
    (y : Y.finitePoints) :
    ∃ s : Finset X.finitePoints, (∀ x : X.finitePoints, x ∈ s ↔ f.base x.1 = y.1) ∧
      (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobeniusEnd.charpolyRev =
        ∏ x ∈ s, Polynomial.expand _ ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 /
          (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1) (F.stalk x).frobeniusEnd.charpolyRev := by
  classical
  -- the closed point `y`, as the spectrum of its residue field, a finite extension of `k₀`
  let Z : Scheme.{u} := Spec (Y.residueField y.1)
  let i : Z ⟶ Y := Y.fromSpecResidueField y.1
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : Finite (Y.residueField y.1) := y.2
  have : IsFinite (Z ↘ Spec (CommRingCat.of k₀)) := by
    change IsFinite (i ≫ Y ↘ Spec (CommRingCat.of k₀))
    rw [← Scheme.Hom.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff]
    let := ((Y ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap y.1).toAlgebra
    exact Module.Finite.of_finite
  -- the fibre `X_y = X ×_Y Spec κ(y)`
  obtain ⟨Xy, g, f', hH⟩ : ∃ (Xy : Scheme.{u}) (g : Xy ⟶ X) (f' : Xy ⟶ Z), IsPullback g f' f i :=
    ⟨_, _, _, IsPullback.of_hasPullback f i⟩
  let : Xy.Over (Spec (CommRingCat.of k₀)) := ⟨g ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : g.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : f'.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change f' ≫ i ≫ Y ↘ Spec (CommRingCat.of k₀) = g ≫ X ↘ Spec (CommRingCat.of k₀)
    rw [← Category.assoc, ← hH.w, Category.assoc, comp_over]⟩
  have : IsSeparated f' := MorphismProperty.of_isPullback hH ‹_›
  have : LocallyQuasiFinite f' := MorphismProperty.of_isPullback hH ‹_›
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hH ‹_›
  have : QuasiCompact f' := MorphismProperty.of_isPullback hH ‹_›
  have : IsPreimmersion g :=
    MorphismProperty.of_isPullback hH.flip (inferInstance : IsPreimmersion i)
  have hX' : Xy ↘ Spec (CommRingCat.of k₀) = f' ≫ Z ↘ Spec (CommRingCat.of k₀) :=
    (comp_over f' _).symm
  have : IsSeparated (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  have : LocallyOfFiniteType (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  have : QuasiCompact (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  have : LocallyQuasiFinite (Xy ↘ Spec (CommRingCat.of k₀)) := by rw [hX']; infer_instance
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_upperStar_higherLowerShriek
    hH F
  -- the degree `d` of `y` and the unique point `z₀` of `Z`
  set d := (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 with hd_def
  have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ y.2
  let z₀ : Z := IsLocalRing.closedPoint (Y.residueField y.1)
  have hiz : ∀ z : Z, i.base z = y.1 := fun z ↦ Scheme.fromSpecResidueField_apply _ _
  have : ∀ z : Z, IsIso (i.residueFieldMap z) := fun z ↦ Scheme.Hom.isIso_residueFieldMap i z
  have hz₀ : z₀ ∈ Z.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso i z₀).1 ((hiz z₀).symm ▸ y.2)
  have hdegZ : ∀ z : Z, (Z ↘ Spec (CommRingCat.of k₀)).degreeOver z = d := fun z ↦ by
    change (i ≫ Y ↘ Spec (CommRingCat.of k₀)).degreeOver z = d
    rw [Scheme.Hom.degreeOver_comp_of_isIso, hiz]
  have hy : (⟨i.base z₀, Scheme.Hom.map_mem_finitePoints i hz₀⟩ : Y.finitePoints) = y :=
    Subtype.ext (hiz z₀)
  -- `H_c^0` of the point
  have hZ : (((WeilSheaf.upperStar i).obj ((WeilSheaf.higherLowerShriek k₀ l f 0).obj
      F)).compactlySupportedCohomology 0).frobeniusEnd.charpolyRev = Polynomial.expand _ d
        (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).stalk y).frobeniusEnd.charpolyRev := by
    rw [WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton _ ⟨z₀, hz₀⟩,
      hdegZ, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def,
      WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar, hy, hdegZ, hiz, ← hd_def,
      Nat.div_self (Nat.pos_of_ne_zero hd), pow_one]
  -- `H_c^0` of the fibre
  have : ∀ x : Xy, IsIso (g.residueFieldMap x) := fun x ↦ Scheme.Hom.isIso_residueFieldMap g x
  have hdegX : ∀ x : Xy, (Xy ↘ Spec (CommRingCat.of k₀)).degreeOver x =
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver (g.base x) := fun x ↦
    Scheme.Hom.degreeOver_comp_of_isIso g (X ↘ Spec (CommRingCat.of k₀)) x
  have : Finite Xy :=
    Scheme.Hom.finite_of_locallyQuasiFinite_toSpecField (Xy ↘ Spec (CommRingCat.of k₀))
  let : Fintype Xy.finitePoints := Fintype.ofFinite _
  let φ : Xy.finitePoints → X.finitePoints :=
    fun x ↦ ⟨g.base x.1, Scheme.Hom.map_mem_finitePoints g x.2⟩
  have hφ : Function.Injective φ := fun a b hab ↦
    Subtype.ext (g.isEmbedding.injective (congrArg Subtype.val hab))
  have hfφ : ∀ x : Xy.finitePoints, f.base (φ x).1 = y.1 := fun x ↦
    (congrArg (fun h : Xy ⟶ Y ↦ h.base x.1) hH.w).trans (hiz _)
  have hdvd : ∀ x : Xy.finitePoints, d ∣ (X ↘ Spec (CommRingCat.of k₀)).degreeOver (φ x).1 :=
    fun x ↦ by
      have := Scheme.Hom.degreeOver_dvd_of_isOver (k₀ := k₀) f (φ x).2
      rwa [hfφ] at this
  have hXy : (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology
      0).frobeniusEnd.charpolyRev =
      Polynomial.expand _ d (∏ x : Xy.finitePoints, Polynomial.expand _
        ((X ↘ Spec (CommRingCat.of k₀)).degreeOver (φ x).1 / d)
          (F.stalk (φ x)).frobeniusEnd.charpolyRev) := by
    rw [WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_locallyQuasiFinite, map_prod]
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [← Polynomial.expand_mul, Nat.mul_div_cancel' (hdvd x), hdegX, LinearMap.charpolyRev_def,
      LinearMap.charpolyRev_def, WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar, hdegX,
      Nat.div_self (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ (φ x).2)), pow_one]
  have hEq := E.localPolynomial_eq
  simp only [FrobeniusModule.localPolynomial] at hEq
  rw [hZ, hXy] at hEq
  refine ⟨Finset.univ.image φ, fun x ↦ ⟨?_, fun hx ↦ ?_⟩, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨x, rfl⟩
    exact hfφ x
  · -- every closed point above `y` lies in the fibre
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := i) x.1 z₀
      (hx.trans (hiz z₀).symm)
    have hgp : g.base (hH.isoPullback.inv.base p) = x.1 :=
      (congrArg (fun h ↦ h.base p) hH.isoPullback_inv_fst).trans hp
    have hmem : hH.isoPullback.inv.base p ∈ Xy.finitePoints :=
      (Scheme.Hom.mem_finitePoints_iff_of_isIso g _).1 (hgp ▸ x.2)
    exact Finset.mem_image.2 ⟨⟨_, hmem⟩, Finset.mem_univ _, Subtype.ext hgp⟩
  · rw [Finset.prod_image fun a _ b _ hab ↦ hφ hab]
    exact Polynomial.expand_injective (Nat.pos_of_ne_zero hd) hEq

end StalkFormula

end AlgebraicGeometry
