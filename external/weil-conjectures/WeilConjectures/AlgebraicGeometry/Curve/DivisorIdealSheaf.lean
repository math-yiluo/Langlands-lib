/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Ideal sheaves of effective divisors on a smooth curve

Let `C` be an integral smooth curve over a field `k`. The local rings of `C` at closed points
are discrete valuation rings, so a rational function `f ∈ k(C)` is regular on an open `V` as
soon as its order of vanishing is nonnegative at every point of `V`
(`AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg`).

An effective divisor `E = ∑_P n_P [P]` defines the invertible ideal sheaf
`𝒪_C(-E) = ∏_P 𝓘_P^{n_P}` (`AlgebraicGeometry.Scheme.Divisor.idealSheaf`). The order at `P` of a
local generator of `𝒪_C(-E)` is `n_P`, and every invertible ideal sheaf is of this form. These
ideal sheaves give a concrete description of line bundles on `C`: `𝒪_C(-E₁) ≅ 𝒪_C(-E₂)` if and
only if `E₁ - E₂` is principal, and every invertible module is `𝒪_C(E₁) ⊗ 𝒪_C(-E₂)`. This is the
input for the identification of the divisor class group with the Picard group
(`AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic`, blueprint
`proposition-cohomology-smooth-affine-curve`).

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.ordAt`: the order at a point of an ideal sheaf, the
  order of vanishing of a local generator.
- `AlgebraicGeometry.Scheme.Divisor.idealSheaf`: the ideal sheaf `𝒪_C(-E)` of an effective
  divisor `E`.
- `AlgebraicGeometry.Scheme.IdealSheafData.toModulesOfLE`: the inclusion `I ⊆ J` of ideal sheaves
  as a morphism of modules.
- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.ratCoord`: the coordinate in the function
  field of a section of an invertible module with respect to a trivialization.

## Main statements

- `AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_ord_nonneg`: a rational function
  with nonnegative orders on `V` is regular on `V`.
- `AlgebraicGeometry.Scheme.Divisor.ordAt_idealSheaf`: `𝒪_C(-E)` has order `n_P` at `P`.
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_toModules_iso_dual_tensorObj_mul`:
  `I ≅ Jᵛ ⊗ I J` for invertible ideal sheaves `I` and `J`.
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_eq_idealSheaf`: every invertible
  ideal sheaf is `𝒪_C(-E)` for an effective divisor `E`.
- `AlgebraicGeometry.Scheme.Divisor.nonempty_toModules_idealSheaf_iso_of_ord_eq`,
  `AlgebraicGeometry.Scheme.Divisor.exists_ord_eq_of_nonempty_iso`: `𝒪_C(-E₂) ≅ 𝒪_C(-E₁)` if and
  only if `E₁ - E₂` is the divisor of a rational function.
- `AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_dual_toModules_idealSheaf_tensorObj`:
  every invertible module is `𝒪_C(E₁) ⊗ 𝒪_C(-E₂)` (blueprint
  `theorem-riemann-roch-coherent-serre-duality--1`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Order

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section Integral

variable [IsIntegral X]

lemma germToFunctionField_map {U V : X.Opens} (h : V ≤ U) [Nonempty V] [Nonempty U]
    (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) = X.germToFunctionField U a :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ a

/-- Two sections of the structure sheaf of an integral scheme are equal as soon as they have the
same image in the function field (there is nothing to check over the empty open). -/
lemma eq_of_germToFunctionField_eq {W : X.Opens} {a b : Γ(X, W)}
    (h : ∀ _ : Nonempty W, X.germToFunctionField W a = X.germToFunctionField W b) : a = b := by
  rcases isEmpty_or_nonempty W with hW | hW
  · have : Subsingleton Γ(X, W) := CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty (by ext z; exact iff_false_intro fun hz ↦ hW.false ⟨z, hz⟩))
    exact Subsingleton.elim _ _
  · exact X.germToFunctionField_injective W (h hW)

/-- The order of vanishing of a regular function is nonnegative. -/
lemma ord_germToFunctionField_nonneg [IsLocallyNoetherian X] {U : X.Opens} [Nonempty U]
    (a : Γ(X, U)) {y : X} (hy : y ∈ U) : 0 ≤ X.ord (X.germToFunctionField U a) y := by
  by_cases hy1 : coheight y = 1
  · by_cases ha : X.germToFunctionField U a = 0
    · rw [ha, ord_zero]
      rfl
    rw [le_ord_iff hy1 ha, ← algebraMap_germ_eq_germToFunctionField _ hy]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hy1.le
    have hne : X.presheaf.germ U y hy a ≠ 0 := by
      rintro h0
      rw [← algebraMap_germ_eq_germToFunctionField _ hy, h0, map_zero] at ha
      exact ha rfl
    exact Ring.ordFrac_ge_one_of_ne_zero hne
  · rw [ord_eq_zero_of_coheight_neq_one hy1]

/-- A point of coheight zero of an integral scheme is its generic point. -/
lemma eq_genericPoint_of_coheight_eq_zero {y : X} (hy : coheight y = 0) : y = genericPoint X := by
  rw [coheight_eq_zero] at hy
  have h : y ≤ genericPoint X := (genericPoint_spec X).specializes trivial
  have h' := hy h
  exact ((genericPoint_spec X).specializes trivial).antisymm h' |>.eq.symm

omit [IsIntegral X] in
/-- On an affine open `U`, the restriction of a generator of an ideal sheaf generates it on every
smaller affine open. -/
lemma IdealSheafData.ideal_eq_span_map (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U)
    {b : Γ(X, U.1)} (hb : I.ideal U = Ideal.span {b}) :
    I.ideal V = Ideal.span {X.presheaf.map (homOfLE h).op b} := by
  rw [← I.map_ideal h, hb, Ideal.map_span, Set.image_singleton]

omit [IsIntegral X] in
/-- Every point of an open `O` has an affine neighbourhood inside `O` on which a locally principal
ideal sheaf is principal. -/
lemma IdealSheafData.IsLocallyPrincipal.exists_ideal_eq_span {I : X.IdealSheafData}
    (hI : I.IsLocallyPrincipal) {y : X} {O : X.Opens} (hyO : y ∈ O) :
    ∃ U : X.affineOpens, y ∈ U.1 ∧ U.1 ≤ O ∧ ∃ b : Γ(X, U.1), I.ideal U = Ideal.span {b} := by
  obtain ⟨U, hyU, ⟨b, hb⟩⟩ := hI y
  obtain ⟨g, hgO, hyg⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ O) ⟨y, hyU, hyO⟩ hyU
  have hWU : X.affineBasicOpen g ≤ U := X.basicOpen_le g
  exact ⟨X.affineBasicOpen g, hyg, hgO.trans inf_le_right, _,
    I.ideal_eq_span_map hWU hb⟩

omit [IsIntegral X] in
/-- Every point of an open `O` has an affine neighbourhood inside `O` on which two locally
principal ideal sheaves are principal. -/
lemma IdealSheafData.IsLocallyPrincipal.exists_ideal_eq_span₂ {I J : X.IdealSheafData}
    (hI : I.IsLocallyPrincipal) (hJ : J.IsLocallyPrincipal) {y : X} {O : X.Opens} (hyO : y ∈ O) :
    ∃ W : X.affineOpens, y ∈ W.1 ∧ W.1 ≤ O ∧ (∃ a : Γ(X, W.1), I.ideal W = Ideal.span {a}) ∧
      ∃ b : Γ(X, W.1), J.ideal W = Ideal.span {b} := by
  obtain ⟨U, hyU, hUO, a, ha⟩ := hI.exists_ideal_eq_span hyO
  obtain ⟨W, hyW, hWU, b, hb⟩ := hJ.exists_ideal_eq_span hyU
  exact ⟨W, hyW, hWU.trans hUO, ⟨_, I.ideal_eq_span_map (V := W) hWU ha⟩, b, hb⟩

variable [IsLocallyNoetherian X]

/-- **The order of a local generator of an ideal sheaf is well defined.** If `b` and `b'`
generate an ideal sheaf `I` on affine neighbourhoods of `y`, they have the same order at `y`:
on a common basic open they generate the same principal ideal, so they differ by a unit. -/
lemma IdealSheafData.ord_eq_of_ideal_eq_span (I : X.IdealSheafData) {U U' : X.affineOpens}
    {b : Γ(X, U.1)} {b' : Γ(X, U'.1)} {y : X} (hy : y ∈ U.1) (hy' : y ∈ U'.1)
    (hb : I.ideal U = Ideal.span {b}) (hb' : I.ideal U' = Ideal.span {b'}) :
    haveI : Nonempty U.1 := ⟨⟨y, hy⟩⟩
    haveI : Nonempty U'.1 := ⟨⟨y, hy'⟩⟩
    X.ord (X.germToFunctionField U.1 b) y = X.ord (X.germToFunctionField U'.1 b') y := by
  have : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  have : Nonempty U'.1 := ⟨⟨y, hy'⟩⟩
  obtain ⟨g, hgU', hyg⟩ := U.2.exists_basicOpen_le ⟨y, hy'⟩ hy
  have hWU : X.affineBasicOpen g ≤ U := X.basicOpen_le g
  have hWU' : X.affineBasicOpen g ≤ U' := hgU'
  have : Nonempty (X.basicOpen g) := ⟨⟨y, hyg⟩⟩
  obtain ⟨u, hu⟩ : Associated (X.presheaf.map (homOfLE (X.basicOpen_le g)).op b)
      (X.presheaf.map (homOfLE hgU').op b') :=
    Ideal.span_singleton_eq_span_singleton.mp
      ((I.ideal_eq_span_map hWU hb).symm.trans (I.ideal_eq_span_map hWU' hb'))
  have h3 : X.germToFunctionField (X.basicOpen g)
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op b) *
      X.germToFunctionField (X.basicOpen g) u.1 =
      X.germToFunctionField (X.basicOpen g) (X.presheaf.map (homOfLE hgU').op b') := by
    rw [← map_mul, hu]
  rw [germToFunctionField_map, germToFunctionField_map] at h3
  rw [← h3]
  by_cases hb0 : X.germToFunctionField U.1 b = 0
  · rw [hb0, zero_mul]
  have hu0 : X.germToFunctionField (X.basicOpen g) u.1 ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective (X.basicOpen g))).mpr u.isUnit.ne_zero
  rw [ord_mul hb0 hu0, ord_of_isUnit u.isUnit hyg, add_zero]

open Classical in
/-- The **order** of an ideal sheaf `I` at a point `y`: the order of vanishing at `y` of a
generator of `I` on an affine neighbourhood of `y` (and `0` if there is none). It does not depend
on the generator by `AlgebraicGeometry.Scheme.IdealSheafData.ord_eq_of_ideal_eq_span`. -/
noncomputable def IdealSheafData.ordAt (I : X.IdealSheafData) (y : X) : ℤ :=
  if h : ∃ (U : X.affineOpens) (_ : y ∈ U.1) (b : Γ(X, U.1)), I.ideal U = Ideal.span {b} then
    haveI : Nonempty h.choose.1 := ⟨⟨y, h.choose_spec.choose⟩⟩
    X.ord (X.germToFunctionField h.choose.1 h.choose_spec.choose_spec.choose) y
  else 0

/-- The order of an ideal sheaf at `y` is the order of any local generator at `y`. -/
lemma IdealSheafData.ordAt_eq (I : X.IdealSheafData) {U : X.affineOpens} {b : Γ(X, U.1)}
    {y : X} (hy : y ∈ U.1) (hb : I.ideal U = Ideal.span {b}) :
    haveI : Nonempty U.1 := ⟨⟨y, hy⟩⟩
    I.ordAt y = X.ord (X.germToFunctionField U.1 b) y := by
  have h : ∃ (U : X.affineOpens) (_ : y ∈ U.1) (b : Γ(X, U.1)), I.ideal U = Ideal.span {b} :=
    ⟨U, hy, b, hb⟩
  rw [ordAt, dite_eq_left h]
  exact I.ord_eq_of_ideal_eq_span h.choose_spec.choose hy h.choose_spec.choose_spec.choose_spec hb

/-- The order of an ideal sheaf at a point is nonnegative. -/
lemma IdealSheafData.ordAt_nonneg (I : X.IdealSheafData) (y : X) : 0 ≤ I.ordAt y := by
  by_cases h : ∃ (U : X.affineOpens) (_ : y ∈ U.1) (b : Γ(X, U.1)), I.ideal U = Ideal.span {b}
  · obtain ⟨U, hy, b, hb⟩ := h
    have : Nonempty U.1 := ⟨⟨y, hy⟩⟩
    rw [I.ordAt_eq hy hb]
    exact ord_germToFunctionField_nonneg b hy
  · rw [IdealSheafData.ordAt, dite_eq_right h]

/-- The unit ideal sheaf has order zero everywhere. -/
@[simp]
lemma IdealSheafData.ordAt_top (y : X) : (⊤ : X.IdealSheafData).ordAt y = 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  rw [(⊤ : X.IdealSheafData).ordAt_eq (U := ⟨U, hU⟩) (b := 1) hyU (by simp)]
  exact ord_of_isUnit isUnit_one hyU

/-- **The order of a product of invertible ideal sheaves is the sum of the orders.** -/
lemma IdealSheafData.ordAt_mul {I J : X.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) (y : X) : (I * J).ordAt y = I.ordAt y + J.ordAt y := by
  obtain ⟨U, hyU, -, a, ha⟩ := hI.isLocallyPrincipal.exists_ideal_eq_span (O := ⊤) trivial
  obtain ⟨V, hyV, hVU, b, hb⟩ := hJ.isLocallyPrincipal.exists_ideal_eq_span hyU
  have hVU' : V ≤ U := hVU
  have : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  have : Nonempty V.1 := ⟨⟨y, hyV⟩⟩
  have ha' := I.ideal_eq_span_map hVU' ha
  have hab : (I * J).ideal V = Ideal.span {X.presheaf.map (homOfLE hVU').op a * b} := by
    rw [ideal_mul, Pi.mul_apply, ha', hb, Ideal.span_singleton_mul_span_singleton]
  rw [IdealSheafData.ordAt_eq _ hyV hab, I.ordAt_eq hyV ha', J.ordAt_eq hyV hb, map_mul]
  have h0 (c : Γ(X, V.1)) (hc : c ∈ nonZeroDivisors Γ(X, V.1)) :
      X.germToFunctionField V.1 c ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr (nonZeroDivisors.ne_zero hc)
  exact ord_mul (h0 _ (hI.mem_nonZeroDivisors ha')) (h0 _ (hJ.mem_nonZeroDivisors hb))

lemma IdealSheafData.ordAt_pow {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) (y : X) :
    (I ^ n).ordAt y = n * I.ordAt y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, IdealSheafData.ordAt_mul (hI.pow n) hI, ih]
    push_cast
    ring

/-- The order of a quotient: `ord (a / b) = ord a - ord b` for nonzero `a` and `b`. -/
lemma ord_div {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (y : X) :
    X.ord (a / b) y = X.ord a y - X.ord b y := by
  have h := ord_mul (x := y) (div_ne_zero ha hb) hb
  rw [div_mul_cancel₀ a hb] at h
  omega

end Integral

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f]

include f in
/-- Every point of a smooth curve has coheight at most one. -/
lemma coheight_le_one_of_smoothOfRelativeDimension_one (y : C) : coheight y ≤ 1 := by
  have hle : ringKrullDim (C.presheaf.stalk y) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim y).trans
      (by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension f 1)
  rw [ringKrullDim_stalk_eq_coheight] at hle
  exact_mod_cast hle

include f in
/-- A closed point of a smooth curve has coheight one. -/
lemma coheight_eq_one_of_isClosed {P : C} (hP : IsClosed {P}) : coheight P = 1 := by
  have h := ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one f hP
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

include f in
/-- On a quasi-compact smooth curve, a point of coheight one is closed: its closure contains a
closed point, which has coheight one as well. -/
lemma isClosed_of_coheight_eq_one [CompactSpace C] {y : C} (hy : coheight y = 1) :
    IsClosed {y} := by
  by_contra hnc
  obtain ⟨z, hz, hzc⟩ :=
    isClosed_closure.exists_closed_singleton (S := closure {y}) ⟨y, subset_closure rfl⟩
  have hne : z ≠ y := fun h ↦ hnc (h ▸ hzc)
  have h := coheight_add_one_le
    (lt_of_specializes_of_ne C (specializes_iff_mem_closure.2 hz) hne)
  rw [hy, coheight_eq_one_of_isClosed f hzc] at h
  exact absurd h (by decide)

variable [IsIntegral C] [IsLocallyNoetherian C]

omit [IsLocallyNoetherian C] in
include f in
/-- The local ring of a smooth curve at a point of coheight one is a discrete valuation ring. -/
lemma isDiscreteValuationRing_stalk_of_coheight_eq_one {y : C} (hy : coheight y = 1) :
    IsDiscreteValuationRing (C.presheaf.stalk y) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have := IsRegular.of_smooth f
  exact IsRegularLocalRing.isDiscreteValuationRing _
    (by rw [ringKrullDim_stalk_eq_coheight, hy]; rfl)

include f in
/-- A rational function on a smooth curve with nonnegative order at `y` lies in the local ring
at `y`. -/
lemma exists_algebraMap_eq_of_ord_nonneg {x : C.functionField} {y : C}
    (hy : 0 ≤ C.ord x y) : ∃ s : C.presheaf.stalk y, algebraMap _ C.functionField s = x := by
  rcases (coheight_le_one_of_smoothOfRelativeDimension_one f y).lt_or_eq with h | h
  · obtain rfl := eq_genericPoint_of_coheight_eq_zero (Order.lt_one_iff.mp h)
    obtain ⟨U, hU, c, hc⟩ := C.presheaf.exists_germ_eq x
    have : Nonempty U := ⟨⟨_, hU⟩⟩
    exact ⟨C.presheaf.germ U _ hU c, (algebraMap_germ_eq_germToFunctionField _ hU c).trans hc⟩
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one f h
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (C.presheaf.stalk y)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hy
  have : Ring.KrullDimLE 1 (C.presheaf.stalk y) := krullDimLE_of_coheight_le h.le
  have hord : Ring.ordFrac (C.presheaf.stalk y) x =
      Ring.ordFrac (C.presheaf.stalk y) (algebraMap _ C.functionField (π ^ n)) := by
    rw [map_pow, map_pow, Ring.ordFrac_irreducible hπ, ← WithZero.exp_nsmul, nsmul_eq_mul,
      mul_one, ← hn]
    exact (ord_eq_iff h hx).mp rfl
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq _ _ hord
  refine ⟨(u⁻¹ : (C.presheaf.stalk y)ˣ) * π ^ n, ?_⟩
  rw [map_mul, ← hu, Units.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul,
    Units.inv_mul, map_one, one_mul]

include f in
/-- **Regular functions on a smooth curve.** A rational function whose order of vanishing is
nonnegative at every point of a nonempty open `V` of a smooth curve is regular on `V`: it is the
image of a section over `V`. Locally this holds since the local rings at closed points are
discrete valuation rings, and these local sections glue. -/
theorem exists_germToFunctionField_eq_of_ord_nonneg {V : C.Opens} [Nonempty V]
    {x : C.functionField} (hx : ∀ y ∈ V, 0 ≤ C.ord x y) :
    ∃ c : Γ(C, V), C.germToFunctionField V c = x := by
  have key (y : V) : ∃ (W : C.Opens) (hW : W ≤ V) (hyW : y.1 ∈ W) (c : Γ(C, W)),
      haveI : Nonempty W := ⟨⟨_, hyW⟩⟩
      C.germToFunctionField W c = x := by
    obtain ⟨s, hs⟩ := exists_algebraMap_eq_of_ord_nonneg f (hx y.1 y.2)
    obtain ⟨W, hWV, hyW, c, hc⟩ := C.presheaf.exists_le_germ_eq s y.2
    have : Nonempty W := ⟨⟨_, hyW⟩⟩
    exact ⟨W, hWV, hyW, c, by rw [← algebraMap_germ_eq_germToFunctionField _ hyW, hc, hs]⟩
  choose W hWV hyW c hc using key
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' C.sheaf W V (fun y ↦ homOfLE (hWV y))
    (fun y hy ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyW _⟩) c fun y z ↦ by
      refine eq_of_germToFunctionField_eq fun hne ↦ ?_
      have : Nonempty (W y) := ⟨⟨_, hyW y⟩⟩
      have : Nonempty (W z) := ⟨⟨_, hyW z⟩⟩
      exact (germToFunctionField_map inf_le_left (c y)).trans
        ((hc y).trans ((hc z).symm.trans (germToFunctionField_map inf_le_right (c z)).symm))
  obtain ⟨y⟩ := ‹Nonempty V›
  have : Nonempty (W y) := ⟨⟨_, hyW y⟩⟩
  exact ⟨t, (germToFunctionField_map (hWV y) t).symm.trans ((congrArg _ (ht y)).trans (hc y))⟩

include f in
/-- A rational function of order zero at every point of a nonempty open `V` of a smooth curve is
a unit on `V`. -/
theorem exists_isUnit_germToFunctionField_eq_of_ord_eq_zero {V : C.Opens} [Nonempty V]
    {x : C.functionField} (hx0 : x ≠ 0) (hx : ∀ y ∈ V, C.ord x y = 0) :
    ∃ c : Γ(C, V), IsUnit c ∧ C.germToFunctionField V c = x := by
  obtain ⟨c, hc⟩ := exists_germToFunctionField_eq_of_ord_nonneg f fun y hy ↦ (hx y hy).ge
  obtain ⟨d, hd⟩ := exists_germToFunctionField_eq_of_ord_nonneg f (x := x⁻¹) fun y hy ↦ by
    have h := ord_mul (x := y) hx0 (inv_ne_zero hx0)
    have h1 := ord_of_isUnit (U := V) isUnit_one hy
    rw [map_one] at h1
    rw [mul_inv_cancel₀ hx0, hx y hy, h1] at h
    omega
  refine ⟨c, IsUnit.of_mul_eq_one d (C.germToFunctionField_injective V ?_), hc⟩
  rw [map_mul, map_one, hc, hd, mul_inv_cancel₀ hx0]

/-! ### The order of the ideal sheaf of a closed point -/

omit [IsIntegral C] [IsLocallyNoetherian C] in
/-- The ideal sheaf of a closed point `P` is the unit ideal on affine opens avoiding `P`. -/
lemma vanishingIdeal_ideal_eq_top {P : C} (hP : IsClosed {P}) {U : C.Opens} (hU : IsAffineOpen U)
    (hPU : P ∉ U) : (IdealSheafData.vanishingIdeal ⟨{P}, hP⟩).ideal ⟨U, hU⟩ = ⊤ := by
  rw [IdealSheafData.vanishingIdeal_ideal]
  have : hU.fromSpec ⁻¹' {P} = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hy
    have : hU.fromSpec y ∈ (U : Set C) := hU.range_fromSpec ▸ ⟨y, rfl⟩
    exact hPU (hy ▸ this)
  erw [this]
  exact PrimeSpectrum.vanishingIdeal_empty

omit [IsIntegral C] [IsLocallyNoetherian C] in
/-- On an affine open `U` containing a closed point `P`, the ideal sheaf of `P` is the prime
ideal of `P`. -/
lemma vanishingIdeal_ideal_eq_primeIdealOf {P : C} (hP : IsClosed {P}) {U : C.Opens}
    (hU : IsAffineOpen U) (hPU : P ∈ U) :
    (IdealSheafData.vanishingIdeal ⟨{P}, hP⟩).ideal ⟨U, hU⟩ =
      (hU.primeIdealOf ⟨P, hPU⟩).asIdeal := by
  rw [IdealSheafData.vanishingIdeal_ideal]
  have : hU.fromSpec ⁻¹' {P} = {hU.primeIdealOf ⟨P, hPU⟩} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hy
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hy, hU.fromSpec_primeIdealOf]
    · rintro rfl; exact hU.fromSpec_primeIdealOf ⟨P, hPU⟩
  erw [this]
  exact PrimeSpectrum.vanishingIdeal_singleton _

include f in
/-- The ideal sheaf of a closed point `P` of a smooth curve has order one at `P`: a local
generator is a uniformizer of the discrete valuation ring `𝒪_{C,P}`. -/
lemma ordAt_vanishingIdeal_self {P : C} (hP : IsClosed {P}) :
    (IdealSheafData.vanishingIdeal ⟨{P}, hP⟩).ordAt P = 1 := by
  have hP1 := coheight_eq_one_of_isClosed f hP
  have := isDiscreteValuationRing_stalk_of_coheight_eq_one f hP1
  obtain ⟨⟨U, hU⟩, hPU, s, hs0, hs⟩ := exists_affineOpen_isRegularPrincipal_vanishingIdeal hP
  have : Nonempty U := ⟨⟨P, hPU⟩⟩
  rw [IdealSheafData.ordAt_eq _ hPU hs]
  let x : U := ⟨P, hPU⟩
  let := TopCat.Presheaf.algebra_section_stalk C.presheaf x
  have := hU.isLocalization_stalk x
  have hmax : IsLocalRing.maximalIdeal (C.presheaf.stalk P) =
      Ideal.span {C.presheaf.germ U P hPU s} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf x).asIdeal
      (C.presheaf.stalk P), ← vanishingIdeal_ideal_eq_primeIdealOf hP hU hPU, hs,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hirr : Irreducible (C.presheaf.germ U P hPU s) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hne : C.germToFunctionField U s ≠ 0 :=
    (map_ne_zero_iff _ (C.germToFunctionField_injective U)).mpr (nonZeroDivisors.ne_zero hs0)
  have : Ring.KrullDimLE 1 (C.presheaf.stalk P) := krullDimLE_of_coheight_le hP1.le
  rw [ord_eq_iff hP1 hne, ← algebraMap_germ_eq_germToFunctionField _ hPU]
  exact Ring.ordFrac_irreducible hirr

omit [IsIntegral C] [IsLocallyNoetherian C] in
/-- The ideal sheaf of a closed point `P` is the unit ideal near every other point. -/
lemma exists_vanishingIdeal_ideal_eq_top {P y : C} (hP : IsClosed {P}) (hy : y ≠ P) :
    ∃ U : C.affineOpens, y ∈ U.1 ∧
      (IdealSheafData.vanishingIdeal ⟨{P}, hP⟩).ideal U = Ideal.span {1} := by
  obtain ⟨U, hU, hyU, hUP⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨{P}ᶜ, hP.isOpen_compl⟩) (x := y) hy
  exact ⟨⟨U, hU⟩, hyU, by
    rw [Ideal.span_singleton_one, vanishingIdeal_ideal_eq_top hP hU fun h ↦ hUP h rfl]⟩

/-- The ideal sheaf of a closed point `P` has order zero away from `P`. -/
lemma ordAt_vanishingIdeal_of_ne {P y : C} (hP : IsClosed {P}) (hy : y ≠ P) :
    (IdealSheafData.vanishingIdeal ⟨{P}, hP⟩).ordAt y = 0 := by
  obtain ⟨U, hyU, hU⟩ := exists_vanishingIdeal_ideal_eq_top hP hy
  have : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  rw [IdealSheafData.ordAt_eq _ hyU hU]
  exact ord_of_isUnit isUnit_one hyU

end Curve

/-! ### The ideal sheaf of an effective divisor -/

namespace Divisor

/-- The ideal sheaf `𝒪_X(-E) = ∏_P 𝓘_P^{n_P}` of an effective divisor `E = ∑_P n_P [P]`, given
as a finitely supported function `closedPoints X →₀ ℕ`, where `𝓘_P` is the ideal sheaf of the
closed point `P`. -/
noncomputable def idealSheaf (E : closedPoints X →₀ ℕ) : X.IdealSheafData :=
  E.prod fun P n ↦ IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩ ^ n

@[simp]
lemma idealSheaf_zero : idealSheaf (0 : closedPoints X →₀ ℕ) = ⊤ :=
  Finsupp.prod_zero_index

lemma idealSheaf_add (E E' : closedPoints X →₀ ℕ) :
    idealSheaf (E + E') = idealSheaf E * idealSheaf E' :=
  Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ ↦ pow_add _

@[simp]
lemma idealSheaf_single (P : closedPoints X) (n : ℕ) :
    idealSheaf (Finsupp.single P n) = IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩ ^ n :=
  Finsupp.prod_single_index (pow_zero _)

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f]

include f in
/-- The ideal sheaf of an effective divisor on a smooth curve is invertible: every effective
divisor is an effective Cartier divisor.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`,
`theorem-riemann-roch-coherent-serre-duality`) -/
lemma isInvertible_idealSheaf (E : closedPoints C →₀ ℕ) : (idealSheaf E).IsInvertible := by
  induction E using Finsupp.induction_linear with
  | zero => exact idealSheaf_zero (X := C) ▸ IdealSheafData.isInvertible_top
  | add E E' hE hE' => exact idealSheaf_add E E' ▸ hE.mul hE'
  | single P n =>
    exact idealSheaf_single P n ▸
      (isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f P.2).pow n

include f in
/-- **Effective divisors are effective Cartier divisors.** On a smooth curve, for every finite
set `s` of closed points and multiplicities `n`, the ideal sheaf `∏_{P ∈ s} 𝓘_P^{n_P}` of the
effective divisor `∑_{P ∈ s} n_P [P]` is invertible: each `𝓘_P` is invertible
(`isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one`), and products of invertible
ideal sheaves are invertible.

(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
lemma isInvertible_prod_vanishingIdeal_pow (s : Finset (closedPoints C))
    (n : closedPoints C → ℕ) :
    (∏ P ∈ s, IdealSheafData.vanishingIdeal ⟨{P.1}, P.2⟩ ^ n P).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IdealSheafData.isInvertible_top
  | insert P s hP ih =>
    rw [Finset.prod_insert hP]
    exact ((isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f P.2).pow _)
      |>.mul ih


variable [IsIntegral C] [IsLocallyNoetherian C]

include f in
/-- The order of `𝒪_C(-E)` at a closed point `P` is the multiplicity of `P` in `E`. -/
lemma ordAt_idealSheaf (E : closedPoints C →₀ ℕ) (P : closedPoints C) :
    (idealSheaf E).ordAt P.1 = E P := by
  induction E using Finsupp.induction_linear with
  | zero => simp
  | add E E' hE hE' =>
    rw [idealSheaf_add, IdealSheafData.ordAt_mul (isInvertible_idealSheaf f E)
      (isInvertible_idealSheaf f E'), hE, hE', Finsupp.add_apply, Nat.cast_add]
  | single Q n =>
    rw [idealSheaf_single, IdealSheafData.ordAt_pow
      (isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f Q.2)]
    by_cases h : P = Q
    · subst h
      rw [ordAt_vanishingIdeal_self f P.2, Finsupp.single_eq_same, mul_one]
    · rw [ordAt_vanishingIdeal_of_ne Q.2 fun h' ↦ h (Subtype.ext h'),
        Finsupp.single_eq_of_ne h, mul_zero, Nat.cast_zero]

include f in
/-- The ideal sheaf `𝒪_C(-E)` has order zero at points which are not closed. -/
lemma ordAt_idealSheaf_of_not_isClosed (E : closedPoints C →₀ ℕ) {y : C}
    (hy : ¬ IsClosed {y}) : (idealSheaf E).ordAt y = 0 := by
  induction E using Finsupp.induction_linear with
  | zero => simp
  | add E E' hE hE' =>
    rw [idealSheaf_add, IdealSheafData.ordAt_mul (isInvertible_idealSheaf f E)
      (isInvertible_idealSheaf f E'), hE, hE', add_zero]
  | single Q n =>
    rw [idealSheaf_single, IdealSheafData.ordAt_pow
      (isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f Q.2),
      ordAt_vanishingIdeal_of_ne Q.2 fun h ↦ hy (by rw [h]; exact Q.2), mul_zero]

end Curve

end Divisor

/-! ### Sections of ideal sheaves and products of invertible ideal sheaves -/

section Sections

open Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

/-- The inclusion `Γ(W, J) → Γ(X, W)` of the sections of the ideal sheaf `J.toModules` into the
sections of `𝒪_X`, induced by the inclusion `J ⊆ 𝒪_X`. -/
noncomputable def IdealSheafData.sectionsι (J : X.IdealSheafData) (W : X.Opens) :
    Γ(J.toModules, W) →+ Γ(X, W) :=
  (J.toModulesι.app W).hom

lemma IdealSheafData.sectionsι_apply (J : X.IdealSheafData) (W : X.Opens)
    (m : Γ(J.toModules, W)) : J.sectionsι W m = J.toModulesι.app W m :=
  rfl


lemma IdealSheafData.sectionsι_injective (J : X.IdealSheafData) (W : X.Opens) :
    Function.Injective (J.sectionsι W) :=
  J.injective_toModulesι_app W

lemma IdealSheafData.sectionsι_smul (J : X.IdealSheafData) {W : X.Opens} (a : Γ(X, W))
    (m : Γ(J.toModules, W)) : J.sectionsι W (a • m) = a * J.sectionsι W m :=
  Modules.Hom.app_smul J.toModulesι a m

lemma IdealSheafData.sectionsι_map (J : X.IdealSheafData) {W W' : X.Opens} (h : W' ≤ W)
    (m : Γ(J.toModules, W)) :
    J.sectionsι W' (J.toModules.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (J.sectionsι W m) :=
  Modules.Hom.app_presheaf_map J.toModulesι (homOfLE h) m

lemma IdealSheafData.sectionsι_mem_idealOfOpens (J : X.IdealSheafData) (W : X.Opens)
    (m : Γ(J.toModules, W)) : J.sectionsι W m ∈ J.idealOfOpens W :=
  (J.range_toModulesι_app_eq_idealOfOpens W).subset ⟨m, rfl⟩

/-- A generator `b` of an invertible ideal sheaf on an affine open `U` is the image of a free
generator of `J.toModules` on `U`. -/
lemma IdealSheafData.IsInvertible.exists_isFreeGenerator {J : X.IdealSheafData}
    (hJ : J.IsInvertible) {U : X.affineOpens} {b : Γ(X, U.1)} (hb : J.ideal U = Ideal.span {b}) :
    ∃ s : Γ(J.toModules, U.1), J.sectionsι U.1 s = b ∧ Modules.IsFreeGenerator s := by
  obtain ⟨s, hs⟩ := J.exists_toModulesι_app_eq (hb ▸ Ideal.mem_span_singleton_self b)
  refine ⟨s, hs, hJ.isFreeGenerator s fun V h ↦ ?_⟩
  rw [hs]
  exact J.ideal_eq_span_map h hb

/-- The ideal cut out by an ideal sheaf on an open is monotone in the ideal sheaf. -/
lemma IdealSheafData.idealOfOpens_mono {I J : X.IdealSheafData} (h : I ≤ J) (U : X.Opens) :
    I.idealOfOpens U ≤ J.idealOfOpens U := by
  intro x hx
  rw [IdealSheafData.mem_idealOfOpens_iff] at hx ⊢
  have key : ∀ φ : J.subscheme ⟶ X, φ = J.subschemeι → φ.app U x = 0 →
      J.subschemeι.app U x = 0 := by
    rintro φ rfl h
    exact h
  refine key _ (IdealSheafData.inclusion_subschemeι h) ?_
  have : (IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ U) (I.subschemeι.app U x) = 0 := by
    rw [hx, map_zero]
  exact this

/-- The inclusion `I ⊆ J` of ideal sheaves, as a morphism `I.toModules ⟶ J.toModules` of
`𝒪_X`-modules. -/
noncomputable def IdealSheafData.toModulesOfLE {I J : X.IdealSheafData} (h : I ≤ J) :
    I.toModules ⟶ J.toModules :=
  kernel.lift _ I.toModulesι <| Modules.hom_ext _ _ fun W ↦ by
    ext m
    exact (J.mem_idealOfOpens_iff).mp
      (IdealSheafData.idealOfOpens_mono h W (I.sectionsι_mem_idealOfOpens W m))

@[reassoc (attr := simp)]
lemma IdealSheafData.toModulesOfLE_toModulesι {I J : X.IdealSheafData} (h : I ≤ J) :
    IdealSheafData.toModulesOfLE h ≫ J.toModulesι = I.toModulesι :=
  kernel.lift_ι _ _ _

lemma IdealSheafData.sectionsι_toModulesOfLE {I J : X.IdealSheafData} (h : I ≤ J)
    (U : X.Opens) (m : Γ(I.toModules, U)) :
    J.sectionsι U ((IdealSheafData.toModulesOfLE h).app U m) = I.sectionsι U m :=
  congr($(IdealSheafData.toModulesOfLE_toModulesι h).app U m)

lemma IdealSheafData.mul_le_left' (I J : X.IdealSheafData) : I * J ≤ I := by
  change (I * J).ideal ≤ I.ideal
  intro U
  exact (Ideal.mul_le_left : I.ideal U * J.ideal U ≤ I.ideal U)

/-- **The zero scheme of the inclusion `I J ⊆ I` is `J`.** On an affine open on which `I = (a)`
and `J = (b)`, the inclusion sends the free generator `a b` of `I J` to `b` times the free
generator `a` of `I`. -/
theorem IdealSheafData.IsInvertible.zeroLocus_toModulesOfLE_mul {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Modules.Hom.zeroLocus (IdealSheafData.toModulesOfLE (I.mul_le_left' J)) = J := by
  have hIJ := hI.mul hJ
  have := hI.isInvertible_toModules
  have := hIJ.isInvertible_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible I.toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible (I * J).toModules
  have key (x : X) : ∃ W : X.affineOpens, x ∈ W.1 ∧
      (Modules.Hom.zeroLocus (IdealSheafData.toModulesOfLE (I.mul_le_left' J))).ideal W =
        J.ideal W := by
    obtain ⟨W, hxW, -, ⟨a, ha⟩, b, hb⟩ :=
      hI.isLocallyPrincipal.exists_ideal_eq_span₂ hJ.isLocallyPrincipal (O := ⊤) (y := x) trivial
    have hab : (I * J).ideal W = Ideal.span {a * b} := by
      rw [ideal_mul, Pi.mul_apply, ha, hb, Ideal.span_singleton_mul_span_singleton]
    obtain ⟨s₁, hs₁, he₁⟩ := hIJ.exists_isFreeGenerator hab
    obtain ⟨s₂, hs₂, he₂⟩ := hI.exists_isFreeGenerator ha
    refine ⟨W, hxW, ?_⟩
    rw [Modules.Hom.ideal_zeroLocus _ W he₁ he₂ (b := b), hb]
    refine I.sectionsι_injective W.1 ?_
    rw [IdealSheafData.sectionsι_toModulesOfLE, I.sectionsι_smul, hs₁, hs₂, mul_comm]
  choose W hxW hW using key
  exact IdealSheafData.ext_of_iSup_eq_top W
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) hW

/-- **The ideal sheaf of a sum of effective Cartier divisors.** For invertible ideal sheaves `I`
and `J`, `I ≅ Jᵛ ⊗ I J`, i.e. `𝒪(-D) ≅ 𝒪(D') ⊗ 𝒪(-D-D')`. -/
theorem IdealSheafData.IsInvertible.nonempty_toModules_iso_dual_tensorObj_mul
    {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Nonempty (I.toModules ≅ J.toModulesᵛ ⊗ (I * J).toModules) := by
  have := hI.isInvertible_toModules
  have := (hI.mul hJ).isInvertible_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible I.toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible (I * J).toModules
  have h := IdealSheafData.IsInvertible.zeroLocus_toModulesOfLE_mul hI hJ
  have hZ : (Modules.Hom.zeroLocus (IdealSheafData.toModulesOfLE (I.mul_le_left' J))).IsInvertible
    := by rw [h]; exact hJ
  obtain ⟨e⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj
    (IdealSheafData.toModulesOfLE (I.mul_le_left' J)) hZ
  exact ⟨e ≪≫ eqToIso (by rw [h])⟩

variable [IsIntegral X]

/-- A local generator of an invertible ideal sheaf has nonzero image in the function field. -/
lemma IdealSheafData.IsInvertible.germToFunctionField_ne_zero {J : X.IdealSheafData}
    (hJ : J.IsInvertible) {W : X.affineOpens} [Nonempty W.1] {b : Γ(X, W.1)}
    (hb : J.ideal W = Ideal.span {b}) : X.germToFunctionField W.1 b ≠ 0 :=
  (map_ne_zero_iff _ (X.germToFunctionField_injective W.1)).mpr
    (nonZeroDivisors.ne_zero (hJ.mem_nonZeroDivisors hb))

/-- The image in the function field of a multiple of the restriction of a section of an ideal
sheaf. -/
lemma IdealSheafData.germToFunctionField_sectionsι_smul_map (J : X.IdealSheafData)
    {W W' : X.Opens} (h : W' ≤ W) [Nonempty W'] [Nonempty W] (a : Γ(X, W'))
    (s : Γ(J.toModules, W)) :
    X.germToFunctionField W' (J.sectionsι W' (a • J.toModules.presheaf.map (homOfLE h).op s)) =
      X.germToFunctionField W' a * X.germToFunctionField W (J.sectionsι W s) := by
  rw [J.sectionsι_smul, J.sectionsι_map, map_mul, germToFunctionField_map]

/-- The image in the function field of the restriction of a section of an ideal sheaf. -/
lemma IdealSheafData.germToFunctionField_sectionsι_map (J : X.IdealSheafData)
    {W W' : X.Opens} (h : W' ≤ W) [Nonempty W'] [Nonempty W] (s : Γ(J.toModules, W)) :
    X.germToFunctionField W' (J.sectionsι W' (J.toModules.presheaf.map (homOfLE h).op s)) =
      X.germToFunctionField W (J.sectionsι W s) := by
  rw [J.sectionsι_map, germToFunctionField_map]

end Sections

/-! ### Isomorphisms between ideal sheaves of effective divisors -/

namespace Divisor

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsIntegral C] [IsNoetherian C]

include f in
/-- **Linearly equivalent effective divisors have isomorphic ideal sheaves.** If
`E₁ - E₂ = div g` for a nonzero rational function `g` on a smooth curve, then multiplication by
`g` is an isomorphism `𝒪_C(-E₂) ≅ 𝒪_C(-E₁)`: near every point, with local generators `b₂` of
`𝒪_C(-E₂)` and `b₁` of `𝒪_C(-E₁)`, the function `g b₂ / b₁` has order zero everywhere, hence is a
unit, so `g b₂` is again a local generator of `𝒪_C(-E₁)`. -/
theorem nonempty_toModules_idealSheaf_iso_of_ord_eq {E₁ E₂ : closedPoints C →₀ ℕ}
    {g : C.functionField} (hg : g ≠ 0) (h : ∀ P : closedPoints C, C.ord g P.1 = E₁ P - E₂ P) :
    Nonempty ((idealSheaf E₂).toModules ≅ (idealSheaf E₁).toModules) := by
  have hJ₁ := isInvertible_idealSheaf f E₁
  have hJ₂ := isInvertible_idealSheaf f E₂
  have key (x : C) : ∃ (W : C.affineOpens) (_ : x ∈ W.1) (s : Γ((idealSheaf E₂).toModules, W.1))
      (t : Γ((idealSheaf E₁).toModules, W.1)), Modules.IsFreeGenerator s ∧
      Modules.IsFreeGenerator t ∧ ∀ _ : Nonempty W.1,
        C.germToFunctionField W.1 ((idealSheaf E₁).sectionsι W.1 t) =
          g * C.germToFunctionField W.1 ((idealSheaf E₂).sectionsι W.1 s) := by
    obtain ⟨W, hxW, -, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
      hJ₁.isLocallyPrincipal.exists_ideal_eq_span₂ hJ₂.isLocallyPrincipal (O := ⊤) (y := x)
        trivial
    have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
    have hb₁0 := hJ₁.germToFunctionField_ne_zero hb₁
    have hb₂0 := hJ₂.germToFunctionField_ne_zero hb₂
    obtain ⟨u, hu, hgu⟩ := exists_isUnit_germToFunctionField_eq_of_ord_eq_zero f (V := W.1)
      (x := g * C.germToFunctionField W.1 b₂ / C.germToFunctionField W.1 b₁)
      (div_ne_zero (mul_ne_zero hg hb₂0) hb₁0) fun z hz ↦ by
        by_cases hz1 : coheight z = 1
        · have hzc := isClosed_of_coheight_eq_one f hz1
          rw [ord_div (mul_ne_zero hg hb₂0) hb₁0, ord_mul hg hb₂0, h ⟨z, hzc⟩,
            ← (idealSheaf E₂).ordAt_eq hz hb₂, ← (idealSheaf E₁).ordAt_eq hz hb₁,
            ordAt_idealSheaf f E₂ ⟨z, hzc⟩, ordAt_idealSheaf f E₁ ⟨z, hzc⟩]
          ring
        · exact ord_eq_zero_of_coheight_neq_one hz1 _
    have hub : (idealSheaf E₁).ideal W = Ideal.span {u * b₁} := by
      rw [hb₁, Ideal.span_singleton_mul_left_unit hu]
    obtain ⟨s, hs, hsf⟩ := hJ₂.exists_isFreeGenerator hb₂
    obtain ⟨t, ht, htf⟩ := hJ₁.exists_isFreeGenerator hub
    refine ⟨W, hxW, s, t, hsf, htf, fun _ ↦ ?_⟩
    rw [ht, hs, map_mul, hgu, div_mul_cancel₀ _ hb₁0]
  choose W hxW s t hs ht hst using key
  refine Modules.nonempty_iso_of_isFreeGenerator (U := fun x ↦ (W x).1) (e := s) (f := t)
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) hs ?_ ht
  intro i j W' hi hj a b hab
  refine (idealSheaf E₁).sectionsι_injective W' (eq_of_germToFunctionField_eq fun hW' ↦ ?_)
  obtain ⟨y⟩ := id hW'
  have : Nonempty (W i).1 := ⟨⟨_, hi y.2⟩⟩
  have : Nonempty (W j).1 := ⟨⟨_, hj y.2⟩⟩
  have hab' := congrArg (fun m ↦ C.germToFunctionField W' ((idealSheaf E₂).sectionsι W' m)) hab
  dsimp only at hab'
  rw [IdealSheafData.germToFunctionField_sectionsι_smul_map,
    IdealSheafData.germToFunctionField_sectionsι_smul_map] at hab'
  rw [IdealSheafData.germToFunctionField_sectionsι_smul_map,
    IdealSheafData.germToFunctionField_sectionsι_smul_map, hst i, hst j]
  linear_combination g * hab'

include f in
/-- **Isomorphic ideal sheaves of effective divisors are linearly equivalent.** An isomorphism
`𝒪_C(-E₂) ≅ 𝒪_C(-E₁)` of ideal sheaves on a smooth curve is multiplication by a nonzero rational
function `g`, and then `div g = E₁ - E₂`. -/
theorem exists_ord_eq_of_nonempty_iso {E₁ E₂ : closedPoints C →₀ ℕ}
    (e : (idealSheaf E₂).toModules ≅ (idealSheaf E₁).toModules) :
    ∃ g : C.functionField, g ≠ 0 ∧ ∀ P : closedPoints C, C.ord g P.1 = E₁ P - E₂ P := by
  set J₁ := idealSheaf E₁
  set J₂ := idealSheaf E₂
  have hJ₁ := isInvertible_idealSheaf f E₁
  have hJ₂ := isInvertible_idealSheaf f E₂
  -- a reference section `s₀` of `J₂` over a nonempty affine open `V₀`
  obtain ⟨V₀, hV₀, -, b₀, hb₀⟩ :=
    hJ₂.isLocallyPrincipal.exists_ideal_eq_span (O := ⊤) (y := genericPoint C) trivial
  have : Nonempty V₀.1 := ⟨⟨_, hV₀⟩⟩
  obtain ⟨s₀, hs₀, -⟩ := hJ₂.exists_isFreeGenerator hb₀
  set c₀ := J₁.sectionsι V₀.1 (e.hom.app V₀.1 s₀)
  have hb0 := hJ₂.germToFunctionField_ne_zero hb₀
  have hc0 : C.germToFunctionField V₀.1 c₀ ≠ 0 := by
    refine (map_ne_zero_iff _ (C.germToFunctionField_injective V₀.1)).mpr fun hc ↦ ?_
    have h1 : e.hom.app V₀.1 s₀ = 0 :=
      J₁.sectionsι_injective V₀.1 (hc.trans (map_zero _).symm)
    have h2 : s₀ = 0 := by
      have := congrArg (e.inv.app V₀.1) h1
      rwa [← ConcreteCategory.comp_apply, ← Modules.Hom.comp_app, e.hom_inv_id,
        Modules.Hom.id_app, map_zero] at this
    apply hb0
    rw [← hs₀, h2, map_zero, map_zero]
  set g := C.germToFunctionField V₀.1 c₀ / C.germToFunctionField V₀.1 b₀
  -- `e` is multiplication by `g`
  have key (W : C.Opens) [Nonempty W] (m : Γ(J₂.toModules, W)) :
      C.germToFunctionField W (J₁.sectionsι W (e.hom.app W m)) =
        g * C.germToFunctionField W (J₂.sectionsι W m) := by
    obtain ⟨⟨y, hyW⟩⟩ := ‹Nonempty W›
    obtain ⟨z, hzW, hzV⟩ : ((W : Set C) ∩ V₀.1).Nonempty :=
      nonempty_preirreducible_inter W.2 V₀.1.2 ⟨y, hyW⟩ ⟨_, hV₀⟩
    set W' : C.Opens := W ⊓ V₀.1
    have hle₁ : W' ≤ W := inf_le_left
    have hle₂ : W' ≤ V₀.1 := inf_le_right
    have : Nonempty W' := ⟨⟨z, hzW, hzV⟩⟩
    set m' := J₂.toModules.presheaf.map (homOfLE hle₁).op m
    set s' := J₂.toModules.presheaf.map (homOfLE hle₂).op s₀
    have h1 : J₂.sectionsι W' s' • m' = J₂.sectionsι W' m' • s' :=
      J₂.sectionsι_injective W' (by rw [J₂.sectionsι_smul, J₂.sectionsι_smul, mul_comm])
    have h2 := congrArg (fun n ↦ C.germToFunctionField W' (J₁.sectionsι W' (e.hom.app W' n))) h1
    dsimp only at h2
    rw [Modules.Hom.app_smul, Modules.Hom.app_smul, J₁.sectionsι_smul, J₁.sectionsι_smul,
      map_mul, map_mul] at h2
    have r1 := J₂.germToFunctionField_sectionsι_map hle₁ m
    have r2 := J₂.germToFunctionField_sectionsι_map hle₂ s₀
    have r3 := J₁.germToFunctionField_sectionsι_map hle₁ (e.hom.app W m)
    have r4 := J₁.germToFunctionField_sectionsι_map hle₂ (e.hom.app V₀.1 s₀)
    rw [← Modules.Hom.app_presheaf_map] at r3 r4
    rw [r1, r2, r3, r4, hs₀] at h2
    simp only [g]
    field_simp
    linear_combination h2
  refine ⟨g, div_ne_zero hc0 hb0, fun P ↦ ?_⟩
  -- compare with local generators at `P`
  obtain ⟨W, hPW, -, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    hJ₁.isLocallyPrincipal.exists_ideal_eq_span₂ hJ₂.isLocallyPrincipal (O := ⊤) (y := P.1)
      trivial
  have : Nonempty W.1 := ⟨⟨_, hPW⟩⟩
  obtain ⟨t₁, ht₁, he₁⟩ := hJ₁.exists_isFreeGenerator hb₁
  obtain ⟨t₂, ht₂, he₂⟩ := hJ₂.exists_isFreeGenerator hb₂
  obtain ⟨u, hu⟩ := he₁.exists_unit_smul_eq (Modules.IsFreeGenerator.app_hom e he₂)
  have h1 := key W.1 t₂
  rw [hu, J₁.sectionsι_smul, ht₁, ht₂, map_mul] at h1
  have hb₁0 := hJ₁.germToFunctionField_ne_zero hb₁
  have hb₂0 := hJ₂.germToFunctionField_ne_zero hb₂
  have hu0 : C.germToFunctionField W.1 (u : Γ(C, W.1)) ≠ 0 :=
    (map_ne_zero_iff _ (C.germToFunctionField_injective W.1)).mpr u.isUnit.ne_zero
  have h2 := congrArg (fun a ↦ C.ord a P.1) h1
  simp only at h2
  rw [ord_mul hu0 hb₁0, ord_mul (div_ne_zero hc0 hb0) hb₂0, ord_of_isUnit u.isUnit hPW,
    ← J₁.ordAt_eq hPW hb₁, ← J₂.ordAt_eq hPW hb₂, ordAt_idealSheaf f E₁ P,
    ordAt_idealSheaf f E₂ P] at h2
  change C.ord (C.germToFunctionField V₀.1 c₀ / C.germToFunctionField V₀.1 b₀) P.1 = _
  omega

end Divisor

/-! ### Invertible ideal sheaves are ideal sheaves of effective divisors -/

section Curve

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsIntegral C] [IsNoetherian C]

/-- The order of an invertible ideal sheaf on a Noetherian integral scheme is nonzero at only
finitely many points: near each point of a finite affine cover it is the order of a single
nonzero function. -/
lemma IdealSheafData.IsInvertible.finite_setOf_ordAt_ne_zero {I : C.IdealSheafData}
    (hI : I.IsInvertible) : {y : C | I.ordAt y ≠ 0}.Finite := by
  choose U hyU _hUO b hb using fun y : C ↦
    hI.isLocallyPrincipal.exists_ideal_eq_span (O := ⊤) (y := y) trivial
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ ((U y).1 : Set C))
    (fun y ↦ (U y).1.2) fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyU y⟩
  let S (y : C) : Set C := haveI : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
    {z | C.ord (C.germToFunctionField (U y).1 (b y)) z ≠ 0}
  have hS (y : C) : (S y).Finite := by
    have : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
    exact finite_setOf_ord_ne_zero (hI.germToFunctionField_ne_zero (hb y))
  refine (t.finite_toSet.biUnion fun y _ ↦ hS y).subset fun z hz ↦ ?_
  obtain ⟨y, hyt, hzy⟩ : ∃ y ∈ t, z ∈ (U y).1 := by simpa using ht (Set.mem_univ z)
  have : Nonempty (U y).1 := ⟨⟨y, hyU y⟩⟩
  refine Set.mem_biUnion hyt ?_
  change C.ord (C.germToFunctionField (U y).1 (b y)) z ≠ 0
  rwa [← I.ordAt_eq hzy (hb y)]

include f in
/-- **Every effective Cartier divisor on a smooth curve is a sum of closed points.** An
invertible ideal sheaf `I` on a smooth integral curve is the ideal sheaf `𝒪_C(-E)` of the
effective divisor `E = ∑_P ord_P(I) [P]`: near every point, local generators of `I` and of
`𝒪_C(-E)` have the same orders everywhere, so they differ by a unit. Here
`𝒪_C(-E) = ∏_P 𝓘_P^{n_P}` has order `n_P` at the closed point `P`
(`AlgebraicGeometry.Scheme.Divisor.ordAt_idealSheaf`), i.e. its stalk at `P` is `(t_P^{n_P})`
for a uniformizer `t_P` of the discrete valuation ring `𝒪_{C,P}`, and order `0` elsewhere.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`,
`theorem-riemann-roch-coherent-serre-duality`, `theorem-riemann-roch-coherent-serre-duality`) -/
theorem IdealSheafData.IsInvertible.exists_eq_idealSheaf {I : C.IdealSheafData}
    (hI : I.IsInvertible) : ∃ E : closedPoints C →₀ ℕ, I = Divisor.idealSheaf E := by
  have hfin : {P : closedPoints C | (I.ordAt P.1).toNat ≠ 0}.Finite :=
    (hI.finite_setOf_ordAt_ne_zero.preimage Subtype.val_injective.injOn).subset fun P hP ↦ by
      change (I.ordAt P.1).toNat ≠ 0 at hP
      change I.ordAt P.1 ≠ 0
      omega
  let E : closedPoints C →₀ ℕ := Finsupp.ofSupportFinite (fun P ↦ (I.ordAt P.1).toNat) hfin
  refine ⟨E, ?_⟩
  have hJ := Divisor.isInvertible_idealSheaf f E
  have hord (y : C) : I.ordAt y = (Divisor.idealSheaf E).ordAt y := by
    by_cases hy : IsClosed {y}
    · rw [Divisor.ordAt_idealSheaf f E ⟨y, hy⟩]
      simp only [E]
      exact (Int.toNat_of_nonneg (I.ordAt_nonneg y)).symm
    · rw [Divisor.ordAt_idealSheaf_of_not_isClosed f E hy]
      obtain ⟨U, hyU, -, b, hb⟩ :=
        hI.isLocallyPrincipal.exists_ideal_eq_span (O := ⊤) (y := y) trivial
      have : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
      rw [I.ordAt_eq hyU hb]
      exact ord_eq_zero_of_coheight_neq_one (fun h ↦ hy (isClosed_of_coheight_eq_one f h)) _
  have key (x : C) : ∃ W : C.affineOpens, x ∈ W.1 ∧
      I.ideal W = (Divisor.idealSheaf E).ideal W := by
    obtain ⟨W, hxW, -, ⟨a, ha⟩, b, hb⟩ :=
      hI.isLocallyPrincipal.exists_ideal_eq_span₂ hJ.isLocallyPrincipal (O := ⊤) (y := x) trivial
    have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
    have ha0 := hI.germToFunctionField_ne_zero ha
    have hb0 := hJ.germToFunctionField_ne_zero hb
    obtain ⟨u, hu, hgu⟩ := exists_isUnit_germToFunctionField_eq_of_ord_eq_zero f (V := W.1)
      (div_ne_zero ha0 hb0) fun z hz ↦ by
        rw [ord_div ha0 hb0, ← I.ordAt_eq hz ha, ← (Divisor.idealSheaf E).ordAt_eq hz hb, hord,
          sub_self]
    have hab : a = u * b :=
      C.germToFunctionField_injective W.1 (by rw [map_mul, hgu, div_mul_cancel₀ _ hb0])
    refine ⟨W, hxW, ?_⟩
    rw [ha, hb, hab, Ideal.span_singleton_mul_left_unit hu]
  choose W hxW hW using key
  exact IdealSheafData.ext_of_iSup_eq_top W
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) hW

end Curve

/-! ### Rational coordinates of sections of invertible modules -/

section RationalCoordinate

variable {M : X.Modules}

/-- Sections of a sheaf of modules over an empty open are all equal. -/
lemma Modules.eq_of_isEmpty {W : X.Opens} (hW : IsEmpty W) (m m' : Γ(M, W)) : m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun _ : W ↦ W) W (fun _ ↦ 𝟙 W)
    (fun x hx ↦ (hW.false ⟨x, hx⟩).elim) m m' fun i ↦ (hW.false i).elim

variable [IsIntegral X]

/-- **Restriction of sections of an invertible module on an integral scheme is injective.**
Locally the module is trivial, and restriction of functions to a nonempty open is injective. -/
lemma Modules.presheaf_map_injective [SheafOfModules.IsInvertible.{u, u, u} M] {W W' : X.Opens}
    (h : W' ≤ W) [Nonempty W'] : Function.Injective (M.presheaf.map (homOfLE h).op) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨⟨y, hyW'⟩⟩ := ‹Nonempty W'›
  have key (x : W) : ∃ (V : X.Opens) (hV : V ≤ W), x.1 ∈ V ∧
      M.presheaf.map (homOfLE hV).op m = 0 := by
    obtain ⟨U, hxU, hUW, e, he⟩ := Modules.exists_isFreeGenerator M x.2
    obtain ⟨r, hr⟩ := he.exists_smul_eq (M.presheaf.map (homOfLE hUW).op m)
    refine ⟨U.1, hUW, hxU, ?_⟩
    obtain ⟨z, hzU, hzW'⟩ : ((U.1 : Set X) ∩ W').Nonempty :=
      nonempty_preirreducible_inter U.1.2 W'.2 ⟨x, hxU⟩ ⟨y, hyW'⟩
    have hle₁ : U.1 ⊓ W' ≤ U.1 := inf_le_left
    have hle₂ : U.1 ⊓ W' ≤ W' := inf_le_right
    have : Nonempty (U.1 ⊓ W' : X.Opens) := ⟨⟨z, hzU, hzW'⟩⟩
    have : Nonempty U.1 := ⟨⟨_, hxU⟩⟩
    have h1 : X.presheaf.map (homOfLE hle₁).op r • M.presheaf.map (homOfLE hle₁).op e = 0 := by
      rw [← Modules.map_smul, hr, Modules.presheaf_map_homOfLE_map_homOfLE,
        ← Modules.presheaf_map_homOfLE_map_homOfLE h hle₂, hm, map_zero]
    have h2 : X.presheaf.map (homOfLE hle₁).op r = 0 :=
      (he.map hle₁).smul_left_injective (h1.trans (zero_smul _ _).symm)
    have h3 : r = 0 := eq_of_germToFunctionField_eq fun _ ↦ by
      rw [← germToFunctionField_map hle₁, h2, map_zero, map_zero]
    rw [← hr, h3, zero_smul]
  choose V hV hxV hm0 using key
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun x : W ↦ V x) W
    (fun x ↦ homOfLE (hV x)) (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩)
    m 0 fun x ↦ (hm0 x).trans (map_zero _).symm

omit [IsIntegral X] in
lemma Modules.IsFreeGenerator.ne_zero {U : X.Opens} [Nonempty U] {e : Γ(M, U)}
    (he : Modules.IsFreeGenerator e) : e ≠ 0 := by
  intro h0
  have : (1 : Γ(X, U)) = 0 := he.smul_left_injective (by simp only [h0, smul_zero])
  exact one_ne_zero this

namespace Modules.IsFreeGenerator

variable {U : X.Opens} {e : Γ(M, U)} (he : Modules.IsFreeGenerator e)

/-- The *rational coordinate* of a section `m` of `M` over `W` with respect to a free generator
`e` of `M` over `U`, on an integral scheme: the image in the function field of the coefficient
of `m` along `e` on `W ⊓ U`. -/
noncomputable def ratCoord {W : X.Opens} [Nonempty (W ⊓ U : X.Opens)] (m : Γ(M, W)) :
    X.functionField :=
  X.germToFunctionField (W ⊓ U)
    ((he.map inf_le_right).coeff (M.presheaf.map (homOfLE inf_le_left).op m))

include he in
lemma ratCoord_smul {W : X.Opens} [Nonempty (W ⊓ U : X.Opens)] [Nonempty W] (a : Γ(X, W))
    (m : Γ(M, W)) : he.ratCoord (a • m) = X.germToFunctionField W a * he.ratCoord m := by
  rw [ratCoord, ratCoord, Modules.map_smul, coeff_smul_left, map_mul, germToFunctionField_map]

lemma ratCoord_zero {W : X.Opens} [Nonempty (W ⊓ U : X.Opens)] :
    he.ratCoord (0 : Γ(M, W)) = 0 := by
  rw [ratCoord, map_zero, coeff_zero, map_zero]

lemma ratCoord_map {W W' : X.Opens} (h : W' ≤ W) [Nonempty (W' ⊓ U : X.Opens)]
    [Nonempty (W ⊓ U : X.Opens)] (m : Γ(M, W)) :
    he.ratCoord (M.presheaf.map (homOfLE h).op m) = he.ratCoord m := by
  have hle : W' ⊓ U ≤ W ⊓ U := inf_le_inf_right U h
  rw [ratCoord, ratCoord, ← germToFunctionField_map hle]
  congr 1
  rw [coeff_eq_iff, ← Modules.presheaf_map_homOfLE_map_homOfLE (inf_le_right : W ⊓ U ≤ U) hle,
    ← Modules.map_smul, coeff_smul, Modules.presheaf_map_homOfLE_map_homOfLE,
    Modules.presheaf_map_homOfLE_map_homOfLE]

lemma ratCoord_injective [SheafOfModules.IsInvertible.{u, u, u} M] {W : X.Opens}
    [Nonempty (W ⊓ U : X.Opens)] : Function.Injective (he.ratCoord (W := W)) := by
  intro m m' hmm
  have h1 := X.germToFunctionField_injective (W ⊓ U) hmm
  have h2 : M.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op m =
      M.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op m' := by
    rw [← (he.map inf_le_right).coeff_smul (M.presheaf.map _ m), h1,
      (he.map inf_le_right).coeff_smul]
  exact Modules.presheaf_map_injective inf_le_left h2

end Modules.IsFreeGenerator

end RationalCoordinate

/-! ### Every invertible module is a quotient of ideal sheaves of effective divisors -/

section Curve

open Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsIntegral C] [IsNoetherian C]

include f in
/-- **Every invertible module on a smooth curve comes from divisors.** For an invertible module
`ℒ` on a smooth integral curve there are effective divisors `E₁` and `E₂` with
`ℒ ≅ 𝒪_C(E₁) ⊗ 𝒪_C(-E₂)`, where `𝒪_C(E₁) = 𝒪_C(-E₁)ᵛ`.

Fix a trivialization `e₀` of `ℒ` on a nonempty open `U₀`, and trivializations `eᵢ` on a finite
open cover. The rational functions `gᵢ = e₀ / eᵢ` have finitely many zeros and poles; let `E₂`
be a large multiple of the sum of these points. Near every point, with a local generator `b` of
`𝒪_C(-E₂)`, the function `b gᵢ` is regular, and `b ↦ b gᵢ eᵢ = b e₀` glues to a nonzero morphism
`ψ : 𝒪_C(-E₂) ⟶ ℒ` (which is "multiplication by `e₀`"). Its zero scheme is an effective
Cartier divisor `E₁`, so `ℒ ≅ 𝒪_C(E₁) ⊗ 𝒪_C(-E₂)`. -/
theorem Modules.exists_nonempty_iso_dual_toModules_idealSheaf_tensorObj (ℒ : C.Modules)
    [ℒ.IsInvertible] : ∃ E₁ E₂ : closedPoints C →₀ ℕ,
      Nonempty (ℒ ≅ (Divisor.idealSheaf E₁).toModulesᵛ ⊗ (Divisor.idealSheaf E₂).toModules) := by
  classical
  have := Modules.IsInvertible.sheafOfModules_isInvertible ℒ
  -- a reference trivialization `e₀` of `ℒ` on a nonempty open `U₀`
  obtain ⟨U₀, hU₀, -, e₀, he₀⟩ :=
    Modules.exists_isFreeGenerator ℒ (W := ⊤) (x := genericPoint C) trivial
  have hmeet (W : C.Opens) (y : C) (hy : y ∈ W) : Nonempty (W ⊓ U₀.1 : C.Opens) := by
    obtain ⟨z, hzW, hzU⟩ := nonempty_preirreducible_inter W.2 U₀.1.2 ⟨y, hy⟩ ⟨_, hU₀⟩
    exact ⟨⟨z, hzW, hzU⟩⟩
  -- trivializations `e i` on a finite cover
  choose V hxV _hV e he using fun x : C ↦
    Modules.exists_isFreeGenerator ℒ (W := ⊤) (x := x) trivial
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((V x).1 : Set C))
    (fun x ↦ (V x).1.2) fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩
  have hne (i : C) : (e i) ≠ 0 := by
    have : Nonempty (V i).1 := ⟨⟨i, hxV i⟩⟩
    exact (he i).ne_zero
  -- the rational functions `g i = e₀ / e i`
  let g (i : C) : C.functionField :=
    haveI := hmeet (V i).1 i (hxV i)
    (he₀.ratCoord (e i))⁻¹
  have hg (i : C) : g i ≠ 0 := by
    have := hmeet (V i).1 i (hxV i)
    refine inv_ne_zero fun h0 ↦ hne i (he₀.ratCoord_injective ?_)
    rw [h0, he₀.ratCoord_zero]
  -- the finitely many zeros and poles of the `g i`, and the divisor `E`
  let S (i : C) : Set (closedPoints C) := {P | C.ord (g i) P.1 ≠ 0}
  have hS (i : C) : (S i).Finite :=
    (finite_setOf_ord_ne_zero (hg i)).preimage Subtype.val_injective.injOn
  let T : Finset (closedPoints C) := t.biUnion fun i ↦ (hS i).toFinset
  let N : ℕ := t.sup fun i ↦ (hS i).toFinset.sup fun P ↦ (-C.ord (g i) P.1).toNat
  let E : closedPoints C →₀ ℕ := ∑ P ∈ T, Finsupp.single P N
  have hE (i : C) (hi : i ∈ t) (P : closedPoints C) : 0 ≤ C.ord (g i) P.1 + E P := by
    by_cases hP : C.ord (g i) P.1 = 0
    · rw [hP, zero_add]
      exact Nat.cast_nonneg _
    have hPS : P ∈ (hS i).toFinset := (hS i).mem_toFinset.2 hP
    have hPT : P ∈ T := Finset.mem_biUnion.2 ⟨i, hi, hPS⟩
    have hEP : E P = N := by
      simp only [E, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', hPT,
        ite_true]
    have h1 : (-C.ord (g i) P.1).toNat ≤ N :=
      (Finset.le_sup (f := fun P ↦ (-C.ord (g i) P.1).toNat) hPS).trans
        (Finset.le_sup (f := fun i ↦ (hS i).toFinset.sup fun P ↦ (-C.ord (g i) P.1).toNat) hi)
    rw [hEP]
    have h2 := Int.self_le_toNat (-C.ord (g i) P.1)
    omega
  -- the ideal sheaf `J = 𝒪_C(-E)` and the local data of `ψ : J ⟶ ℒ`
  set J := Divisor.idealSheaf E
  have hJ := Divisor.isInvertible_idealSheaf f E
  have := hJ.isInvertible_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible J.toModules
  have key (x : C) : ∃ (W : C.affineOpens) (_ : x ∈ W.1) (s : Γ(J.toModules, W.1))
      (σ : Γ(ℒ, W.1)), Modules.IsFreeGenerator s ∧
      ∀ [Nonempty W.1] [Nonempty (W.1 ⊓ U₀.1 : C.Opens)],
        he₀.ratCoord σ = C.germToFunctionField W.1 (J.sectionsι W.1 s) := by
    obtain ⟨i, hit, hxi⟩ : ∃ i ∈ t, x ∈ (V i).1 := by simpa using ht (Set.mem_univ x)
    obtain ⟨W, hxW, hWV, b, hb⟩ := hJ.isLocallyPrincipal.exists_ideal_eq_span hxi
    have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
    have hb0 := hJ.germToFunctionField_ne_zero hb
    obtain ⟨c, hc⟩ := exists_germToFunctionField_eq_of_ord_nonneg f (V := W.1)
      (x := C.germToFunctionField W.1 b * g i) fun z hz ↦ by
        by_cases hz1 : coheight z = 1
        · have hzc := isClosed_of_coheight_eq_one f hz1
          rw [ord_mul hb0 (hg i), ← J.ordAt_eq hz hb, Divisor.ordAt_idealSheaf f E ⟨z, hzc⟩,
            add_comm]
          exact hE i hit ⟨z, hzc⟩
        · rw [ord_eq_zero_of_coheight_neq_one hz1]
    obtain ⟨s, hs, hsf⟩ := hJ.exists_isFreeGenerator hb
    refine ⟨W, hxW, s, c • ℒ.presheaf.map (homOfLE hWV).op (e i), hsf, ?_⟩
    intro _ _
    have := hmeet (V i).1 i (hxV i)
    rw [he₀.ratCoord_smul, he₀.ratCoord_map, hc, hs, mul_assoc]
    simp only [g]
    rw [inv_mul_cancel₀, mul_one]
    intro h0
    exact hne i (he₀.ratCoord_injective (h0.trans he₀.ratCoord_zero.symm))
  choose W hxW s σ hs hσ using key
  have hcov : ⨆ x, (W x).1 = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  have hc : ∀ i j (W' : C.Opens) (hi : W' ≤ (W i).1) (hj : W' ≤ (W j).1) (a b : Γ(C, W')),
      a • J.toModules.presheaf.map (homOfLE hi).op (s i) =
        b • J.toModules.presheaf.map (homOfLE hj).op (s j) →
      a • ℒ.presheaf.map (homOfLE hi).op (σ i) = b • ℒ.presheaf.map (homOfLE hj).op (σ j) := by
    intro i j W' hi hj a b hab
    rcases isEmpty_or_nonempty W' with hW' | ⟨⟨y, hy⟩⟩
    · exact Modules.eq_of_isEmpty hW' _ _
    have : Nonempty W' := ⟨⟨y, hy⟩⟩
    have : Nonempty (W i).1 := ⟨⟨y, hi hy⟩⟩
    have : Nonempty (W j).1 := ⟨⟨y, hj hy⟩⟩
    have := hmeet W' y hy
    have := hmeet (W i).1 y (hi hy)
    have := hmeet (W j).1 y (hj hy)
    refine he₀.ratCoord_injective ?_
    have hab' := congrArg (fun m ↦ C.germToFunctionField W' (J.sectionsι W' m)) hab
    dsimp only at hab'
    rw [J.germToFunctionField_sectionsι_smul_map, J.germToFunctionField_sectionsι_smul_map]
      at hab'
    rw [he₀.ratCoord_smul, he₀.ratCoord_smul, he₀.ratCoord_map, he₀.ratCoord_map, hσ, hσ, hab']
  let ψ : J.toModules ⟶ ℒ := Modules.glueHom hcov hs hc
  -- `ψ` is nonzero
  have hψ : ψ ≠ 0 := by
    intro h0
    set x := genericPoint C
    have : Nonempty (W x).1 := ⟨⟨x, hxW x⟩⟩
    have := hmeet (W x).1 x (hxW x)
    have h1 := Modules.isGlueValue_glueHom_app hcov hs hc (s x) x (W x).1 le_rfl le_rfl 1
      (by rw [one_smul])
    rw [Modules.presheaf_map_id_apply, Modules.presheaf_map_id_apply, one_smul] at h1
    have h2 : σ x = 0 := by
      rw [← h1, show Modules.glueHom hcov hs hc = 0 from h0]
      rfl
    have h3 := hσ x
    rw [h2, he₀.ratCoord_zero] at h3
    have h4 : J.sectionsι (W x).1 (s x) = J.sectionsι (W x).1 0 := by
      rw [map_zero]
      exact C.germToFunctionField_injective _ (h3.symm.trans (map_zero _).symm)
    exact (hs x).ne_zero (J.sectionsι_injective _ h4)
  have hZ : (Modules.Hom.zeroLocus ψ).IsInvertible :=
    (Modules.Hom.isLocallyPrincipal_zeroLocus ψ).isInvertible fun h ↦
      hψ ((Modules.Hom.zeroLocus_eq_bot_iff ψ).mp h)
  obtain ⟨E₁, hE₁⟩ := hZ.exists_eq_idealSheaf f
  obtain ⟨iso⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj ψ hZ
  exact ⟨E₁, E, ⟨iso ≪≫ eqToIso (by rw [hE₁])⟩⟩

end Curve

end AlgebraicGeometry.Scheme
