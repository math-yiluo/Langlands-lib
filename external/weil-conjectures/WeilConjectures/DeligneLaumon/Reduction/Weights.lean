/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.WeilSheaf.Defs
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.WeilSheaf.HomologySequence
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Triangle

/-!
# Mixed weight bounds for constructible Weil sheaves and complexes

This file sets up the language in which the Deligne–Laumon reduction to the affine line
(blueprint section `chap-The-Deligne-Laumon-theorem-in-general`) is stated. A constructible Weil
sheaf is `ι`-*mixed of weights at most* `w` if it admits a finite filtration whose successive
quotients are punctually `ι`-pure of some weight at most `w`, and a bounded constructible Weil
complex `K` is mixed of weights at most `w` if `𝓗ᵇK` is mixed of weights at most `w + b` for every
`b`.

## Conventions

The `ℓ`-adic formalism these statements are phrased against is the provisional interface of
`WeilConjectures.WeilSheaf.Defs`: the abelian categories `AlgebraicGeometry.WeilSheaf k₀ l X` of
constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`, their bounded derived categories
`AlgebraicGeometry.WeilComplex k₀ l X`, lissity, the geometric stalks with their local
Frobenius, the punctual weight conditions
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` and
`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`, the reality condition
`AlgebraicGeometry.WeilSheaf.IsReal`, and the direct images with compact support
`AlgebraicGeometry.WeilSheaf.higherLowerShriek` (`Rʳf₀!`) and
`AlgebraicGeometry.WeilComplex.derivedLowerShriek` (`Rf₀!`). The notions that other blueprint
blocks own are opaque placeholders there, each tagged `TODO(unify)` with the node that owns it;
what this block owns is the mixed upper bounds defined below.

Cohomological indexing is used throughout: `AlgebraicGeometry.WeilComplex.homologySheaf b` is
the `b`-th *cohomology* sheaf `𝓗ᵇK`, as in `DerivedCategory.homologyFunctor`, so the bound for
a complex of weights at most `w` is `w + b` in degree `b`, Deligne's convention.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost` and
  `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost`: mixed of weights at most `w`, for a
  sheaf and for a complex.
- `AlgebraicGeometry.WeilSheaf.IsMixed`: mixed, that is, mixed of weights at most `w` for some
  `w`.
- `AlgebraicGeometry.HasDirectImageWeightBound`: the direct-image weight assertion for a single
  morphism, the statement the reductions of `chap-The-Deligne-Laumon-theorem-in-general` propagate,
  and its complex form `AlgebraicGeometry.HasDirectImageComplexWeightBound`.

Monotonicity in the bound and the bound for a zero sheaf are proved
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.mono_weight` and
`AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_of_isZero`), and the closure properties the
blueprint records alongside the definition — under subobjects, quotients and extensions — are
proved: `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_mono`, `.of_epi` and
`.of_mono_cokernel`. They come from the general closure properties of objects with a finite
filtration (`CategoryTheory.ObjectProperty.filtrationClosure`), applied to the property
`AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeightLE` of being punctually pure of some weight
at most `w`, which is closed under subobjects and quotients since the stalk functors are exact
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.of_mono`). From them, the middle term
of an exact sequence whose outer terms are mixed of weights at most `w` is mixed of weights at
most `w`
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_exact`), and so is a sheaf with a finite
filtration whose successive quotients are
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_filtration`).

A mixed sheaf whose local Frobenius eigenvalues are bounded by `q_y ^ (v / 2)` is mixed of
weights at most `v` (`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_hasWeightsAtMost`,
blueprint `lemma-bounding-weights-mixed-sheaf--1`), and exact functors raising punctual weights by
`c` raise mixed weight bounds by `c` (`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.map_add`).

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1, for
  mixed sheaves and their weight bounds.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-! ### Mixed sheaves -/

/-- `F` is `ι`-mixed of weights at most `w` if it admits a finite filtration

```
0 = G 0 ↪--- G 1 ↪--- ⋯ ↪--- G n ≅ F
         |        |            |
         v        v            v
      coker φ 0   ⋯      coker φ (n-1)
```

whose successive quotients `coker φᵢ` are punctually `ι`-pure of some weight at most `w`
(blueprint: `definition-weights`, `definition-weights--2`). -/
def WeilSheaf.IsMixedOfWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) :
    Prop :=
  ∃ (n : ℕ) (G : Fin (n + 1) → WeilSheaf k₀ l X)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      IsZero (G 0) ∧ IsIsomorphic (G (Fin.last n)) F ∧ (∀ i : Fin n, Mono (φ i)) ∧
        ∀ i : Fin n, ∃ v ≤ w, (cokernel (φ i)).IsPunctuallyPureOfWeight ι v

/-- `F` is `ι`-*mixed* if it is mixed of weights at most `w` for some `w`, that is, if it admits
a finite filtration with punctually `ι`-pure quotients
(blueprint: `definition-weights`). -/
def WeilSheaf.IsMixed (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop :=
  ∃ w : ℝ, F.IsMixedOfWeightsAtMost ι w

namespace WeilSheaf

variable {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X} {w w' : ℝ}

theorem IsMixedOfWeightsAtMost.isMixed (h : F.IsMixedOfWeightsAtMost ι w) : F.IsMixed ι :=
  ⟨w, h⟩

/-- Mixed upper bounds are monotone in the bound (blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.mono_weight (h : F.IsMixedOfWeightsAtMost ι w) (hw : w ≤ w') :
    F.IsMixedOfWeightsAtMost ι w' := by
  obtain ⟨n, G, φ, h0, hlast, hmono, hpure⟩ := h
  refine ⟨n, G, φ, h0, hlast, hmono, fun i ↦ ?_⟩
  obtain ⟨v, hv, hvpure⟩ := hpure i
  exact ⟨v, hv.trans hw, hvpure⟩

/-- A zero sheaf is mixed of weights at most `w`, for every `w`: the filtration of length zero
exhibits it (blueprint: `definition-weights`). -/
theorem isMixedOfWeightsAtMost_of_isZero (hF : IsZero F) (w : ℝ) :
    F.IsMixedOfWeightsAtMost ι w :=
  ⟨0, fun _ ↦ F, fun i ↦ i.elim0, hF, ⟨Iso.refl F⟩, fun i ↦ i.elim0, fun i ↦ i.elim0⟩

variable (ι w) in
/-- The property of a Weil sheaf of being punctually `ι`-pure of some weight at most `w`; the
sheaves mixed of weights at most `w` are those with a finite filtration whose successive
quotients have this property. -/
def isPunctuallyPureOfWeightLE : ObjectProperty (WeilSheaf k₀ l X) :=
  fun F ↦ ∃ v ≤ w, F.IsPunctuallyPureOfWeight ι v

instance : (isPunctuallyPureOfWeightLE (k₀ := k₀) (l := l) (X := X) ι w).IsClosedUnderSubobjects
    where
  prop_of_mono f _ := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_mono f⟩

instance : (isPunctuallyPureOfWeightLE (k₀ := k₀) (l := l) (X := X) ι w).IsClosedUnderQuotients
    where
  prop_of_epi f _ := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_epi f⟩

instance :
    (isPunctuallyPureOfWeightLE (k₀ := k₀) (l := l) (X := X) ι w).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨v, hv, h⟩ ↦ ⟨v, hv, h.of_epi e.hom⟩

/-- Being mixed of weights at most `w` is admitting a finite filtration whose successive
quotients are punctually `ι`-pure of some weight at most `w`. -/
theorem isMixedOfWeightsAtMost_iff_filtrationClosure :
    F.IsMixedOfWeightsAtMost ι w ↔ (isPunctuallyPureOfWeightLE ι w).filtrationClosure F := by
  rw [ObjectProperty.filtrationClosure_iff]
  rfl

/-- A subobject of a sheaf mixed of weights at most `w` is mixed of weights at most `w`: intersect
the filtration (blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.of_mono (i : G ⟶ F) [Mono i] (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.prop_of_mono _ i h

/-- A quotient of a sheaf mixed of weights at most `w` is mixed of weights at most `w`: take the
images of the filtration (blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.of_epi (p : F ⟶ G) [Epi p] (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  exact ObjectProperty.prop_of_epi _ p h

/-- An extension of a sheaf mixed of weights at most `w` by another one is mixed of weights at
most `w`: splice the two filtrations (blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.of_mono_cokernel (i : G ⟶ F) [Mono i]
    (hG : G.IsMixedOfWeightsAtMost ι w) (hQ : (cokernel i).IsMixedOfWeightsAtMost ι w) :
    F.IsMixedOfWeightsAtMost ι w := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at hG hQ ⊢
  exact ObjectProperty.prop_X₂_of_shortExact _
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance)
    hG hQ

/-- Mixed upper bounds are invariant under isomorphism (blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.of_iso (e : F ≅ G) (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  obtain ⟨n, H, φ, h0, ⟨e'⟩, hmono, hpure⟩ := h
  exact ⟨n, H, φ, h0, ⟨e' ≪≫ e⟩, hmono, hpure⟩

/-- In an exact sequence `A ⟶ B ⟶ C` of Weil sheaves whose outer terms are mixed of weights at
most `w`, the middle term is mixed of weights at most `w`: the kernel of `B ⟶ C` is a quotient
of `A`, and the cokernel of its inclusion is a subobject of `C`
(blueprint: `lemma-weight-bounds-partitions`, step 0). -/
theorem IsMixedOfWeightsAtMost.of_exact {S : ShortComplex (WeilSheaf k₀ l X)} (hS : S.Exact)
    (h₁ : S.X₁.IsMixedOfWeightsAtMost ι w) (h₃ : S.X₃.IsMixedOfWeightsAtMost ι w) :
    S.X₂.IsMixedOfWeightsAtMost ι w :=
  have := hS.epi_kernelLift
  (h₁.of_epi (kernel.lift S.g S.f S.zero)).of_mono_cokernel (kernel.ι S.g)
    (h₃.of_mono (Abelian.factorThruCoimage S.g))


/-- The middle term of a short exact sequence `0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0` of Weil sheaves whose outer
terms are mixed of weights at most `w` is mixed of weights at most `w`: splice the filtration of
`G'` with the inverse image of that of `G''` (blueprint:
`proposition-weights-under-usual-operations--2`, part 2). -/
theorem IsMixedOfWeightsAtMost.of_shortExact {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (h₁ : S.X₁.IsMixedOfWeightsAtMost ι w)
    (h₃ : S.X₃.IsMixedOfWeightsAtMost ι w) : S.X₂.IsMixedOfWeightsAtMost ι w :=
  .of_exact hS.exact h₁ h₃

/-- A direct summand, more generally a retract, of a Weil sheaf mixed of weights at most `w` is
mixed of weights at most `w`: it is a Weil subsheaf (blueprint:
`proposition-weights-under-usual-operations--2`, part 3). -/
theorem IsMixedOfWeightsAtMost.of_retract (h : Retract G F) (hF : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w :=
  have : Mono h.i := mono_of_mono_fac h.retract
  hF.of_mono h.i

/-- A subobject of a Weil sheaf with weights at most `v` has weights at most `v`: its stalks are
Frobenius-stable subspaces. -/
theorem HasWeightsAtMost.of_mono {v : ℝ} (f : F ⟶ G) [Mono f] (h : G.HasWeightsAtMost ι v) :
    F.HasWeightsAtMost ι v := fun x ↦
  FrobeniusModule.HasWeightsAtMost.of_injective _ (stalkAtMap_frobenius _ _ _ f)
    (injective_stalkAtMap _ _ _ f) (h x)

/-- A quotient of a Weil sheaf with weights at most `v` has weights at most `v`: its stalks are
Frobenius-equivariant quotients. -/
theorem HasWeightsAtMost.of_epi {v : ℝ} (f : F ⟶ G) [Epi f] (h : F.HasWeightsAtMost ι v) :
    G.HasWeightsAtMost ι v := fun x ↦
  FrobeniusModule.HasWeightsAtMost.of_surjective _ (stalkAtMap_frobenius _ _ _ f)
    (surjective_stalkAtMap _ _ _ f) (h x)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A zero Weil sheaf is punctually pure of every weight: its stalks vanish. -/
theorem isPunctuallyPureOfWeight_of_isZero (hF : IsZero F) (w : ℝ) :
    F.IsPunctuallyPureOfWeight ι w := fun x α hα ↦ by
  have : x ∉ F.support := by rw [support_eq_empty_of_isZero hF]; exact id
  have : Subsingleton (F.stalk x).carrier := not_nontrivial_iff_subsingleton.1 this
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  exact (hv.2 (Subsingleton.elim _ _)).elim


/-- A nonzero Weil sheaf punctually pure of weight `u` with weights at most `v` has `u ≤ v`: it has
a nonzero stalk at some closed point, and an eigenvalue there. -/
theorem IsPunctuallyPureOfWeight.le_of_hasWeightsAtMost {u v : ℝ}
    (hu : F.IsPunctuallyPureOfWeight ι u) (hv : F.HasWeightsAtMost ι v) (hF : ¬ IsZero F) :
    u ≤ v := by
  obtain ⟨x, hx⟩ := exists_nontrivial_stalk_of_not_isZero F hF
  have := (F.stalk x).finiteDimensional
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (F.stalk x).frobeniusEnd
  have h1 := hu x α hα
  have h2 := hv x α hα
  rw [h1] at h2
  have hq : 1 < ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) := by
    rw [Scheme.Hom.residueCard]
    exact_mod_cast Nat.one_lt_pow (Scheme.Hom.degreeOver_ne_zero _ x.2) Finite.one_lt_card
  have := (Real.rpow_le_rpow_left_iff hq).1 h2
  linarith

/-- **Punctual cutoff for an already mixed sheaf.** Let `G` be a constructible Weil sheaf on a
separated `k₀`-scheme of finite type, mixed of weights at most some `u`. If every eigenvalue
`α` of the local Frobenius of `G` at every closed point `y` satisfies `|ι α| ≤ q_y ^ (v / 2)`,
then `G` is mixed of weights at most `v`: a nonzero pure quotient of a mixed filtration has a
nonzero stalk at some closed point, and its eigenvalues there are eigenvalues of `G`
(blueprint: `lemma-bounding-weights-mixed-sheaf--1`). -/
theorem IsMixedOfWeightsAtMost.of_hasWeightsAtMost
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {u v : ℝ}
    (h : F.IsMixedOfWeightsAtMost ι u) (hv : F.HasWeightsAtMost ι v) :
    F.IsMixedOfWeightsAtMost ι v := by
  rw [isMixedOfWeightsAtMost_iff_filtrationClosure] at h ⊢
  revert hv
  induction h with
  | of_isZero hX => exact fun _ ↦ .of_isZero hX
  | of_mono i _ hi ih =>
    intro hv
    refine .of_mono i (ih (hv.of_mono i)) ?_
    obtain ⟨w', -, hpure⟩ := hi
    by_cases hz : IsZero (cokernel i)
    · exact ⟨v, le_rfl, isPunctuallyPureOfWeight_of_isZero hz v⟩
    · exact ⟨w', hpure.le_of_hasWeightsAtMost (hv.of_epi (cokernel.π i)) hz, hpure⟩

/-- A sheaf with a finite filtration `0 = G 0 ↪ G 1 ↪ ⋯ ↪ G n ≅ F` whose successive quotients
`coker φᵢ` are mixed of weights at most `w` is mixed of weights at most `w`: splice the filtrations
of the quotients along the filtration of `F` (blueprint: `theorem-direct-image-mixed-sheaf--1`, the
extension step along the abutment filtration). -/
theorem IsMixedOfWeightsAtMost.of_filtration {n : ℕ} (G : Fin (n + 1) → WeilSheaf k₀ l X)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ) (h0 : IsZero (G 0))
    (hlast : IsIsomorphic (G (Fin.last n)) F) [∀ i, Mono (φ i)]
    (h : ∀ i : Fin n, (cokernel (φ i)).IsMixedOfWeightsAtMost ι w) :
    F.IsMixedOfWeightsAtMost ι w := by
  have key : ∀ (i : ℕ) (hi : i < n + 1), (G ⟨i, hi⟩).IsMixedOfWeightsAtMost ι w := by
    intro i
    induction i with
    | zero => exact fun _ ↦ isMixedOfWeightsAtMost_of_isZero h0 w
    | succ i ih =>
      intro hi
      exact (ih (by omega)).of_mono_cokernel (φ ⟨i, by omega⟩) (h ⟨i, by omega⟩)
  exact (key n (by omega)).of_iso hlast.some

end WeilSheaf

section Map

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}

namespace WeilSheaf

/-- An exact functor between Weil sheaves which raises punctual purity weights by `c` raises
mixed upper weight bounds by `c`: it carries a mixed filtration to a mixed filtration. -/
theorem IsMixedOfWeightsAtMost.map_add (Φ : WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (c : ℝ)
    (hΦ : ∀ (v : ℝ) (G : WeilSheaf k₀ l X), G.IsPunctuallyPureOfWeight ι v →
      (Φ.obj G).IsPunctuallyPureOfWeight ι (v + c))
    {w : ℝ} {F : WeilSheaf k₀ l X} (hF : F.IsMixedOfWeightsAtMost ι w) :
    (Φ.obj F).IsMixedOfWeightsAtMost ι (w + c) := by
  obtain ⟨n, G, φ, h0, ⟨e⟩, hmono, hpure⟩ := hF
  refine ⟨n, fun i ↦ Φ.obj (G i), fun i ↦ Φ.map (φ i), Φ.map_isZero h0, ⟨Φ.mapIso e⟩,
    fun i ↦ ?_, fun i ↦ ?_⟩
  · have := hmono i
    infer_instance
  · obtain ⟨v, hv, h⟩ := hpure i
    exact ⟨v + c, by linarith, (hΦ v _ h).of_epi (PreservesCokernel.iso Φ (φ i)).hom⟩

/-- An exact functor between Weil sheaves which preserves punctual purity of every weight
preserves mixed upper weight bounds: it carries a mixed filtration to a mixed filtration. -/
theorem IsMixedOfWeightsAtMost.map (Φ : WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (hΦ : ∀ (v : ℝ) (G : WeilSheaf k₀ l X), G.IsPunctuallyPureOfWeight ι v →
      (Φ.obj G).IsPunctuallyPureOfWeight ι v)
    {w : ℝ} {F : WeilSheaf k₀ l X} (hF : F.IsMixedOfWeightsAtMost ι w) :
    (Φ.obj F).IsMixedOfWeightsAtMost ι w := by
  simpa using hF.map_add Φ 0 (by simpa using hΦ)

end WeilSheaf

end Map

/-! ### Mixed complexes -/

/-- A bounded constructible Weil complex `K` is `ι`-*mixed of weights at most* `w` if its `b`-th
cohomology sheaf `𝓗ᵇK` is mixed of weights at most `w + b`, for every `b`; equivalently, the
bound in total degree `n` is `w + n` (blueprint: `definition-weights`). -/
def WeilComplex.IsMixedOfWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (w : ℝ) : Prop :=
  ∀ b : ℤ, ((WeilComplex.homologySheaf b).obj K).IsMixedOfWeightsAtMost ι (w + (b : ℝ))

/-- Mixed upper bounds of Weil complexes are invariant under isomorphism
(blueprint: `definition-weights`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.of_iso {ι : PadicAlgCl l →+* ℂ}
    {K L : WeilComplex k₀ l X} {w : ℝ} (e : K ≅ L) (h : K.IsMixedOfWeightsAtMost ι w) :
    L.IsMixedOfWeightsAtMost ι w :=
  fun b ↦ (h b).of_iso ((WeilComplex.homologySheaf b).mapIso e)

namespace WeilComplex

variable {ι : PadicAlgCl l →+* ℂ} {K L : WeilComplex k₀ l X} {w : ℝ}

/-- Mixed upper bounds of Weil complexes are monotone in the bound
(blueprint: `definition-weights`). -/
theorem IsMixedOfWeightsAtMost.mono_weight {w' : ℝ} (h : K.IsMixedOfWeightsAtMost ι w)
    (hw : w ≤ w') : K.IsMixedOfWeightsAtMost ι w' :=
  fun b ↦ (h b).mono_weight (by linarith)

/-- **Extension stability of complex weights.** If `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` is a distinguished
triangle of Weil complexes and `K₁`, `K₃` are mixed of weights at most `w`, then so is `K₂`: in
each degree `j` the exact sequence `𝓗ʲK₁ ⟶ 𝓗ʲK₂ ⟶ 𝓗ʲK₃` exhibits `𝓗ʲK₂` as an extension of a
subsheaf of `𝓗ʲK₃` by a quotient of `𝓗ʲK₁` (blueprint: `lemma-weights-exact-sequence`). -/
theorem IsMixedOfWeightsAtMost.of_distTriang (T : Triangle (WeilComplex k₀ l X))
    (hT : T ∈ distTriang _) (h₁ : T.obj₁.IsMixedOfWeightsAtMost ι w)
    (h₃ : T.obj₃.IsMixedOfWeightsAtMost ι w) : T.obj₂.IsMixedOfWeightsAtMost ι w :=
  fun b ↦ WeilSheaf.IsMixedOfWeightsAtMost.of_exact (homologySheaf_exact₂ T b hT) (h₁ b) (h₃ b)

/-- **Retract stability of complex weights.** A direct summand, more generally a retract, of a
Weil complex mixed of weights at most `w` is mixed of weights at most `w`: its cohomology sheaves
are retracts of those of the ambient complex. -/
theorem IsMixedOfWeightsAtMost.of_retract (h : Retract K L) (hL : L.IsMixedOfWeightsAtMost ι w) :
    K.IsMixedOfWeightsAtMost ι w :=
  fun b ↦ (hL b).of_retract (h.map (homologySheaf b))

/-- A shift `K[n]` of a Weil complex mixed of weights at most `w` is mixed of weights at most
`w + n`. -/
theorem IsMixedOfWeightsAtMost.shift (hK : K.IsMixedOfWeightsAtMost ι w) (n : ℤ) :
    (K⟦n⟧).IsMixedOfWeightsAtMost ι (w + n) := fun a ↦
  ((hK (n + a)).of_iso (homologySheafShiftIso K n a (n + a) rfl).symm).mono_weight
    (by push_cast; linarith)

/-- A Weil complex `K` is mixed of weights at most `w` as soon as `K[n]` is mixed of weights at
most `w + n`. -/
theorem IsMixedOfWeightsAtMost.of_shift {n : ℤ} (hK : (K⟦n⟧).IsMixedOfWeightsAtMost ι (w + n)) :
    K.IsMixedOfWeightsAtMost ι w := fun a ↦
  ((hK (a - n)).of_iso (homologySheafShiftIso K n (a - n) a (by lia))).mono_weight
    (by push_cast; linarith)

/-- A Weil sheaf placed in degree `a` is mixed of weights at most `w` as a complex if and only if
the sheaf is mixed of weights at most `w + a` (blueprint: `definition-weights--6`). -/
theorem isMixedOfWeightsAtMost_singleComplex_iff (a : ℤ) (G : WeilSheaf k₀ l X) :
    (singleComplex a G).IsMixedOfWeightsAtMost ι w ↔ G.IsMixedOfWeightsAtMost ι (w + a) := by
  refine ⟨fun h ↦ (h a).of_iso (homologySheafSingleComplexIso a G), fun h b ↦ ?_⟩
  by_cases hb : b = a
  · subst hb
    exact h.of_iso (homologySheafSingleComplexIso b G).symm
  · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
      (isZero_homologySheaf_singleComplex hb G) _

/-- A Weil sheaf, viewed as a complex in degree zero, is mixed of weights at most `w` if and only
if the sheaf is (blueprint: `definition-weights--6`). -/
theorem isMixedOfWeightsAtMost_toComplex_iff (G : WeilSheaf k₀ l X) :
    (WeilSheaf.toComplex.obj G).IsMixedOfWeightsAtMost ι w ↔ G.IsMixedOfWeightsAtMost ι w := by
  rw [WeilSheaf.toComplex_obj, isMixedOfWeightsAtMost_singleComplex_iff]
  simp

end WeilComplex

/-- The direct-image weight assertion of the blueprint theorem
`theorem-direct-image-mixed-sheaf--1`, for a single morphism `f : X ⟶ Y` of `k₀`-schemes: every
constructible Weil sheaf `F` on `X` that is mixed of weights at most `w` has `Rʳf₀!F` mixed of
weights at most `w + r`, for every `r`. The reductions of the blueprint section
`chap-The-Deligne-Laumon-theorem-in-general` propagate this assertion along compositions and
open–closed decompositions. -/
def HasDirectImageWeightBound (k₀ : Type u) [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (ι : PadicAlgCl l →+* ℂ) {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] : Prop :=
  haveI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  ∀ (w : ℝ) (F : WeilSheaf k₀ l X), F.IsMixedOfWeightsAtMost ι w →
    ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj F).IsMixedOfWeightsAtMost ι (w + r)

/-- The complex form of the direct-image weight assertion, for a single morphism `f : X ⟶ Y` of
`k₀`-schemes: `Rf₀!` carries every Weil complex on `X` that is mixed of weights at most `w` to a
Weil complex mixed of weights at most `w`, for every `w`
(blueprint: `lemma-weight-bounds-partitions`). -/
def HasDirectImageComplexWeightBound (k₀ : Type u) [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (ι : PadicAlgCl l →+* ℂ) {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] : Prop :=
  haveI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  ∀ (w : ℝ) (K : WeilComplex k₀ l X), K.IsMixedOfWeightsAtMost ι w →
    ((WeilComplex.derivedLowerShriek k₀ l f).obj K).IsMixedOfWeightsAtMost ι w


/-! ### Passage from sheaves to complexes -/

section Devissage

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

variable {ι : PadicAlgCl l →+* ℂ}
open _root_.DerivedCategory in
/-- A Weil sheaf placed in degree `b` is the shift by `-b` of the sheaf placed in degree `0`. -/
noncomputable def singleComplexIsoShift (b : ℤ) (G : WeilSheaf k₀ l X) :
    singleComplex b G ≅ (WeilSheaf.toComplex.obj G)⟦-b⟧ :=
  ObjectProperty.isoMk _
    ((((singleFunctors (ProEtaleWeilSheaf k₀ l X)).shiftIso (-b) b 0 (by lia)).app G.obj).symm ≪≫
      (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (-b)).app
        (WeilSheaf.toComplex.obj G)).symm)

/-- A triangulated functor `Φ` between Weil complexes that carries every Weil sheaf mixed of
weights at most `v`, placed in degree zero, to a complex mixed of weights at most `v`, carries a
Weil sheaf mixed of weights at most `w + b`, placed in degree `b`, to a complex mixed of weights
at most `w`. -/
theorem IsMixedOfWeightsAtMost.map_singleComplex
    (Φ : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y) [Φ.CommShift ℤ]
    (hΦ : ∀ (v : ℝ) (G : WeilSheaf k₀ l X), G.IsMixedOfWeightsAtMost ι v →
      (Φ.obj (WeilSheaf.toComplex.obj G)).IsMixedOfWeightsAtMost ι v)
    {w : ℝ} (b : ℤ) {G : WeilSheaf k₀ l X} (hG : G.IsMixedOfWeightsAtMost ι (w + b)) :
    (Φ.obj (singleComplex b G)).IsMixedOfWeightsAtMost ι w := by
  have := ((hΦ _ G hG).shift (-b)).of_iso
    ((Φ.commShiftIso (-b)).app (WeilSheaf.toComplex.obj G)).symm
  refine (this.of_iso (Φ.mapIso (singleComplexIsoShift b G)).symm).mono_weight ?_
  push_cast
  linarith

set_option maxHeartbeats 2000000 in
-- the triangle of Weil complexes lifted from the truncation triangle is checked by unfolding the
-- full subcategory structure, which needs more heartbeats
open _root_.DerivedCategory in
/-- **Passage from sheaves to complexes.** Let `Φ` be a triangulated functor between Weil
complexes which carries every Weil sheaf mixed of weights at most `v`, placed in degree zero, to a
Weil complex mixed of weights at most `v`, for every `v`. Then `Φ` carries every Weil complex
mixed of weights at most `w` to a Weil complex mixed of weights at most `w`: by induction on the
length of a bounded complex `K`, using the truncation triangle `τ_{<b}K ⟶ K ⟶ 𝓗ᵇ(K)[-b] ⟶`
and the extension stability of complex weights. This is the output of the hypercohomology
spectral sequence `E₂^{a,b} = 𝓗ᵃ(Φ 𝓗ᵇ(K)) ⇒ 𝓗ᵃ⁺ᵇ(Φ K)` used in the blueprint
(blueprint: `lemma-finite-quasi-finite-direct-images--2`). -/
theorem IsMixedOfWeightsAtMost.map_of_forall_toComplex
    (Φ : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hΦ : ∀ (v : ℝ) (G : WeilSheaf k₀ l X), G.IsMixedOfWeightsAtMost ι v →
      (Φ.obj (WeilSheaf.toComplex.obj G)).IsMixedOfWeightsAtMost ι v)
    {w : ℝ} {K : WeilComplex k₀ l X} (hK : K.IsMixedOfWeightsAtMost ι w) :
    (Φ.obj K).IsMixedOfWeightsAtMost ι w := by
  let P := WeilComplex.objectProperty k₀ l X
  suffices H : ∀ (n : ℕ) (a : ℤ) (K : WeilComplex k₀ l X), K.obj.IsGE a →
      K.obj.IsLE (a + n - 1) → K.IsMixedOfWeightsAtMost ι w →
        (Φ.obj K).IsMixedOfWeightsAtMost ι w by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
    have : K.obj.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le _ b _ (by lia)
    exact H _ a K ha this hK
  intro n
  induction n with
  | zero =>
    intro a K _ _ _
    have : K.obj.IsLE (a - 1) := by simpa using ‹K.obj.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK0 : IsZero K := by
      refine IsZero.of_full_of_faithful_of_isZero P.ι _ ?_
      exact TStructure.t.isZero K.obj (a - 1) a (by lia)
    exact fun b ↦ WeilSheaf.isMixedOfWeightsAtMost_of_isZero
      ((homologySheaf b).map_isZero (Φ.map_isZero hK0)) _
  | succ n ih =>
    intro a K _ _ hK
    set b : ℤ := a + n
    let T := (TStructure.t.triangleLTGE b).obj K.obj
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K.obj
    have : T.obj₃.IsLE b := by
      have : K.obj.IsLE b := TStructure.t.isLE_of_le _ (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K.obj) b)
    have : T.obj₃.IsGE b :=
      inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K.obj) b)
    obtain ⟨Z, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
    have h₁ : IsZero ((homologyFunctor _ (b + 1)).obj T.obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor _ b).obj T.obj₁) := isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀ h₁
    -- `𝓗ᵇK ≅ Z`
    let eZ : (homologyFunctor _ b).obj K.obj ≅ Z :=
      asIso ((homologyFunctor _ b).map T.mor₂) ≪≫ (homologyFunctor _ b).mapIso e ≪≫
        (singleFunctorCompHomologyFunctorIso _ b).app Z
    let G : WeilSheaf k₀ l X := ⟨Z, (WeilSheaf.objectProperty k₀ l X).prop_of_iso eZ (K.2.2 b)⟩
    have hP₃ : P T.obj₃ := P.prop_of_iso e.symm (singleComplex b G).2
    have hP₁ : P T.obj₁ := P.ext_of_isTriangulatedClosed₁ T hT K.2 hP₃
    let T' : Triangle (WeilComplex k₀ l X) :=
      Triangle.mk (X := ⟨T.obj₁, hP₁⟩) (Y := K) (Z := ⟨T.obj₃, hP₃⟩)
        (ObjectProperty.homMk T.mor₁) (ObjectProperty.homMk T.mor₂)
        (P.fullyFaithfulι.preimage (T.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨T.obj₁, hP₁⟩))
    have hT' : T' ∈ distTriang _ := by
      refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (Iso.refl _) ?_ ?_ ?_)
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl
      · simp only [Iso.refl_hom, Category.id_comp]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        change P.ι.map (P.fullyFaithfulι.preimage _) ≫ (P.ι.commShiftIso (1 : ℤ)).hom.app _ = _
        rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _
    have hT'' := Φ.map_distinguished T' hT'
    refine IsMixedOfWeightsAtMost.of_distTriang (Φ.mapTriangle.obj T') hT'' ?_ ?_
    · -- the truncation `τ_{<b}K` is handled by induction
      have hGE : T.obj₁.IsGE a :=
        inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K.obj) a)
      have hLE : T.obj₁.IsLE (a + n - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      refine ih a ⟨T.obj₁, hP₁⟩ hGE hLE fun q ↦ ?_
      · have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
        by_cases hq : q < b
        · have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
            isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
              (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
          let e' : (homologySheaf q).obj K ≅
              (homologySheaf q).obj (⟨T.obj₁, hP₁⟩ : WeilComplex k₀ l X) :=
            ObjectProperty.isoMk _ (asIso ((homologyFunctor _ q).map T.mor₁)).symm
          exact (hK q).of_iso e'
        · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
            ((isZero_homologySheaf_obj_iff q (⟨T.obj₁, hP₁⟩ : WeilComplex k₀ l X)).2
              (isZero_of_isLE T.obj₁ (b - 1) q (by lia))) _
    · -- the last term is `𝓗ᵇ(K)` placed in degree `b`
      have hG : G.IsMixedOfWeightsAtMost ι (w + b) := (hK b).of_iso (ObjectProperty.isoMk _ eZ)
      exact (IsMixedOfWeightsAtMost.map_singleComplex Φ hΦ b hG).of_iso
        (Φ.mapIso (ObjectProperty.isoMk _ e.symm))

end WeilComplex

end Devissage

end AlgebraicGeometry
