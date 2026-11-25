/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.StalkExtensionByZero

/-!
# The formal reductions of the Deligne–Laumon direct-image bound

The Deligne–Laumon bound — that `Rʳf₀!F` is mixed of weights at most `w + r` (blueprint
`theorem-direct-image-mixed-sheaf--1`, stated for a single morphism as
`AlgebraicGeometry.HasDirectImageWeightBound`) — is reduced to the case of a relative affine line
by three formal steps, all of which are proved in this file:

- it propagates along compositions, by the composition isomorphism `R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!`
  and the passage from sheaves to complexes, which replaces the compact-support Leray spectral
  sequence;
- it propagates from an open and its closed complement to the ambient scheme, by the open–closed
  triangle;
- it holds outright for separated quasi-finite morphisms, whose compact-support direct image is
  exact and preserves both mixedness and punctual upper weight bounds.

Once it holds for `f`, it passes from sheaves to complexes: `Rf₀!` preserves Weil complexes mixed
of weights at most `w`, by dévissage along the truncation triangles
(`AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex`), which replaces
the hypercohomology spectral sequence.

The six-functor input — composition, base change and the open–closed triangles of `Rf₀!` — is
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`.

## Main statements

- `AlgebraicGeometry.HasDirectImageWeightBound.isMixedOfWeightsAtMost_derivedLowerShriek`:
  blueprint `lemma-finite-quasi-finite-direct-images--2`.
- `AlgebraicGeometry.HasDirectImageWeightBound.comp`: blueprint
`theorem-direct-image-mixed-sheaf--1`,
  through its form `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp` for
  a single sheaf (`theorem-direct-image-mixed-sheaf--1`).
- `AlgebraicGeometry.HasDirectImageWeightBound.of_openClosed`: blueprint
  `lemma-weight-bounds-partitions--1`.
- `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.of_openClosed`: blueprint
  `lemma-mixedness-open-closed--1`.
- `AlgebraicGeometry.HasDirectImageComplexWeightBound.of_openClosed`,
  `AlgebraicGeometry.HasDirectImageWeightBound.of_openClosed_target`,
  `AlgebraicGeometry.HasDirectImageComplexWeightBound.of_openClosed_target` and
  `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_of_shortExact`: blueprint
  `lemma-weight-bounds-partitions`, the open–closed reductions on the source and on the
  target and the reduction along short exact sequences of coefficients.
- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite`:
  blueprint `lemma-finite-quasi-finite-direct-images`, part 2, and its consequence
  `AlgebraicGeometry.HasDirectImageWeightBound.of_locallyQuasiFinite`; part 1 is
  `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite` in
  `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing`, part 3 is
  `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights`.
- `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isFinite`: blueprint
  `lemma-finite-quasi-finite-direct-images--2`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1.8 and
  §3.3, where the composition and quasi-finite steps appear.
- [Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*][laumon1987], Publ. Math. IHÉS **65** (1987), for the reduction to the affine line.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- The direct-image weight assertion only depends on the morphism, not on the instance
arguments through which it is stated. -/
theorem HasDirectImageWeightBound.of_eq {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] {f f' : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f'] [LocallyOfFiniteType f']
    [QuasiCompact f'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (h : f = f')
    (hf : HasDirectImageWeightBound k₀ ι f) : HasDirectImageWeightBound k₀ ι f' := by
  subst h
  exact hf

/-! ### Pullbacks of sheaves and complexes -/

section UpperStar

variable {W X : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (h : W ⟶ X) [h.IsOver (Spec (CommRingCat.of k₀))]

variable [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Pulling back along an immersion `h : W ⟶ X` preserves mixed upper weight bounds: restrict
the filtration, a closed point of `W` being a closed point of `X` with the same residue field,
stalk and local Frobenius (blueprint: `lemma-weight-bounds-partitions`, restriction).

The pullback is exact and preserves punctual purity along any morphism of `k₀`-schemes
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.upperStar`), so the immersion hypothesis
is not used. -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.upperStar [IsImmersion h] {w : ℝ}
    {F : WeilSheaf k₀ l X} (hF : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.upperStar h).obj F).IsMixedOfWeightsAtMost ι w :=
  hF.map (WeilSheaf.upperStar h) fun _ _ hG ↦ WeilSheaf.IsPunctuallyPureOfWeight.upperStar hG h

/-- Pulling back along an immersion `h : W ⟶ X` carries Weil complexes mixed of weights at most
`w` to Weil complexes mixed of weights at most `w`: `h^*` is exact, so it commutes with taking
cohomology sheaves, and it preserves mixed upper bounds of sheaves
(blueprint: `lemma-weight-bounds-partitions`, restriction).

The pullback of Weil complexes is triangulated and carries a Weil sheaf placed in degree zero to
its pullback placed in degree zero, so the sheaf case and the passage from sheaves to complexes
(`AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex`) apply. -/
theorem WeilComplex.IsMixedOfWeightsAtMost.upperStar [IsImmersion h] {w : ℝ}
    {K : WeilComplex k₀ l X} (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.upperStar h).obj K).IsMixedOfWeightsAtMost ι w :=
  WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex _ (fun _ G hG ↦
    ((WeilComplex.isMixedOfWeightsAtMost_toComplex_iff _).2 (hG.upperStar h)).of_iso
      (WeilComplex.upperStarToComplexIso h G).symm) hK

end UpperStar

/-! ### Passage from sheaves to complexes -/

section SheavesToComplexes

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- If `Rʳf₀!G` is mixed of weights at most `w + r` for every `r`, then `Rf₀!G` is mixed of
weights at most `w` as a complex, its cohomology sheaves vanishing in negative degrees. -/
theorem WeilSheaf.isMixedOfWeightsAtMost_derivedLowerShriek_toComplex {w : ℝ}
    {G : WeilSheaf k₀ l X}
    (hG : ∀ r : ℕ,
      ((WeilSheaf.higherLowerShriek k₀ l f r).obj G).IsMixedOfWeightsAtMost ι (w + r)) :
    ((WeilComplex.derivedLowerShriek k₀ l f).obj
      (WeilSheaf.toComplex.obj G)).IsMixedOfWeightsAtMost ι w := fun n ↦ by
  obtain ⟨r, rfl⟩ | hn : (∃ r : ℕ, n = r) ∨ n < 0 := by
    rcases le_or_gt 0 n with h | h
    · exact Or.inl ⟨n.toNat, (Int.toNat_of_nonneg h).symm⟩
    · exact Or.inr h
  · exact hG r
  · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
      (WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G hn) _

/-- If the direct-image weight assertion holds for `f : X ⟶ Y`, then `Rf₀!` carries bounded
constructible Weil complexes mixed of weights at most `w` to complexes mixed of weights at most
`w` (blueprint: `lemma-finite-quasi-finite-direct-images--2`).

The blueprint argument is the hypercohomology spectral sequence
`E₂^{a,b} = Rᵃf₀!𝓗ᵇ(K) ⇒ 𝓗ᵃ⁺ᵇ(Rf₀!K)`; its output is obtained here by dévissage along the
truncation triangles of `K`
(`AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex`). -/
theorem HasDirectImageWeightBound.isMixedOfWeightsAtMost_derivedLowerShriek
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (hf : HasDirectImageWeightBound k₀ ι f) {w : ℝ} {K : WeilComplex k₀ l X}
    (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerShriek k₀ l f).obj K).IsMixedOfWeightsAtMost ι w :=
  WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex _
    (fun v G hG ↦ WeilSheaf.isMixedOfWeightsAtMost_derivedLowerShriek_toComplex (hf v G hG)) hK

end SheavesToComplexes

/-! ### Composition

The blueprint argument for the composition step runs through the composition isomorphism
`R(f ≫ g)₀! ≅ Rg₀! ∘ Rf₀!` (`proposition-composition-base-change-rf-shriek--1`) and the
compact-support Leray spectral sequence `E₂^{a,b} = Rᵃg₀!Rᵇf₀!F ⇒ Rᵃ⁺ᵇ(f ≫ g)₀!F`. The output of the
spectral sequence needed here is the passage from sheaves to complexes for `g`, applied to the
complex `Rf₀!F`. -/

section Composition

variable {X Z Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Z} {g : Z ⟶ Y}
  [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- Let `F` be a Weil sheaf on `X` such that `Rᵇf₀!F` is mixed of weights at most `w + b` for every
`b`, and suppose the direct-image weight assertion holds for `g`. Then `Rⁿ(f ≫ g)₀!F` is mixed of
weights at most `w + n` for every `n` (blueprint: `theorem-direct-image-mixed-sheaf--1`, for a
single sheaf).

The complex `Rf₀!F` is mixed of weights at most `w`, hence so is `Rg₀!Rf₀!F ≅ R(f ≫ g)₀!F` by the
passage from sheaves to complexes for `g`; this is the output of the compact-support Leray
spectral sequence `E₂^{a,b} = Rᵃg₀!Rᵇf₀!F ⇒ Rᵃ⁺ᵇ(f ≫ g)₀!F`. -/
theorem WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp {w : ℝ} {F : WeilSheaf k₀ l X}
    (hF : ∀ b : ℕ,
      ((WeilSheaf.higherLowerShriek k₀ l f b).obj F).IsMixedOfWeightsAtMost ι (w + b))
    (hg : HasDirectImageWeightBound k₀ ι g) (n : ℕ) :
    ((WeilSheaf.higherLowerShriek k₀ l (f ≫ g) n).obj F).IsMixedOfWeightsAtMost ι (w + n) := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) (f := f)
    (g := g)
  exact (hg.isMixedOfWeightsAtMost_derivedLowerShriek
    (WeilSheaf.isMixedOfWeightsAtMost_derivedLowerShriek_toComplex hF)).of_iso
      (e.app (WeilSheaf.toComplex.obj F)).symm n

/-- If the direct-image weight assertion holds for `f : X ⟶ Z` and for `g : Z ⟶ Y`, then it holds
for `f ≫ g`:

```
X --- f ---> Z --- g ---> Y
 \                        ^
  `-------- f ≫ g --------'
```

(blueprint: `theorem-direct-image-mixed-sheaf--1`, proved as
`theorem-direct-image-mixed-sheaf--1`). -/
theorem HasDirectImageWeightBound.comp (hf : HasDirectImageWeightBound k₀ ι f)
    (hg : HasDirectImageWeightBound k₀ ι g) : HasDirectImageWeightBound k₀ ι (f ≫ g) :=
  fun w F hF ↦ WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_comp (hf w F hF) hg

end Composition

/-! ### Open–closed decompositions

The open–closed reduction runs through the open–closed triangle
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ K[1]`, its image under `Rf₀!`, the long exact cohomology sequence of a
triangle and compact support base change. -/

section OpenClosed

/-- Extension by zero `j₀!` along an open immersion `j : U ⟶ X` carries Weil complexes mixed of
weights at most `w` to Weil complexes mixed of weights at most `w`: it has the same stalks at the
points of `U` and zero stalks elsewhere, and extends filtrations by zero
(blueprint: `lemma-weight-bounds-partitions`, part 2). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek_of_isOpenImmersion
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec
    (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] {w : ℝ} {K : WeilComplex k₀ l U}
    (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerShriek k₀ l j).obj K).IsMixedOfWeightsAtMost ι w := by
  refine WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex _ (fun v G hG ↦ ?_) hK
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion j G
  exact ((WeilComplex.isMixedOfWeightsAtMost_toComplex_iff _).2
    (hG.map (WeilSheaf.extensionByZero j) fun _ _ h ↦ h.extensionByZero j)).of_iso e.symm

/-- **Finite pushforward preserves upper weights** (blueprint:
`lemma-finite-quasi-finite-direct-images--2`): for a finite morphism `g : Z ⟶ X` of `k₀`-schemes and
a Weil complex `K` on `Z` mixed of weights at most `w`, the complex `Rg₀*K = Rg₀!K` is mixed of
weights at most `w`.

By the passage from sheaves to complexes it suffices to treat a Weil sheaf `G`, and by the
distinguished triangles of the short exact sequences of a mixed filtration of `G`, a punctually
pure quotient `Q` of weight at most `w`. As `g₀*` is exact, `Rg₀*Q` is `g₀*Q` placed in degree
zero, which is punctually pure of the same weight
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.lowerStar_of_isFinite`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isFinite
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec
    (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (g : Z ⟶ X) [IsFinite g] [g.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {w : ℝ}
    {K : WeilComplex k₀ l Z} (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerStar g).obj K).IsMixedOfWeightsAtMost ι w := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  refine WeilComplex.IsMixedOfWeightsAtMost.map_of_forall_toComplex _ (fun v G hG ↦ ?_) hK
  rw [WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure] at hG
  induction hG with
  | of_isZero hG =>
    exact fun b ↦ WeilSheaf.isMixedOfWeightsAtMost_of_isZero
      ((WeilComplex.homologySheaf b).map_isZero
        ((WeilComplex.derivedLowerStar g).map_isZero (WeilSheaf.toComplex.map_isZero hG))) _
  | @of_mono G' G i _ _ hQ ih =>
    have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      .mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)) inferInstance
        inferInstance
    refine WeilComplex.IsMixedOfWeightsAtMost.of_distTriang _
      ((WeilComplex.derivedLowerStar g).map_distinguished _
        (WeilSheaf.singleTriangle_distinguished hS)) ih ?_
    obtain ⟨u, hu, hpure⟩ := hQ
    intro b
    obtain ⟨n, rfl⟩ | hb : (∃ n : ℕ, b = n) ∨ b < 0 := by
      rcases le_or_gt 0 b with h | h
      · exact Or.inl ⟨b.toNat, (Int.toNat_of_nonneg h).symm⟩
      · exact Or.inr h
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact WeilSheaf.isMixedOfWeightsAtMost_iff_filtrationClosure.2
          (ObjectProperty.prop_of_iso _
            (WeilSheaf.homologySheafZeroDerivedLowerStarIso g (cokernel i)).symm
            (ObjectProperty.le_filtrationClosure _ ⟨u, by simpa using hu,
              hpure.lowerStar_of_isFinite g⟩))
      · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
          (WeilSheaf.isZero_higherLowerStar_of_isFinite g _ n hn) _
    · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
        (WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg g _ hb) _

/-- The direct image `i₀*` along a closed immersion `i : Z ⟶ X` carries Weil complexes mixed of
weights at most `w` to Weil complexes mixed of weights at most `w`, the case of a closed
immersion of the finite pushforward bound (blueprint: `lemma-finite-quasi-finite-direct-images--2`,
used in `lemma-weight-bounds-partitions`, part 2). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isClosedImmersion
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec
    (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {w : ℝ}
    {K : WeilComplex k₀ l Z} (hK : K.IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.derivedLowerStar i).obj K).IsMixedOfWeightsAtMost ι w :=
  hK.derivedLowerStar_of_isFinite i

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the two
outer terms `j₀!j₀^*K` and `i₀*i₀^*K` of the localization triangle
`j₀!j₀^*K ⟶ K ⟶ i₀*i₀^*K ⟶ K[1]` are mixed of weights at most `w`, then so is `K`
(blueprint: `lemma-mixedness-open-closed--1`).

This is the extension stability of complex weights (`lemma-weights-exact-sequence`) along the
localization triangle (`proposition-extension-zero-restriction-closed-subscheme--8`). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.of_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) {w : ℝ} {K : WeilComplex k₀ l X}
    (hU : ((WeilComplex.derivedLowerShriek k₀ l j).obj
      ((WeilComplex.upperStar j).obj K)).IsMixedOfWeightsAtMost ι w)
    (hZ : ((WeilComplex.derivedLowerStar i).obj
      ((WeilComplex.upperStar i).obj K)).IsMixedOfWeightsAtMost ι w) :
    K.IsMixedOfWeightsAtMost ι w := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := WeilComplex.exists_distTriang_openClosed j i hij K
  exact (WeilComplex.IsMixedOfWeightsAtMost.of_distTriang T hT (hU.of_iso e₁.symm)
    (hZ.of_iso e₃.symm)).of_iso e₂

/-- Let `G` be a Weil sheaf on `X`, let `j : U ⟶ X` be an open immersion whose closed complement
is `i : Z ⟶ X`, and suppose that `j₀^*G` and `i₀^*G` are mixed of weights at most `w`. Then `G`
is mixed of weights at most `w` (blueprint: `lemma-weight-bounds-partitions`, part 2).

The blueprint argument applies `lemma-mixedness-open-closed--1` to `G` placed in degree zero. -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [X.Over
    (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) {w : ℝ} {G : WeilSheaf k₀ l X}
    (hU : ((WeilSheaf.upperStar j).obj G).IsMixedOfWeightsAtMost ι w)
    (hZ : ((WeilSheaf.upperStar i).obj G).IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  rw [← WeilComplex.isMixedOfWeightsAtMost_toComplex_iff] at hU hZ ⊢
  exact WeilComplex.IsMixedOfWeightsAtMost.of_openClosed hij
    ((hU.of_iso (WeilComplex.upperStarToComplexIso j G).symm).derivedLowerShriek_of_isOpenImmersion
      j)
    ((hZ.of_iso (WeilComplex.upperStarToComplexIso i G).symm).derivedLowerStar_of_isClosedImmersion
      i)

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`, and let
`f : X ⟶ Y`. Applying `Rf₀!` to the open–closed triangle of a Weil sheaf `F` and taking
cohomology sheaves gives exact sequences
`Rʳ(j ≫ f)₀! j₀^*F ⟶ Rʳf₀!F ⟶ Rʳ(i ≫ f)₀! i₀^*F`
(blueprint: `lemma-weight-bounds-partitions`, part 1, using `lem-sp-long-exact-of-triangle`).
-/
theorem WeilSheaf.exists_exact_higherLowerShriek_of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (F : WeilSheaf k₀ l X) (r : ℕ) :
    ∃ S : ShortComplex (WeilSheaf k₀ l Y), S.Exact ∧
      Nonempty (S.X₁ ≅ (WeilSheaf.higherLowerShriek k₀ l (j ≫ f) r).obj
        ((WeilSheaf.upperStar j).obj F)) ∧
      Nonempty (S.X₂ ≅ (WeilSheaf.higherLowerShriek k₀ l f r).obj F) ∧
      Nonempty (S.X₃ ≅ (WeilSheaf.higherLowerShriek k₀ l (i ≫ f) r).obj
        ((WeilSheaf.upperStar i).obj F)) := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_openClosed
    j i hij f (WeilSheaf.toComplex.obj F)
  refine ⟨_, WeilComplex.homologySheaf_exact₂ T r hT, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact (WeilComplex.homologySheaf r).mapIso (e₁ ≪≫
      (WeilComplex.derivedLowerShriek k₀ l (j ≫ f)).mapIso
        (WeilComplex.upperStarToComplexIso j F))
  · exact (WeilComplex.homologySheaf r).mapIso e₂
  · exact (WeilComplex.homologySheaf r).mapIso (e₃ ≪≫
      (WeilComplex.derivedLowerShriek k₀ l (i ≫ f)).mapIso
        (WeilComplex.upperStarToComplexIso i F))

/-- Compact support base change for the total direct image: for a pullback square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h₀^*Rf₀!K ≅ Rf'₀!g₀^*K`, so that `h₀^*Rf₀!K` is mixed of weights at most `w`
as soon as `Rf'₀!g₀^*K` is (blueprint: `prop-functor-package`, item 4, used in
`lemma-weight-bounds-partitions`, part 2). -/
theorem WeilComplex.IsMixedOfWeightsAtMost.upperStar_derivedLowerShriek_of_isPullback
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) {w : ℝ}
    {K : WeilComplex k₀ l X}
    (hK : ((WeilComplex.derivedLowerShriek k₀ l f').obj
      ((WeilComplex.upperStar g).obj K)).IsMixedOfWeightsAtMost ι w) :
    ((WeilComplex.upperStar h).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj K)).IsMixedOfWeightsAtMost ι w := by
  obtain ⟨e⟩ := WeilComplex.nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) hH
  exact hK.of_iso (e.app K).symm

/-- Applying `Rʳf₀!` to a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` of Weil sheaves gives an
exact sequence `Rʳf₀!F' ⟶ Rʳf₀!F ⟶ Rʳf₀!F''`, a piece of the long exact sequence of the
distinguished triangle `F' ⟶ F ⟶ F'' ⟶ F'[1]`
(blueprint: `lemma-perverse-sheaves-curve--1` and `lem-sp-long-exact-of-triangle`, used in
`lemma-weight-bounds-partitions`, part 3). -/
theorem WeilSheaf.exact_map_higherLowerShriek {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (r : ℕ) :
    (S.map (WeilSheaf.higherLowerShriek k₀ l f r)).Exact := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  exact WeilComplex.homologySheaf_exact₂ _ r
    ((WeilComplex.derivedLowerShriek k₀ l f).map_distinguished _
      (WeilSheaf.singleTriangle_distinguished hS))

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the
direct-image weight assertion holds for `j ≫ f` and for `i ≫ f`, then it holds for `f`:

```
U --- j ---> X <--- i --- Z
  \          |          /
   `- j ≫ f  | f   i ≫ f -'
       \     v     /
        `--> Y <--'
```

(blueprint: `lemma-weight-bounds-partitions--1`; this is part 1 of
`lemma-weight-bounds-partitions`, sheaf form). -/
theorem HasDirectImageWeightBound.of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (hU : HasDirectImageWeightBound k₀ ι (j ≫ f))
    (hZ : HasDirectImageWeightBound k₀ ι (i ≫ f)) :
    HasDirectImageWeightBound k₀ ι f := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  -- In each degree `r` the exact sequence `Rʳ(j ≫ f)₀! j₀^*F ⟶ Rʳf₀!F ⟶ Rʳ(i ≫ f)₀! i₀^*F`
  -- has outer terms mixed of weights at most `w + r`, hence so is the middle term.
  intro w F hF r
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilSheaf.exists_exact_higherLowerShriek_of_openClosed (f := f) hij F r
  exact (WeilSheaf.IsMixedOfWeightsAtMost.of_exact hS
    ((hU w _ (hF.upperStar j) r).of_iso e₁.symm)
    ((hZ w _ (hF.upperStar i) r).of_iso e₃.symm)).of_iso e₂

/-- Let `j : U ⟶ X` be an open immersion whose closed complement is `i : Z ⟶ X`. If the complex
form of the direct-image weight assertion holds for `j ≫ f` and for `i ≫ f`, then it holds for
`f` (blueprint: `lemma-weight-bounds-partitions`, part 1, complex form).

The blueprint argument applies `Rf₀!` to the open–closed triangle of `K` and uses the extension
stability of complex weights (`lemma-weights-exact-sequence`). -/
theorem HasDirectImageComplexWeightBound.of_openClosed {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] {i : Z ⟶ X} [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of k₀))] {f : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (hU : HasDirectImageComplexWeightBound k₀ ι (j ≫ f))
    (hZ : HasDirectImageComplexWeightBound k₀ ι (i ≫ f)) :
    HasDirectImageComplexWeightBound k₀ ι f := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver j (S := Spec (CommRingCat.of k₀))
  have := locallyOfFiniteType_over_of_isOver i (S := Spec (CommRingCat.of k₀))
  intro w K hK
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    WeilComplex.exists_distTriang_derivedLowerShriek_openClosed j i hij f K
  exact (WeilComplex.IsMixedOfWeightsAtMost.of_distTriang T hT
    ((hU w _ (hK.upperStar j)).of_iso e₁.symm)
    ((hZ w _ (hK.upperStar i)).of_iso e₃.symm)).of_iso e₂

section Target

variable {X Y V T X_V X_T : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k₀))]
  [T.Over (Spec (CommRingCat.of k₀))] [X_V.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X_V ↘ Spec (CommRingCat.of k₀))]
  [X_T.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X_T ↘ Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  {j : V ⟶ Y} [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  {i : T ⟶ Y} [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  {f_V : X_V ⟶ V} [f_V.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f_V]
  [LocallyOfFiniteType f_V] [QuasiCompact f_V] [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (V ↘ Spec (CommRingCat.of k₀))]
  {g_V : X_V ⟶ X} [g_V.IsOver (Spec (CommRingCat.of k₀))]
  {f_T : X_T ⟶ T} [f_T.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f_T]
  [LocallyOfFiniteType f_T] [QuasiCompact f_T] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
  {g_T : X_T ⟶ X} [g_T.IsOver (Spec (CommRingCat.of k₀))]

/-- Let `j : V ⟶ Y` be an open immersion whose closed complement is `i : T ⟶ Y`, and let
`f_V : X_V ⟶ V` and `f_T : X_T ⟶ T` be the base changes of `f : X ⟶ Y`. If the complex form of
the direct-image weight assertion holds for `f_V` and for `f_T`, then it holds for `f`
(blueprint: `lemma-weight-bounds-partitions`, part 2, complex form).

By compact support base change the restrictions of `Rf₀!K` to `V` and `T` are mixed of weights
at most `w`; extension by zero along `j` and the direct image along `i` preserve this, and the
open–closed devissage `lemma-mixedness-open-closed--1` concludes. -/
theorem HasDirectImageComplexWeightBound.of_openClosed_target
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (H_V : IsPullback g_V f_V f j)
    (H_T : IsPullback g_T f_T f i) (h_V : HasDirectImageComplexWeightBound k₀ ι f_V)
    (h_T : HasDirectImageComplexWeightBound k₀ ι f_T) :
    HasDirectImageComplexWeightBound k₀ ι f := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  have : IsOpenImmersion g_V := MorphismProperty.of_isPullback H_V.flip ‹_›
  have : IsClosedImmersion g_T := MorphismProperty.of_isPullback H_T.flip ‹_›
  intro w K hK
  exact WeilComplex.IsMixedOfWeightsAtMost.of_openClosed hij
    (.derivedLowerShriek_of_isOpenImmersion j
      (.upperStar_derivedLowerShriek_of_isPullback H_V (h_V w _ (hK.upperStar g_V))))
    (.derivedLowerStar_of_isClosedImmersion i
      (.upperStar_derivedLowerShriek_of_isPullback H_T (h_T w _ (hK.upperStar g_T))))

/-- Let `j : V ⟶ Y` be an open immersion whose closed complement is `i : T ⟶ Y`, and let
`f_V : X_V ⟶ V` and `f_T : X_T ⟶ T` be the base changes of `f : X ⟶ Y`. If the direct-image
weight assertion holds for `f_V` and for `f_T`, then it holds for `f`
(blueprint: `lemma-weight-bounds-partitions`, part 2, sheaf form).

By the passage from sheaves to complexes the complex form of the assertion holds for `f_V` and
`f_T`; the complex form of the target reduction gives it for `f`, and it is applied to `F` placed
in degree zero. -/
theorem HasDirectImageWeightBound.of_openClosed_target
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (H_V : IsPullback g_V f_V f j)
    (H_T : IsPullback g_T f_T f i) (h_V : HasDirectImageWeightBound k₀ ι f_V)
    (h_T : HasDirectImageWeightBound k₀ ι f_T) :
    HasDirectImageWeightBound k₀ ι f := by
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over f (Spec (CommRingCat.of k₀))]; infer_instance
  intro w F hF r
  exact HasDirectImageComplexWeightBound.of_openClosed_target hij H_V H_T
    (fun _ _ hK ↦ h_V.isMixedOfWeightsAtMost_derivedLowerShriek hK)
    (fun _ _ hK ↦ h_T.isMixedOfWeightsAtMost_derivedLowerShriek hK) w _
    ((WeilComplex.isMixedOfWeightsAtMost_toComplex_iff F).2 hF) r

end Target

/-- Let `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` be a short exact sequence of Weil sheaves on `X`. If `Rʳf₀!F'`
and `Rʳf₀!F''` are mixed of weights at most `w + r` for every `r`, then so is `Rʳf₀!F`
(blueprint: `lemma-weight-bounds-partitions`, part 3). -/
theorem WeilSheaf.isMixedOfWeightsAtMost_higherLowerShriek_of_shortExact {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) {w : ℝ}
    (h₁ : ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj S.X₁).IsMixedOfWeightsAtMost ι
      (w + r))
    (h₃ : ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj S.X₃).IsMixedOfWeightsAtMost ι
      (w + r))
    (r : ℕ) :
    ((WeilSheaf.higherLowerShriek k₀ l f r).obj S.X₂).IsMixedOfWeightsAtMost ι (w + r) :=
  WeilSheaf.IsMixedOfWeightsAtMost.of_exact (WeilSheaf.exact_map_higherLowerShriek f hS r)
    (h₁ r) (h₃ r)

end OpenClosed

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes and a Weil sheaf `F` on `X`,
the complex `Rf₀!F` is concentrated in degree `0`, and it is mixed of weights at most `w` if `F`
is (blueprint: `lemma-finite-quasi-finite-direct-images`, parts 1 and 2).

Zariski's main theorem factors `f` as a quasi-compact open immersion `j : X ⟶ T` followed by a
finite morphism `p : T ⟶ Y`, so that `Rf₀! ≅ Rp₀! ∘ Rj₀! ≅ Rp₀* ∘ j₀!`; the extension by zero
`j₀!` is exact and preserves mixedness, and the finite direct image `p₀*` is exact and preserves
mixedness (`lemma-finite-quasi-finite-direct-images--2`). -/
theorem WeilSheaf.isZero_higherLowerShriek_and_isMixedOfWeightsAtMost_of_quasiFinite
    (F : WeilSheaf k₀ l X) :
    (∀ r : ℕ, 0 < r → IsZero ((WeilSheaf.higherLowerShriek k₀ l f r).obj F)) ∧
      ∀ (ι : PadicAlgCl l →+* ℂ) (w : ℝ), F.IsMixedOfWeightsAtMost ι w →
        ((WeilComplex.derivedLowerShriek k₀ l f).obj
          (WeilSheaf.toComplex.obj F)).IsMixedOfWeightsAtMost ι w := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  obtain ⟨T, j, p, hj, hjc, hp, hjp⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  let : T.Over (Spec (CommRingCat.of k₀)) := ⟨p ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change j ≫ p ≫ Y ↘ Spec (CommRingCat.of k₀) = _
    rw [← Category.assoc, hjp, comp_over]⟩
  have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ _))
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := inferInstanceAs (QuasiCompact (p ≫ _))
  have : QuasiSeparated (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (p ≫ _))
  subst hjp
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j p
  obtain ⟨e'⟩ := WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion j F
  let E := e.app (WeilSheaf.toComplex.obj F) ≪≫ (WeilComplex.derivedLowerShriek k₀ l p).mapIso e' ≪≫
    WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar p _
  refine ⟨fun r hr ↦ ?_, fun ι w hF ↦ ?_⟩
  · exact (WeilSheaf.isZero_higherLowerStar_of_isFinite p _ r hr).of_iso
      ((WeilComplex.homologySheaf r).mapIso E)
  · refine WeilComplex.IsMixedOfWeightsAtMost.of_iso E.symm ?_
    exact WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isFinite p
      ((WeilComplex.isMixedOfWeightsAtMost_toComplex_iff _).2
        (hF.map (WeilSheaf.extensionByZero j) fun _ _ h ↦ h.extensionByZero j))

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the exact functor `f₀!`
preserves mixed upper weight bounds (blueprint: `lemma-finite-quasi-finite-direct-images`,
`lemma-finite-quasi-finite-direct-images`, part 2). -/
theorem WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite {w : ℝ}
    {F : WeilSheaf k₀ l X} (h : F.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).IsMixedOfWeightsAtMost ι w := by
  have := (WeilSheaf.isZero_higherLowerShriek_and_isMixedOfWeightsAtMost_of_quasiFinite f
    F).2 ι w h 0
  exact this.mono_weight (by simp)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The direct-image weight assertion holds for a separated quasi-finite morphism `f`: `Rʳf₀!`
vanishes for `r > 0`, and `f₀!` preserves mixed upper weight bounds
(blueprint: `lemma-finite-quasi-finite-direct-images`). -/
theorem HasDirectImageWeightBound.of_locallyQuasiFinite : HasDirectImageWeightBound k₀ ι f := by
  have := locallyOfFiniteType_over_of_isOver f (S := Spec (CommRingCat.of k₀))
  intro w F hF r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa using hF.higherLowerShriek_zero_of_quasiFinite f
  · exact WeilSheaf.isMixedOfWeightsAtMost_of_isZero
      (isZero_higherLowerShriek_of_quasiFinite f r hr F) _

end QuasiFinite

end AlgebraicGeometry
