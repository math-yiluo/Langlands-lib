/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Stratification of a sheaf on a relative affine line

A Weil sheaf on the relative affine line `𝔸¹_S`, punctually pure of weight `w`, is built by
finitely many open–closed decompositions of the source from pieces which are either separated
quasi-finite over `S`, or open in a relative affine line `𝔸¹_V` over an immersion `V ⟶ S`, with
surjective projection to `V`, and carry a lisse sheaf
(blueprint: `proposition-relative-affine-line--1`).

## Main definitions

- `AlgebraicGeometry.WeilSheaf.HasRelativeLineStratification`: a stratification of a Weil sheaf
  over `S` into quasi-finite pieces and pure lisse relative-line pieces, glued along open–closed
  decompositions.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification`: blueprint
  `proposition-relative-affine-line--1`.

## Proof

Noetherian induction on the closed subsets of `S`: for a nonempty reduced closed subscheme `T` of
`S`, choose an integral affine open `V` of `T`. The sheaf is lisse on a dense open `U` of the
integral scheme `𝔸¹_V` (`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`); the
complement of `U` lies in the zero locus of a nonzero polynomial `g`, and over the principal open
`W = D(b)` of its leading coefficient every fibre of `𝔸¹_W ⟶ W` meets `U`, while the complement
of `U` has finite fibres
(`AlgebraicGeometry.AffineSpace.exists_basicOpen_forall_exists_mem_and_finite`). So `𝔸¹_W` is the
union of the relative-line piece `U ∩ 𝔸¹_W` and of a quasi-finite closed piece. The induction
hypothesis applies to the reduced complement of `W` in `T`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

section Instances

variable {T X : Scheme.{u}} [T.Over (Spec (CommRingCat.of k₀))]

instance [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))] :
    LocallyOfFiniteType (𝔸(PUnit.{u + 1}; T) ↘ Spec (CommRingCat.of k₀)) := by
  rw [← CategoryTheory.comp_over (𝔸(PUnit.{u + 1}; T) ↘ T) (Spec (CommRingCat.of k₀))]
  infer_instance

instance (U : T.Opens) [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))] :
    LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
  rw [← CategoryTheory.comp_over U.ι (Spec (CommRingCat.of k₀))]
  infer_instance

/-- The base change `𝔸¹_X ⟶ 𝔸¹_T` of a morphism over `k₀` is a morphism over `k₀`. -/
instance [X.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ T) [f.IsOver (Spec (CommRingCat.of k₀))] :
    (AffineSpace.map PUnit.{u + 1} f).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
  rw [← CategoryTheory.comp_over (𝔸(PUnit.{u + 1}; T) ↘ T) (Spec (CommRingCat.of k₀)),
    ← CategoryTheory.comp_over (𝔸(PUnit.{u + 1}; X) ↘ X) (Spec (CommRingCat.of k₀)),
    AffineSpace.map_over_assoc, comp_over f]⟩

end Instances

namespace WeilSheaf

/-- A Weil sheaf punctually pure of weight `w` is mixed of weights at most `w`, through the
filtration of length one. -/
theorem IsPunctuallyPureOfWeight.isMixedOfWeightsAtMost_stratification {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} {w : ℝ} (hF : F.IsPunctuallyPureOfWeight ι w) :
    F.IsMixedOfWeightsAtMost ι w :=
  isMixedOfWeightsAtMost_iff_filtrationClosure.2
    (ObjectProperty.le_filtrationClosure (P := isPunctuallyPureOfWeightLE ι w) _
      ⟨w, le_rfl, hF⟩)

end WeilSheaf

section Stratification

variable (ι) (w : ℝ) {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))]

/-- A Weil sheaf `F` on a `k₀`-scheme `X` over `S` (through `h : X ⟶ S`) *has a relative-line
stratification with pure pieces of weight `w`* if it is built, by finitely many open–closed
decompositions `U ↪ X ↩ Z` of the source, from pieces of the following two kinds:

- `h` is separated and quasi-finite, and `F` is mixed of weights at most `w`;
- `h` factors as an open immersion `v : X ⟶ 𝔸¹_V` with surjective projection to `V`, followed by
  the projection `𝔸¹_V ⟶ V` and an immersion `c : V ⟶ S`, and `F` is lisse and punctually pure of
  weight `w`:

```
X --- v ---> 𝔸¹_V --- ↘ ---> V --- c ---> S
```

(blueprint: `proposition-relative-affine-line--1`, the finite stratifications of source and target
refined to open–closed filtrations). -/
inductive WeilSheaf.HasRelativeLineStratification :
    ∀ {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))], WeilSheaf k₀ l X → Prop
  /-- A separated quasi-finite piece. -/
  | quasiFinite {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated h] [LocallyQuasiFinite h]
      [LocallyOfFiniteType h] [QuasiCompact h] (F : WeilSheaf k₀ l X)
      (hF : F.IsMixedOfWeightsAtMost ι w) :
      WeilSheaf.HasRelativeLineStratification h F
  /-- A piece open in a relative affine line, carrying a lisse sheaf punctually pure of
  weight `w`. -/
  | affineLine {X V : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [V.Over (Spec (CommRingCat.of k₀))] [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] (v : X ⟶ 𝔸(PUnit.{u + 1}; V))
      [IsOpenImmersion v] [QuasiCompact v] [v.IsOver (Spec (CommRingCat.of k₀))]
      (hv : Surjective (v ≫ 𝔸(PUnit.{u + 1}; V) ↘ V)) (c : V ⟶ S) [IsImmersion c]
      [QuasiCompact c] [c.IsOver (Spec (CommRingCat.of k₀))] (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))] (hh : h = (v ≫ 𝔸(PUnit.{u + 1}; V) ↘ V) ≫ c)
      (F : WeilSheaf k₀ l X) (hF : F.IsLisse) (hpure : F.IsPunctuallyPureOfWeight ι w) :
      WeilSheaf.HasRelativeLineStratification h F
  /-- Gluing along an open immersion `j` and its closed complement `i`. -/
  | openClosed {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType
  (U ↘ Spec (CommRingCat.of k₀))]
      [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
      [Z.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
      (j : U ⟶ X)
      [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] (i : Z ⟶ X)
      [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
      (hij : IsCompl (Set.range j.base) (Set.range i.base)) (h : X ⟶ S)
      [h.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
      WeilSheaf.HasRelativeLineStratification (j ≫ h) ((WeilSheaf.upperStar j).obj F) →
      WeilSheaf.HasRelativeLineStratification (i ≫ h) ((WeilSheaf.upperStar i).obj F) →
      WeilSheaf.HasRelativeLineStratification h F

variable {ι w}

/-- A relative-line stratification over `h` is one over any morphism equal to `h`. -/
theorem WeilSheaf.HasRelativeLineStratification.of_eq {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {h h' : X ⟶ S} [h.IsOver (Spec (CommRingCat.of k₀))] [h'.IsOver (Spec (CommRingCat.of k₀))]
    (e : h = h') {F : WeilSheaf k₀ l X} (H : F.HasRelativeLineStratification ι w h) :
    F.HasRelativeLineStratification ι w h' := by
  subst e
  exact H

/-- A punctually pure sheaf on an empty scheme has a relative-line stratification: the empty
scheme is quasi-finite over `S`. -/
theorem WeilSheaf.HasRelativeLineStratification.of_isEmpty {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [IsEmpty X] (h : X ⟶ S) [h.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated h]
    [LocallyOfFiniteType h] [QuasiCompact h] {F : WeilSheaf k₀ l X}
    (hF : F.IsPunctuallyPureOfWeight ι w) : F.HasRelativeLineStratification ι w h :=
  have : LocallyQuasiFinite h :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.finite_empty.subset fun x _ ↦ isEmptyElim x
  .quasiFinite h F hF.isMixedOfWeightsAtMost_stratification
variable [IsSeparated (S ↘ Spec (CommRingCat.of k₀))]

/-- Let `W` be an affine open of a `k₀`-scheme `V`, with an immersion `c : W ⟶ S`, and `U` an open
of `𝔸¹_V` meeting every fibre over `W`, whose complement has finite fibres over `W`. If a pullback
`n^* G` of a sheaf punctually pure of weight `w` is lisse on `U`, then its restriction to `𝔸¹_W`
has a relative-line stratification over `S`: `𝔸¹_W` is the union of the relative-line piece
`U ∩ 𝔸¹_W` and of its quasi-finite closed complement. -/
theorem WeilSheaf.hasRelativeLineStratification_of_forall_exists_mem_and_finite
    {V B : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    (W : V.Opens) [IsAffine W] (c : W.toScheme ⟶ S) [IsImmersion c] [QuasiCompact c]
    [c.IsOver (Spec (CommRingCat.of k₀))] (U : 𝔸(PUnit.{u + 1}; V).Opens)
    (n : 𝔸(PUnit.{u + 1}; V) ⟶ B) (n' : 𝔸(PUnit.{u + 1}; W) ⟶ B)
    [n.IsOver (Spec (CommRingCat.of k₀))] [n'.IsOver (Spec (CommRingCat.of k₀))]
    (hn : AffineSpace.map PUnit.{u + 1} W.ι ≫ n = n') {G : WeilSheaf k₀ l B}
    (hG : G.IsPunctuallyPureOfWeight ι w)
    (hU : ((WeilSheaf.upperStar U.ι).obj ((WeilSheaf.upperStar n).obj G)).IsLisse)
    (hb : ∀ s ∈ W, (∃ x ∈ U, (𝔸(PUnit.{u + 1}; V) ↘ V) x = s) ∧
      {x | x ∉ U ∧ (𝔸(PUnit.{u + 1}; V) ↘ V) x = s}.Finite) :
    ((WeilSheaf.upperStar n').obj G).HasRelativeLineStratification ι w
      (𝔸(PUnit.{u + 1}; W) ↘ W ≫ c) := by
  obtain ⟨m, hm⟩ : ∃ m, AffineSpace.map PUnit.{u + 1} W.ι = m := ⟨_, rfl⟩
  have : IsOpenImmersion m := hm ▸ inferInstance
  have : m.IsOver (Spec (CommRingCat.of k₀)) := hm ▸ inferInstance
  have hmo : m ≫ 𝔸(PUnit.{u + 1}; V) ↘ V = 𝔸(PUnit.{u + 1}; W) ↘ W ≫ W.ι := by
    rw [← hm, AffineSpace.map_over]
  have := LocallyOfFiniteType.isLocallyNoetherian (𝔸(PUnit.{u + 1}; W) ↘ Spec (CommRingCat.of k₀))
  have : QuasiCompact (W.toScheme ↘ Spec (CommRingCat.of k₀)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have : IsSeparated (W.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c]; infer_instance
  have hW (s : W.toScheme) : W.ι s ∈ W := by simp
  -- the reduced closed complement of `m⁻¹ U`
  let C : Closeds 𝔸(PUnit.{u + 1}; W) := ⟨((m ⁻¹ᵁ U : 𝔸(PUnit.{u + 1}; W).Opens) :
    Set 𝔸(PUnit.{u + 1}; W))ᶜ, (m ⁻¹ᵁ U).isOpen.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨i ≫ 𝔸(PUnit.{u + 1}; W) ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]; infer_instance
  have hrange : Set.range i = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  refine .openClosed (k₀ := k₀) (l := l) (j := (m ⁻¹ᵁ U).ι) (i := i)
    (h := 𝔸(PUnit.{u + 1}; W) ↘ W ≫ c)
    (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl) _ ?_ ?_
  · -- the relative-line piece `m⁻¹ U`
    refine .affineLine (V := W.toScheme) (m ⁻¹ᵁ U).ι ?_ c _
      (by simp only [Category.assoc]) _ (hU.upperStar_opensι_preimage U m n n' (hm ▸ hn))
      ((hG.upperStar _).upperStar _)
    refine ⟨fun s ↦ ?_⟩
    obtain ⟨a, haU, has⟩ := (hb (W.ι s) (hW s)).1
    obtain ⟨y, rfl⟩ : a ∈ Set.range m := by
      rw [← hm, AffineSpace.range_map]
      exact ⟨s, has.symm⟩
    refine ⟨⟨y, haU⟩, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← has, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hmo]
    rfl
  · -- the quasi-finite piece
    have : LocallyQuasiFinite (i ≫ 𝔸(PUnit.{u + 1}; W) ↘ W) := by
      refine .of_finite_preimage_singleton _ fun s ↦ ?_
      refine (Set.Finite.preimage (f := fun z ↦ m (i z))
        (m.isOpenEmbedding.injective.comp i.isClosedEmbedding.injective).injOn
        (hb (W.ι s) (hW s)).2).subset ?_
      rintro z (hz : (i ≫ _) z = s)
      refine ⟨fun hzU ↦ (hrange ▸ ⟨z, rfl⟩ : i z ∈ (C : Set _)) hzU, ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hmo, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have : LocallyQuasiFinite (i ≫ 𝔸(PUnit.{u + 1}; W) ↘ W ≫ c) := by
      rw [← Category.assoc]; infer_instance
    exact .quasiFinite _ _ ((hG.upperStar _).upperStar _).isMixedOfWeightsAtMost_stratification

variable [QuasiCompact (S ↘ Spec (CommRingCat.of k₀))]

/-- **The generic step.** Let `c : T ⟶ S` be an immersion from a nonempty reduced `k₀`-scheme of
finite type, and `G` a Weil sheaf on `𝔸¹_T` punctually pure of weight `w`. There is a nonempty
open `W` of an open `V` of `T` such that the restriction of `G` to `𝔸¹_W` has a relative-line
stratification over `S`: over a suitable principal open `W` of an integral affine open `V`, the
lissity locus of `G` on `𝔸¹_V` meets every fibre, and its complement is quasi-finite. -/
theorem WeilSheaf.exists_hasRelativeLineStratification_affineSpace_map {T : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [IsReduced T] [Nonempty T] (c : T ⟶ S) [IsImmersion c] [QuasiCompact c]
    [c.IsOver (Spec (CommRingCat.of k₀))] {G : WeilSheaf k₀ l 𝔸(PUnit.{u + 1}; T)}
    (hG : G.IsPunctuallyPureOfWeight ι w) :
    ∃ (V : T.Opens) (W : V.toScheme.Opens), (W : Set V.toScheme).Nonempty ∧
      ((WeilSheaf.upperStar (AffineSpace.map PUnit.{u + 1} (W.ι ≫ V.ι))).obj
        G).HasRelativeLineStratification ι w (𝔸(PUnit.{u + 1}; W) ↘ W ≫ W.ι ≫ V.ι ≫ c) := by
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c]; infer_instance
  have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
  -- an integral affine open `V` of `T`
  obtain ⟨t⟩ := ‹Nonempty T›
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {t}
    isIrreducible_singleton
  obtain ⟨o, ho, ⟨x, hxo⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨V, hV, hxV, hVo⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⟨o, ho⟩) hxo
  have : IsAffine V := hV
  have : IrreducibleSpace V := Subtype.irreducibleSpace
    ⟨⟨x, hxV⟩, (hZ.1.2.open_subset V.isOpen fun y hy ↦ hoZ (hVo hy))⟩
  have : IsIntegral V := isIntegral_of_irreducibleSpace_of_isReduced _
  -- the lissity locus `U` on `𝔸¹_V`
  have : QuasiCompact (𝔸(PUnit.{u + 1}; V) ↘ Spec (CommRingCat.of k₀)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  obtain ⟨U, hUd, hUl⟩ := WeilSheaf.exists_dense_isLisse_upperStar
    ((WeilSheaf.upperStar (AffineSpace.map PUnit.{u + 1} V.ι)).obj G)
  have : Nonempty 𝔸(PUnit.{u + 1}; V) := by
    obtain ⟨a, -⟩ := (𝔸(PUnit.{u + 1}; V) ↘ V).surjective ⟨x, hxV⟩
    exact ⟨a⟩
  obtain ⟨b, hbne, hb⟩ :=
    AffineSpace.exists_basicOpen_forall_exists_mem_and_finite U hUd.nonempty
  have : IsAffine (V.toScheme.basicOpen b) := (isAffineOpen_top V.toScheme).basicOpen b
  exact ⟨V, V.toScheme.basicOpen b, hbne,
    hasRelativeLineStratification_of_forall_exists_mem_and_finite _ (_ ≫ V.ι ≫ c) U _ _
      (AffineSpace.map_comp _ _).symm hG hUl hb⟩
variable [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]

/-- The base change `𝔸¹_T ⟶ 𝔸¹_S` of a closed immersion is a closed immersion. -/
instance {T : Scheme.{u}} (c : T ⟶ S) [IsClosedImmersion c] :
    IsClosedImmersion (AffineSpace.map PUnit.{u + 1} c) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (AffineSpace.isPullback_map c).flip
    inferInstance

/-- **Noetherian induction.** For a reduced closed subscheme `T` of `S` and a Weil sheaf `G` on
`𝔸¹_T` punctually pure of weight `w`, `G` has a relative-line stratification over `S`: the
generic step (`WeilSheaf.exists_hasRelativeLineStratification_affineSpace_map`) treats the
relative affine line over a nonempty open `W` of `T`, and the induction hypothesis the one over
the reduced complement of `W`. -/
theorem WeilSheaf.hasRelativeLineStratification_of_isClosedImmersion (Z : Closeds S)
    (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))] [IsReduced T] (c : T ⟶ S)
    [IsClosedImmersion c] [c.IsOver (Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l 𝔸(PUnit.{u + 1}; T)) (hG : G.IsPunctuallyPureOfWeight ι w)
    (hcZ : Set.range c ⊆ Z) :
    G.HasRelativeLineStratification ι w (𝔸(PUnit.{u + 1}; T) ↘ T ≫ c) := by
  have := isNoetherian_of_locallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))
  induction Z using WellFoundedLT.induction generalizing T with
  | ind Z ih =>
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c]; infer_instance
  have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
  have := LocallyOfFiniteType.isLocallyNoetherian (𝔸(PUnit.{u + 1}; T) ↘ Spec (CommRingCat.of k₀))
  cases isEmpty_or_nonempty T
  · have : IsEmpty 𝔸(PUnit.{u + 1}; T) := ⟨fun x ↦ isEmptyElim ((𝔸(PUnit.{u + 1}; T) ↘ T) x)⟩
    exact .of_isEmpty _ hG
  obtain ⟨V, W, ⟨w₀, hw₀⟩, H⟩ := exists_hasRelativeLineStratification_affineSpace_map c hG
  -- the reduced closed complement `T'` of `W` in `T`
  let C : Closeds T := ⟨(Set.range (W.ι ≫ V.ι))ᶜ,
    (W.ι ≫ V.ι).isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨i ≫ T ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over i]; infer_instance
  have hrange : Set.range i = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let Z' : Closeds S := ⟨c '' C, c.isClosedEmbedding.isClosedMap _ C.isClosed⟩
  have hZ' : Z' < Z := by
    refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hcZ ⟨t, ht⟩) fun h ↦ ?_
    have : c ((W.ι ≫ V.ι) ⟨w₀, hw₀⟩) ∈ (Z' : Set S) := h ▸ hcZ ⟨_, rfl⟩
    obtain ⟨t, ht, hti⟩ := this
    exact ht (c.isClosedEmbedding.injective hti ▸ ⟨⟨w₀, hw₀⟩, rfl⟩)
  have H' := ih Z' hZ' _ (i ≫ c) _ ((hG.upperStar (AffineSpace.map PUnit.{u + 1} i)))
    (by rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]; exact subset_rfl)
  refine .openClosed (k₀ := k₀) (l := l) (j := AffineSpace.map PUnit.{u + 1} (W.ι ≫ V.ι))
    (i := AffineSpace.map PUnit.{u + 1} i) (h := 𝔸(PUnit.{u + 1}; T) ↘ T ≫ c) ?_ G
    (.of_eq (by simp only [AffineSpace.map_over_assoc, Category.assoc]) H)
    (.of_eq (by simp only [AffineSpace.map_over_assoc]) H')
  rw [AffineSpace.range_map, AffineSpace.range_map, hrange]
  exact isCompl_compl.preimage _

/-- Let `S` be a separated `k₀`-scheme of finite type and `F` a Weil sheaf on the relative affine
line `𝔸¹_S`, punctually `ι`-pure of weight `w`. Then `F` has a relative-line stratification over
`S` with pure pieces of weight `w`: there are finite stratifications of source and target, refined
to open–closed filtrations, such that each source stratum is either separated quasi-finite over
its target stratum, or open in its relative affine line with surjective projection and carries a
lisse restriction of `F` (blueprint: `proposition-relative-affine-line--1`).

Over an integral affine open `Spec B` of `S`, the complement of the lissity locus of `F` is cut
out by an ideal of `B[T]` containing a nonzero polynomial; over the principal open of its leading
coefficient it is finite, and its complement is open in the relative affine line with nonempty
fibres. Noetherian induction on `S` covers the rest. -/
theorem WeilSheaf.IsPunctuallyPureOfWeight.hasRelativeLineStratification {w : ℝ}
    {F : WeilSheaf k₀ l 𝔸(PUnit.{u + 1}; S)} (hF : F.IsPunctuallyPureOfWeight ι w) :
    F.HasRelativeLineStratification ι w (𝔸(PUnit.{u + 1}; S) ↘ S) := by
  -- `𝔸¹_S` is the union of the empty open and of the relative affine line over `S_red`
  let c := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds S)).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds S)).subscheme.Over
      (Spec (CommRingCat.of k₀)) := ⟨c ≫ S ↘ Spec (CommRingCat.of k₀)⟩
  have : c.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds S)).subscheme ↘
      Spec (CommRingCat.of k₀)) := by
    rw [← comp_over c]; infer_instance
  have H := hasRelativeLineStratification_of_isClosedImmersion ⊤ _ c _
    (hF.upperStar (AffineSpace.map PUnit.{u + 1} c)) (Set.subset_univ _)
  have : IsEmpty (⊥ : 𝔸(PUnit.{u + 1}; S).Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : 𝔸(PUnit.{u + 1}; S).Opens).ι := inferInstance
  refine .openClosed (k₀ := k₀) (l := l) (j := (⊥ : 𝔸(PUnit.{u + 1}; S).Opens).ι)
    (i := AffineSpace.map PUnit.{u + 1} c) (h := 𝔸(PUnit.{u + 1}; S) ↘ S) ?_ F
    (.of_isEmpty _ (hF.upperStar _)) (.of_eq (AffineSpace.map_over c).symm H)
  rw [Scheme.Opens.range_ι, AffineSpace.range_map, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact isCompl_bot_top

end Stratification

end AlgebraicGeometry
