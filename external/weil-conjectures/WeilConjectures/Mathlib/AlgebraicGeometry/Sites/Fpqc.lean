/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Points of fppf coverings

A covering sieve of the fppf topology is jointly surjective, through flat morphisms locally of
finite presentation: every point of the base lies in the image of such a morphism of the sieve.
We record this for the fppf topology on `Scheme` and for its localization to `Over S`.

# Descent of properties of morphisms along fpqc coverings

A property of morphisms which is local at the target and descends along faithfully flat
quasi-compact morphisms descends along every covering sieve of the fpqc topology
(`AlgebraicGeometry.Scheme.of_isPullback_of_mem_fpqcTopology`).

Over an affine scheme, a covering sieve of the fpqc topology is refined by a finite covering
family of flat morphisms from affine schemes
(`AlgebraicGeometry.Scheme.exists_finite_affine_flat_of_mem_fpqcTopology`). Likewise an fppf
covering family of an affine scheme is refined by a finite fppf covering family of affine opens
of its members (`AlgebraicGeometry.Scheme.exists_finite_fppf_affine_open_refinement`).

# Single-morphism coverings over a base

A flat, surjective, quasi-compact morphism over `S` generates an fpqc covering sieve of `Over S`
(`AlgebraicGeometry.Scheme.singleton_mem_over_fpqcTopology`), and similarly for the fppf topology.
A presheaf on `Over S` whose restriction along `Over.map g` is an fpqc sheaf satisfies the sheaf
condition for such morphisms between objects over `S'`
(`AlgebraicGeometry.Scheme.isSheafFor_singleton_of_isSheaf_overMap`).

# The structure sheaf is a sheaf for subcanonical topologies

The étale topology is coarser than the fppf topology, hence subcanonical. For every
subcanonical topology on `Scheme`, for instance the fpqc, fppf and étale topologies, the global
sections functor `Γ` is a sheaf (`AlgebraicGeometry.Scheme.isSheaf_Γ`): for a ring `R`, the
presheaf `U ↦ (R ⟶ Γ(U, 𝒪_U))` is represented by `Spec R`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A covering sieve of the fppf topology on a scheme `X` is jointly surjective through flat
morphisms locally of finite presentation: every point of `X` is in the image of some flat
morphism locally of finite presentation `g : Y ⟶ X` of the sieve. -/
lemma exists_flat_mem_of_mem_fppfTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ fppfTopology X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g.base := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)), inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : fppfPrecoverage.{u}.HasIsos := by unfold fppfPrecoverage; infer_instance
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨hR₁, hR₂⟩, hle⟩ := hS
  obtain ⟨_, _, h, hx⟩ := hR₁ x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, (hR₂ hg).1, (hR₂ hg).2, hx⟩

/-- A covering sieve of the fppf topology on `Over S` is jointly surjective through morphisms
whose underlying morphism of schemes is flat and locally of finite presentation. -/
lemma exists_flat_mem_of_mem_fppfTopology_over {S : Scheme.{u}} {T : Over S} {R : Sieve T}
    (hR : R ∈ fppfTopology.over S T) (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T), R g ∧ Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      t ∈ Set.range g.left.base := by
  obtain ⟨Y, g, ⟨Z, h, k, hh, rfl⟩, hg₁, hg₂, hx⟩ :=
    exists_flat_mem_of_mem_fppfTopology ((GrothendieckTopology.mem_over_iff _ _).1 hR) t
  refine ⟨Over.mk (k ≫ Z.hom), Over.homMk k ≫ h, R.downward_closed hh _, ?_, ?_, ?_⟩
  all_goals simpa using ‹_›

section Descent

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine case of `AlgebraicGeometry.Scheme.of_isPullback_of_mem_fpqcTopology`. -/
private lemma of_isPullback_of_mem_fpqcTopology_of_isAffine {T Z : Scheme.{u}} [IsAffine T]
    {S : Sieve T} (hS : S ∈ fpqcTopology T) (f : Z ⟶ T)
    (H : ∀ ⦃Y W : Scheme.{u}⦄ (h : Y ⟶ T) (a : W ⟶ Z) (b : W ⟶ Y), S h →
      IsPullback a b f h → P b) : P f := by
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨𝒰, _, rfl⟩ := mem_propQCPrecoverage_iff_exists_quasiCompactCover.mp hR
  obtain ⟨𝒱, φ, _, -⟩ := QuasiCompactCover.exists_hom 𝒰
  have : Small.{u} 𝒱.cover.I₀ := Countable.toSmall (α := 𝒱.I₀)
  let p : ∐ 𝒱.cover.X ⟶ T := Sigma.desc 𝒱.cover.f
  have hflat : Flat p := by
    have : ∀ j, Flat (𝒱.cover.f j) := 𝒱.map_prop
    infer_instance
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have : IsAffine (∐ 𝒱.cover.X) := inferInstance
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) p :=
    ⟨⟨Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range, hflat⟩, inferInstance⟩
  refine MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) hp ?_
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (sigmaOpenCover _)]
  intro j
  have hsq := (IsPullback.of_hasPullback (pullback.fst p f) (Sigma.ι 𝒱.cover.X j)).paste_horiz
    (IsPullback.of_hasPullback p f).flip
  have hj : Sigma.ι 𝒱.cover.X j ≫ p = 𝒱.cover.f j := Sigma.ι_comp_desc _ _
  rw [hj] at hsq
  refine H _ _ _ ?_ hsq
  rw [← φ.w₀ j]
  exact S.downward_closed (hle _ _ (𝒰.toPreZeroHypercover.presieve₀_f (φ.s₀ j))) _

set_option backward.isDefEq.respectTransparency.types false in
/-- **Descent of properties of morphisms along fpqc coverings.** Let `P` be a property of
morphisms of schemes which is local at the target and descends along faithfully flat
quasi-compact morphisms. If every base change of `f : Z ⟶ T` along a morphism of an fpqc
covering sieve of `T` has `P`, then `f` has `P`. -/
lemma of_isPullback_of_mem_fpqcTopology {T Z : Scheme.{u}} {S : Sieve T}
    (hS : S ∈ fpqcTopology T) (f : Z ⟶ T)
    (H : ∀ ⦃Y W : Scheme.{u}⦄ (h : Y ⟶ T) (a : W ⟶ Z) (b : W ⟶ Y), S h →
      IsPullback a b f h → P b) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover T.affineCover fun i ↦ ?_
  refine of_isPullback_of_mem_fpqcTopology_of_isAffine
    (fpqcTopology.pullback_stable (T.affineCover.f i) hS) _ fun Y W h a b hh hab ↦ ?_
  exact H _ _ _ hh (hab.paste_horiz (IsPullback.of_hasPullback f (T.affineCover.f i)))

set_option backward.isDefEq.respectTransparency.types false in
/-- **Descent of properties of morphisms along fpqc coverings**, for a covering family
`{g i : T' i ⟶ T}`: if `P` is moreover stable under base change and the base changes `b i` of
`f` along the `g i` have `P`, then `f` has `P`.
(blueprint: `lem-weil-pbc-fpqc-family-descent-of-single-morphism-descent`) -/
lemma of_isPullback_of_ofArrows_mem_fpqcTopology [P.IsStableUnderBaseChange] {T Z : Scheme.{u}}
    {ι : Type*} {T' : ι → Scheme.{u}} {g : ∀ i, T' i ⟶ T}
    (hg : Sieve.ofArrows T' g ∈ fpqcTopology T) (f : Z ⟶ T) {Z' : ι → Scheme.{u}}
    (a : ∀ i, Z' i ⟶ Z) (b : ∀ i, Z' i ⟶ T' i) (hab : ∀ i, IsPullback (a i) (b i) f (g i))
    (H : ∀ i, P (b i)) : P f := by
  refine of_isPullback_of_mem_fpqcTopology hg f fun Y W h a' b' hh hpb ↦ ?_
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hh
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_right' hpb (hab i)) (H i)

end Descent

/-- A covering sieve of the fpqc topology on a scheme `X` is jointly surjective: every point of
`X` is in the image of some morphism of the sieve. -/
lemma exists_mem_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X} (hS : S ∈ fpqcTopology X)
    (x : X) : ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x ∈ Set.range g.base := by
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨-, hR, -⟩, hle⟩ := hS
  obtain ⟨_, g, h, hx⟩ := hR x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, hx⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A covering sieve of the fpqc topology on an affine scheme `V` contains a finite family of flat
morphisms from affine schemes which itself generates a covering sieve. -/
lemma exists_finite_affine_flat_of_mem_fpqcTopology {V : Scheme.{u}} [IsAffine V] {S : Sieve V}
    (hS : S ∈ fpqcTopology V) :
    ∃ (κ : Type u) (W : κ → Scheme.{u}) (f : ∀ j, W j ⟶ V), Finite κ ∧ (∀ j, IsAffine (W j)) ∧
      (∀ j, Flat (f j)) ∧ (∀ j, S (f j)) ∧ Sieve.ofArrows W f ∈ fpqcTopology V := by
  have hS' := hS
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS'
  obtain ⟨R, hR, hle⟩ := hS'
  obtain ⟨𝒰, _, rfl⟩ := mem_propQCPrecoverage_iff_exists_quasiCompactCover.mp hR
  obtain ⟨𝒱, φ, _, -⟩ : ∃ (𝒱 : Scheme.AffineCover.{u} @Flat V) (φ : 𝒱.cover ⟶ 𝒰.qculift),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (φ.h₀ j) := QuasiCompactCover.exists_hom _
  have h𝒰 (k : 𝒰.qculift.I₀) : 𝒰.presieve₀ (𝒰.qculift.f k) := by
    rcases k with k | k
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  refine ⟨𝒱.cover.I₀, 𝒱.cover.X, 𝒱.cover.f, inferInstance, fun j ↦ inferInstanceAs
    (IsAffine (Spec _)), fun j ↦ 𝒱.map_prop j, fun j ↦ ?_, Cover.mem_propQCTopology 𝒱.cover⟩
  rw [← φ.w₀ j]
  exact S.downward_closed (hle _ _ (h𝒰 _)) _

/-- An fppf covering family of an affine scheme `U` is refined by a finite fppf covering family
consisting of affine opens of its members. Source: Stacks Project, Topologies, Lemma 34.7.4
(Tag 021P).

Every point of `U` lies in the image of an affine open of some member. The composite of the
inclusion of such an affine open with the original morphism is flat and locally of finite
presentation, so its image is open; quasi-compactness of `U` selects finitely many of them. -/
theorem exists_finite_fppf_affine_open_refinement {U : Scheme.{u}} [IsAffine U]
    {I : Type v} (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ U)
    (hf : Presieve.ofArrows T f ∈ fppfPrecoverage U) :
    ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (T (i j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
        Presieve.ofArrows (fun j ↦ (V j).toScheme)
          (fun j ↦ (V j).ι ≫ f (i j)) ∈ fppfPrecoverage U := by
  rw [fppfPrecoverage, ofArrows_mem_precoverage_iff] at hf
  obtain ⟨hsurj, hP⟩ := hf
  choose i t ht using hsurj
  choose W hW htW _ using fun x ↦
    exists_isAffineOpen_mem_and_subset (x := t x) (U := ⊤) trivial
  have hP' (x : U) :
      Flat ((W x).ι ≫ f (i x)) ∧ LocallyOfFinitePresentation ((W x).ι ≫ f (i x)) := by
    obtain ⟨_, _⟩ := hP (i x)
    exact ⟨inferInstance, inferInstance⟩
  have hopen (x : U) : IsOpen (Set.range ((W x).ι ≫ f (i x))) := by
    obtain ⟨_, _⟩ := hP' x
    exact ((W x).ι ≫ f (i x)).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hopen fun x _ ↦
    Set.mem_iUnion.2 ⟨x, ⟨t x, htW x⟩, by simpa using ht x⟩
  refine ⟨s.card, fun j ↦ i (s.equivFin.symm j), fun j ↦ W _, fun j ↦ hW _, ?_⟩
  rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun j ↦ hP' _⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  obtain ⟨j, rfl⟩ : ∃ j, (s.equivFin.symm j : U) = y := ⟨s.equivFin ⟨y, hy⟩, by simp⟩
  exact ⟨j, hxy⟩

/-- A covering sieve of the fppf topology on an affine scheme `U` contains a finite fppf covering
family of morphisms from affine schemes. -/
lemma exists_finite_affine_of_mem_fppfTopology {U : Scheme.{u}} [IsAffine U] {S : Sieve U}
    (hS : S ∈ fppfTopology U) :
    ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (g : ∀ j, V j ⟶ U), (∀ j, IsAffine (V j)) ∧
      (∀ j, S (g j)) ∧ Presieve.ofArrows V g ∈ fppfPrecoverage U := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)), inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : fppfPrecoverage.{u}.HasIsos := by unfold fppfPrecoverage; infer_instance
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨ι, T, f, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨n, i, V, hV, hmem⟩ := exists_finite_fppf_affine_open_refinement T f hR
  exact ⟨n, _, _, fun j ↦ hV j, fun j ↦ S.downward_closed (hle _ _ ⟨i j⟩) _, hmem⟩

/-- A single flat, surjective, quasi-compact morphism `φ : Y₁ ⟶ Y` over `S` generates a covering
sieve of the fpqc topology on `Over S`. -/
lemma singleton_mem_over_fpqcTopology {S : Scheme.{u}} {Y Y₁ : Over S} (φ : Y₁ ⟶ Y)
    [Flat φ.left] [Surjective φ.left] [QuasiCompact φ.left] :
    Sieve.generate (.singleton φ) ∈ (fpqcTopology.over S) Y := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv Y (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Presieve.ofArrows_pUnit]
  exact φ.left.singleton_mem_fpqcPrecoverage

/-- A single flat, surjective morphism `φ : Y₁ ⟶ Y` over `S`, locally of finite presentation,
generates a covering sieve of the fppf topology on `Over S`. -/
lemma singleton_mem_over_fppfTopology {S : Scheme.{u}} {Y Y₁ : Over S} (φ : Y₁ ⟶ Y)
    [Flat φ.left] [Surjective φ.left] [LocallyOfFinitePresentation φ.left] :
    Sieve.generate (.singleton φ) ∈ (fppfTopology.over S) Y := by
  rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0}]
  change Sieve.overEquiv Y (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Presieve.ofArrows_pUnit]
  exact φ.left.singleton_mem_fppfPrecoverage

/-- Let `g : S' ⟶ S` be a morphism of schemes and `G` a presheaf on `Over S` whose restriction
along `Over.map g` is an fpqc sheaf. Then `G` satisfies the sheaf condition for every flat,
surjective, quasi-compact morphism `φ : Y₁ ⟶ Y` over `S` whose target factors through `g` by some
`a : Y ⟶ S'`:
```
  Y₁ --φ--> Y --a--> S'
             \       |
              \      g
               \     v
                ---> S
```
Indeed `φ` is the image under `Over.map g` of the covering `φ : (Y₁, φ ≫ a) ⟶ (Y, a)` of the fpqc
site of `S'`. -/
lemma isSheafFor_singleton_of_isSheaf_overMap {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : (Over S)ᵒᵖ ⥤ Type*} (hG : Presheaf.IsSheaf (fpqcTopology.over S') ((Over.map g).op ⋙ G))
    {Y Y₁ : Over S} (φ : Y₁ ⟶ Y) [Flat φ.left] [Surjective φ.left] [QuasiCompact φ.left]
    (a : Y.left ⟶ S') (ha : a ≫ g = Y.hom) :
    Presieve.IsSheafFor G (.singleton φ) := by
  let φ' : Over.mk (φ.left ≫ a) ⟶ Over.mk a := Over.homMk φ.left
  have : Flat φ'.left := ‹Flat φ.left›
  have : Surjective φ'.left := ‹Surjective φ.left›
  have : QuasiCompact φ'.left := ‹QuasiCompact φ.left›
  have h' := ((isSheaf_iff_isSheaf_of_type _ _).1 hG).isSheafFor _
    (singleton_mem_over_fpqcTopology φ')
  rw [Presieve.isSheafFor_singleton] at h'
  -- `Y` and `Y₁` are the images of `(Y, a)` and `(Y₁, φ ≫ a)` under `Over.map g`
  let eY : (Over.map g).obj (Over.mk a) ≅ Y := Over.isoMk (Iso.refl _) (by simp [ha])
  let eY₁ : (Over.map g).obj (Over.mk (φ.left ≫ a)) ≅ Y₁ :=
    Over.isoMk (Iso.refl _) (by simp [ha, Over.w φ])
  have hsq : (Over.map g).map φ' ≫ eY.hom = eY₁.hom ≫ φ := by
    ext
    simp [eY, eY₁, φ']
  have hcomp {A B C : Over S} (f : A ⟶ B) (h : B ⟶ C) (z : G.obj (.op C)) :
      G.map f.op (G.map h.op z) = G.map (f ≫ h).op z := by
    simp
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  obtain ⟨y', hy', huniq⟩ := h' (G.map eY₁.hom.op x) fun {Z} p₁ p₂ hp ↦ by
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]
    rw [hcomp, hcomp]
    refine hx _ _ ?_
    rw [Category.assoc, Category.assoc, ← hsq, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      hp]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hy' huniq
  have h₁ : φ ≫ eY.inv = eY₁.inv ≫ (Over.map g).map φ' := by
    rw [Iso.comp_inv_eq, Category.assoc, hsq, Iso.inv_hom_id_assoc]
  refine ⟨G.map eY.inv.op y', ?_, fun z hz ↦ ?_⟩
  · beta_reduce
    rw [hcomp, h₁, ← hcomp, hy', hcomp, Iso.inv_hom_id, op_id, Functor.map_id_apply]
  · have := huniq (G.map eY.hom.op z) (by rw [hcomp, hsq, ← hcomp, hz])
    rw [← this, hcomp, Iso.inv_hom_id, op_id, Functor.map_id_apply]

/-- Étale coverings are fppf coverings. -/
lemma etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono
    (precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)

/-- **Zariski coverings are fppf coverings.** A family of open immersions covering a scheme `T` is
an fppf covering of `T`: open immersions are flat and locally of finite presentation (on the level
of covering families this is Mathlib's `zariskiPrecoverage_le_fppfPrecoverage`), so every Zariski
covering sieve is an fppf covering sieve.

(blueprint: `lem-pc-zariski-coverings-are-fppf`) -/
lemma zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

instance : etaleTopology.{u}.Subcanonical :=
  .of_le etaleTopology_le_fppfTopology

/-- The global sections functor `Γ` is a sheaf for every subcanonical topology on `Scheme`:
for a ring `R`, the presheaf `U ↦ (R ⟶ Γ(U, 𝒪_U))` is represented by `Spec R`. -/
lemma isSheaf_Γ (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf J Scheme.Γ := fun R ↦
  have := (ΓSpec.representableBy R).isRepresentable
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

end AlgebraicGeometry.Scheme
