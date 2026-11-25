/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Simple
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Simple constructible sheaves

Let `X` be a scheme whose underlying space is Noetherian and `Λ` a Noetherian ring. This file
classifies the simple objects of the abelian category of constructible sheaves of `Λ`-modules on
the small étale site of `X` (blueprint `lem-trf-simple-constructible`): they are the sheaves
`i_{x!} M`, where `x` is a point with `{x}` locally closed, `i_{x!}` is the extension by zero
along `Spec κ(x) ⟶ X`, and `M` is a simple constructible sheaf on `Spec κ(x)`, that is a simple
finite `Λ`-module with a continuous action of the absolute Galois group of `κ(x)`. On a scheme
of finite type over a field the point `x` is closed and `i_{x!} = i_{x*}`. In particular a nonzero
locally constant sheaf on a connected scheme of positive dimension, of finite type over a field,
is not a finite extension of simple constructible sheaves.

Supports are measured by `AlgebraicGeometry.Etale.stalkZeroLocus`, the set of points at all of
whose geometric points the stalks vanish; the stalks of a locally constant sheaf vanish on a
clopen set (`AlgebraicGeometry.Etale.isClopen_stalkZeroLocus`).

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_openImmersionLowerShriek_lowerStar_of_simple`: a simple
  constructible sheaf is `i_{x!} M` for a locally closed point `x` and a simple `M`.
- `AlgebraicGeometry.Etale.simple_openImmersionLowerShriek_lowerStar`: conversely each such
  `i_{x!} M` is simple.
- `AlgebraicGeometry.Etale.exists_iso_lowerStar_fromSpecResidueField_of_simple`: over a field,
  `x` is a closed point and `F ≅ i_{x*} M`.
- `AlgebraicGeometry.Etale.not_forall_prop_of_isLocallyConstantSheaf`: a nonzero locally constant
  sheaf on a connected scheme of positive dimension of finite type over a field is not a finite
  extension of simple constructible sheaves.

## Implementation notes

"Simple object of the abelian category of constructible sheaves" is Mathlib's `Simple` for the
full subcategory `(Etale.constructibleSheaf (ModuleCat Λ) X).FullSubcategory`; by `simple_iff`,
since constructible sheaves are closed under kernels, it says that the sheaf is nonzero and that
its constructible subsheaves are zero or everything. The extension by zero `i_{x!}` along the
immersion `Spec κ(x) ⟶ X` is written as `j_! g_*` for an open `j : W ⟶ X` in which `x` is closed
and the closed immersion `g : Spec κ(x) ⟶ W`
(`AlgebraicGeometry.exists_isClosedImmersion_comp_ι_eq_fromSpecResidueField`).
"Finite extension of simple sheaves" is spelled through the universal property of the closure
under extensions.
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X Y : Scheme.{u}}

/-- The stalks of a zero sheaf vanish. -/
lemma isZero_sheafFiber_of_isZero {I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hI : IsZero I) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsZero ((pointSmallEtale s).sheafFiber.obj I) :=
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  (pointSmallEtale s).sheafFiber.map_isZero hI

/-- A sheaf of modules is zero exactly when its stalks vanish everywhere: the geometric points
form a conservative family. -/
lemma isZero_iff_stalkZeroLocus_eq_univ (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero I ↔ stalkZeroLocus I = Set.univ := by
  refine ⟨fun hI ↦ Set.eq_univ_of_forall fun x Ω _ _ s _ ↦ isZero_sheafFiber_of_isZero hI s,
    fun hall ↦ ?_⟩
  have : IsIso (0 : I ⟶ I) := isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj I) :=
      ((hall ▸ Set.mem_univ x : x ∈ stalkZeroLocus I) _ (X.algClosurePoint x)
        (X.algClosurePoint_base x _)).of_iso
        (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app I)
    exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : I ⟶ I), zero_comp]

/-- The stalks of a pullback `f^* I` at the geometric points over `y` are those of `I` at the
geometric points over `f y`. -/
lemma mem_stalkZeroLocus_upperStar (f : Y ⟶ X)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {y : Y}
    (hy : f.base y ∈ stalkZeroLocus I) :
    y ∈ stalkZeroLocus (((f)^*[ModuleCat.{u + 1} Λ]).obj I) := fun Ω _ _ s hs ↦
  (hy Ω (s ≫ f) (by rw [← hs]; rfl)).of_iso
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f s).app I)

/-- Conversely, along an immersion `f`, every geometric point over `f y` lifts to `Y`, so the
stalks of `I` vanish over `f y` when those of `f^* I` vanish over `y`. -/
lemma mem_stalkZeroLocus_of_upperStar (f : Y ⟶ X) [IsImmersion f]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {y : Y}
    (hy : y ∈ stalkZeroLocus (((f)^*[ModuleCat.{u + 1} Λ]).obj I)) :
    f.base y ∈ stalkZeroLocus I := by
  intro Ω _ _ s hs
  have h₁ : Set.range s.base ⊆ Set.range f.coborderRange.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint Ω), hs]
    exact ⟨f.liftCoborder.base y, by rw [← Scheme.Hom.comp_apply, f.liftCoborder_ι]⟩
  set s' := IsOpenImmersion.lift f.coborderRange.ι s h₁
  have hs' : s' ≫ f.coborderRange.ι = s := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨t, ht, -⟩ := IsClosedImmersion.existsUnique_fac_of_field f.liftCoborder s' (by
    refine ⟨y, f.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, f.liftCoborder_ι, ← hs, ← hs']
    rfl)
  have htf : t ≫ f = s := by rw [← f.liftCoborder_ι, ← Category.assoc, ht, hs']
  subst htf
  refine (hy Ω t ?_).of_iso ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f t).app I).symm
  exact f.isEmbedding.injective hs

/-- The range of the closed complement of an open subscheme `W` is the complement of `W`. -/
lemma range_closedComplement_eq_compl_range_ι (W : X.Opens) :
    Set.range W.closedComplement.base = (Set.range W.ι.base)ᶜ := by
  rw [W.range_closedComplement, Scheme.Opens.range_ι]

/-- A constructible sheaf all of whose constructible subsheaves are zero or everything is
supported either inside or outside a given open. -/
lemma subset_stalkZeroLocus_or_compl_subset
    [TopologicalSpace.NoetherianSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (hF : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : G ⟶ F), Mono ι →
      IsConstructibleSheaf G → IsZero G ∨ IsIso ι) (W : X.Opens) :
    (W : Set X) ⊆ stalkZeroLocus F ∨ (W : Set X)ᶜ ⊆ stalkZeroLocus F := by
  have hij := range_closedComplement_eq_compl_range_ι W
  have hS :=
    Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) W.ι W.closedComplement F hij
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsConstructibleSheaf (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    IsConstructibleSheaf.upperStar _ _
  have := IsConstructibleSheaf.openImmersionLowerShriek W.ι W.closedComplement hij
    (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)
  rcases hF _ _ hS.mono_f this with h | h
  · left
    intro x hx
    have hz : IsZero (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      (((W.ι)^*[ModuleCat.{u + 1} Λ]).map_isZero h).of_iso
        (asIso (((W.ι)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).counit.app F))).symm
    have := mem_stalkZeroLocus_of_upperStar W.ι F (y := ⟨x, hx⟩)
      ((isZero_iff_stalkZeroLocus_eq_univ _).1 hz ▸ Set.mem_univ _)
    exact this
  · right
    intro x hx
    have h₃ : IsZero ((W.closedComplement)_*[ModuleCat.{u + 1} Λ].obj
        (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj F)) := hS.isIso_f_iff.1 h
    have hz : IsZero (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj F) :=
      (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).map_isZero h₃).of_iso
        (asIso ((Etale.upperStarLowerStarAdjunction _ W.closedComplement).counit.app _)).symm
    obtain ⟨z, rfl⟩ : x ∈ Set.range W.closedComplement.base := by
      rw [hij, Scheme.Opens.range_ι]; exact hx
    exact mem_stalkZeroLocus_of_upperStar W.closedComplement F
      ((isZero_iff_stalkZeroLocus_eq_univ _).1 hz ▸ Set.mem_univ _)

/-- A nonzero constructible sheaf all of whose constructible subsheaves are zero or everything
is supported at a single point. -/
lemma exists_compl_stalkZeroLocus_eq_singleton
    [TopologicalSpace.NoetherianSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF₀ : ¬ IsZero F)
    (hF : ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : G ⟶ F), Mono ι →
      IsConstructibleSheaf G → IsZero G ∨ IsIso ι) :
    ∃ x : X, (stalkZeroLocus F)ᶜ = {x} := by
  obtain ⟨x, hx⟩ : ((stalkZeroLocus F)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact fun h ↦ hF₀ ((isZero_iff_stalkZeroLocus_eq_univ F).2 h)
  refine ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy ↦ ?_⟩⟩
  by_contra hxy
  obtain ⟨U, hU, hUxy⟩ := exists_isOpen_xor_mem hxy
  rcases subset_stalkZeroLocus_or_compl_subset F hF ⟨U, hU⟩ with h | h <;>
    rcases hUxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hy (h h₁)
  · exact hx (h h₁)
  · exact hx (h h₂)
  · exact hy (h h₂)

/-- If a constructible sheaf is supported at a single point `x`, then `{x}` is locally closed:
on the stratum through `x` the sheaf is locally constant, so its support there is open. -/
lemma isLocallyClosed_singleton_of_compl_stalkZeroLocus_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] {x : X}
    (hx : (stalkZeroLocus F)ᶜ = {x}) : IsLocallyClosed ({x} : Set X) := by
  obtain ⟨str, hstr⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (str.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
  set h := str.immersion i
  have := hstr i
  have hpre : stalkZeroLocus (((h)^*[ModuleCat.{u + 1} Λ]).obj F) =
      h.base ⁻¹' stalkZeroLocus F :=
    Set.ext fun _ ↦ ⟨mem_stalkZeroLocus_of_upperStar h F, mem_stalkZeroLocus_upperStar h F⟩
  have hopen : IsOpen (h.base ⁻¹' {x}) := by
    rw [← hx, Set.preimage_compl, ← hpre]
    exact (isClopen_stalkZeroLocus _).isClosed.isOpen_compl
  obtain ⟨V, hV, hVpre⟩ := h.isEmbedding.isInducing.isOpen_iff.1 hopen
  rw [← str.range_immersion i] at hi
  obtain ⟨d, hd⟩ := hi
  have : ({x} : Set X) = V ∩ Set.range h.base := by
    refine Set.ext fun z ↦ ⟨?_, ?_⟩
    · rintro rfl
      refine ⟨?_, d, hd⟩
      have : d ∈ h.base ⁻¹' V := by rw [hVpre]; exact hd
      rwa [Set.mem_preimage, hd] at this
    · rintro ⟨hzV, e, rfl⟩
      have : e ∈ h.base ⁻¹' V := hzV
      rwa [hVpre] at this
  rw [this]
  exact hV.isLocallyClosed.inter h.isLocallyClosed_range

/-- A sheaf whose stalks vanish off an open `W` is the extension by zero of its restriction
to `W`: the counit `j_! j^* F ⟶ F` of `j_! ⊣ j^*` is an isomorphism. -/
lemma isIso_counit_app_of_compl_subset_stalkZeroLocus
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (W : X.Opens)
    (hF : (W : Set X)ᶜ ⊆ stalkZeroLocus F) :
    IsIso ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).counit.app F) := by
  have hij := range_closedComplement_eq_compl_range_ι W
  let S := Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) W.ι W.closedComplement
    (disjoint_range_of_range_eq_compl _ _ hij) F
  have hS : S.ShortExact :=
    Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) W.ι W.closedComplement F hij
  have hZ : IsZero (((W.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj F) := by
    refine (isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun z ↦ ?_)
    refine mem_stalkZeroLocus_upperStar _ _ (hF ?_)
    have : W.closedComplement.base z ∈ (Set.range W.ι.base)ᶜ := hij ▸ ⟨z, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  exact hS.isIso_f_iff.2 (((W.closedComplement)_*[ModuleCat.{u + 1} Λ]).map_isZero hZ)

/-- A sheaf whose stalks vanish off the range of a closed immersion `g` is the direct image of
its restriction: the unit `G ⟶ g_* g^* G` of `g^* ⊣ g_*` is an isomorphism. -/
lemma isIso_unit_app_of_compl_subset_stalkZeroLocus {Z : Scheme.{u}} (g : Z ⟶ Y)
    [IsClosedImmersion g] (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : (Set.range g.base)ᶜ ⊆ stalkZeroLocus G) :
    IsIso ((Etale.upperStarLowerStarAdjunction _ g).unit.app G) := by
  let W' := openComplementOfIsClosedImmersion g
  have hij' : Set.range g.base = (Set.range W'.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm
  let S' := Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) W'.ι g
    (disjoint_range_of_range_eq_compl _ _ hij') G
  have hS' : S'.ShortExact :=
    Etale.shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) W'.ι g G hij'
  have hZ' : IsZero (((W'.ι)^*[ModuleCat.{u + 1} Λ]).obj G) := by
    refine (isZero_iff_stalkZeroLocus_eq_univ _).2 (Set.eq_univ_of_forall fun w ↦ ?_)
    refine mem_stalkZeroLocus_upperStar _ _ (hG ?_)
    have : W'.ι.base w ∈ (Set.range W'.ι.base) := ⟨w, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  exact hS'.isIso_g_iff.2 (((W'.ι)_!open[ModuleCat.{u + 1} Λ]).map_isZero hZ')

/-- If `g : Spec κ(x) ⟶ W` is a closed immersion with `g ≫ W.ι = Spec κ(x) ⟶ X`, then the
points of `W` mapping to `x` are those of the range of `g`. -/
lemma mem_range_of_ι_eq {x : X} (W : X.Opens) (g : Spec (X.residueField x) ⟶ W)
    (hg : g ≫ W.ι = X.fromSpecResidueField x) {w : W} (hw : W.ι.base w = x) :
    w ∈ Set.range g.base := by
  obtain ⟨p, hp⟩ : x ∈ Set.range (X.fromSpecResidueField x).base := by
    rw [Scheme.range_fromSpecResidueField]; rfl
  refine ⟨p, W.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, hg, hp, hw]

/-- A sheaf supported at a point `x`, closed in an open `W`, is the extension by zero along
`W ⟶ X` of the direct image of its restriction to `x`. -/
lemma isIso_of_compl_stalkZeroLocus_subset
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {x : X}
    (hx : (stalkZeroLocus F)ᶜ ⊆ {x}) (W : X.Opens) (hxW : x ∈ W)
    (g : Spec (X.residueField x) ⟶ W) [IsClosedImmersion g]
    (hg : g ≫ W.ι = X.fromSpecResidueField x) :
    IsIso ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).counit.app F) ∧
      IsIso ((Etale.upperStarLowerStarAdjunction _ g).unit.app
        (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  have hmem : ∀ y, y ≠ x → y ∈ stalkZeroLocus F := fun y hy ↦ by
    by_contra h; exact hy (hx h)
  refine ⟨isIso_counit_app_of_compl_subset_stalkZeroLocus F W fun y hy ↦
    hmem y fun h ↦ hy (h ▸ hxW), isIso_unit_app_of_compl_subset_stalkZeroLocus g _
      fun w hw ↦ mem_stalkZeroLocus_upperStar _ _ (hmem _ fun h ↦ hw ?_)⟩
  exact mem_range_of_ι_eq W g hg h

/-- A sheaf supported at a point `x`, closed in an open `W`, is the extension by zero along
`W ⟶ X` of the direct image of its restriction to `x`. -/
lemma nonempty_iso_of_compl_stalkZeroLocus_subset
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {x : X}
    (hx : (stalkZeroLocus F)ᶜ ⊆ {x}) (W : X.Opens) (hxW : x ∈ W)
    (g : Spec (X.residueField x) ⟶ W) [IsClosedImmersion g]
    (hg : g ≫ W.ι = X.fromSpecResidueField x) :
    Nonempty (F ≅ (W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj
      (((g)^*[ModuleCat.{u + 1} Λ]).obj (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)))) := by
  obtain ⟨h₁, h₂⟩ := isIso_of_compl_stalkZeroLocus_subset F hx W hxW g hg
  exact ⟨(asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).counit.app F)).symm ≪≫
    ((W.ι)_!open[ModuleCat.{u + 1} Λ]).mapIso
      (asIso ((Etale.upperStarLowerStarAdjunction _ g).unit.app
      (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)))⟩

/-- A constructible sheaf is a simple object of the abelian category of constructible sheaves
exactly when it is nonzero and each of its constructible subsheaves is zero or all of it. -/
lemma simple_iff [IsNoetherianRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F) :
    Simple (⟨F, hF⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory) ↔
      ¬ IsZero F ∧ ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : G ⟶ F),
        Mono ι → IsConstructibleSheaf G → IsZero G ∨ IsIso ι := by
  set P := Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X
  constructor
  · intro hs
    refine ⟨fun h ↦ Simple.not_isZero (⟨F, hF⟩ : P.FullSubcategory)
      ((IsZero.iff_id_eq_zero _).2 (ObjectProperty.hom_ext _ ((IsZero.iff_id_eq_zero F).1 h))),
      fun G ι hι hG ↦ ?_⟩
    let ι' : (⟨G, hG⟩ : P.FullSubcategory) ⟶ ⟨F, hF⟩ := ObjectProperty.homMk ι
    have : Mono ι' := P.ι.mono_of_mono_map hι
    by_cases h0 : ι' = 0
    · left
      have : ι = 0 := congrArg InducedCategory.Hom.hom h0
      have : Mono (0 : G ⟶ F) := this ▸ hι
      exact IsZero.of_mono_zero G F
    · right
      have := isIso_of_mono_of_nonzero h0
      exact (ObjectProperty.isIso_hom_iff ι').2 this
  · rintro ⟨hF₀, hsub⟩
    refine ⟨fun {G'} f hf ↦ ⟨fun hiso h0 ↦ ?_, fun h0 ↦ ?_⟩⟩
    · have : 𝟙 (⟨F, hF⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory) =
          0 := by
        rw [← IsIso.inv_hom_id f]; simp [h0]
      exact hF₀ ((IsZero.iff_id_eq_zero F).2 (congrArg InducedCategory.Hom.hom this))
    · have hG' : IsConstructibleSheaf G'.obj := G'.2
      have hk : IsConstructibleSheaf (kernel f.hom) := IsConstructibleSheaf.kernel f.hom
      have hm : Mono f.hom := by
        refine Preadditive.mono_of_kernel_zero ?_
        let k : (⟨kernel f.hom, hk⟩ : P.FullSubcategory) ⟶ G' := ObjectProperty.homMk (kernel.ι _)
        have : k ≫ f = 0 := ObjectProperty.hom_ext _ (kernel.condition _)
        exact congrArg InducedCategory.Hom.hom ((cancel_mono f).1 (this.trans zero_comp.symm))
      rcases hsub G'.obj f.hom hm hG' with h | h
      · exact (h0 (ObjectProperty.hom_ext _ (h.eq_of_src _ _))).elim
      · exact (ObjectProperty.isIso_hom_iff f).1 h

/-- The extension by zero along an open `W ⟶ X` of the direct image along a closed immersion
into `W` of a constructible sheaf is constructible. -/
lemma isConstructibleSheaf_openImmersionLowerShriek_lowerStar [TopologicalSpace.NoetherianSpace X]
    (W : X.Opens) {Z : Scheme.{u}}
    (g : Z ⟶ W) [IsClosedImmersion g] (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf N] :
    IsConstructibleSheaf ((W.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((g)_*[ModuleCat.{u + 1} Λ].obj N)) := by
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let W' := openComplementOfIsClosedImmersion g
  have : TopologicalSpace.NoetherianSpace W' := W'.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W'.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij' : Set.range g.base = (Set.range W'.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm
  have := IsConstructibleSheaf.lowerStar_of_isClosedImmersion W'.ι g hij' N
  exact IsConstructibleSheaf.openImmersionLowerShriek W.ι W.closedComplement
    (range_closedComplement_eq_compl_range_ι W) _

/-- Blueprint `lem-trf-simple-constructible`: simple constructible sheaves.

Let `X` be a scheme with Noetherian underlying space and `Λ` a Noetherian ring. Every simple
object `F` of the abelian category of constructible sheaves of `Λ`-modules on `X_ét` is of the
form `i_{x!} M`: there is a point `x` with `{x}` locally closed, and `i_{x!}` is the extension by
zero `j_! g_*` along `Spec κ(x) ⟶[g] W ⟶[j] X`, where `W` is an open in which `x` is closed and
`g` a closed immersion, and `M` is a simple constructible sheaf on `Spec κ(x)`, that is a simple
finite `Λ`-module with a continuous action of `Gal(κ(x)ˢᵉᵖ / κ(x))`. Moreover `F` is supported
at `x`: its stalks vanish at the geometric points over every other point. -/
theorem exists_iso_openImmersionLowerShriek_lowerStar_of_simple
    [IsNoetherianRing Λ] [TopologicalSpace.NoetherianSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsConstructibleSheaf F)
    [Simple (⟨F, hF⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory)] :
    ∃ x : X, IsLocallyClosed ({x} : Set X) ∧ (stalkZeroLocus F)ᶜ = {x} ∧
      ∃ (W : X.Opens) (g : Spec (X.residueField x) ⟶ W), x ∈ W ∧ IsClosedImmersion g ∧
        g ≫ W.ι = X.fromSpecResidueField x ∧
        ∃ (M : Sheaf (Spec (X.residueField x)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
          (hM : IsConstructibleSheaf M),
          Simple (⟨M, hM⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) _).FullSubcategory) ∧
          Nonempty (F ≅ (W.ι)_!open[ModuleCat.{u + 1} Λ].obj
            ((g)_*[ModuleCat.{u + 1} Λ].obj M)) := by
  obtain ⟨hF₀, hsub⟩ := (simple_iff F hF).1 ‹_›
  obtain ⟨x, hx⟩ := exists_compl_stalkZeroLocus_eq_singleton F hF₀ hsub
  have hlc := isLocallyClosed_singleton_of_compl_stalkZeroLocus_eq F hx
  obtain ⟨W, g, hxW, hgc, hg⟩ := exists_isClosedImmersion_comp_ι_eq_fromSpecResidueField hlc
  obtain ⟨e⟩ := nonempty_iso_of_compl_stalkZeroLocus_subset F hx.le W hxW g hg
  set M := ((g)^*[ModuleCat.{u + 1} Λ]).obj (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F)
  have : IsConstructibleSheaf (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj F) :=
    IsConstructibleSheaf.upperStar _ _
  have hM : IsConstructibleSheaf M := IsConstructibleSheaf.upperStar _ _
  refine ⟨x, hlc, hx, W, g, hxW, hgc, hg, M, hM, (simple_iff M hM).2 ⟨fun h ↦ hF₀ ?_,
    fun N ι hι hN ↦ ?_⟩, ⟨e⟩⟩
  · exact (((W.ι)_!open[ModuleCat.{u + 1} Λ]).map_isZero
      (((g)_*[ModuleCat.{u + 1} Λ]).map_isZero h)).of_iso e
  · have := isConstructibleSheaf_openImmersionLowerShriek_lowerStar W g N
    rcases hsub _ (((W.ι)_!open[ModuleCat.{u + 1} Λ]).map (((g)_*[ModuleCat.{u + 1} Λ]).map ι) ≫
      e.inv) inferInstance this with h | h
    · exact .inl (IsZero.of_full_of_faithful_of_isZero ((g)_*[ModuleCat.{u + 1} Λ]) _
        (IsZero.of_full_of_faithful_of_isZero ((W.ι)_!open[ModuleCat.{u + 1} Λ]) _ h))
    · have : IsIso (((W.ι)_!open[ModuleCat.{u + 1} Λ]).map
          (((g)_*[ModuleCat.{u + 1} Λ]).map ι)) := IsIso.of_isIso_comp_right _ e.inv
      have := isIso_of_fully_faithful ((W.ι)_!open[ModuleCat.{u + 1} Λ])
        (((g)_*[ModuleCat.{u + 1} Λ]).map ι)
      exact .inr (isIso_of_fully_faithful ((g)_*[ModuleCat.{u + 1} Λ]) ι)

/-- The extension by zero `j_! g_* M` along `Spec κ(x) ⟶[g] W ⟶[j] X` is supported at `x`. -/
lemma compl_stalkZeroLocus_openImmersionLowerShriek_lowerStar_subset {x : X} (W : X.Opens)
    (g : Spec (X.residueField x) ⟶ W) [IsClosedImmersion g]
    (hg : g ≫ W.ι = X.fromSpecResidueField x)
    (M : Sheaf (Spec (X.residueField x)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (stalkZeroLocus ((W.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((g)_*[ModuleCat.{u + 1} Λ].obj M)))ᶜ ⊆ {x} := by
  intro y hy
  by_contra hyx
  apply hy
  set K := (W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj M)
  by_cases hyW : y ∈ W
  · let W' := openComplementOfIsClosedImmersion g
    have hji' : Disjoint (Set.range W'.ι.base) (Set.range g.base) := by
      rw [Scheme.Opens.range_ι]; exact disjoint_compl_left
    have hz : IsZero (((W'.ι)^*[ModuleCat.{u + 1} Λ]).obj (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
      (Etale.isZero_upperStar_lowerStar_of_disjoint_range _ W'.ι g hji' M).of_iso
        (((W'.ι)^*[ModuleCat.{u + 1} Λ]).mapIso (asIso
          ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).unit.app
            ((g)_*[ModuleCat.{u + 1} Λ].obj M))).symm)
    have hw : (⟨y, hyW⟩ : W) ∈ (W' : Set W) := fun h ↦
      hyx (by
        obtain ⟨p, hp⟩ := h
        have : W.ι.base (g.base p) = y := by rw [hp]; rfl
        rw [← this, ← Scheme.Hom.comp_apply, hg, ← Scheme.range_fromSpecResidueField]
        exact ⟨p, rfl⟩)
    obtain ⟨w', hw'⟩ : (⟨y, hyW⟩ : W) ∈ Set.range W'.ι.base := by
      rw [Scheme.Opens.range_ι]; exact hw
    have h₁ := mem_stalkZeroLocus_of_upperStar W'.ι _
      ((isZero_iff_stalkZeroLocus_eq_univ _).1 hz ▸ Set.mem_univ w')
    rw [hw'] at h₁
    exact mem_stalkZeroLocus_of_upperStar W.ι K h₁
  · have hij := range_closedComplement_eq_compl_range_ι W
    obtain ⟨z, rfl⟩ : y ∈ Set.range W.closedComplement.base := by
      rw [hij, Scheme.Opens.range_ι]; exact hyW
    exact mem_stalkZeroLocus_of_upperStar W.closedComplement K
      ((isZero_iff_stalkZeroLocus_eq_univ _).1
      (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range (ModuleCat.{u + 1} Λ) W.ι
        W.closedComplement (disjoint_range_of_range_eq_compl _ _ hij) _) ▸ Set.mem_univ z)

/-- The stalks of a subsheaf vanish where those of the ambient sheaf do. -/
lemma stalkZeroLocus_subset_of_mono {G K : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : G ⟶ K) [Mono ι] : stalkZeroLocus K ⊆ stalkZeroLocus G := fun _ hy Ω _ _ s hs ↦
  have : Mono ((pointSmallEtale s).sheafFiber.map ι) := inferInstance
  IsZero.of_mono ((pointSmallEtale s).sheafFiber.map ι) (hy Ω s hs)

/-- Blueprint `lem-trf-simple-constructible`, converse: for a point `x`, closed in an open `W`,
and a simple constructible sheaf `M` on `Spec κ(x)`, the extension by zero `i_{x!} M = j_! g_* M`
along `Spec κ(x) ⟶[g] W ⟶[j] X` is a simple object of the abelian category of constructible
sheaves on `X_ét`: its constructible subsheaves are `i_{x!} N` for the subsheaves `N` of `M`. -/
theorem simple_openImmersionLowerShriek_lowerStar [IsNoetherianRing Λ]
    [TopologicalSpace.NoetherianSpace X] {x : X} (W : X.Opens) (hxW : x ∈ W)
    (g : Spec (X.residueField x) ⟶ W) [IsClosedImmersion g]
    (hg : g ≫ W.ι = X.fromSpecResidueField x)
    (M : Sheaf (Spec (X.residueField x)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : IsConstructibleSheaf M)
    [Simple (⟨M, hM⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) _).FullSubcategory)] :
    Simple (⟨(W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj M),
      isConstructibleSheaf_openImmersionLowerShriek_lowerStar W g M⟩ :
        (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory) := by
  obtain ⟨hM₀, hMsub⟩ := (simple_iff M hM).1 ‹_›
  set K := (W.ι)_!open[ModuleCat.{u + 1} Λ].obj ((g)_*[ModuleCat.{u + 1} Λ].obj M)
  have hK := compl_stalkZeroLocus_openImmersionLowerShriek_lowerStar_subset W g hg M
  refine (simple_iff K _).2 ⟨fun h ↦ hM₀ (IsZero.of_full_of_faithful_of_isZero
    ((g)_*[ModuleCat.{u + 1} Λ]) _ (IsZero.of_full_of_faithful_of_isZero
      ((W.ι)_!open[ModuleCat.{u + 1} Λ]) _ h)), fun G ι hι hG ↦ ?_⟩
  have hGx : (stalkZeroLocus G)ᶜ ⊆ {x} :=
    (Set.compl_subset_compl.2 (stalkZeroLocus_subset_of_mono ι)).trans hK
  obtain ⟨hεG, hηG⟩ := isIso_of_compl_stalkZeroLocus_subset G hGx W hxW g hg
  obtain ⟨hεK, hηK⟩ := isIso_of_compl_stalkZeroLocus_subset K hK W hxW g hg
  -- the restriction of `ι` to `x`
  set ιW := ((W.ι)^*[ModuleCat.{u + 1} Λ]).map ι
  set N := ((g)^*[ModuleCat.{u + 1} Λ]).obj (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj G)
  let c : ((g)^*[ModuleCat.{u + 1} Λ]).obj (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj K) ≅ M :=
    ((g)^*[ModuleCat.{u + 1} Λ]).mapIso (asIso
      ((Etale.openImmersionLowerShriekUpperStarAdjunction _ W.ι).unit.app
        ((g)_*[ModuleCat.{u + 1} Λ].obj M))).symm ≪≫
      asIso ((Etale.upperStarLowerStarAdjunction _ g).counit.app M)
  have : IsConstructibleSheaf (((W.ι)^*[ModuleCat.{u + 1} Λ]).obj G) :=
    IsConstructibleSheaf.upperStar _ _
  have hN : IsConstructibleSheaf N := IsConstructibleSheaf.upperStar _ _
  rcases hMsub N (((g)^*[ModuleCat.{u + 1} Λ]).map ιW ≫ c.hom) inferInstance hN with h | h
  · left
    obtain ⟨e⟩ := nonempty_iso_of_compl_stalkZeroLocus_subset G hGx W hxW g hg
    exact (((W.ι)_!open[ModuleCat.{u + 1} Λ]).map_isZero
      (((g)_*[ModuleCat.{u + 1} Λ]).map_isZero h)).of_iso e
  · right
    have : IsIso (((g)^*[ModuleCat.{u + 1} Λ]).map ιW) := IsIso.of_isIso_comp_right _ c.hom
    have hW : IsIso ιW := by
      have hnat := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.naturality ιW
      have : ιW = (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
          ((g)_*[ModuleCat.{u + 1} Λ]).map (((g)^*[ModuleCat.{u + 1} Λ]).map ιW) ≫
          inv ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _) := by
        rw [← Category.assoc, IsIso.eq_comp_inv]
        exact hnat
      rw [this]
      infer_instance
    have hnat := (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
      W.ι).counit.naturality ι
    have : ι = inv ((Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
        W.ι).counit.app G) ≫ ((W.ι)_!open[ModuleCat.{u + 1} Λ]).map ιW ≫
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) W.ι).counit.app
          K := by
      rw [IsIso.eq_inv_comp]
      exact hnat.symm
    rw [this]
    infer_instance

/-- A simple constructible sheaf isomorphic to the image of a constructible sheaf `M` under a
fully faithful functor which preserves monomorphisms and constructibility makes `M` simple. -/
lemma simple_of_iso_obj [IsNoetherianRing Λ] {Z : Scheme.{u}}
    (H : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [H.Full] [H.Faithful]
    [H.PreservesZeroMorphisms] [H.PreservesMonomorphisms]
    (hH : ∀ N, IsConstructibleSheaf N → IsConstructibleSheaf (H.obj N))
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hM : IsConstructibleSheaf M)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsConstructibleSheaf F)
    [Simple (⟨F, hF⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory)]
    (e : F ≅ H.obj M) :
    Simple (⟨M, hM⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) Z).FullSubcategory) := by
  obtain ⟨hF₀, hsub⟩ := (simple_iff F hF).1 ‹_›
  refine (simple_iff M hM).2 ⟨fun h ↦ hF₀ ((H.map_isZero h).of_iso e), fun N ι hι hN ↦ ?_⟩
  rcases hsub _ (H.map ι ≫ e.inv) inferInstance (hH N hN) with h | h
  · exact .inl (IsZero.of_full_of_faithful_of_isZero H _ h)
  · have : IsIso (H.map ι) := IsIso.of_isIso_comp_right _ e.inv
    exact .inr (isIso_of_fully_faithful H ι)

/-- Blueprint `lem-trf-simple-constructible`, the case of a scheme of finite type over a field:
the point `x` supporting a simple constructible sheaf `F` is then a closed point (a locally
closed point of a Jacobson space is closed), and `i_{x!} = i_{x*}`: `F` is the direct image
`i_{x*} M` along the closed immersion `i_x : Spec κ(x) ⟶ X` of a simple constructible sheaf `M`
on `Spec κ(x)`. -/
theorem exists_iso_lowerStar_fromSpecResidueField_of_simple [IsNoetherianRing Λ] {k : Type u}
    [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsConstructibleSheaf F)
    [Simple (⟨F, hF⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory)] :
    ∃ x : X, IsClosed ({x} : Set X) ∧ (stalkZeroLocus F)ᶜ = {x} ∧
      ∃ (M : Sheaf (Spec (X.residueField x)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (hM : IsConstructibleSheaf M),
        Simple (⟨M, hM⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) _).FullSubcategory) ∧
        Nonempty (F ≅ (X.fromSpecResidueField x)_*[ModuleCat.{u + 1} Λ].obj M) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  obtain ⟨x, hlc, hx, -⟩ := exists_iso_openImmersionLowerShriek_lowerStar_of_simple F hF
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace aX
  have hxc : IsClosed ({x} : Set X) := isClosed_singleton_of_isLocallyClosed_singleton hlc
  set i := X.fromSpecResidueField x
  have : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.1 hxc
  have hu := isIso_unit_app_of_compl_subset_stalkZeroLocus i F (by
    rw [Scheme.range_fromSpecResidueField, ← hx, compl_compl])
  let e := asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F)
  have hM : IsConstructibleSheaf ((i)^*[ModuleCat.{u + 1} Λ].obj F) :=
    IsConstructibleSheaf.upperStar _ _
  let W := openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]; exact (compl_compl _).symm
  refine ⟨x, hxc, hx, _, hM, simple_of_iso_obj ((i)_*[ModuleCat.{u + 1} Λ])
    (fun N hN ↦ IsConstructibleSheaf.lowerStar_of_isClosedImmersion W.ι i hij N) _ hM F hF e,
    ⟨e⟩⟩

/-- The stalks of the middle term of a short exact sequence vanish where those of the outer
terms do. -/
lemma stalkZeroLocus_inter_subset {S : ShortComplex (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact) :
    stalkZeroLocus S.X₁ ∩ stalkZeroLocus S.X₃ ⊆ stalkZeroLocus S.X₂ := by
  rintro y ⟨h₁, h₃⟩ Ω _ _ s hs
  have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  have hS' := hS.map_of_exact (pointSmallEtale s).sheafFiber
  exact hS'.exact.isZero_X₂ ((h₁ Ω s hs).eq_of_src _ _) ((h₃ Ω s hs).eq_of_tgt _ _)

/-- Blueprint `lem-trf-simple-constructible`, last assertion: on a connected scheme `X` of
positive dimension and of finite type over a field, a nonzero locally constant sheaf `L` is not a
finite extension of simple constructible sheaves. Stated through the universal property of the
closure under extensions: there is a property of sheaves containing zero, closed under
isomorphisms and extensions, holding for every simple constructible sheaf, but not for `L`. The
property is "the stalks vanish at the non-closed points": a simple constructible sheaf is
supported at a closed point, while the stalks of `L` vanish on a clopen set, which is empty. -/
theorem not_forall_prop_of_isLocallyConstantSheaf [IsNoetherianRing Λ] {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [ConnectedSpace X]
    (hX : 0 < topologicalKrullDim X) (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf L] (hL : ¬ IsZero L) :
    ¬ ∀ P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      P.ContainsZero → P.IsClosedUnderIsomorphisms → P.IsClosedUnderExtensions →
      (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : IsConstructibleSheaf F),
        Simple (⟨F, hF⟩ : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).FullSubcategory) →
          P F) → P L := by
  intro h
  let Q : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun F ↦ ∀ y : X, ¬ IsClosed ({y} : Set X) → y ∈ stalkZeroLocus F
  have hQ := h Q ⟨⟨0, isZero_zero _, fun y _ ↦
      (isZero_iff_stalkZeroLocus_eq_univ (0 : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ))).1 (isZero_zero _) ▸ Set.mem_univ y⟩⟩
    ⟨fun e hF y hy ↦ stalkZeroLocus_subset_of_mono e.inv (hF y hy)⟩
    ⟨fun {S} hS h₁ h₃ y hy ↦ stalkZeroLocus_inter_subset hS ⟨h₁ y hy, h₃ y hy⟩⟩
    (fun F hF _ y hy ↦ by
      obtain ⟨x, hxc, hx, -⟩ := exists_iso_lowerStar_fromSpecResidueField_of_simple aX F hF
      by_contra hyF
      have : y ∈ (stalkZeroLocus F)ᶜ := hyF
      rw [hx, Set.mem_singleton_iff] at this
      exact hy (this ▸ hxc))
  obtain ⟨y, hy⟩ := exists_not_isClosed_singleton_of_topologicalKrullDim_pos hX
  have hne : stalkZeroLocus L ≠ Set.univ := fun h ↦ hL ((isZero_iff_stalkZeroLocus_eq_univ L).2 h)
  rcases isClopen_iff.1 (isClopen_stalkZeroLocus L) with h' | h'
  · exact (h' ▸ hQ y hy : y ∈ (∅ : Set X))
  · exact hne h'

end Etale

end AlgebraicGeometry
