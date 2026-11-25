/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # The weak Serre property in the module-valued slice encoding

Source: Stacks Project, Modules on Sites, Tag 093U (3), transported through the
constant-ring equivalence and the equivalence of iterated slices.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def restrictionConstants
    {D E : Type u} [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology D) (S : GrothendieckTopology E)
    (B : Type u) [CommRing B] (G : D ⥤ E)
    [G.IsContinuous T S] [G.IsCocontinuous T S] :
    constantSheaf S (ModuleCat.{u} B) ⋙
        G.sheafPushforwardContinuous (ModuleCat.{u} B) T S ≅
      constantSheaf T (ModuleCat.{u} B) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Eᵒᵖ)
      (G.pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} B) T S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.constCompWhiskeringLeftIso _ G.op)
      (presheafToSheaf T (ModuleCat.{u} B))

private def finiteModels {D : Type u} [SmallCategory D]
    (T : GrothendieckTopology D) (B : Type u) [CommRing B] :
    ObjectProperty (Sheaf T (ModuleCat.{u} B)) :=
  fun F ↦ ∀ V : D, ∃ S : Sieve V, S ∈ T V ∧
    ∀ (W : D) (f : W ⟶ V), S f →
      ∃ M : ModuleCat.{u} B, Module.Finite B M ∧
        Nonempty (F.over W ≅ (constantSheaf (T.over W) (ModuleCat.{u} B)).obj M)

private instance finiteModels_iso {D : Type u} [SmallCategory D]
    (T : GrothendieckTopology D) (B : Type u) [CommRing B] :
    (finiteModels T B).IsClosedUnderIsomorphisms where
  of_iso e h V := by
    obtain ⟨S, hS, hs⟩ := h V
    refine ⟨S, hS, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨i⟩⟩ := hs W f hf
    exact ⟨M, hM, ⟨(T.overPullback _ W).mapIso e.symm ≪≫ i⟩⟩

private theorem finiteModels_weakSerre {D : Type u} [SmallCategory D]
    (T : GrothendieckTopology D) (B : Type u) [CommRing B] [IsNoetherianRing B] :
    (finiteModels T B).IsClosedUnderKernels ∧
      (finiteModels T B).IsClosedUnderCokernels ∧
      (finiteModels T B).IsClosedUnderExtensions := by
  let R := (constantSheaf T RingCat.{u}).obj (RingCat.of B)
  let α := toSheafify T ((Functor.const Dᵒᵖ).obj (RingCat.of B))
  obtain ⟨G, hG, ⟨c⟩, hslice⟩ := site_moduleSheaf_restriction_equivalence T B R α
  have : G.IsEquivalence := hG
  have compare (F : SheafOfModules.{u} R) :
      finiteModels T B (G.obj F) ↔ SheafOfModules.IsFiniteTypeLocallyConstant T B F := by
    have localCompare (W : D) (M : ModuleCat.{u} B) :
        Nonempty (F.over W ≅ ((SheafOfModules.strictPerfectConstantSheaf T B).obj M).over W) ↔
          Nonempty ((G.obj F).over W ≅
            (constantSheaf (T.over W) (ModuleCat.{u} B)).obj M) := by
      obtain ⟨GW, hGW, ⟨eW⟩⟩ := hslice W
      have : GW.IsEquivalence := hGW
      let cW : GW.obj (((SheafOfModules.strictPerfectConstantSheaf T B).obj M).over W) ≅
          (constantSheaf (T.over W) (ModuleCat.{u} B)).obj M :=
        eW.app _ ≪≫ (T.overPullback _ W).mapIso (c.app M) ≪≫
          (T.overPullbackConstantSheafIso (ModuleCat.{u} B) W).app M
      constructor
      · rintro ⟨i⟩
        exact ⟨(eW.app F).symm ≪≫ GW.mapIso i ≪≫ cW⟩
      · rintro ⟨i⟩
        exact ⟨GW.asEquivalence.fullyFaithfulFunctor.preimageIso
          (eW.app F ≪≫ i ≪≫ cW.symm)⟩
    constructor
    all_goals
      intro h V
      obtain ⟨S, hS, hs⟩ := h V
      refine ⟨S, hS, fun W f hf ↦ ?_⟩
      obtain ⟨M, hM, hi⟩ := hs W f hf
      first
      | exact ⟨M, hM, (localCompare W M).mp hi⟩
      | exact ⟨M, hM, (localCompare W M).mpr hi⟩
  let E := G.asEquivalence.inverse
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have h (F : Sheaf T (ModuleCat.{u} B)) :
      finiteModels T B F ↔ SheafOfModules.IsFiniteTypeLocallyConstant T B (E.obj F) := by
    rw [← compare]
    exact ⟨(finiteModels T B).prop_of_iso (G.asEquivalence.counitIso.app F).symm,
      (finiteModels T B).prop_of_iso (G.asEquivalence.counitIso.app F)⟩
  have ringedIso {F H : SheafOfModules.{u} R} (i : F ≅ H)
      (hF : SheafOfModules.IsFiniteTypeLocallyConstant T B F) :
      SheafOfModules.IsFiniteTypeLocallyConstant T B H := by
    intro V
    obtain ⟨S, hS, hs⟩ := hF V
    refine ⟨S, hS, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨j⟩⟩ := hs W f hf
    exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso i.symm ≪≫ j⟩⟩
  obtain ⟨hk, hx⟩ :=
    SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions T B
  have kernels (F H : Sheaf T (ModuleCat.{u} B)) (f : F ⟶ H)
      (hF : finiteModels T B F) (hH : finiteModels T B H) :
      finiteModels T B (kernel f) ∧ finiteModels T B (cokernel f) := by
    obtain ⟨hK, hC⟩ := hk _ _ (E.map f) ((h F).mp hF) ((h H).mp hH)
    exact ⟨(h _).mpr (ringedIso (PreservesKernel.iso E f).symm hK),
      (h _).mpr (ringedIso (PreservesCokernel.iso E f).symm hC)⟩
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · intro X hX
    cases hX with
    | of_isLimit f k hlim hf =>
      exact (finiteModels T B).prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hlim)
        (kernels _ _ f hf.1 hf.2).1
  · intro X hX
    cases hX with
    | of_isColimit f k hlim hf =>
      exact (finiteModels T B).prop_of_iso
        ((cokernelIsCokernel f).coconePointUniqueUpToIso hlim) (kernels _ _ f hf.1 hf.2).2
  · intro S hS h₁ h₃
    exact (h _).mpr (hx (S.map E) (hS.map_of_exact E) ((h _).mp h₁) ((h _).mp h₃))

private theorem iteratedSliceModels {C : Type u} [SmallCategory C]
    (T : GrothendieckTopology C) (B : Type u) [CommRing B] {U : C}
    (F : Sheaf (T.over U) (ModuleCat.{u} B)) (W : Over U) (M : ModuleCat.{u} B) :
    Nonempty (F.over W ≅ (constantSheaf ((T.over U).over W) (ModuleCat.{u} B)).obj M) ↔
      Nonempty ((T.overMapPullback (ModuleCat.{u} B) W.hom).obj F ≅
        (constantSheaf (T.over W.left) (ModuleCat.{u} B)).obj M) := by
  let e := W.iteratedSliceEquiv.sheafCongr ((T.over U).over W) (T.over W.left)
    (ModuleCat.{u} B)
  let c : e.functor.obj
      ((constantSheaf ((T.over U).over W) (ModuleCat.{u} B)).obj M) ≅
      (constantSheaf (T.over W.left) (ModuleCat.{u} B)).obj M :=
    (restrictionConstants (T.over W.left) ((T.over U).over W) B
      W.iteratedSliceBackward).app M
  let i : e.functor.obj (F.over W) ≅
      (T.overMapPullback (ModuleCat.{u} B) W.hom).obj F := Iso.refl _
  constructor
  · rintro ⟨j⟩
    exact ⟨i.symm ≪≫ e.functor.mapIso j ≪≫ c⟩
  · rintro ⟨j⟩
    exact ⟨e.fullyFaithfulFunctor.preimageIso (i ≪≫ j ≪≫ c.symm)⟩

private noncomputable def flatModel_restrict {C : Type u} [SmallCategory C]
    (T : GrothendieckTopology C) (B : Type u) [CommRing B] {U V W : C}
    (F : Sheaf (T.over U) (ModuleCat.{u} B)) (g : V ⟶ U) (f : W ⟶ V)
    (M : ModuleCat.{u} B)
    (i : (T.overMapPullback (ModuleCat.{u} B) g).obj F ≅
      (constantSheaf (T.over V) (ModuleCat.{u} B)).obj M) :
    (T.overMapPullback (ModuleCat.{u} B) (f ≫ g)).obj F ≅
      (constantSheaf (T.over W) (ModuleCat.{u} B)).obj M :=
  ((T.overMapPullbackComp (ModuleCat.{u} B) f g).app F).symm ≪≫
    (T.overMapPullback (ModuleCat.{u} B) f).mapIso i ≪≫
      (restrictionConstants (T.over W) (T.over V) B (Over.map f)).app M

/-- Finite locally constant sheaves on a slice are closed under kernels,
cokernels and extensions, in the module-valued sheaf encoding.

Source: Stacks Project, Modules on Sites, Tag 093U (3).
(auxiliary; not a blueprint node)

Proof: On the site C/U, take the constant ring sheaf and the equivalence between
module-valued sheaves and modules over that ring. Its slice comparison and the
constant-sheaf restriction isomorphism identify the displayed property with
IsFiniteTypeLocallyConstant. Covering sieves on an object V/U correspond to
covering sieves on V. Each contains a J-cover, since J is stable under base
change and composition and contains isomorphisms. Conversely a J-cover generates
a covering sieve; the property of admitting a constant finite trivialization is
stable under further restriction, so the displayed covers yield the sieve
condition. The canonical equivalence (C/U)/(V/U) ≌ C/V identifies the restriction
functors and their constants. Thus these are exactly the same local
trivializations. Apply finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
on C/U. Equivalences are exact, and their kernel, cokernel and short exact
sequence comparisons transport the three closure properties back. No
nonempty-cover or nonzero-ring condition is used. -/
theorem site_finiteLocallyConstant_weakSerre
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (B : Type u) [CommRing B] [IsNoetherianRing B] (U : C) :
    let P : ObjectProperty (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) :=
      fun F ↦ ∀ (V : C) (g : V ⟶ U),
        ∃ (I : Type u) (W : I → C) (f : ∀ i : I, W i ⟶ V),
          Presieve.ofArrows W f ∈ J V ∧
          ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
            ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i ≫ g)).obj F ≅
              (constantSheaf (J.toGrothendieck.over (W i)) (ModuleCat.{u} B)).obj M)
    P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions := by
  let P : ObjectProperty (Sheaf (J.toGrothendieck.over U) (ModuleCat.{u} B)) :=
    fun F ↦ ∀ (V : C) (g : V ⟶ U),
      ∃ (I : Type u) (W : I → C) (f : ∀ i : I, W i ⟶ V),
        Presieve.ofArrows W f ∈ J V ∧
        ∀ i : I, ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
          ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f i ≫ g)).obj F ≅
            (constantSheaf (J.toGrothendieck.over (W i)) (ModuleCat.{u} B)).obj M)
  change P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions
  have hP : P = finiteModels (J.toGrothendieck.over U) B := by
    funext F
    apply propext
    constructor
    · intro h V
      let S : Sieve V.left :=
        { arrows W f := ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
            ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f ≫ V.hom)).obj F ≅
              (constantSheaf (J.toGrothendieck.over W) (ModuleCat.{u} B)).obj M)
          downward_closed := by
            intro W Z f hf g
            obtain ⟨M, hM, ⟨i⟩⟩ := hf
            refine ⟨M, hM, ⟨?_⟩⟩
            simpa only [Category.assoc] using
              flatModel_restrict J.toGrothendieck B F (f ≫ V.hom) g M i }
      obtain ⟨I, W, f, hcover, hs⟩ := h V.left V.hom
      have hS : S ∈ J.toGrothendieck V.left := by
        apply J.toGrothendieck.superset_covering _ (J.generate_mem_toGrothendieck hcover)
        rw [Sieve.generate_le_iff]
        exact Presieve.ofArrows_le_iff.mpr hs
      refine ⟨(Sieve.overEquiv V).symm S,
        J.toGrothendieck.overEquiv_symm_mem_over V S hS, fun W f hf ↦ ?_⟩
      have ht := (Sieve.overEquiv_symm_iff S f).mp hf
      change ∃ M : ModuleCat.{u} B, Module.Finite B M ∧ Nonempty
        ((J.toGrothendieck.overMapPullback (ModuleCat.{u} B) (f.left ≫ V.hom)).obj F ≅
          (constantSheaf (J.toGrothendieck.over W.left) (ModuleCat.{u} B)).obj M) at ht
      rw [Over.w f] at ht
      obtain ⟨M, hM, hi⟩ := ht
      exact ⟨M, hM, (iteratedSliceModels J.toGrothendieck B F W M).mpr hi⟩
    · intro h V g
      obtain ⟨S, hS, hs⟩ := h (Over.mk g)
      have ht : Sieve.overEquiv (Over.mk g) S ∈ J.toGrothendieck V := hS
      obtain ⟨R, hR, hle⟩ := J.mem_toGrothendieck_iff_of_isStableUnderComposition.mp ht
      obtain ⟨I, W, f, rfl⟩ := R.exists_eq_ofArrows
      refine ⟨I, W, f, hR, fun i ↦ ?_⟩
      have hi := (Sieve.overEquiv_iff S (f i)).mp (hle _ _ ⟨i⟩)
      obtain ⟨M, hM, hMiso⟩ := hs (Over.mk (f i ≫ g)) (Over.homMk (f i)) hi
      exact ⟨M, hM, (iteratedSliceModels J.toGrothendieck B F (Over.mk (f i ≫ g)) M).mp
        hMiso⟩
  rw [hP]
  exact finiteModels_weakSerre (J.toGrothendieck.over U) B

end CategoryTheory
