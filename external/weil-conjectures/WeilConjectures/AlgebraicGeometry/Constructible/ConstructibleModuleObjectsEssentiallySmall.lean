/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LocallyInjective
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Subobject.WellPowered

/-! # Essential smallness of constructible module objects

Source: blueprint `lemma-hypotheses-brown-representability--5`, local finite-presentation counting.
(blueprint: lem-sfb-constructible-module-objects-essentially-small)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem mono_to_product_of_local_isos
    {C : Type*} [Category C] [Abelian C] {I : Type v}
    {D : I → Type*} [∀ i, Category (D i)] [∀ i, Abelian (D i)]
    (F : ∀ i, C ⥤ D i) (G : ∀ i, D i ⥤ C) (adj : ∀ i, F i ⊣ G i)
    [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)]
    (detect : ∀ M : C, (∀ i, IsZero ((F i).obj M)) → IsZero M)
    (B : ∀ i, D i) [HasProduct (fun i ↦ (G i).obj (B i))]
    (M : C) (e : ∀ i, (F i).obj M ≅ B i) :
    Mono (Pi.lift (fun i ↦ (adj i).homEquiv M (B i) (e i).hom)) := by
  let f := Pi.lift (fun i ↦ (adj i).homEquiv M (B i) (e i).hom)
  apply Preadditive.mono_of_isZero_kernel
  apply detect
  intro i
  have h : kernel.ι f ≫ (adj i).homEquiv M (B i) (e i).hom = 0 := by
    rw [← Pi.lift_comp_π (fun i ↦ (adj i).homEquiv M (B i) (e i).hom) i,
      ← Category.assoc, kernel.condition, zero_comp]
  have h' : (F i).map (kernel.ι f) ≫ (e i).hom = 0 := by
    apply ((adj i).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, h, Adjunction.homAddEquiv_zero]
  have h'' : (F i).map (kernel.ι f) = 0 := by
    simpa only [← cancel_mono (e i).hom, zero_comp] using h'
  have : Mono (0 : (F i).obj (kernel f) ⟶ (F i).obj M) := h'' ▸ inferInstance
  exact IsZero.of_mono_zero ((F i).obj (kernel f)) ((F i).obj M)

private theorem small_subobject_domains {C : Type*} [Category.{v} C]
    [LocallySmall.{v} C] [WellPowered.{v} C] (E : C) :
    ObjectProperty.EssentiallySmall.{v}
      (MonoOver.forget E ⋙ Over.forget E).essImage := by
  have : EssentiallySmall.{v} (MonoOver E) := essentiallySmall_monoOver E
  rw [← ObjectProperty.map_top]
  infer_instance

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

section ZeroDetection

open Scheme TopologicalSpace Opposite
open scoped ZeroObject

-- The local-vanishing and finite-cover arguments below adapt the proved module-sheaf
-- argument in UpperLowerStar.Detection to abelian groups. Cover detection uses the
-- proved localization-restriction conservativity theorem, without a new admitted input.
variable {U Z : Scheme.{u}} (g : Z ⟶ U)

/-- The forgetful functor of modules preserves the colimits computing the left Kan extension
along the opposite of base change: they are filtered, base change being representably flat. -/
private instance ab_preservesColimitsOfShape_costructuredArrow_overPullback (Y) :
    PreservesColimitsOfShape
    (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y)
    (forget Ab.{u + 1}) := by
  have : IsFiltered (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ Y.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  infer_instance

variable (F : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})

/-- **Local vanishing.** If the image of a section `s` of `F` over `V` under the unit
`F ⟶ g_* g^* F` vanishes, then there is a pro-étale cover of `V ×_U Z` each of whose members
factors through the base change `V' ×_U Z` of a morphism `f : V' ⟶ V` of the pro-étale site
with `s|_{V'} = 0`. -/
private theorem ab_exists_mem_precoverage_map_eq_zero {V : U.ProEt} (s : ToType (F.obj.obj (op V)))
    (hs : ((upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app F).hom.app (op V) s =
      0) :
    ∃ (P : Presieve ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V)),
      P ∈ Scheme.ProEt.precoverage Z _ ∧
      ∀ ⦃T⦄ (φ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V), P φ →
        ∃ (V' : U.ProEt) (f : V' ⟶ V)
          (ψ : T ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V'),
          ψ ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f = φ ∧
            F.obj.map f.op s = 0 := by
  set G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ g
  have hunit : ((upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app F).hom.app
      (op V) = (G.op.leftKanExtensionUnit F.obj).app (op V) ≫
        (toSheafify _ (G.op.leftKanExtension F.obj)).app (op (G.obj V)) := rfl
  rw [hunit, ConcreteCategory.comp_apply] at hs
  have hS := Presheaf.equalizerSieve_mem (Scheme.ProEt.topology Z)
    (toSheafify (Scheme.ProEt.topology Z) (G.op.leftKanExtension F.obj)) (X := op (G.obj V))
      ((G.op.leftKanExtensionUnit F.obj).app (op V) s) 0
      (hs.trans (map_zero _).symm)
  obtain ⟨P, hP, hle⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  refine ⟨P, hP, fun T φ hφ ↦ ?_⟩
  have h₁ := hle _ _ hφ
  obtain ⟨V', f, ψ, hψ, h⟩ := Functor.exists_map_eq_of_leftKanExtensionUnit_eq G F.obj φ s 0
    (by simpa using h₁)
  exact ⟨V', f, ψ, hψ, by simpa using h⟩

/-- **Restrictions along a quasi-compact jointly surjective family detect sections.** Let
`g k : Z k ⟶ U` be finitely many quasi-compact morphisms jointly covering `U`. A section `s` of
a pro-étale sheaf of modules `F` on `U` whose images under the units `F ⟶ (g k)_* (g k)^* F` all
vanish is zero: `s` vanishes on weakly étale neighbourhoods of the points of every
`V ×_U Z k` (`AlgebraicGeometry.ProEtale.exists_mem_precoverage_map_eq_zero`), and these
neighbourhoods form a pro-étale cover of `V`
(`AlgebraicGeometry.QuasiCompactCover.of_comp_factor`). -/
private theorem ab_eq_zero_of_forall_unit_app_eq_zero {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (F : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) {V : U.ProEt}
    (s : ToType (F.obj.obj (op V)))
    (hs : ∀ k, ((upperStarLowerStarAdjunction Ab.{u + 1} (g k)).unit.app F).hom.app
      (op V) s = 0) :
    s = 0 := by
  have hlocal := fun k ↦ ab_exists_mem_precoverage_map_eq_zero (g k) F s (hs k)
  choose P hP hPs using hlocal
  choose ι T φ hTφ using fun k ↦ (P k).exists_eq_ofArrows
  choose V' f ψ hψ hf using fun (p : Σ k, ι k) ↦
    hPs p.1 (φ p.1 p.2) (by rw [hTφ p.1]; exact .mk p.2)
  let D : PreZeroHypercover V.left := ⟨Σ k, ι k, fun p ↦ (V' p).left, fun p ↦ (f p).left⟩
  let E (k : κ) : PreZeroHypercover
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (g k)).obj V).left :=
    ⟨ι k, fun m ↦ (T k m).left, fun m ↦ (φ k m).left⟩
  have hE (k : κ) : (E k).presieve₀ ∈ Scheme.proetalePrecoverage _ := by
    have := hP k
    rw [hTφ k, Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at this
    exact this
  have : ∀ k, QuasiCompactCover (E k) := fun k ↦
    Scheme.presieve₀_mem_qcPrecoverage_iff.1 (hE k).1
  have hD : QuasiCompactCover D := by
    refine QuasiCompactCover.of_comp_factor (fun k ↦ pullback.fst V.hom (g k)) (fun x ↦ ?_) E D
      (fun k m ↦ ⟨k, m⟩) (fun k m ↦ (ψ ⟨k, m⟩).left ≫ pullback.fst _ _) fun k m ↦ ?_
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      exact ⟨k, w, hw⟩
    · have := congrArg (fun a ↦ a.left ≫ pullback.fst V.hom (g k)) (hψ ⟨k, m⟩)
      simpa using this
  have hDmem : D.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD, ?_⟩
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2 ⟨fun x ↦ ?_, fun p ↦ ?_⟩
    · obtain ⟨k, z, hz⟩ := hg (V.hom x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
      obtain ⟨m, τ, rfl⟩ :=
        ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (hE k).2).1 w
      refine ⟨⟨k, m⟩, (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ |>.base τ, ?_⟩
      have key : (ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left =
          (φ k m).left ≫ pullback.fst V.hom (g k) := by
        rw [← hψ ⟨k, m⟩]
        simp
      rw [← hw]
      change ((ψ ⟨k, m⟩).left ≫ pullback.fst _ _ ≫ (f ⟨k, m⟩).left).base τ =
        ((φ k m).left ≫ pullback.fst V.hom (g k)).base τ
      exact congrArg (fun a ↦ a.base τ) key
    · exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) (f p).left
        V.hom V.prop (by rw [MorphismProperty.Over.w (f p)]; exact (V' p).prop)
  have hmem : Presieve.ofArrows V' f ∈ Scheme.ProEt.precoverage U V := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hDmem
  have hS : Sieve.generate (Presieve.ofArrows V' f) ∈ Scheme.ProEt.topology U V :=
    Scheme.ProEt.mem_topology_iff.2 ⟨_, hmem, Sieve.le_generate _⟩
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget Ab.{u + 1}) F.property) _ hS
  rw [← Presieve.isSheafFor_iff_generate] at hsh
  refine hsh.isSeparatedFor.ext fun _ _ ⟨p⟩ ↦ ?_
  change F.obj.map (f p).op s = F.obj.map (f p).op 0
  rw [hf p, map_zero]

/-- **Pullbacks along a quasi-compact jointly surjective family are jointly faithful.** A
morphism of pro-étale sheaves of modules on `U` whose pullbacks along finitely many
quasi-compact morphisms `g k : Z k ⟶ U` jointly covering `U` vanish is zero. -/
private theorem ab_eq_zero_of_forall_upperStar_map_eq_zero
    {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}}
    (g : ∀ k, Z k ⟶ U) [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    {F G : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}} (φ : F ⟶ G)
    (h : ∀ k, (g k)^*[Ab.{u + 1}].map φ = 0) : φ = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ConcreteCategory.hom_ext _ _ (fun x ↦ ?_)))
  refine ab_eq_zero_of_forall_unit_app_eq_zero g hg G (φ.hom.app V x) fun k ↦ ?_
  have h0 : φ ≫ (upperStarLowerStarAdjunction Ab.{u + 1} (g k)).unit.app G = 0 := by
    have := (upperStarLowerStarAdjunction Ab.{u + 1} (g k)).unit.naturality φ
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map, h k,
      Functor.map_zero, comp_zero] at this
    exact this
  have := congrArg (fun ψ ↦ (ψ.hom.app V) x) h0
  simpa using this

private theorem ab_isZero_of_cover {X : Scheme.{u}}
    (V : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (h : ∀ j, IsZero ((upperStar Ab.{u + 1} (V.f j)).obj F)) : IsZero F := by
  let : ∀ j, WeaklyEtale (V.f j) :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 V.mem₀.2 |>.2
  have : IsIso (0 : F ⟶ 0) := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} (0 : F ⟶ 0)
      V.f V.mem₀ fun j ↦ ?_
    let e := upperStarIsoLocalizationRestriction Ab.{u + 1} (V.f j) inferInstance
    exact isIso_of_source_target_iso_zero _ ((h j).of_iso (e.app F).symm).isoZero
      (((upperStar Ab.{u + 1} (V.f j)).map_isZero (isZero_zero _)).of_iso
        (e.app 0).symm).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

private theorem ab_isZero_of_stratum_cover (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : Scheme.Stratification X)
    (V : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (h : ∀ a j, IsZero ((upperStar Ab.{u + 1} ((V a).f j)).obj
      ((upperStar Ab.{u + 1} (S.immersion a)).obj F))) : IsZero F := by
  have : IsNoetherian X := {}
  have hstr (a : Fin S.n) : IsZero ((upperStar Ab.{u + 1} (S.immersion a)).obj F) :=
    ab_isZero_of_cover (V a) _ (h a)
  have : ∀ a : Fin S.n, NoetherianSpace (S.domain a) := fun a ↦
    (S.immersion a).isEmbedding.noetherianSpace
  have : ∀ a : Fin S.n, QuasiCompact (S.immersion a) := fun a ↦ inferInstance
  rw [IsZero.iff_id_eq_zero]
  apply ab_eq_zero_of_forall_upperStar_map_eq_zero S.immersion
  · intro x
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · intro a
    rw [(upperStar Ab.{u + 1} (S.immersion a)).map_id]
    exact (hstr a).eq_of_src _ _

end ZeroDetection

private theorem pullback_module_isLeftAdjoint {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (T : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj T] :
    ((upperStar Ab.{u + 1} f).mapMod T).IsLeftAdjoint := by
  exact ((upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction T).isLeftAdjoint

private theorem pullback_module_additive {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (T : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj T] :
    ((upperStar Ab.{u + 1} g).mapMod T).Additive where
  map_add {M N a b} := by
    apply Mod.hom_ext
    exact (upperStar Ab.{u + 1} g).map_add

private theorem pullback_module_preservesFiniteLimits {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (T : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj T] :
    PreservesFiniteLimits ((upperStar Ab.{u + 1} f).mapMod T) := by
  infer_instance

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]

private structure ConstructiblePresentationData where
  S : Scheme.Stratification X
  V : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a)
  presentation : ∀ (a : Fin S.n) (j : (V a).I₀),
        Σ n : ℕ, Σ m : ℕ,
          Mod.finiteFree ((upperStar Ab.{u + 1} ((V a).f j)).obj
            ((upperStar Ab.{u + 1} (S.immersion a)).obj R)) m ⟶
          Mod.finiteFree ((upperStar Ab.{u + 1} ((V a).f j)).obj
            ((upperStar Ab.{u + 1} (S.immersion a)).obj R)) n

/-- Constructible module objects over a fixed sheaf of rings on a Noetherian scheme
form an essentially small class in the sheaf morphism universe.

Source: blueprint `lemma-hypotheses-brown-representability--5`, steps 1–10; the proved
local-vanishing argument in `UpperLowerStar.Detection` and cover conservativity in
`LowerShriek.Open.Conservative` of the source library.
(blueprint: lem-sfb-constructible-module-objects-essentially-small)

Proof: stratifications, pro-etale covers, ranks, and finite presentation matrices
form a small set of local data. For fixed such data, pull back to each cover member
of each stratum. These exact left adjoints jointly detect zero objects. The adjoints
of the prescribed local isomorphisms embed any realizing module into the product of
the right adjoints of the prescribed local cokernels: the kernel has zero pullback
everywhere and is therefore zero. Zero detection is proved: restrictions to a
pro-etale cover are conservative, and the local-vanishing argument for finitely many
quasi-compact, jointly surjective immersions detects sections. Noetherianity makes
the stratum immersions quasi-compact. The module category is Grothendieck abelian,
hence well-powered, so subobjects of each fixed product form an essentially small
class. The union over the small collection of local data remains essentially small.
-/
theorem constructibleModuleObjects_essentiallySmall :
    ObjectProperty.EssentiallySmall.{u + 1} (IsConstructibleModuleObject R) := by
  classical
  have : IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    Mod.isGrothendieckAbelian.{u + 1} R
  let Data := ConstructiblePresentationData X R
  let F (d : Data) (i : Σ a : Fin d.S.n, (d.V a).I₀) :=
    (upperStar Ab.{u + 1} (d.S.immersion i.1)).mapMod R ⋙
      (upperStar Ab.{u + 1} ((d.V i.1).f i.2)).mapMod
        ((upperStar Ab.{u + 1} (d.S.immersion i.1)).obj R)
  have hadj : ∀ (d : Data) (i : Σ a : Fin d.S.n, (d.V a).I₀),
      (F d i).IsLeftAdjoint := by
    intro d i
    let := pullback_module_isLeftAdjoint (d.S.immersion i.1) R
    let := pullback_module_isLeftAdjoint ((d.V i.1).f i.2)
      ((upperStar Ab.{u + 1} (d.S.immersion i.1)).obj R)
    exact Functor.isLeftAdjoint_comp _ _
  let G (d : Data) (i : Σ a : Fin d.S.n, (d.V a).I₀) := Functor.rightAdjoint (F d i)
  let adj (d : Data) (i : Σ a : Fin d.S.n, (d.V a).I₀) :=
    Adjunction.ofIsLeftAdjoint (F d i)
  let B (d : Data) (i : Σ a : Fin d.S.n, (d.V a).I₀) := cokernel (d.presentation i.1 i.2).2.2
  let : HasProducts.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := fun I ↦
    HasLimitsOfSize.has_limits_of_shape (Discrete I)
  let : HasProducts.{u} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    hasProducts_shrink.{u, u + 1}
  let E (d : Data) := ∏ᶜ fun i ↦ (G d i).obj (B d i)
  let Q (d : Data) := (MonoOver.forget (E d) ⋙ Over.forget (E d)).essImage
  have : ∀ d, ObjectProperty.EssentiallySmall.{u + 1} (Q d) := fun d ↦ small_subobject_domains (E d)
  apply ObjectProperty.EssentiallySmall.of_le (Q := ⨆ d, Q d)
  intro M hM
  obtain ⟨S, hS⟩ := hM
  choose V hV using hS
  choose n m f hf using hV
  let d : Data := ⟨S, V, fun a j ↦ ⟨n a j, m a j, f a j⟩⟩
  have detect (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (hN : ∀ i, IsZero ((F d i).obj N)) : IsZero N := by
    have hz : IsZero N.X := ab_isZero_of_stratum_cover X S V N.X (by
      intro a j
      exact (Mod.forget ((upperStar Ab.{u + 1} ((V a).f j)).obj
        ((upperStar Ab.{u + 1} (S.immersion a)).obj R))).map_isZero (hN ⟨a, j⟩))
    rw [IsZero.iff_id_eq_zero]
    apply (Mod.forget R).map_injective
    simpa using hz.eq_of_src (𝟙 N.X) 0
  let e (i : Σ a : Fin S.n, (V a).I₀) := (hf i.1 i.2).some
  have hadd : ∀ i, (F d i).Additive := by
    intro i
    let := pullback_module_additive (S.immersion i.1) R
    let := pullback_module_additive ((V i.1).f i.2)
      ((upperStar Ab.{u + 1} (S.immersion i.1)).obj R)
    infer_instance
  have hfinite : ∀ i, PreservesFiniteLimits (F d i) := by
    intro i
    let := pullback_module_preservesFiniteLimits (S.immersion i.1) R
    let := pullback_module_preservesFiniteLimits ((V i.1).f i.2)
      ((upperStar Ab.{u + 1} (S.immersion i.1)).obj R)
    exact Limits.comp_preservesFiniteLimits _ _
  have hm : Mono (Pi.lift (fun i ↦ (adj d i).homEquiv M (B d i) (e i).hom)) :=
    mono_to_product_of_local_isos (F d) (G d) (adj d) detect (B d) M e
  simp only [ObjectProperty.prop_iSup_iff]
  exact ⟨d, MonoOver.mk (Pi.lift (fun i ↦ (adj d i).homEquiv M (B d i) (e i).hom)),
    ⟨Iso.refl M⟩⟩

end AlgebraicGeometry.ProEtale
