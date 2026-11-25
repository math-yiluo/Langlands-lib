/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Local constancy of a finite ring action

Source: Stacks Project, Modules on Sites, Tag 093S, finite-operation refinement;
Sites, Tag 00WK (blueprint: lem-sp-finite-ring-action-local-constancy).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

noncomputable section

section ScalarRestriction

variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  (Λ : Type (max uC vC)) [CommRing Λ] {R : Sheaf K RingCat.{max uC vC}}
  (η : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)

private def scalarPresheaf (F : SheafOfModules.{max uC vC} R) :
    Cᵒᵖ ⥤ ModuleCat.{max uC vC} Λ where
  obj U := ((PresheafOfModules.restrictScalars η).obj F.val).obj U
  map f := ((PresheafOfModules.restrictScalars η).obj F.val).map f
  map_id U := by ext x; simp; rfl
  map_comp f g := by ext x; simp; rfl

private def scalarSheaf : SheafOfModules.{max uC vC} R ⥤ Sheaf K (ModuleCat.{max uC vC} Λ) where
  obj F := ⟨scalarPresheaf K Λ η F,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat Λ) AddCommGrpCat) F.isSheaf⟩
  map f := ⟨{ app := fun U ↦ ((PresheafOfModules.restrictScalars η).map f.val).app U,
              naturality := by
                intro U V g
                ext x
                exact PresheafOfModules.naturality_apply
                  ((PresheafOfModules.restrictScalars η).map f.val) g x }⟩

private def scalarSheafFullyFaithful [Presheaf.IsLocallySurjective K η] :
    (scalarSheaf K Λ η).FullyFaithful where
  preimage {F G} f := by
    refine ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective (J := K) η G.isSheaf).symm ?_⟩
    exact { app := f.hom.app
            naturality := fun g ↦ by ext x; exact NatTrans.naturality_apply f.hom g x }
  map_preimage f := by ext U x; rfl
  preimage_map {F G} f := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.restrictHomEquivOfIsLocallySurjective (J := K) η G.isSheaf).injective
    ext U x
    rfl

private def constantLinearUnit [Presheaf.IsLocallyInjective K η]
    [Presheaf.IsLocallySurjective K η] (M : ModuleCat.{max uC vC} Λ) :
    (Functor.const Cᵒᵖ).obj M ⟶
      scalarPresheaf K Λ η ((PresheafOfModules.sheafification η).obj
        ((siteConstantModulePresheafGeneral (C := C) Λ).obj M)) where
  app U := (PresheafOfModules.toSheafify η
    (toSheafify K ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf)).app U
  naturality := by
    intro U V f
    ext x
    exact NatTrans.naturality_apply
      (toSheafify K ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf) f x

private def constantScalarIso [Presheaf.IsLocallyInjective K η]
    [Presheaf.IsLocallySurjective K η] (M : ModuleCat.{max uC vC} Λ) :
    (constantSheaf K (ModuleCat Λ)).obj M ≅
      (scalarSheaf K Λ η).obj ((PresheafOfModules.sheafification η).obj
        ((siteConstantModulePresheafGeneral (C := C) Λ).obj M)) := by
  let a := constantLinearUnit K Λ η M
  let φ : (constantSheaf K (ModuleCat Λ)).obj M ⟶
      (scalarSheaf K Λ η).obj ((PresheafOfModules.sheafification η).obj
        ((siteConstantModulePresheafGeneral (C := C) Λ).obj M)) :=
    ⟨sheafifyLift K a ((scalarSheaf K Λ η).obj _).property⟩
  have hi : Presheaf.IsLocallyInjective K a := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem K
      (toSheafify K ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf) x y h
  have hs : Presheaf.IsLocallySurjective K a := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem K
      (toSheafify K ((siteConstantModulePresheafGeneral (C := C) Λ).obj M).presheaf) x
  have he : toSheafify K _ ≫ φ.hom = a := toSheafify_sheafifyLift _ _ _
  have : IsIso φ := by
    rw [← Sheaf.isLocallyBijective_iff_isIso φ]
    rw [← he] at hi hs
    exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp hi,
      (Presheaf.comp_isLocallySurjective_iff _ _ _).mp hs⟩
  exact asIso φ

end ScalarRestriction

section SliceConstants

variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  {Λ : Type (max uC vC)} [CommRing Λ]

private def overConstantIso (M : ModuleCat.{max uC vC} Λ) (U : C) :
    (constantSheaf (K.over U) (ModuleCat Λ)).obj M ≅
      ((constantSheaf K (ModuleCat Λ)).obj M).over U :=
  ((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat Λ) (K.over U) K).app ((Functor.const Cᵒᵖ).obj M)

private def iteratedConstantIso {T : C} (f : Over T) (M : ModuleCat.{max uC vC} Λ) :
    (constantSheaf (K.over f.left) (ModuleCat Λ)).obj M ≅
      (f.iteratedSliceBackward.sheafPushforwardContinuous (ModuleCat Λ)
        (K.over f.left) ((K.over T).over f)).obj
          ((constantSheaf ((K.over T).over f) (ModuleCat Λ)).obj M) :=
  (f.iteratedSliceBackward.pushforwardContinuousSheafificationCompatibility
    (ModuleCat Λ) (K.over f.left) ((K.over T).over f)).app
      ((Functor.const (Over f)ᵒᵖ).obj M)

private def ringedModelIso {R : Sheaf K RingCat.{max uC vC}}
    (η : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective K η] [Presheaf.IsLocallySurjective K η]
    (F : SheafOfModules.{max uC vC} R) (U : C) (M : ModuleCat.{max uC vC} Λ)
    (e : ((scalarSheaf K Λ η).obj F).over U ≅
      (constantSheaf (K.over U) (ModuleCat Λ)).obj M) :
    F.over U ≅ ((PresheafOfModules.sheafification η).obj
      ((siteConstantModulePresheafGeneral (C := C) Λ).obj M)).over U := by
  let ηU : (Functor.const (Over U)ᵒᵖ).obj (RingCat.of Λ) ⟶ (R.over U).obj :=
    Functor.whiskerLeft (Over.forget U).op η
  have : Presheaf.IsLocallySurjective (K.over U) ηU :=
    Presheaf.isLocallySurjective_whisker (K.over U) K (Over.forget U) η
  apply (scalarSheafFullyFaithful (K.over U) Λ (R := R.over U) ηU).preimageIso
  exact e ≪≫ overConstantIso K M U ≪≫
    (K.overPullback (ModuleCat Λ) U).mapIso (constantScalarIso K Λ η M)

end SliceConstants

section FiniteRefinement

open CategoryTheory.Sheaf.ConstantForget

variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  {Λ : Type (max uC vC)} [CommRing Λ] [Finite Λ]
  {F : Sheaf K (ModuleCat.{max uC vC} Λ)} {X : Type (max uC vC)} [Finite X]

-- The construction of ConstantForget, retaining its actual finite image module.
private theorem finite_constant_refinement
    (e : (sheafCompose K (CategoryTheory.forget (ModuleCat.{max uC vC} Λ))).obj F ≅
      (constantSheaf K (Type (max uC vC))).obj X) (T : C) :
    ∃ S ∈ K T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f →
      ∃ M : ModuleCat.{max uC vC} Λ, Finite M ∧
        Nonempty (F.over U ≅ (constantSheaf (K.over U) (ModuleCat Λ)).obj M) := by
  classical
  let : Fintype ((X × X) ⊕ (Λ × X) ⊕ Unit) := Fintype.ofFinite _
  -- the finitely many sections whose restrictions have to be of the form `σ_z`
  let t : (X × X) ⊕ (Λ × X) ⊕ Unit → F.obj.obj (op T)
    | .inl p => σ e T p.1 + σ e T p.2
    | .inr (.inl p) => p.1 • σ e T p.2
    | .inr (.inr _) => 0
  let Si : (X × X) ⊕ (Λ × X) ⊕ Unit → Sieve T := fun i ↦
    Presheaf.imageSieve (toSheafify K ((Functor.const Cᵒᵖ).obj X)) (e.hom.hom.app (op T) (t i))
  have hSi : ∀ i, Si i ∈ K T := fun i ↦ Presheaf.imageSieve_mem K _ _
  refine ⟨Finset.univ.inf Si, K.finsetInf_mem _ _ hSi, fun U f hf ↦ ?_⟩
  have hf' : ∀ i, ∃ z, F.obj.map f.op (t i) = F.obj.map f.op (σ e T z) := fun i ↦
    exists_eq_map_σ e (t i) f (Finset.inf_le (Finset.mem_univ i) (f := Si) _ hf)
  let ρ : F.obj.obj (op T) →ₗ[Λ] F.obj.obj (op U) := (F.obj.map f.op).hom
  -- the restrictions of the `σ_x` form a submodule `N` of `F(U)`
  let N : Submodule Λ (F.obj.obj (op U)) :=
    { carrier := Set.range fun x ↦ ρ (σ e T x)
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        obtain ⟨z, hz⟩ := hf' (.inl (x, y))
        exact ⟨z, by rw [← map_add]; exact hz.symm⟩
      zero_mem' := by
        obtain ⟨z, hz⟩ := hf' (.inr (.inr ()))
        exact ⟨z, by rw [← map_zero ρ]; exact hz.symm⟩
      smul_mem' := by
        rintro c _ ⟨x, rfl⟩
        obtain ⟨z, hz⟩ := hf' (.inr (.inl (c, x)))
        exact ⟨z, by rw [← map_smul]; exact hz.symm⟩ }
  -- the morphism from the constant presheaf at `N` to `F|_U`
  let α : (Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N) ⟶ (F.over U).obj :=
    { app V := ModuleCat.ofHom ((F.obj.map V.unop.hom.op).hom ∘ₗ N.subtype)
      naturality V W g := by
        ext n
        change F.obj.map W.unop.hom.op n.1 = F.obj.map g.unop.left.op (F.obj.map V.unop.hom.op n.1)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w] }
  let φ : (constantSheaf (K.over U) (ModuleCat.{max uC vC} Λ)).obj (ModuleCat.of Λ N) ⟶ F.over U :=
    ⟨sheafifyLift (K.over U) α (F.over U).property⟩
  have hφ : toSheafify (K.over U) _ ≫ φ.hom = α := toSheafify_sheafifyLift _ _ _
  -- the restriction of the sheafification map of the constant presheaf at `X`
  let τ := Functor.whiskerLeft (Over.forget U).op
    (toSheafify K ((Functor.const Cᵒᵖ).obj X))
  have : Presheaf.IsLocallyInjective K (toSheafify K ((Functor.const Cᵒᵖ).obj X)) :=
    (K.W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective K (toSheafify K ((Functor.const Cᵒᵖ).obj X)) :=
    (K.W_toSheafify _).isLocallySurjective
  have hτi : Presheaf.IsLocallyInjective (K.over U) τ :=
    Presheaf.isLocallyInjective_whisker (K.over U) K (Over.forget U) _
  have hτs : Presheaf.IsLocallySurjective (K.over U) τ :=
    Presheaf.isLocallySurjective_whisker (K.over U) K (Over.forget U) _
  -- the value of `α` on the restriction of `σ_x`
  have hα (V : (Over U)ᵒᵖ) (x : X) :
      e.hom.hom.app (op V.unop.left) (α.app V ⟨ρ (σ e T x), x, rfl⟩) = τ.app V x := by
    change e.hom.hom.app (op V.unop.left)
      (F.obj.map V.unop.hom.op (F.obj.map f.op (σ e T x))) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact hom_app_map_σ e _ x
  have hαi : Presheaf.IsLocallyInjective (K.over U) α := by
    refine ⟨fun {V} n₁ n₂ h ↦ ?_⟩
    obtain ⟨x₁, hx₁⟩ := n₁.2
    obtain ⟨x₂, hx₂⟩ := n₂.2
    have e₁ : n₁ = ⟨ρ (σ e T x₁), x₁, rfl⟩ := Subtype.ext hx₁.symm
    have e₂ : n₂ = ⟨ρ (σ e T x₂), x₂, rfl⟩ := Subtype.ext hx₂.symm
    have h' : τ.app V x₁ = τ.app V x₂ := by
      rw [← hα, ← hα, ← e₁, ← e₂, h]
    refine K.over U |>.superset_covering ?_ (Presheaf.equalizerSieve_mem _ τ x₁ x₂ h')
    intro W g (hg : x₁ = x₂)
    change ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N)).map g.op n₁ =
      ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N)).map g.op n₂
    rw [e₁, e₂, hg]
  have hαs : Presheaf.IsLocallySurjective (K.over U) α := by
    refine ⟨fun {V} s ↦ ?_⟩
    refine K.over U |>.superset_covering ?_
      (Presheaf.imageSieve_mem _ τ (e.hom.hom.app (op V.left) s))
    rintro W g ⟨x, hx⟩
    refine ⟨⟨ρ (σ e T x), x, rfl⟩, injective_hom_app e W.left ?_⟩
    rw [hα]
    exact hx.trans (NatTrans.naturality_apply e.hom.hom g.left.op s).symm
  have : Presheaf.IsLocallyInjective (K.over U)
      (toSheafify (K.over U) ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N))) :=
    ((K.over U).W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective (K.over U)
      (toSheafify (K.over U) ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N))) :=
    ((K.over U).W_toSheafify _).isLocallySurjective
  have : IsIso φ := by
    rw [← Sheaf.isLocallyBijective_iff_isIso φ]
    rw [← hφ] at hαi hαs
    exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp hαi,
      (Presheaf.comp_isLocallySurjective_iff _ _ _).mp hαs⟩
  have : Finite N := Set.finite_range (fun x ↦ ρ (σ e T x))
  exact ⟨ModuleCat.of Λ N, inferInstance, ⟨(asIso φ).symm⟩⟩

end FiniteRefinement

section LocalRefinement

variable {C : Type uC} [Category.{vC} C] (K : GrothendieckTopology C)
  {Λ : Type (max uC vC)} [CommRing Λ] [Finite Λ]
  (G : Sheaf K (ModuleCat.{max uC vC} Λ))

private theorem finite_trivialization_refinement {T : C} {X : Type (max uC vC)} [Finite X]
    (e : ((sheafCompose K (CategoryTheory.forget (ModuleCat Λ))).obj G).over T ≅
      (constantSheaf (K.over T) (Type (max uC vC))).obj X) :
    ∃ S ∈ K T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f →
      ∃ M : ModuleCat.{max uC vC} Λ, Finite M ∧
        Nonempty (G.over U ≅ (constantSheaf (K.over U) (ModuleCat Λ)).obj M) := by
  obtain ⟨S, hS, h⟩ :=
    finite_constant_refinement (K.over T) (F := G.over T) (Λ := Λ) e (Over.mk (𝟙 T))
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 T)) S, hS, fun U f hf ↦ ?_⟩
  let V : Over T := Over.mk (f ≫ 𝟙 T)
  let g : V ⟶ Over.mk (𝟙 T) := Over.homMk f rfl
  obtain ⟨M, hM, ⟨eM⟩⟩ := h g ((Sieve.overEquiv_iff _ _).mp hf)
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (V.iteratedSliceBackward.sheafPushforwardContinuous (ModuleCat Λ)
    (K.over V.left) ((K.over T).over V)).mapIso eM ≪≫ (iteratedConstantIso K V M).symm

end LocalRefinement

private theorem covering_refinement {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) {U : C} {S : Sieve U}
    (hS : S ∈ J.toGrothendieck U) : ∃ T ∈ J U, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : C, {a : Z ⟶ X // R a}
    let V : I → C := fun i ↦ i.1
    let a : ∀ i : I, V i ⟶ X := fun i ↦ i.2.1
    have heq : Presieve.ofArrows V a = R := by
      funext Z b
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.2.2
      · intro hb
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨Z, b, hb⟩
    obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 I X V a (heq ▸ hR) Y f
    refine ⟨Presieve.ofArrows P p, hp, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hle _ _ i.2.2) (q i)
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have hh : ∀ (Y : C) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg

/-- A module sheaf over a finite constant ring is locally a finite constant module if
its underlying set sheaf is finite locally constant.

Source: Stacks Project, Modules on Sites, Tag 093S, finite-operation refinement, and
Sites, Tag 00WK (blueprint: lem-sp-finite-ring-action-local-constancy).

Proof:
1. Fix an object and a cover trivializing the underlying set sheaf by a finite set S.
   Work on each slice. Constant sheaves restrict to slice constants compatibly with
   their unit sections (lem-cbc-sieve-slice-sheafification). Let sigma_s be the sections
   labelled by S; their restrictions retain these labels.
2. Apply local representation (lem-weil-pbc-site-sheafification-sections-local) to zero,
   all sums sigma_s + sigma_t, and all scalar multiples lambda sigma_s. The two sets
   of labels and scalars are finite. Successive base changes and compositions of
   covers give a common refinement on which each section has a label. Including zero
   handles S empty: its representation can give an empty covering.
3. On a member W, the actual image of S in F(W) is a finite Lambda-submodule M:
   zero, addition and scalar multiplication are closed, and negatives use scalar -1.
   Restrictions define a natural linear map from the constant module presheaf M
   to F restricted to W. No injectivity of the labels in F(W) is required.
4. Module sheafification extends this map to a map of module sheaves
   (lem-pc-sites-module-sheafification-interface). Slice compatibility identifies the
   coefficient sheaf with the restricted constant ring. Forgetting to sets identifies
   this map with set sheafification (lem-pc-sites-sheafification-underlying-sets).
5. The presheaf map is locally surjective by local representation of labels. It is
   locally injective by local equality of labels in set sheafification, using
   lem-weil-pbc-site-sheafification-sections-local. Distinct labels can become equal
   on an empty-covered object; the resulting empty cover suffices. Thus the sheaf map
   is an isomorphism by lem-cbc-set-presheaf-sheafification-local-bijection.
6. The inverse is linear and natural by cancellation with the bijective linear map.
   Compose with the initial covers and relocalize (def-pur-localized-ringed-site).
   This proves the claim without points or nonempty objects, including the zero ring.

The constant module on the slice is the restriction of the recorded
`CategoryTheory.commutativeSiteConstantModuleFunctor`: module sheafification of the
identity-restriction constant module presheaf along the constant commutative ring
sheafification unit with commutativity forgotten. Constant sheafification commutes
with localization by lem-cbc-sieve-slice-sheafification. Site objects and morphisms
have independent universes; coefficient sets and modules lie in their maximum. -/
theorem finite_ring_action_local_constancy
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (Λ : Type (max uC vC)) [CommRing Λ] [Finite Λ]
    (F : CategoryTheory.ringedSiteModules.{max uC vC}
      ((sheafCompose J.toGrothendieck
        (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})).obj
          ((constantSheaf J.toGrothendieck CommRingCat.{max uC vC}).obj
            (CommRingCat.of Λ))))
    (hF : ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ X : Type (max uC vC), Finite X ∧
          Nonempty
            ((((sheafCompose J.toGrothendieck
                (CategoryTheory.forget AddCommGrpCat.{max uC vC})).obj
              ((SheafOfModules.toSheaf _).obj F)).over V) ≅
              (constantSheaf (J.toGrothendieck.over V) (Type (max uC vC))).obj X)) :
    ∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ M : ModuleCat.{max uC vC} Λ, Finite M ∧
          Nonempty (F.over V ≅
            ((commutativeSiteConstantModuleFunctor J.toGrothendieck Λ).obj M).over V) := by
  classical
  let K := J.toGrothendieck
  let η := realizationRingUnit K Λ
  have : Presheaf.IsLocallyInjective K η := (realizationRingUnit_locallyBijective K Λ).1
  have : Presheaf.IsLocallySurjective K η := (realizationRingUnit_locallyBijective K Λ).2
  let G := (scalarSheaf K Λ η).obj F
  intro U
  obtain ⟨S, hS, h⟩ := hF U
  have hh : ∀ (V : C) (f : V ⟶ U) (_ : S f),
      ∃ Q : Presieve V, Q ∈ J V ∧
        ∀ (W : C) (g : W ⟶ V), Q g →
          ∃ M : ModuleCat.{max uC vC} Λ, Finite M ∧
            Nonempty (F.over W ≅
              ((commutativeSiteConstantModuleFunctor K Λ).obj M).over W) := by
    intro V f hf
    obtain ⟨X, hX, ⟨e⟩⟩ := h V f hf
    have : Finite X := hX
    obtain ⟨A, hA, hAM⟩ := finite_trivialization_refinement K G e
    obtain ⟨Q, hQ, hQA⟩ := covering_refinement J hJ hA
    refine ⟨Q, hQ, fun W g hg ↦ ?_⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := hAM g (hQA _ _ hg)
    exact ⟨M, hM, ⟨ringedModelIso K η F W M eM⟩⟩
  choose Q hQ hQM using hh
  refine ⟨S.bind (fun {V f} hf ↦ Q V f hf),
    hJ.2.1 U S (fun {V} f hf ↦ Q V f hf) hS hQ, ?_⟩
  intro W g hg
  obtain ⟨V, a, f, hf, ha, rfl⟩ := hg
  exact hQM V f hf W a ha

end

end SheafOfModules
