import Langlands.Sheaf.Renard.ClosedRestrictionExactStatements
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Restriction of a complex vector sheaf to a subset

Renard (9 July 2026), II.2.5, printed p.42 / PDF p.48: for a sheaf `F` on `X` and a locally
closed subset `Y`, the restriction `F|_Y` is the sheaf on `Y` whose fibre at `y` is `F_y` and
whose sections over an open `U` of `Y` are those which, near each point of `U`, coincide with
the restriction of a section of `F`.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.LocallyClosedRestriction

open CategoryTheory TopologicalSpace Opposite Limits
open VectorSheafScalars (VectorSheaf)

universe u

variable {X : Type u} [TopologicalSpace X]

section Construction

variable (F : VectorSheaf X) (Y : Set X)

/-- The fibre of `F|_Y` at `y ∈ Y`: the stalk `F_y`. -/
abbrev Fiber (y : TopCat.of Y) : Type u :=
  F.presheaf.stalk (y.1 : X)

/-- A family of germs over an open `V` of `Y` which is the family of germs of one section of
`F` over an open `W` of `X` containing `V`. -/
def isRestrictedGerm : TopCat.PrelocalPredicate (Fiber F Y) where
  pred {V} f := ∃ (W : Opens X) (t : F.presheaf.obj (op W)) (hW : ∀ y : V, (y.1.1 : X) ∈ W),
    ∀ y : V, f y = F.presheaf.germ W y.1.1 (hW y) t
  res i f := by
    rintro ⟨W, t, hW, h⟩
    exact ⟨W, t, fun y => hW ⟨y.1, i.le y.2⟩, fun y => h ⟨y.1, i.le y.2⟩⟩

/-- Renard's condition: near each point, the family coincides with the restriction of a
section of `F`. -/
def isLocallyRestrictedGerm : TopCat.LocalPredicate (Fiber F Y) :=
  (isRestrictedGerm F Y).sheafify

variable {F Y}

theorem isRestrictedGerm_zero (V : Opens (TopCat.of Y)) :
    (isRestrictedGerm F Y).pred (fun y : V => (0 : Fiber F Y y)) :=
  ⟨⊤, 0, fun _ => trivial, fun _ => (map_zero _).symm⟩

theorem isLocallyRestrictedGerm_add {V : Opens (TopCat.of Y)} {f g : ∀ y : V, Fiber F Y y}
    (hf : (isLocallyRestrictedGerm F Y).pred f) (hg : (isLocallyRestrictedGerm F Y).pred g) :
    (isLocallyRestrictedGerm F Y).pred (fun y => f y + g y) := by
  refine TopCat.PrelocalPredicate.sheafify_inductionOn₂' (isRestrictedGerm F Y)
    (isRestrictedGerm F Y) (isRestrictedGerm F Y) (fun a b => a + b) ?_ hf hg
  rintro U V a b ⟨W₁, t₁, h₁, e₁⟩ ⟨W₂, t₂, h₂, e₂⟩
  refine ⟨W₁ ⊓ W₂, F.presheaf.map (homOfLE inf_le_left).op t₁ +
    F.presheaf.map (homOfLE inf_le_right).op t₂,
    fun y => ⟨h₁ ⟨y.1, (Opens.mem_inf.mp y.2).1⟩, h₂ ⟨y.1, (Opens.mem_inf.mp y.2).2⟩⟩,
    fun y => ?_⟩
  have hy : (y.1.1 : X) ∈ W₁ ⊓ W₂ :=
    ⟨h₁ ⟨y.1, (Opens.mem_inf.mp y.2).1⟩, h₂ ⟨y.1, (Opens.mem_inf.mp y.2).2⟩⟩
  refine (congrArg₂ (· + ·)
    ((e₁ ⟨y.1, (Opens.mem_inf.mp y.2).1⟩).trans
      (TopCat.Presheaf.germ_res_apply F.presheaf
        (homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁)) y.1.1 hy t₁).symm)
    ((e₂ ⟨y.1, (Opens.mem_inf.mp y.2).2⟩).trans
      (TopCat.Presheaf.germ_res_apply F.presheaf
        (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)) y.1.1 hy t₂).symm)).trans ?_
  exact (map_add _ _ _).symm

theorem isLocallyRestrictedGerm_smul {V : Opens (TopCat.of Y)} (c : ℂ)
    {f : ∀ y : V, Fiber F Y y} (hf : (isLocallyRestrictedGerm F Y).pred f) :
    (isLocallyRestrictedGerm F Y).pred (fun y => c • f y) := by
  refine TopCat.PrelocalPredicate.sheafify_inductionOn' (isRestrictedGerm F Y)
    (fun a => c • a) ?_ hf
  rintro U a ⟨W, t, hW, e⟩
  exact ⟨W, c • t, hW, fun y =>
    (congrArg (fun v => c • v) (e y)).trans (map_smul _ c t).symm⟩

variable (F Y)

/-- The sections of `F|_Y` over an open `V` of `Y`, a complex subspace of the families of
germs. -/
def sections (V : Opens (TopCat.of Y)) : Submodule ℂ (∀ y : V, Fiber F Y y) where
  carrier := {f | (isLocallyRestrictedGerm F Y).pred f}
  add_mem' hf hg := isLocallyRestrictedGerm_add hf hg
  zero_mem' := TopCat.PrelocalPredicate.sheafifyOf (isRestrictedGerm_zero V)
  smul_mem' c _ hf := isLocallyRestrictedGerm_smul c hf

theorem mem_sections_iff {V : Opens (TopCat.of Y)} (f : ∀ y : V, Fiber F Y y) :
    f ∈ sections F Y V ↔ (isLocallyRestrictedGerm F Y).pred f :=
  Iff.rfl

/-- Restriction of families of germs to a smaller open of `Y`. -/
def restrictLinear {V V' : Opens (TopCat.of Y)} (i : V' ⟶ V) :
    sections F Y V →ₗ[ℂ] sections F Y V' where
  toFun f := ⟨fun y => f.1 ⟨y.1, i.le y.2⟩, (isLocallyRestrictedGerm F Y).res i f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The presheaf of complex vector spaces of `F|_Y`. -/
def presheaf : TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of Y) where
  obj V := ModuleCat.of ℂ (sections F Y V.unop)
  map i := ModuleCat.ofHom (restrictLinear F Y i.unop)
  map_id _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    rfl

/-- Forgetting the vector space structure gives Mathlib's presheaf of families satisfying the
local predicate. -/
def underlyingIso : presheaf F Y ⋙ forget (ModuleCat.{u} ℂ) ≅
    TopCat.subpresheafToTypes (isLocallyRestrictedGerm F Y).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun f => ⟨f.1, f.2⟩)
      inv := TypeCat.ofHom (fun f => ⟨f.1, f.2⟩) }) (by
    intro U V i
    apply ConcreteCategory.hom_ext
    intro f
    rfl)

theorem presheaf_isSheaf : (presheaf F Y).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget (ModuleCat.{u} ℂ))]
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff (underlyingIso F Y)).mpr
    (TopCat.subpresheafToTypes.isSheaf (isLocallyRestrictedGerm F Y))

/-- Renard's restriction `F|_Y` of a complex vector sheaf to a subset `Y`. -/
def restrict : VectorSheaf Y :=
  ⟨presheaf F Y, presheaf_isSheaf F Y⟩

theorem restrict_map_apply {V V' : Opens (TopCat.of Y)} (i : V' ⟶ V)
    (f : (restrict F Y).presheaf.obj (op V)) (y : V') :
    ((restrict F Y).presheaf.map i.op f).1 y = f.1 ⟨y.1, i.le y.2⟩ :=
  rfl

end Construction

/-! ## Restriction of sections of `F` -/

section Sections

variable (F : VectorSheaf X) (Y : Set X)

/-- The open `W ∩ Y` of `Y`. -/
def traceOpen (W : Opens X) : Opens (TopCat.of Y) :=
  ⟨Subtype.val ⁻¹' (W : Set X), W.isOpen.preimage continuous_subtype_val⟩

theorem mem_traceOpen {W : Opens X} {y : Y} : y ∈ traceOpen Y W ↔ (y : X) ∈ W :=
  Iff.rfl

/-- The restriction to `W ∩ Y` of a section of `F` over `W`: its family of germs. -/
def restrictSection (W : Opens X) : F.presheaf.obj (op W) →ₗ[ℂ]
    (restrict F Y).presheaf.obj (op (traceOpen Y W)) where
  toFun t := ⟨fun y => F.presheaf.germ W y.1.1 y.2 t,
    TopCat.PrelocalPredicate.sheafifyOf (P := isRestrictedGerm F Y)
      ⟨W, t, fun y => y.2, fun _ => rfl⟩⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext y
    exact map_add _ _ _
  map_smul' _ _ := by
    apply Subtype.ext
    funext y
    exact map_smul _ _ _

theorem restrictSection_apply (W : Opens X) (t : F.presheaf.obj (op W))
    (y : traceOpen Y W) :
    (restrictSection F Y W t).1 y = F.presheaf.germ W y.1.1 y.2 t :=
  rfl

end Sections

/-! ## Stalks: `(F|_Y)_y = F_y` -/

section Stalks

variable (F : VectorSheaf X) (Y : Set X)

/-- Evaluation at `y` of the families of germs. -/
def evalLinear (y : TopCat.of Y) (V : TopologicalSpace.OpenNhds y) :
    (restrict F Y).presheaf.obj (op V.1) →ₗ[ℂ] F.presheaf.stalk (y.1 : X) where
  toFun f := f.1 ⟨y, V.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cocone of evaluations at `y`. -/
def evalCocone (y : TopCat.of Y) :
    Cocone ((TopologicalSpace.OpenNhds.inclusion y).op ⋙ (restrict F Y).presheaf) where
  pt := F.presheaf.stalk (y.1 : X)
  ι :=
    { app := fun V => ModuleCat.ofHom (evalLinear F Y y V.unop)
      naturality := by
        intro V V' i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        rfl }

/-- The map from the stalk of `F|_Y` at `y` to the fibre `F_y`, evaluating families of germs. -/
def stalkToFiber (y : TopCat.of Y) :
    (restrict F Y).presheaf.stalk y ⟶ F.presheaf.stalk (y.1 : X) :=
  colimit.desc _ (evalCocone F Y y)

theorem stalkToFiber_germ (V : Opens (TopCat.of Y)) (y : TopCat.of Y) (hy : y ∈ V)
    (f : (restrict F Y).presheaf.obj (op V)) :
    stalkToFiber F Y y ((restrict F Y).presheaf.germ V y hy f) = f.1 ⟨y, hy⟩ :=
  congrArg (fun φ : ((TopologicalSpace.OpenNhds.inclusion y).op ⋙ (restrict F Y).presheaf).obj
      (op ⟨V, hy⟩) ⟶ F.presheaf.stalk (y.1 : X) => ConcreteCategory.hom φ f)
    (colimit.ι_desc (evalCocone F Y y) (op ⟨V, hy⟩ : (TopologicalSpace.OpenNhds y)ᵒᵖ))

theorem stalkToFiber_restrictSection (W : Opens X) (t : F.presheaf.obj (op W))
    (y : TopCat.of Y) (hy : y ∈ traceOpen Y W) :
    stalkToFiber F Y y ((restrict F Y).presheaf.germ (traceOpen Y W) y hy
      (restrictSection F Y W t)) = F.presheaf.germ W y.1 hy t :=
  stalkToFiber_germ F Y (traceOpen Y W) y hy (restrictSection F Y W t)

theorem stalkToFiber_surjective (y : TopCat.of Y) :
    Function.Surjective (stalkToFiber F Y y) := by
  intro s
  obtain ⟨W, hyW, t, rfl⟩ := F.presheaf.exists_germ_eq s
  exact ⟨_, stalkToFiber_restrictSection F Y W t y hyW⟩

theorem stalkToFiber_injective (y : TopCat.of Y) :
    Function.Injective (stalkToFiber F Y y) := by
  intro s s' h
  obtain ⟨V, hy, f, rfl⟩ := (restrict F Y).presheaf.exists_germ_eq s
  obtain ⟨V', hy', f', rfl⟩ := (restrict F Y).presheaf.exists_germ_eq s'
  rw [stalkToFiber_germ, stalkToFiber_germ] at h
  obtain ⟨V₁, hy₁, i₁, W₁, t₁, hW₁, e₁⟩ := f.2 ⟨y, hy⟩
  obtain ⟨V₂, hy₂, i₂, W₂, t₂, hW₂, e₂⟩ := f'.2 ⟨y, hy'⟩
  have hgerm : F.presheaf.germ W₁ y.1 (hW₁ ⟨y, hy₁⟩) t₁ =
      F.presheaf.germ W₂ y.1 (hW₂ ⟨y, hy₂⟩) t₂ :=
    (e₁ ⟨y, hy₁⟩).symm.trans (h.trans (e₂ ⟨y, hy₂⟩))
  obtain ⟨W, hyW, iW₁, iW₂, ht⟩ := F.presheaf.germ_eq y.1 _ _ t₁ t₂ hgerm
  let V₃ : Opens (TopCat.of Y) := V₁ ⊓ V₂ ⊓ traceOpen Y W
  have hV₃ : y ∈ V₃ := ⟨⟨hy₁, hy₂⟩, hyW⟩
  refine TopCat.Presheaf.germ_ext (restrict F Y).presheaf V₃ hV₃
    (homOfLE (inf_le_left.trans inf_le_left) ≫ i₁)
    (homOfLE (inf_le_left.trans inf_le_right) ≫ i₂) ?_
  apply Subtype.ext
  funext z
  have hz₁ : z.1 ∈ V₁ := z.2.1.1
  have hz₂ : z.1 ∈ V₂ := z.2.1.2
  have hzW : (z.1.1 : X) ∈ W := z.2.2
  refine (e₁ ⟨z.1, hz₁⟩).trans (Eq.trans ?_ (e₂ ⟨z.1, hz₂⟩).symm)
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf iW₁ _ hzW,
    ← TopCat.Presheaf.germ_res_apply F.presheaf iW₂ _ hzW, ht]

/-- Renard: the fibre of `F|_Y` at `y` is the fibre `F_y`. -/
def stalkIso (y : TopCat.of Y) :
    (restrict F Y).presheaf.stalk y ≅ F.presheaf.stalk (y.1 : X) :=
  (LinearEquiv.ofBijective (stalkToFiber F Y y).hom
    ⟨stalkToFiber_injective F Y y, stalkToFiber_surjective F Y y⟩).toModuleIso

theorem stalkIso_hom (y : TopCat.of Y) : (stalkIso F Y y).hom = stalkToFiber F Y y :=
  rfl

end Stalks

/-! ## Functoriality -/

section Functor

variable {F G H : VectorSheaf X} (Y : Set X)

/-- A morphism of sheaves acts on families of germs through its stalk maps. -/
def mapSections (φ : F ⟶ G) (V : Opens (TopCat.of Y)) :
    (restrict F Y).presheaf.obj (op V) →ₗ[ℂ] (restrict G Y).presheaf.obj (op V) where
  toFun f := ⟨fun y => (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) y.1.1).map φ.hom (f.1 y),
    by
      intro y
      obtain ⟨V₁, hy₁, i₁, W, t, hW, e⟩ := f.2 y
      refine ⟨V₁, hy₁, i₁, W, φ.hom.app (op W) t, hW, fun z => ?_⟩
      exact (congrArg ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) z.1.1).map φ.hom) (e z)).trans
        (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _)⟩
  map_add' _ _ := by
    apply Subtype.ext
    funext y
    exact map_add _ _ _
  map_smul' _ _ := by
    apply Subtype.ext
    funext y
    exact map_smul _ _ _

theorem mapSections_apply (φ : F ⟶ G) (V : Opens (TopCat.of Y))
    (f : (restrict F Y).presheaf.obj (op V)) (y : V) :
    (mapSections Y φ V f).1 y =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) y.1.1).map φ.hom (f.1 y) :=
  rfl

/-- The morphism `F|_Y ⟶ G|_Y` induced by `F ⟶ G`. -/
def restrictMap (φ : F ⟶ G) : restrict F Y ⟶ restrict G Y :=
  ObjectProperty.homMk
    { app := fun V => ModuleCat.ofHom (mapSections Y φ V.unop)
      naturality := by
        intro V V' i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        rfl }

variable (X) in
/-- Restriction to `Y` as a functor from complex vector sheaves on `X` to those on `Y`. -/
def restrictFunctor : VectorSheaf X ⥤ VectorSheaf Y where
  obj F := restrict F Y
  map φ := restrictMap Y φ
  map_id F := by
    apply Sheaf.hom_ext
    ext V f
    apply Subtype.ext
    funext y
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) y.1.1).map (𝟙 F.presheaf) (f.1 y) = f.1 y
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    apply Sheaf.hom_ext
    ext V f
    apply Subtype.ext
    funext y
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) y.1.1).map (φ.hom ≫ ψ.hom) (f.1 y) =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) y.1.1).map ψ.hom
        ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) y.1.1).map φ.hom (f.1 y))
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- Restriction of sections commutes with morphisms. -/
theorem mapSections_restrictSection (φ : F ⟶ G) (W : Opens X) (t : F.presheaf.obj (op W)) :
    mapSections Y φ (traceOpen Y W) (restrictSection F Y W t) =
      restrictSection G Y W (φ.hom.app (op W) t) := by
  apply Subtype.ext
  funext y
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _

end Functor


/-! ## Comparison with the published compact sections over a subset -/

section Compact

variable {X₀ : Type} [TopologicalSpace X₀] (F : VectorSheaf X₀) (Z : Set X₀)

/-- A family of germs over `Z` as a family over the top open of `Z`. -/
abbrev topFamily (t : ∀ z : Z, F.presheaf.stalk (z : X₀)) :
    ∀ y : (⊤ : Opens (TopCat.of Z)), Fiber F Z y :=
  fun y => t y.1

/-- The published predicate `ClosedRestriction.IsLocalRestriction` says exactly that a family of
germs over `Z` is a global section of `F|_Z`. -/
theorem isLocalRestriction_iff (t : ∀ z : Z, F.presheaf.stalk (z : X₀)) :
    ClosedRestriction.IsLocalRestriction F Z t ↔ topFamily F Z t ∈ sections F Z ⊤ := by
  constructor
  · intro ht y
    obtain ⟨V, hyV, σ, hσ⟩ := ht y.1
    exact ⟨traceOpen Z V, hyV, homOfLE le_top, V, σ, fun z => z.2,
      fun z => (hσ z.1 z.2).symm⟩
  · intro ht z
    obtain ⟨V₁, hz₁, i₁, W, σ, hW, e⟩ := ht ⟨z, trivial⟩
    obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp V₁.isOpen
    have hzO : (z : X₀) ∈ O := by
      have : z ∈ (V₁ : Set Z) := hz₁
      rw [← hOV] at this
      exact this
    refine ⟨⟨O, hO⟩ ⊓ W, ⟨hzO, hW ⟨z, hz₁⟩⟩,
      F.presheaf.map (homOfLE (inf_le_right : ⟨O, hO⟩ ⊓ W ≤ W)).op σ, fun y hy => ?_⟩
    have hy₁ : y ∈ V₁ := by
      change y ∈ (V₁ : Set Z)
      rw [← hOV]
      exact hy.1
    rw [TopCat.Presheaf.germ_res_apply]
    exact (e ⟨y, hy₁⟩).symm

/-- A global germ of `F|_Z` vanishes exactly when its value in `F_z` vanishes. -/
theorem Γgerm_eq_zero_iff (f : (restrict F Z).presheaf.obj (op ⊤)) (z : TopCat.of Z) :
    (restrict F Z).presheaf.Γgerm z f = 0 ↔ f.1 ⟨z, trivial⟩ = 0 := by
  rw [← stalkToFiber_germ F Z ⊤ z trivial f]
  constructor
  · intro h
    change stalkToFiber F Z z ((restrict F Z).presheaf.Γgerm z f) = 0
    rw [h, map_zero]
  · intro h
    apply stalkToFiber_injective F Z z
    rw [map_zero]
    exact h

/-- The support of a global section of `F|_Z` (published `CompactSupport.support`) is the set of
points where the family of germs is nonzero. -/
theorem support_eq (f : (restrict F Z).presheaf.obj (op ⊤)) :
    CompactSupport.support (restrict F Z).presheaf f = {z | f.1 ⟨z, trivial⟩ ≠ 0} := by
  ext z
  exact not_congr (Γgerm_eq_zero_iff F Z f z)

theorem mem_compactSupport_of (f : (restrict F Z).presheaf.obj (op ⊤))
    (h : IsCompact {z : Z | f.1 ⟨z, trivial⟩ ≠ 0}) :
    f ∈ CompactSupport.submodule (restrict F Z).presheaf := by
  change IsCompact (CompactSupport.support (restrict F Z).presheaf f)
  rw [support_eq]
  exact h

/-- The published `ClosedRestriction.closedCompactSections F Z` (Renard's `F_c(Z)`) is the space
of compactly supported global sections of `F|_Z`. The subset `Z` is arbitrary. -/
def closedCompactEquiv :
    ClosedRestriction.closedCompactSections F Z ≃ₗ[ℂ]
      CompactSupport.submodule (restrict F Z).presheaf where
  toFun t := ⟨⟨topFamily F Z t.1, (isLocalRestriction_iff F Z t.1).mp t.2.1⟩,
    mem_compactSupport_of F Z _ t.2.2⟩
  invFun f := ⟨fun z => f.1.1 ⟨z, trivial⟩,
    ⟨(isLocalRestriction_iff F Z _).mpr f.1.2, by
      have h := f.2
      change IsCompact (CompactSupport.support (restrict F Z).presheaf f.1) at h
      rw [support_eq] at h
      exact h⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem closedCompactEquiv_apply (t : ClosedRestriction.closedCompactSections F Z)
    (y : (⊤ : Opens (TopCat.of Z))) :
    ((closedCompactEquiv F Z t).1).1 y = t.1 y.1 :=
  rfl

/-- The published restriction `p_Z = ClosedRestriction.restrictToClosed` is, through
`closedCompactEquiv`, the restriction of global sections to `F|_Z`: the germs of `φ` at the
points of `Z`. -/
theorem closedCompactEquiv_restrictToClosed (hZ : IsClosed Z)
    (φ : CompactSupport.submodule F.presheaf) (y : (⊤ : Opens (TopCat.of Z))) :
    ((closedCompactEquiv F Z (ClosedRestriction.restrictToClosed F Z hZ φ)).1).1 y =
      (restrictSection F Z ⊤ φ.1).1 ⟨y.1, trivial⟩ :=
  rfl

end Compact

end Langlands.Sheaf.Renard.LocallyClosedRestriction
