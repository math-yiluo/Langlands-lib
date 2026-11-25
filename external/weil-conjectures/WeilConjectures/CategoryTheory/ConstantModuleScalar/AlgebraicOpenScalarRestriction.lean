/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedCoefficientCounit.RingedCoefficientCounitPresentations
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subterminal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Ordinary scalar restriction and extension from an open subtopos -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedCoefficientCounit

namespace CategoryTheory.ConstantModuleScalar

open Opposite

private abbrev moduleSets {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat.{r})

/-- Sections which are zero or already lie over the open. -/
private def rawSupport {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {R : Sheaf J RingCat.{r}} (M : SheafOfModules.{r} R) :
    Subfunctor ((moduleSets R).obj M).obj where
  obj U := {x | Nonempty (P.obj.obj U) ∨ (show M.val.obj U from x) = 0}
  map f := by
    rintro x (hp | rfl)
    · exact Or.inl (hp.map (P.obj.map f))
    · exact Or.inr (map_zero (M.val.map f).hom)

/-- The local closure of the sections supported on the open is a module. -/
private def supportSubmodule {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {R : Sheaf J RingCat.{r}} (M : SheafOfModules.{r} R) : M.val.Submodule where
  obj U :=
    { carrier := ((rawSupport P M).sheafify J).obj U
      zero_mem' := (rawSupport P M).le_sheafify J U (Or.inr rfl)
      add_mem' := by
        intro x y hx hy
        apply J.superset_covering ?_ (J.intersection_covering hx hy)
        intro V f hf
        rcases hf.1 with hp | hx
        · exact Or.inl hp
        rcases hf.2 with hp | hy
        · exact Or.inl hp
        · change M.val.map f.op x = 0 at hx
          change M.val.map f.op y = 0 at hy
          exact Or.inr (by
            change M.val.map f.op (x + y) = 0
            rw [map_add, hx, hy, add_zero])
      smul_mem' := by
        intro a x hx
        apply J.superset_covering ?_ hx
        intro V f hf
        rcases hf with hp | hx
        · exact Or.inl hp
        · change M.val.map f.op x = 0 at hx
          exact Or.inr (by
            change M.val.map f.op (a • x) = 0
            rw [M.val.map_smul, hx, smul_zero]) }
  map f := (rawSupport P M).sheafify J |>.map f

/-- The module of locally supported sections, as a subsheaf of the given module. -/
private def supportModule {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {R : Sheaf J RingCat.{r}} (M : SheafOfModules.{r} R) : SheafOfModules.{r} R where
  val := (supportSubmodule P M).toPresheafOfModules
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{r})
    rw [isSheaf_iff_isSheaf_of_type]
    exact (rawSupport P M).sheafify_isSheaf
      ((isSheaf_iff_isSheaf_of_type J _).mp ((moduleSets R).obj M).property)

private def supportι {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {R : Sheaf J RingCat.{r}} (M : SheafOfModules.{r} R) : supportModule P M ⟶ M :=
  ⟨(supportSubmodule P M).ι⟩

private instance moduleSets_reflects {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) :
    (moduleSets R).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have hU (U : Cᵒᵖ) : IsIso (f.val.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ConcreteCategory.bijective_of_isIso (((moduleSets R).map f).hom.app U)
    let q : M.val ≅ N.val :=
      PresheafOfModules.isoMk (fun U ↦ asIso (f.val.app U)) (fun {_ _} g ↦ f.val.naturality g)
    have : IsIso ((SheafOfModules.forget R).map f) := inferInstanceAs (IsIso q.hom)
    exact isIso_of_reflects_iso f (SheafOfModules.forget R)

/-- Restriction to the open detects exactly the section maps over objects with a
section of the open. Pointwise products avoid any choice of a sheaf product. -/
private theorem star_isIso_iff {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {X Y : Sheaf J (Type r)} (f : X ⟶ Y) :
    IsIso ((Over.star P).map f) ↔
      ∀ U : Cᵒᵖ, Nonempty (P.obj.obj U) → Function.Bijective (f.hom.app U) := by
  rw [← isIso_iff_of_reflects_iso _ (Over.forget P)]
  change IsIso ((prod.functor.obj P).map f) ↔ _
  rw [← NatIso.isIso_map_iff (CartesianMonoidalCategory.tensorLeftIsoProd P) f]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J (Type r)),
    NatTrans.isIso_iff_isIso_app]
  change (∀ U : Cᵒᵖ, IsIso (TypeCat.ofHom
    (fun x : P.obj.obj U × X.obj.obj U ↦ (x.1, f.hom.app U x.2)))) ↔ _
  simp only [isIso_iff_bijective]
  constructor
  · intro hf U hp
    obtain ⟨p⟩ := hp
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hpq : (p, x) = (p, y) := (hf U).1 (congrArg (_root_.Prod.mk p) hxy)
      exact congrArg _root_.Prod.snd hpq
    · intro y
      obtain ⟨x, hx⟩ := (hf U).2 (p, y)
      change (x.1, f.hom.app U x.2) = (p, y) at hx
      exact ⟨x.2, congrArg _root_.Prod.snd hx⟩
  · intro hf U
    constructor
    · intro x y hxy
      change (x.1, f.hom.app U x.2) = (y.1, f.hom.app U y.2) at hxy
      have hfst : x.1 = y.1 :=
        congrArg (fun z : P.obj.obj U × Y.obj.obj U ↦ z.1) hxy
      have hsnd : f.hom.app U x.2 = f.hom.app U y.2 :=
        congrArg (fun z : P.obj.obj U × Y.obj.obj U ↦ z.2) hxy
      exact _root_.Prod.ext hfst ((hf U ⟨x.1⟩).1 hsnd)
    · intro y
      obtain ⟨x, hx⟩ := (hf U ⟨y.1⟩).2 y.2
      exact ⟨(y.1, x), _root_.Prod.ext rfl hx⟩

private theorem inverse_isIso_iff {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (P : Sheaf J (Type r)) (F : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (e : Sheaf K (Type r) ≌ Over P) (he : F ⋙ e.functor ≅ Over.star P)
    {X Y : Sheaf J (Type r)} (f : X ⟶ Y) :
    IsIso (F.map f) ↔
      ∀ U : Cᵒᵖ, Nonempty (P.obj.obj U) → Function.Bijective (f.hom.app U) := by
  rw [← isIso_iff_of_reflects_iso _ e.functor]
  change IsIso ((F ⋙ e.functor).map f) ↔ _
  rw [NatIso.isIso_map_iff he f, star_isIso_iff]

private theorem supportι_inverse_isIso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (P : Sheaf J (Type r)) (F : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (e : Sheaf K (Type r) ≌ Over P) (he : F ⋙ e.functor ≅ Over.star P)
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    (L : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S)
    (ul : L ⋙ moduleSets S ≅ moduleSets R ⋙ F) (M : SheafOfModules.{r} R) :
    IsIso (L.map (supportι P M)) := by
  have hi : IsIso (F.map ((moduleSets R).map (supportι P M))) := by
    apply (inverse_isIso_iff P F e he _).mpr
    intro U hp
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    exact ⟨⟨x, (rawSupport P M).le_sheafify J U (Or.inl hp)⟩, rfl⟩
  have : IsIso ((moduleSets S).map (L.map (supportι P M))) :=
    (NatIso.isIso_map_iff ul (supportι P M)).mpr hi
  exact isIso_of_reflects_iso _ (moduleSets S)

/-- A left adjoint to restriction has locally supported sections. -/
private theorem extension_supported
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (P : Sheaf J (Type r)) (F : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (e : Sheaf K (Type r) ≌ Over P) (he : F ⋙ e.functor ≅ Over.star P)
    {R : Sheaf J RingCat.{r}} {S : Sheaf K RingCat.{r}}
    {L : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (ul : L ⋙ moduleSets S ≅ moduleSets R ⋙ F)
    {E : SheafOfModules.{r} S ⥤ SheafOfModules.{r} R} (a : E ⊣ L)
    (N : SheafOfModules.{r} S) (U : Cᵒᵖ) (x : (E.obj N).val.obj U) :
    x ∈ ((rawSupport P (E.obj N)).sheafify J).obj U := by
  let i := supportι P (E.obj N)
  have : IsIso (L.map i) := supportι_inverse_isIso P F e he L ul (E.obj N)
  let s : E.obj N ⟶ supportModule P (E.obj N) :=
    (a.homEquiv _ _).symm (a.unit.app N ≫ inv (L.map i))
  have hs : s ≫ i = 𝟙 _ := by
    apply (a.homEquiv _ _).injective
    rw [a.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, a.homEquiv_id]
  have hx := congrArg (fun f : E.obj N ⟶ E.obj N ↦ f.val.app U x) hs
  let y : (supportSubmodule P (E.obj N)).obj U := s.val.app U x
  change y.val = x at hx
  exact hx ▸ y.property

/-- Scalar restriction retains the local support condition. -/
private theorem restriction_supported {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {R S : Sheaf J RingCat.{r}} (α : R ⟶ S) (M : SheafOfModules.{r} S)
    (hM : ∀ U (x : M.val.obj U), x ∈ ((rawSupport P M).sheafify J).obj U) :
    ∀ U (x : ((SheafOfModules.restrictScalars α).obj M).val.obj U),
      x ∈ ((rawSupport P ((SheafOfModules.restrictScalars α).obj M)).sheafify J).obj U := by
  intro U x
  exact hM U x

/-- On locally supported modules, restriction to the open reflects isomorphisms.
Injectivity and surjectivity can both be checked on the covering sieve where a
section is zero or the open has a section. -/
private theorem supported_isIso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (P : Sheaf J (Type r))
    {R : Sheaf J RingCat.{r}} {M N : SheafOfModules.{r} R}
    (hM : ∀ U (x : M.val.obj U), x ∈ ((rawSupport P M).sheafify J).obj U)
    (hN : ∀ U (x : N.val.obj U), x ∈ ((rawSupport P N).sheafify J).obj U)
    (f : M ⟶ N)
    (hf : ∀ U : Cᵒᵖ, Nonempty (P.obj.obj U) → Function.Bijective (f.val.app U)) :
    IsIso f := by
  let g := (moduleSets R).map f
  have hi : Presheaf.IsLocallyInjective J g.hom := by
    constructor
    intro U x y hxy
    apply J.superset_covering ?_ (J.intersection_covering (hM U x) (hM U y))
    intro V i hi
    change M.val.map i.op x = M.val.map i.op y
    have heq : f.val.app (op V) (M.val.map i.op x) =
        f.val.app (op V) (M.val.map i.op y) := by
      rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
      exact congrArg (N.val.map i.op) hxy
    rcases hi.1 with hp | hx
    · exact (hf (op V) hp).1 heq
    rcases hi.2 with hp | hy
    · exact (hf (op V) hp).1 heq
    · exact hx.trans hy.symm
  have hs : Presheaf.IsLocallySurjective J g.hom := by
    constructor
    intro U y
    apply J.superset_covering ?_ (hN (op U) y)
    intro V i hi
    rcases hi with hp | hy
    · exact (hf (op V) hp).2 (N.val.map i.op y)
    · refine ⟨(0 : M.val.obj (op V)), ?_⟩
      change f.val.app (op V) 0 = N.val.map i.op y
      change N.val.map i.op y = 0 at hy
      rw [map_zero (f.val.app (op V)).hom, hy]
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso f (moduleSets R)

set_option linter.unusedVariables false in
/-- The ordinary open-extension mate of the underlying restriction square is invertible.
Source: Stacks 03DI, 03DJ and 03CZ; finite-coefficient transport Step 1
(blueprint: lem-pur-algebraic-open-scalar-restriction).
Proof: form the subsheaf of module sections which are locally zero or lie over P.
The raw supported sections form a submodule on each object; their local closure is
again a submodule and a sheaf. Its inclusion becomes invertible after restriction
to P, since every section over an object with a P-section is already supported.
The adjunction therefore lifts the identity of every extended module through this
inclusion. Every section of an extended module is consequently locally supported.
Scalar restriction retains the sections, zero and restriction maps, so it retains
this support condition. Between supported modules a map invertible over P is
locally injective and locally surjective: work on the covering sieves where the
sections are zero or P has a section. It is therefore an isomorphism of sheaves.
Finally the inverse-mate unit equation shows that applying LA to the mate gives
an isomorphism, since both adjunction units and d are invertible. The displayed
slice equivalence identifies this test with invertibility over P, completing the
proof. Empty opens give locally zero modules. This argument uses neither
finite-free coefficients nor any derived categories. -/
theorem open_restriction_mate_isIso
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J CommRingCat.{r}] [HasWeakSheafify K CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (A B : CommRingCat.{r}) [Algebra A B]
    (F : Sheaf J (Type r) ⥤ Sheaf K (Type r))
    (LA : SheafOfModules.AlgebraicInverseImage F (constantRing J A) (constantRing K A))
    (LB : SheafOfModules.AlgebraicInverseImage F (constantRing J B) (constantRing K B))
    (P : Sheaf J (Type r)) (hP : IsSubterminal P)
    (e : Sheaf K (Type r) ≌ Over P) (he : F ⋙ e.functor ≅ Over.star P)
    (EA : modules (constantRing K A) ⥤ modules (constantRing J A))
    (EB : modules (constantRing K B) ⥤ modules (constantRing J B))
    (a : EA ⊣ LA.modules) (b : EB ⊣ LB.modules)
    [IsIso a.unit] [IsIso b.unit]
    (d : restriction ((constantSheaf J CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B))) ⋙ LA.modules ≅
      LB.modules ⋙ restriction ((constantSheaf K CommRingCat).map
        (CommRingCat.ofHom (algebraMap A B))))
    (h : ∀ M, (underlying (constantRing K A)).map (d.hom.app M) =
      LA.moduleUnderlying.hom.app
        ((restriction ((constantSheaf J CommRingCat).map
          (CommRingCat.ofHom (algebraMap A B)))).obj M) ≫ LB.moduleUnderlying.inv.app M) :
    IsIso ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.inv)) := by
  let rK := restriction ((constantSheaf K CommRingCat).map
    (CommRingCat.ofHom (algebraMap A B)))
  let m := ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.inv))
  have hm (N : modules (constantRing K B)) : IsIso (m.app N) := by
    have hu := unit_mateEquiv_symm b a (TwoSquare.mk _ _ _ _ d.inv) N
    change rK.map (b.unit.app N) ≫ d.inv.app (EB.obj N) =
      a.unit.app (rK.obj N) ≫ LA.modules.map (m.app N) at hu
    have hcomp : IsIso (a.unit.app (rK.obj N) ≫ LA.modules.map (m.app N)) := by
      rw [← hu]
      infer_instance
    have hL : IsIso (LA.modules.map (m.app N)) :=
      IsIso.of_isIso_comp_left (a.unit.app (rK.obj N)) _
    have hF : IsIso (F.map ((underlying (constantRing J A)).map (m.app N))) :=
      (NatIso.isIso_map_iff LA.moduleUnderlying (m.app N)).mp
        (inferInstanceAs (IsIso ((underlying (constantRing K A)).map
          (LA.modules.map (m.app N)))))
    apply supported_isIso P
      (extension_supported P F e he LA.moduleUnderlying a (rK.obj N))
      (restriction_supported P _ (EB.obj N)
        (extension_supported P F e he LB.moduleUnderlying b N)) (m.app N)
    exact (inverse_isIso_iff P F e he _).mp hF
  exact NatIso.isIso_of_isIso_app m

end CategoryTheory.ConstantModuleScalar
