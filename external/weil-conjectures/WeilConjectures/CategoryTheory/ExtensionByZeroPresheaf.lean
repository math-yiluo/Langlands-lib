/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# The extension-by-zero presheaf on a localized ringed site

Source: Stacks Project, Modules on Sites, Lemma 03DI, first paragraph of proof
(blueprint: def-weil-extension-by-zero-presheaf).
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)

open Classical in
/-- At `V`, the extension-by-zero presheaf has a copy of `G(V ⟶ U)` for every map
`V ⟶ U`; scalars from `R(V) = (R.over U)(V ⟶ U)` act on each copy.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheafSection
    (G : SheafOfModules.{v} (R.over U)) (V : Cᵒᵖ) :
    ModuleCat.{max v v₁} (R.obj.obj V) :=
  ModuleCat.of _ (DirectSum (V.unop ⟶ U)
    (fun φ => G.val.obj (Opposite.op (Over.mk φ))))

open Classical in
/-- Restriction sends the `φ` summand through the restriction in `G` along
`(V' ⟶ U) ⟶ (V ⟶ U)` and then includes it in the `φ ≫ a` summand.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheafRestrictAdd
    (G : SheafOfModules.{v} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W) :
    extensionByZeroPresheafSection R U G V →+
      extensionByZeroPresheafSection R U G W :=
  DirectSum.toAddMonoid fun φ : V.unop ⟶ U =>
    (DirectSum.of (fun ψ : W.unop ⟶ U =>
      G.val.obj (Opposite.op (Over.mk ψ))) (a.unop ≫ φ)).comp
      (G.val.map (Opposite.op (Over.homMk a.unop :
        Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))).hom.toAddMonoidHom

open Classical in
private theorem extensionByZeroPresheafRestrictAdd_of
    (G : SheafOfModules.{v} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : G.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U G a
        (DirectSum.of (fun χ : V.unop ⟶ U => G.val.obj (Opposite.op (Over.mk χ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U => G.val.obj (Opposite.op (Over.mk χ))) ψ
        (G.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  simp only [extensionByZeroPresheafRestrictAdd, extensionByZeroPresheafSection,
    DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
  rfl

/-- Restriction is semilinear for the restriction of the ring sheaf.
The claim follows on each direct-sum injection from semilinearity of `G`.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafRestrict_smul
    (G : SheafOfModules.{v} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (r : R.obj.obj V) (s : extensionByZeroPresheafSection R U G V) :
    extensionByZeroPresheafRestrictAdd R U G a (r • s) =
      R.obj.map a r • extensionByZeroPresheafRestrictAdd R U G a s := by
  classical
  induction s using DirectSum.induction_on with
  | zero =>
    rw [smul_zero, (extensionByZeroPresheafRestrictAdd R U G a).map_zero, smul_zero]
  | of φ x =>
    simp only [extensionByZeroPresheafSection, ← DirectSum.of_smul,
      extensionByZeroPresheafRestrictAdd, DirectSum.toAddMonoid_of,
      AddMonoidHom.comp_apply]
    apply congrArg (DirectSum.of _ (a.unop ≫ φ))
    exact G.val.map_smul (Opposite.op (Over.homMk a.unop :
      Over.mk (a.unop ≫ φ) ⟶ Over.mk φ)) r x
  | add x y hx hy =>
    rw [smul_add, (extensionByZeroPresheafRestrictAdd R U G a).map_add,
      (extensionByZeroPresheafRestrictAdd R U G a).map_add, hx, hy, smul_add]

/-- The sectionwise restriction as a morphism to the module obtained by
restriction of scalars along `R.map a`.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheafMap
    (G : SheafOfModules.{v} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W) :
    extensionByZeroPresheafSection R U G V ⟶
      (ModuleCat.restrictScalars (R.obj.map a).hom).obj
        (extensionByZeroPresheafSection R U G W) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.obj.map a).hom).obj
      (extensionByZeroPresheafSection R U G W))
    { toFun := extensionByZeroPresheafRestrictAdd R U G a
      map_add' := (extensionByZeroPresheafRestrictAdd R U G a).map_add
      map_smul' := extensionByZeroPresheafRestrict_smul R U G a }

/-- Identity restriction follows on each summand from the identity law for `G`.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafMap_id
    (G : SheafOfModules.{v} (R.over U)) (V : Cᵒᵖ) :
    extensionByZeroPresheafMap R U G (𝟙 V) =
      (ModuleCat.restrictScalarsId' (R.obj.map (𝟙 V)).hom
        (congrArg RingCat.Hom.hom (R.obj.map_id V))).inv.app _ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change extensionByZeroPresheafRestrictAdd R U G (𝟙 V) s = s
  induction s using DirectSum.induction_on with
  | zero => exact (extensionByZeroPresheafRestrictAdd R U G (𝟙 V)).map_zero
  | of φ x =>
    rw [extensionByZeroPresheafRestrictAdd_of R U G (𝟙 V) φ φ (by simp)]
    have h : Over.homMk (𝟙 V).unop (by simp : (𝟙 V).unop ≫ φ = φ) =
        (𝟙 (Over.mk φ)) := by ext; simp
    rw [h]
    apply congrArg (DirectSum.of _ φ)
    change G.val.map (𝟙 (Opposite.op (Over.mk φ))) x = x
    rw [G.val.map_id]
    rfl
  | add x y hx hy =>
    rw [(extensionByZeroPresheafRestrictAdd R U G (𝟙 V)).map_add, hx, hy]


/-- Composition of restrictions follows on each summand from the
composition law for `G`.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafMap_comp
    (G : SheafOfModules.{v} (R.over U)) {V W X : Cᵒᵖ}
    (a : V ⟶ W) (b : W ⟶ X) :
    extensionByZeroPresheafMap R U G (a ≫ b) =
      extensionByZeroPresheafMap R U G a ≫
        (ModuleCat.restrictScalars (R.obj.map a).hom).map
          (extensionByZeroPresheafMap R U G b) ≫
        (ModuleCat.restrictScalarsComp' (R.obj.map a).hom
          (R.obj.map b).hom (R.obj.map (a ≫ b)).hom
          (congrArg RingCat.Hom.hom (R.obj.map_comp a b))).inv.app _ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change extensionByZeroPresheafRestrictAdd R U G (a ≫ b) s =
    extensionByZeroPresheafRestrictAdd R U G b
      (extensionByZeroPresheafRestrictAdd R U G a s)
  induction s using DirectSum.induction_on with
  | zero =>
    rw [(extensionByZeroPresheafRestrictAdd R U G (a ≫ b)).map_zero,
      (extensionByZeroPresheafRestrictAdd R U G a).map_zero,
      (extensionByZeroPresheafRestrictAdd R U G b).map_zero]
  | of φ x =>
    rw [extensionByZeroPresheafRestrictAdd_of R U G (a ≫ b) φ
      (b.unop ≫ (a.unop ≫ φ)) (by simp [Category.assoc])]
    rw [extensionByZeroPresheafRestrictAdd_of R U G a φ (a.unop ≫ φ) rfl,
      extensionByZeroPresheafRestrictAdd_of R U G b (a.unop ≫ φ)
        (b.unop ≫ (a.unop ≫ φ)) rfl]
    apply congrArg (DirectSum.of _ (b.unop ≫ (a.unop ≫ φ)))
    let f : Over.mk (a.unop ≫ φ) ⟶ Over.mk φ := Over.homMk a.unop
    let g : Over.mk (b.unop ≫ (a.unop ≫ φ)) ⟶ Over.mk (a.unop ≫ φ) :=
      Over.homMk b.unop
    have h : Over.homMk (a ≫ b).unop
        (by simp [Category.assoc] : (a ≫ b).unop ≫ φ = b.unop ≫ (a.unop ≫ φ)) =
        g ≫ f := by ext; rfl
    rw [h]
    change G.val.map (f.op ≫ g.op) x = G.val.map g.op (G.val.map f.op x)
    exact G.val.map_comp_apply f.op g.op x
  | add x y hx hy =>
    rw [(extensionByZeroPresheafRestrictAdd R U G (a ≫ b)).map_add,
      (extensionByZeroPresheafRestrictAdd R U G a).map_add,
      (extensionByZeroPresheafRestrictAdd R U G b).map_add, hx, hy]


/-- The presheaf `V ↦ ⨁ (φ : V ⟶ U), G(V ⟶ U)` of `R`-modules. Its
restriction along `a : V' ⟶ V` sends the `φ` summand into the `a ≫ φ`
summand using the restriction of `G`. This also covers the case of no map
to `U`, when the direct sum is zero. Stacks Project, Lemma 03DI
(blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheafObj
    (G : SheafOfModules.{v} (R.over U)) : PresheafOfModules.{max v v₁} R.obj where
  obj V := extensionByZeroPresheafSection R U G V
  map a := extensionByZeroPresheafMap R U G a
  map_id V := extensionByZeroPresheafMap_id R U G V
  map_comp a b := extensionByZeroPresheafMap_comp R U G a b

/-- On a direct-sum summand, the map induced by `α` is its component at
`V ⟶ U`. Stacks Project, Lemma 03DI
(blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheafHomApp
    {G H : SheafOfModules.{v} (R.over U)} (α : G ⟶ H) (V : Cᵒᵖ) :
    extensionByZeroPresheafSection R U G V ⟶
      extensionByZeroPresheafSection R U H V :=
  ModuleCat.ofHom (DirectSum.lmap fun φ : V.unop ⟶ U =>
    (α.val.app (Opposite.op (Over.mk φ))).hom)

/-- Naturality follows on each summand from naturality of `α` in `Over U`.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafHom_naturality
    {G H : SheafOfModules.{v} (R.over U)} (α : G ⟶ H)
    {V W : Cᵒᵖ} (a : V ⟶ W) :
    extensionByZeroPresheafMap R U G a ≫
        (ModuleCat.restrictScalars (R.obj.map a).hom).map
          (extensionByZeroPresheafHomApp R U α W) =
      extensionByZeroPresheafHomApp R U α V ≫
        extensionByZeroPresheafMap R U H a := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change (extensionByZeroPresheafHomApp R U α W).hom
      (extensionByZeroPresheafRestrictAdd R U G a s) =
    extensionByZeroPresheafRestrictAdd R U H a
      ((extensionByZeroPresheafHomApp R U α V).hom s)
  induction s using DirectSum.induction_on with
  | zero =>
    rw [(extensionByZeroPresheafRestrictAdd R U G a).map_zero, map_zero, map_zero,
      (extensionByZeroPresheafRestrictAdd R U H a).map_zero]
  | of φ x =>
    simp only [extensionByZeroPresheafRestrictAdd, extensionByZeroPresheafHomApp,
      extensionByZeroPresheafSection, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
      ModuleCat.hom_ofHom, DirectSum.lmap_of]
    apply congrArg (DirectSum.of _ (a.unop ≫ φ))
    exact PresheafOfModules.naturality_apply α.val
      (Opposite.op (Over.homMk a.unop : Over.mk (a.unop ≫ φ) ⟶ Over.mk φ)) x
  | add x y hx hy =>
    rw [(extensionByZeroPresheafRestrictAdd R U G a).map_add, map_add, map_add,
      (extensionByZeroPresheafRestrictAdd R U H a).map_add, hx, hy]


/-- The morphism of presheaves induced by `α` acts by `α_(V ⟶ U)` on the
corresponding summand. Stacks Project, Lemma 03DI
(blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheafHom
    {G H : SheafOfModules.{v} (R.over U)} (α : G ⟶ H) :
    extensionByZeroPresheafObj R U G ⟶ extensionByZeroPresheafObj R U H where
  app V := extensionByZeroPresheafHomApp R U α V
  naturality a := extensionByZeroPresheafHom_naturality R U α a

/-- The map induced by the identity sheaf morphism is the identity on each
direct-sum summand. Stacks Project, Lemma 03DI
(blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafHom_id
    (G : SheafOfModules.{v} (R.over U)) :
    extensionByZeroPresheafHom R U (𝟙 G) =
      𝟙 (extensionByZeroPresheafObj R U G) := by
  classical
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  dsimp [extensionByZeroPresheafHom, extensionByZeroPresheafHomApp]
  simp

/-- The map induced by a composite is the composite on each direct-sum
summand. Stacks Project, Lemma 03DI
(blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafHom_comp
    {G H K : SheafOfModules.{v} (R.over U)} (α : G ⟶ H) (β : H ⟶ K) :
    extensionByZeroPresheafHom R U (α ≫ β) =
      extensionByZeroPresheafHom R U α ≫ extensionByZeroPresheafHom R U β := by
  classical
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  dsimp [extensionByZeroPresheafHom, extensionByZeroPresheafHomApp]
  simp

/-- The extension-by-zero presheaf functor from sheaves of modules on the
localized site to presheaves of modules on the original site.
Stacks Project, Lemma 03DI (blueprint: def-weil-extension-by-zero-presheaf). -/
noncomputable def extensionByZeroPresheaf :
    SheafOfModules.{v} (R.over U) ⥤ PresheafOfModules.{max v v₁} R.obj where
  obj G := extensionByZeroPresheafObj R U G
  map α := extensionByZeroPresheafHom R U α
  map_id G := extensionByZeroPresheafHom_id R U G
  map_comp α β := extensionByZeroPresheafHom_comp R U α β

/-- When there is no map `V ⟶ U`, the direct sum defining the section
module is zero. Stacks Project, Lemma 03DI and Lemma 0F6Z
(blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafSection_isEmpty
    (G : SheafOfModules.{v} (R.over U)) (V : Cᵒᵖ)
    [IsEmpty (V.unop ⟶ U)] :
    Subsingleton (extensionByZeroPresheafSection R U G V) := by
  constructor
  intro x y
  apply DirectSum.ext
  intro i
  exact isEmptyElim i

/-- When `V ⟶ U` is unique, the canonical isomorphism sends the injection
of a section into the sole summand to that section, lifted in universe.
Stacks Project, Lemma 03DI and Lemma 0F6Z
(blueprint: def-weil-extension-by-zero-presheaf). -/
theorem extensionByZeroPresheafSection_unique
    (G : SheafOfModules.{v} (R.over U)) (V : Cᵒᵖ)
    [Unique (V.unop ⟶ U)] :
    ∃ e : extensionByZeroPresheafSection R U G V ≅
        (ModuleCat.uliftFunctor.{v₁} (R.obj.obj V)).obj
          (G.val.obj (Opposite.op (Over.mk (default : V.unop ⟶ U)))),
      ∀ s : G.val.obj (Opposite.op (Over.mk (default : V.unop ⟶ U))),
        e.hom (DirectSum.of (fun φ : V.unop ⟶ U =>
          G.val.obj (Opposite.op (Over.mk φ))) default s) = ULift.up s := by
  classical
  let M : (V.unop ⟶ U) → Type v := fun φ => G.val.obj (Opposite.op (Over.mk φ))
  let e : DirectSum (V.unop ⟶ U) M ≃ₗ[R.obj.obj V] M default :=
    { DirectSum.component (R.obj.obj V) (V.unop ⟶ U) M default with
      invFun := DirectSum.of M default
      left_inv := fun s => by
        apply DirectSum.ext
        intro i
        have hi : i = default := Unique.eq_default i
        subst i
        exact DFinsupp.single_eq_same
      right_inv := fun s => DFinsupp.single_eq_same }
  refine ⟨(e.trans ULift.moduleEquiv.symm).toModuleIso, ?_⟩
  intro s
  change ULift.up (e (DirectSum.of M default s)) = ULift.up s
  congr 1



end SheafOfModules
