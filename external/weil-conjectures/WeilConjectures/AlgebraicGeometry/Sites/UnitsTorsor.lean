/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible modules and `𝒪ˣ`-torsors on the Zariski site

For a scheme `X`, invertible `𝒪_X`-modules up to isomorphism are in bijection with torsors under
the sheaf `𝒪_Xˣ` of units on the Zariski site, up to isomorphism.

## Main definitions

- `AlgebraicGeometry.Scheme.unitsSheaf`: the sheaf `𝒪_Xˣ` of units on the Zariski site.
- `AlgebraicGeometry.Scheme.Modules.generatorsTorsor`: for `M` invertible, the `𝒪_Xˣ`-torsor
  `Isom(𝒪_X, M)` of local generators of `M`.
- `AlgebraicGeometry.Scheme.Modules.ofUnitsTorsor`: for a torsor `T`, the invertible module
  `(T × 𝒪_X) / 𝒪_Xˣ`.

## Main statements

- `AlgebraicGeometry.Scheme.Pic.bijective_torsorClass`: the map `L ↦ Isom(𝒪_X, L)`
  (`AlgebraicGeometry.Scheme.Pic.torsorClass`) is a bijection from `Pic(X)` to the isomorphism
  classes of `𝒪_Xˣ`-torsors, with inverse `T ↦ (T × 𝒪_X) / 𝒪_Xˣ`. The bijection is
  `AlgebraicGeometry.Scheme.picEquivQuotientTorsorUnitsSheaf`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The sheaf `𝒪_Xˣ` of units of the structure sheaf on the Zariski site of `X`, written
additively. It is a sheaf because the functor of units preserves limits. -/
noncomputable def unitsSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨X.sheaf.obj ⋙ CommRingCat.unitsAddCommGrp,
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.sheaf.property⟩

variable {X}

/-- A section of `𝒪_Xˣ`, as a unit of the ring of sections. -/
abbrev unitsSheaf.toUnits {U : X.Opensᵒᵖ} (g : X.unitsSheaf.obj.obj U) : Γ(X, U.unop)ˣ :=
  Additive.toMul g

/-- A unit of the ring of sections, as a section of `𝒪_Xˣ`. -/
abbrev unitsSheaf.ofUnits {U : X.Opensᵒᵖ} (g : Γ(X, U.unop)ˣ) : X.unitsSheaf.obj.obj U :=
  Additive.ofMul g

/-- Restriction of sections of `𝒪_Xˣ` commutes with taking inverses in `Γ(X, -)ˣ`. -/
lemma unitsSheaf.val_toUnits_inv_map {U V : X.Opens}
    (i : V ⟶ U) (g : X.unitsSheaf.obj.obj (op U)) :
    (((unitsSheaf.toUnits (X.unitsSheaf.obj.map i.op g))⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
      X.presheaf.map i.op ((unitsSheaf.toUnits g)⁻¹ : Γ(X, U)ˣ) :=
  rfl

namespace Modules

variable {M : X.Modules}

variable (M) in
/-- The subpresheaf of `M` of generators. -/
def generatorsSubfunctor : Subfunctor (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) where
  obj U := {s | IsFreeGenerator (M := M) (U := U.unop) s}
  map {_ _} i _ hs := hs.map (leOfHom i.unop)

lemma isSheaf_generatorsSubfunctor :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (generatorsSubfunctor M).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ (isSheaf_presheaf_comp_forget M)]
  intro U s hs
  exact isFreeGenerator_of_mem (U := U.unop) s hs fun _ _ hi ↦ hi

variable (M) in
/-- The `𝒪_Xˣ`-torsor `Isom(𝒪_X, M)` of an invertible module `M`: its sections over `U` are the
generators of `M` over `U`, on which the units act by multiplication. -/
noncomputable def generatorsTorsor [M.IsInvertible] : Sheaf.Torsor X.unitsSheaf where
  sheaf := ⟨(generatorsSubfunctor M).toFunctor, isSheaf_generatorsSubfunctor⟩
  vadd U g s := ⟨((unitsSheaf.toUnits g : Γ(X, U.unop)ˣ) : Γ(X, U.unop)) •
    (show Γ(M, U.unop) from s.1), IsFreeGenerator.units_smul s.2 _⟩
  zero_vadd U s := Subtype.ext (one_smul _ (show Γ(M, U.unop) from s.1))
  add_vadd U g h s := Subtype.ext (mul_smul _ _ (show Γ(M, U.unop) from s.1))
  map_vadd f g s := Subtype.ext (map_smul M f.unop _ (show Γ(M, _) from s.1))
  bijective_vadd U t := by
    refine ⟨fun g₁ g₂ h ↦ ?_, fun s ↦ ?_⟩
    · have := t.2.smul_left_injective (congr_arg Subtype.val h)
      exact Additive.toMul.injective (Units.ext this)
    · have ht : IsFreeGenerator (show Γ(M, U.unop) from t.1) := t.2
      have hs : IsFreeGenerator (show Γ(M, U.unop) from s.1) := s.2
      have hab : hs.coeff t.1 * ht.coeff s.1 = 1 := by
        refine ht.smul_left_injective ?_
        dsimp only
        rw [mul_smul, ht.coeff_smul, hs.coeff_smul, one_smul]
      refine ⟨unitsSheaf.ofUnits ⟨ht.coeff s.1, hs.coeff t.1, by rw [mul_comm, hab], hab⟩,
        Subtype.ext ?_⟩
      exact ht.coeff_smul _
  nonemptySieve_mem U := by
    intro x hx
    obtain ⟨Y, hxY, hYU, s, hs⟩ := exists_isFreeGenerator M (W := U) hx
    exact ⟨Y.1, homOfLE hYU, ⟨⟨s, hs⟩⟩, hxY⟩

/-- Isomorphic invertible modules have isomorphic torsors of generators. -/
lemma generatorsTorsor_equiv_of_iso {N : X.Modules} [M.IsInvertible] [N.IsInvertible]
    (e : M ≅ N) : M.generatorsTorsor ≈ N.generatorsTorsor := by
  refine ⟨Sheaf.Torsor.Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun s ↦ ⟨e.hom.app U.unop s.1, IsFreeGenerator.app_hom e s.2⟩
      naturality U V f := ?_ }) fun U a s ↦ Subtype.ext ?_⟩
  · ext s
    apply Subtype.ext
    change e.hom.val.app V (M.val.map f s.1) = N.val.map f (e.hom.val.app U s.1)
    exact PresheafOfModules.naturality_apply e.hom.val f s.1
  · exact Hom.app_smul e.hom _ _

section OfUnitsTorsor

variable (T : Sheaf.Torsor X.unitsSheaf)

/-- The sections over `U` of the invertible module `L(T)` of an `𝒪_Xˣ`-torsor `T`: families of
maps `f_V : T(V) → Γ(X, V)` for the opens `V ⊆ U`, compatible with restriction and satisfying
`f_V (g • t) = g⁻¹ f_V t`. They are the `𝒪ˣ`-equivariant maps `T|_U → 𝒪|_U` for the twisted
action, i.e. `L(T) = (T × 𝒪) / 𝒪ˣ`. -/
def unitsTorsorSections (U : X.Opens) :
    AddSubgroup (∀ V : X.Opens, (V ⟶ U) → T.sheaf.obj.obj (op V) → Γ(X, V)) where
  carrier := {f | (∀ ⦃V W : X.Opens⦄ (i : V ⟶ U) (j : W ⟶ V) (t : T.sheaf.obj.obj (op V)),
      f W (j ≫ i) (T.sheaf.obj.map j.op t) = X.presheaf.map j.op (f V i t)) ∧
    ∀ ⦃V : X.Opens⦄ (i : V ⟶ U) (g : X.unitsSheaf.obj.obj (op V)) (t : T.sheaf.obj.obj (op V)),
      f V i (T.vadd (op V) g t) = ((unitsSheaf.toUnits g)⁻¹ : Γ(X, V)ˣ) * f V i t}
  add_mem' {f f'} hf hf' := ⟨fun V W i j t ↦ by simp [hf.1, hf'.1],
    fun V i g t ↦ by simp [hf.2, hf'.2, mul_add]⟩
  zero_mem' := ⟨fun _ _ _ _ _ ↦ by simp, fun _ _ _ _ ↦ by simp⟩
  neg_mem' {f} hf := ⟨fun V W i j t ↦ by simp [hf.1], fun V i g t ↦ by simp [hf.2]⟩

variable {T}

@[ext]
lemma unitsTorsorSections.ext {U : X.Opens} {f f' : unitsTorsorSections T U}
    (h : ∀ (V : X.Opens) (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)), f.1 V i t = f'.1 V i t) :
    f = f' :=
  Subtype.ext (funext fun V ↦ funext fun i ↦ funext fun t ↦ h V i t)

lemma unitsTorsorSections.map_apply {U V W : X.Opens} (f : unitsTorsorSections T U)
    (i : V ⟶ U) (j : W ⟶ V) (t : T.sheaf.obj.obj (op V)) :
    f.1 W (j ≫ i) (T.sheaf.obj.map j.op t) = X.presheaf.map j.op (f.1 V i t) :=
  f.2.1 i j t

lemma unitsTorsorSections.vadd_apply {U V : X.Opens} (f : unitsTorsorSections T U)
    (i : V ⟶ U) (g : X.unitsSheaf.obj.obj (op V)) (t : T.sheaf.obj.obj (op V)) :
    f.1 V i (T.vadd (op V) g t) = ((unitsSheaf.toUnits g)⁻¹ : Γ(X, V)ˣ) * f.1 V i t :=
  f.2.2 i g t

instance (U : X.Opens) : SMul Γ(X, U) (unitsTorsorSections T U) where
  smul a f := ⟨fun V i t ↦ X.presheaf.map i.op a * f.1 V i t,
    fun V W i j t ↦ by
      dsimp only
      rw [unitsTorsorSections.map_apply f, map_mul, Scheme.presheaf_map_map_apply],
    fun V i g t ↦ by
      dsimp only
      rw [unitsTorsorSections.vadd_apply f, mul_left_comm]⟩

@[simp]
lemma unitsTorsorSections.smul_apply {U V : X.Opens} (a : Γ(X, U)) (f : unitsTorsorSections T U)
    (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (a • f).1 V i t = X.presheaf.map i.op a * f.1 V i t :=
  rfl

@[simp]
lemma unitsTorsorSections.add_apply {U V : X.Opens} (f f' : unitsTorsorSections T U)
    (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (f + f').1 V i t = f.1 V i t + f'.1 V i t :=
  rfl

@[simp]
lemma unitsTorsorSections.zero_apply {U V : X.Opens} (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (0 : unitsTorsorSections T U).1 V i t = 0 :=
  rfl

instance (U : X.Opens) : Module Γ(X, U) (unitsTorsorSections T U) where
  one_smul f := by ext; simp
  mul_smul a b f := by ext; simp [mul_assoc]
  smul_zero a := by ext; simp
  smul_add a f f' := by ext; simp [mul_add]
  add_smul a b f := by ext; simp [add_mul]
  zero_smul f := by ext; simp

variable (T) in
/-- The presheaf of abelian groups underlying the invertible module `L(T)` of an
`𝒪_Xˣ`-torsor `T`. -/
noncomputable def unitsTorsorPresheaf : X.Opensᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (unitsTorsorSections T U.unop)
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun f := ⟨fun V j t ↦ f.1 V (j ≫ i.unop) t,
        fun _ _ j k t ↦ unitsTorsorSections.map_apply f (j ≫ i.unop) k t,
        fun _ j g t ↦ unitsTorsorSections.vadd_apply f (j ≫ i.unop) g t⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

instance (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((unitsTorsorPresheaf T).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (unitsTorsorSections T U.unop))

lemma unitsTorsorPresheaf_map_apply {U U' : X.Opensᵒᵖ} (i : U ⟶ U')
    (f : unitsTorsorSections T U.unop) {V : X.Opens} (j : V ⟶ U'.unop)
    (t : T.sheaf.obj.obj (op V)) :
    ((unitsTorsorPresheaf T).map i f).1 V j t = f.1 V (j ≫ i.unop) t :=
  rfl

lemma unitsTorsorPresheaf_map_smul {U U' : X.Opensᵒᵖ} (i : U ⟶ U')
    (a : X.ringCatSheaf.obj.obj U) (f : (unitsTorsorPresheaf T).obj U) :
    (unitsTorsorPresheaf T).map i (a • f) =
      X.ringCatSheaf.obj.map i a • (unitsTorsorPresheaf T).map i f := by
  refine unitsTorsorSections.ext fun V j t ↦ ?_
  change X.presheaf.map (j ≫ i.unop).op a * _ = X.presheaf.map j.op (X.presheaf.map i a) * _
  rw [← Scheme.presheaf_map_map_apply i.unop j]
  rfl

lemma isSheaf_unitsTorsorPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (unitsTorsorPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget Ab.{u}),
    isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  -- the glued values: over `W ⊆ U`, glue the values of the `x` along `S`
  have hy (W : X.Opens) (k : W ⟶ U) (t : T.sheaf.obj.obj (op W)) :
      (Presieve.FamilyOfElements.Compatible (P := X.presheaf ⋙ CategoryTheory.forget CommRingCat)
        (R := (S.pullback k).arrows)
        fun Z l hl ↦ (x (l ≫ k) hl).1 Z (𝟙 Z) (T.sheaf.obj.map l.op t)) := by
    intro Z₁ Z₂ Z' m₁ m₂ l₁ l₂ hl₁ hl₂ hcomm
    change X.presheaf.map m₁.op ((x (l₁ ≫ k) hl₁).1 Z₁ (𝟙 Z₁) _) =
      X.presheaf.map m₂.op ((x (l₂ ≫ k) hl₂).1 Z₂ (𝟙 Z₂) _)
    rw [← unitsTorsorSections.map_apply, ← unitsTorsorSections.map_apply, T.map_map_apply,
      T.map_map_apply, hcomm]
    have := congr_arg (fun f : (unitsTorsorPresheaf T).obj (op Z') ↦
      f.1 Z' (𝟙 Z') (T.sheaf.obj.map (m₂ ≫ l₂).op t))
      (hx m₁ m₂ hl₁ hl₂ (by rw [← Category.assoc, hcomm, Category.assoc]))
    exact this
  have hO (W : X.Opens) (k : W ⟶ U) := X.isSheaf_presheaf_comp_forget _
    ((Opens.grothendieckTopology X).pullback_stable k hS)
  let F : ∀ V : X.Opens, (V ⟶ U) → T.sheaf.obj.obj (op V) → Γ(X, V) :=
    fun W k t ↦ (hO W k).amalgamate _ (hy W k t)
  have hF (W : X.Opens) (k : W ⟶ U) (t : T.sheaf.obj.obj (op W)) ⦃Z : X.Opens⦄ (l : Z ⟶ W)
      (hl : S (l ≫ k)) :
      X.presheaf.map l.op (F W k t) = (x (l ≫ k) hl).1 Z (𝟙 Z) (T.sheaf.obj.map l.op t) :=
    (hO W k).valid_glue (hy W k t) l hl
  have hFmem : F ∈ unitsTorsorSections T U := by
    refine ⟨fun V W i j t ↦ ?_, fun V i g t ↦ ?_⟩
    · refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable (j ≫ i) hS)
        fun Z l hl ↦ ?_
      rw [hF W (j ≫ i) _ l hl, Scheme.presheaf_map_map_apply, hF V i t (l ≫ j) (by simpa using hl),
        T.map_map_apply]
      rfl
    · refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable i hS)
        fun Z l hl ↦ ?_
      rw [hF V i _ l hl, map_mul, hF V i t l hl, T.map_vadd, unitsTorsorSections.vadd_apply]
      congr 1
  refine ⟨⟨F, hFmem⟩, fun V i hi ↦ ?_, fun f hf ↦ ?_⟩
  · refine unitsTorsorSections.ext fun W j t ↦ ?_
    change F W (j ≫ i) t = _
    refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable (j ≫ i) hS)
      fun Z l hl ↦ ?_
    rw [hF W (j ≫ i) t l hl, ← unitsTorsorSections.map_apply]
    have := congr_arg (fun f : (unitsTorsorPresheaf T).obj (op Z) ↦
      f.1 Z (𝟙 Z) (T.sheaf.obj.map l.op t))
      (hx (𝟙 Z) (l ≫ j) hl hi (by simp))
    exact this
  · refine unitsTorsorSections.ext fun W k t ↦ ?_
    change f.1 W k t = F W k t
    refine ext_of_mem ((Opens.grothendieckTopology X).pullback_stable k hS)
      fun Z l hl ↦ ?_
    rw [hF W k t l hl, ← unitsTorsorSections.map_apply, ← hf (l ≫ k) hl]
    rfl

variable (T) in
/-- The invertible `𝒪_X`-module `L(T) = (T × 𝒪_X) / 𝒪_Xˣ` of an `𝒪_Xˣ`-torsor `T`, realised as
the sheaf of `𝒪ˣ`-equivariant maps `T → 𝒪` for the action `g • a = g⁻¹ a` on `𝒪`. -/
noncomputable def ofUnitsTorsor : X.Modules where
  val := PresheafOfModules.ofPresheaf (unitsTorsorPresheaf T)
    fun _ _ i a f ↦ unitsTorsorPresheaf_map_smul i a f
  isSheaf := isSheaf_unitsTorsorPresheaf

@[simp]
lemma ofUnitsTorsor_smul_apply {U V : X.Opens} (a : Γ(X, U)) (f : Γ(ofUnitsTorsor T, U))
    (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U from a • f).1 V i t =
      X.presheaf.map i.op a * (show unitsTorsorSections T U from f).1 V i t :=
  rfl

lemma ofUnitsTorsor_map_apply {U U' V : X.Opens} (j : U' ⟶ U) (f : Γ(ofUnitsTorsor T, U))
    (i : V ⟶ U') (t : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U' from (ofUnitsTorsor T).presheaf.map j.op f).1 V i t =
      (show unitsTorsorSections T U from f).1 V (i ≫ j) t :=
  rfl

variable (T) in
/-- The section `f_t` of `L(T)` over `U` attached to a section `t` of `T` over `U`: it sends
`g • t` to `g⁻¹`. -/
noncomputable def unitsTorsorBasis {U : X.Opens} (t : T.sheaf.obj.obj (op U)) :
    Γ(ofUnitsTorsor T, U) :=
  show unitsTorsorSections T U from
  ⟨fun V i s ↦ ((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ),
    fun V W i j s ↦ by
      dsimp only
      rw [← T.map_map_apply, ← T.map_sub_apply, ← unitsSheaf.val_toUnits_inv_map],
    fun V i g s ↦ by
      dsimp only
      rw [T.sub_vadd_right]
      change (((unitsSheaf.toUnits g *
        unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) = _
      rw [mul_inv, Units.val_mul]⟩

lemma unitsTorsorBasis_apply {U V : X.Opens} (t : T.sheaf.obj.obj (op U)) (i : V ⟶ U)
    (s : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U from unitsTorsorBasis T t).1 V i s =
      ((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ) :=
  rfl

lemma map_unitsTorsorBasis {U V : X.Opens} (t : T.sheaf.obj.obj (op U)) (j : V ⟶ U) :
    (ofUnitsTorsor T).presheaf.map j.op (unitsTorsorBasis T t) =
      unitsTorsorBasis T (T.sheaf.obj.map j.op t) := by
  refine unitsTorsorSections.ext fun W i s ↦ ?_
  rw [ofUnitsTorsor_map_apply, unitsTorsorBasis_apply, unitsTorsorBasis_apply, T.map_map_apply]

/-- Every section of `L(T)` over `U` is a multiple of the basis section `f_t`. -/
lemma eq_smul_unitsTorsorBasis {U : X.Opens} (f : Γ(ofUnitsTorsor T, U))
    (t : T.sheaf.obj.obj (op U)) :
    f = (show unitsTorsorSections T U from f).1 U (𝟙 U) t • unitsTorsorBasis T t := by
  refine unitsTorsorSections.ext fun V i s ↦ ?_
  rw [ofUnitsTorsor_smul_apply, unitsTorsorBasis_apply,
    ← unitsTorsorSections.map_apply (show unitsTorsorSections T U from f) (𝟙 U) i t]
  conv_lhs => rw [← T.sub_vadd (T.sheaf.obj.map i.op t) s]
  rw [unitsTorsorSections.vadd_apply, mul_comm]
  rfl

@[simp]
lemma unitsTorsorBasis_apply_self {U : X.Opens} (t : T.sheaf.obj.obj (op U)) :
    (show unitsTorsorSections T U from unitsTorsorBasis T t).1 U (𝟙 U) t = 1 := by
  rw [unitsTorsorBasis_apply]
  change (((Additive.toMul (T.sub (T.sheaf.obj.map (𝟙 (op U)) t) t))⁻¹ : Γ(X, U)ˣ) : Γ(X, U))
    = 1
  rw [T.sheaf.obj.map_id]
  simp

/-- The basis section `f_t` of `L(T)` is a generator. -/
lemma isFreeGenerator_unitsTorsorBasis {U : X.Opens} (t : T.sheaf.obj.obj (op U)) :
    IsFreeGenerator (M := ofUnitsTorsor T) (unitsTorsorBasis T t) := by
  intro V h
  rw [map_unitsTorsorBasis]
  refine ⟨fun a b hab ↦ ?_, fun f ↦ ⟨_, (eq_smul_unitsTorsorBasis f _).symm⟩⟩
  have := congr_arg (fun f : Γ(ofUnitsTorsor T, V) ↦
    (show unitsTorsorSections T V from f).1 V (𝟙 V) (T.sheaf.obj.map (homOfLE h).op t)) hab
  simpa using this

instance isInvertible_ofUnitsTorsor :
    SheafOfModules.IsInvertible.{u, u, u} (ofUnitsTorsor T) := by
  refine SheafOfModules.isInvertible_of_forall_over_unit (M := ofUnitsTorsor T)
    (I := Σ U : X.Opens, T.sheaf.obj.obj (op U)) (fun p ↦ p.1) ?_
    fun p ↦ ⟨IsFreeGenerator.overIso (isFreeGenerator_unitsTorsorBasis p.2)⟩
  intro V x hx
  obtain ⟨W, f, ⟨t⟩, hxW⟩ := T.nonemptySieve_mem ⊤ x trivial
  exact ⟨V ⊓ W, homOfLE inf_le_left, ⟨⟨W, t⟩, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hxW⟩⟩

/-- Every `𝒪_Xˣ`-torsor `T` is the torsor of generators of `L(T)`, via `t ↦ f_t`. -/
lemma equiv_generatorsTorsor_ofUnitsTorsor : T ≈ (ofUnitsTorsor T).generatorsTorsor := by
  refine ⟨Sheaf.Torsor.Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun t ↦ ⟨unitsTorsorBasis T t, isFreeGenerator_unitsTorsorBasis t⟩
      naturality U V f := ?_ }) fun U g t ↦ Subtype.ext ?_⟩
  · ext t
    apply Subtype.ext
    exact (map_unitsTorsorBasis (U := U.unop) t f.unop).symm
  · refine unitsTorsorSections.ext fun V i s ↦ ?_
    change (((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op (T.vadd U g t)) s))⁻¹ :
      Γ(X, V)ˣ) : Γ(X, V)) = X.presheaf.map i.op (unitsSheaf.toUnits g : Γ(X, U.unop)) *
        (((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s))⁻¹ : Γ(X, V)ˣ) : Γ(X, V))
    rw [T.map_vadd, T.sub_vadd_left]
    change (((unitsSheaf.toUnits (T.sub (T.sheaf.obj.map i.op t) s) /
      unitsSheaf.toUnits (X.unitsSheaf.obj.map i.op g))⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) = _
    rw [inv_div, div_eq_mul_inv, Units.val_mul]
    rfl

end OfUnitsTorsor

section Comparison

variable {T T' : Sheaf.Torsor X.unitsSheaf}

/-- The map `L(T') ⟶ L(T)` induced by an equivariant map `φ : T ⟶ T'` of torsors, given by
precomposition with `φ`. -/
noncomputable def ofUnitsTorsorMap (φ : T.sheaf ⟶ T'.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t)) :
    ofUnitsTorsor T' ⟶ ofUnitsTorsor T :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun f := show unitsTorsorSections T U.unop from
            ⟨fun V i t ↦ (show unitsTorsorSections T' U.unop from f).1 V i (φ.hom.app _ t),
              fun V W i j t ↦ by
                dsimp only
                rw [← unitsTorsorSections.map_apply]
                exact congr_arg _ (NatTrans.naturality_apply φ.hom j.op t),
              fun V i g t ↦ by
                dsimp only
                rw [hφ, unitsTorsorSections.vadd_apply]⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    fun _ _ _ ↦ rfl⟩

lemma ofUnitsTorsorMap_apply (φ : T.sheaf ⟶ T'.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t)) {U V : X.Opens}
    (f : Γ(ofUnitsTorsor T', U)) (i : V ⟶ U) (t : T.sheaf.obj.obj (op V)) :
    (show unitsTorsorSections T U from (ofUnitsTorsorMap φ hφ).app U f).1 V i t =
      (show unitsTorsorSections T' U from f).1 V i (φ.hom.app _ t) := by
  unfold ofUnitsTorsorMap
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma ofUnitsTorsorMap_id :
    ofUnitsTorsorMap (𝟙 T.sheaf) (fun _ _ _ ↦ rfl) = 𝟙 (ofUnitsTorsor T) := by
  refine hom_ext _ _ fun U ↦ ?_
  ext f
  refine unitsTorsorSections.ext fun V i t ↦ ?_
  unfold ofUnitsTorsorMap
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma ofUnitsTorsorMap_comp {T'' : Sheaf.Torsor X.unitsSheaf} (φ : T.sheaf ⟶ T'.sheaf)
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t))
    (ψ : T'.sheaf ⟶ T''.sheaf)
    (hψ : ∀ U g t, ψ.hom.app U (T'.vadd U g t) = T''.vadd U g (ψ.hom.app U t)) :
    ofUnitsTorsorMap ψ hψ ≫ ofUnitsTorsorMap φ hφ =
      ofUnitsTorsorMap (φ ≫ ψ) (fun U g t ↦ by
        change ψ.hom.app U (φ.hom.app U _) = _
        rw [hφ, hψ]
        rfl) := by
  refine hom_ext _ _ fun U ↦ ?_
  ext f
  refine unitsTorsorSections.ext fun V i t ↦ ?_
  unfold ofUnitsTorsorMap
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma ofUnitsTorsorMap_congr {φ φ' : T.sheaf ⟶ T'.sheaf} (h : φ = φ')
    (hφ : ∀ U g t, φ.hom.app U (T.vadd U g t) = T'.vadd U g (φ.hom.app U t))
    (hφ' : ∀ U g t, φ'.hom.app U (T.vadd U g t) = T'.vadd U g (φ'.hom.app U t)) :
    ofUnitsTorsorMap φ hφ = ofUnitsTorsorMap φ' hφ' := by
  subst h
  rfl

/-- Isomorphic torsors have isomorphic modules. -/
lemma nonempty_ofUnitsTorsor_iso (h : T ≈ T') :
    Nonempty (ofUnitsTorsor T ≅ ofUnitsTorsor T') := by
  obtain ⟨e⟩ := h
  refine ⟨{ hom := ofUnitsTorsorMap e.symm.iso.hom e.symm.map_vadd
            inv := ofUnitsTorsorMap e.iso.hom e.map_vadd
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [ofUnitsTorsorMap_comp, ← ofUnitsTorsorMap_id]
    exact ofUnitsTorsorMap_congr e.iso.hom_inv_id _ _
  · rw [ofUnitsTorsorMap_comp, ← ofUnitsTorsorMap_id]
    exact ofUnitsTorsorMap_congr e.iso.inv_hom_id _ _

section ToOfUnitsTorsor

variable [M.IsInvertible]

variable (M) in
/-- The section of `L(Isom(𝒪, M))` attached to a section `m` of `M`: it sends a local
generator `s` to the coefficient of `m` with respect to `s`. -/
noncomputable def toUnitsTorsorSections {U : X.Opens} (m : Γ(M, U)) :
    unitsTorsorSections M.generatorsTorsor U :=
  ⟨fun V i s ↦ IsFreeGenerator.coeff s.2 (M.presheaf.map i.op m),
    fun V W i j s ↦ by
      dsimp only
      rw [← presheaf_map_map_apply i j m]
      exact IsFreeGenerator.coeff_map s.2 (leOfHom j) _,
    fun V i g s ↦ by
      dsimp only
      rw [IsFreeGenerator.coeff_eq_iff]
      change _ • ((unitsSheaf.toUnits g : Γ(X, V)) • _) = _
      rw [smul_smul, mul_assoc, mul_comm _ (unitsSheaf.toUnits g : Γ(X, V)), ← mul_assoc,
        Units.inv_mul, one_mul]
      exact IsFreeGenerator.coeff_smul _ _⟩

lemma toUnitsTorsorSections_apply {U V : X.Opens} (m : Γ(M, U)) (i : V ⟶ U)
    (s : M.generatorsTorsor.sheaf.obj.obj (op V)) :
    (toUnitsTorsorSections M m).1 V i s =
      IsFreeGenerator.coeff s.2 (M.presheaf.map i.op m) :=
  rfl

variable (M) in
/-- The comparison map `M ⟶ L(Isom(𝒪, M))`. -/
noncomputable def toOfUnitsTorsor : M ⟶ ofUnitsTorsor M.generatorsTorsor :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun m := toUnitsTorsorSections M (U := U.unop) m
          map_zero' := unitsTorsorSections.ext fun V i s ↦ by
            rw [toUnitsTorsorSections_apply, map_zero, IsFreeGenerator.coeff_zero]
            rfl
          map_add' m m' := unitsTorsorSections.ext fun V i s ↦ by
            rw [toUnitsTorsorSections_apply, map_add, IsFreeGenerator.coeff_add]
            rfl }
      naturality U U' f := by
        ext m
        refine unitsTorsorSections.ext fun V i s ↦ ?_
        change (toUnitsTorsorSections M (U := U'.unop) (M.presheaf.map f m)).1 V i s =
          (toUnitsTorsorSections M (U := U.unop) m).1 V (i ≫ f.unop) s
        rw [toUnitsTorsorSections_apply, toUnitsTorsorSections_apply, ← presheaf_map_map_apply]
        rfl }
    fun U a m ↦ by
      refine unitsTorsorSections.ext (U := U.unop) fun V i s ↦ ?_
      change (toUnitsTorsorSections M (U := U.unop) (a • m)).1 V i s =
        X.presheaf.map i.op a * (toUnitsTorsorSections M (U := U.unop) m).1 V i s
      rw [toUnitsTorsorSections_apply, toUnitsTorsorSections_apply,
        map_smul, IsFreeGenerator.coeff_smul_left]⟩

lemma toOfUnitsTorsor_app_apply {U : X.Opens} (m : Γ(M, U)) :
    (toOfUnitsTorsor M).app U m = toUnitsTorsorSections M m := by
  unfold toOfUnitsTorsor
  dsimp [Hom.app, Hom.mapPresheaf]
  rfl

lemma bijective_toUnitsTorsorSections (U : X.Opens) :
    Function.Bijective (toUnitsTorsorSections M (U := U)) := by
  have hS := (generatorsTorsor M).nonemptySieve_mem U
  have hM := Modules.isSheaf_presheaf_comp_forget M _ hS
  refine ⟨fun m m' h ↦ ?_, fun F ↦ ?_⟩
  · refine hM.isSeparatedFor.ext fun V f ⟨s⟩ ↦ ?_
    have := congr_arg (fun F : unitsTorsorSections M.generatorsTorsor U ↦ F.1 V f s) h
    simp only [toUnitsTorsorSections_apply] at this
    change M.presheaf.map f.op m = M.presheaf.map f.op m'
    rw [← IsFreeGenerator.coeff_smul s.2 (M.presheaf.map f.op m), this,
      IsFreeGenerator.coeff_smul]
  · -- two generators give the same section `F(s) • s`
    have key {V : X.Opens} (f : V ⟶ U) (s s' : M.generatorsTorsor.sheaf.obj.obj (op V)) :
        F.1 V f s • (show Γ(M, V) from s.1) = F.1 V f s' • (show Γ(M, V) from s'.1) := by
      rw [← (generatorsTorsor M).sub_vadd s s', unitsTorsorSections.vadd_apply]
      change _ = _ • (((unitsSheaf.toUnits ((generatorsTorsor M).sub s s') : Γ(X, V)ˣ) :
        Γ(X, V)) • _)
      rw [smul_smul, mul_assoc, mul_comm _ ((unitsSheaf.toUnits _ : Γ(X, V)ˣ) : Γ(X, V)),
        ← mul_assoc, Units.inv_mul, one_mul]
    let x : Presieve.FamilyOfElements (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
        (Sheaf.nonemptySieve (generatorsTorsor M).sheaf.obj U).arrows :=
      fun V f hf ↦ F.1 V f hf.some • (show Γ(M, V) from hf.some.1)
    have hx : x.Compatible := by
      intro Z₁ Z₂ V g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
      change M.presheaf.map g₁.op (F.1 Z₁ f₁ hf₁.some • _) =
        M.presheaf.map g₂.op (F.1 Z₂ f₂ hf₂.some • _)
      rw [map_smul, map_smul, ← unitsTorsorSections.map_apply,
        ← unitsTorsorSections.map_apply]
      have hc : g₁ ≫ f₁ = g₂ ≫ f₂ := hcomm
      exact (congr_arg (fun k ↦ F.1 V k _ • _) hc).trans
        (key (g₂ ≫ f₂) (M.generatorsTorsor.sheaf.obj.map g₁.op hf₁.some)
          (M.generatorsTorsor.sheaf.obj.map g₂.op hf₂.some))
    refine ⟨hM.amalgamate x hx, unitsTorsorSections.ext fun V i s ↦ ?_⟩
    rw [toUnitsTorsorSections_apply, IsFreeGenerator.coeff_eq_iff]
    have := hM.valid_glue hx i ⟨s⟩
    change M.presheaf.map i.op _ = _ at this
    rw [this]
    exact key i _ _

instance : IsIso (toOfUnitsTorsor M) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have h := bijective_toUnitsTorsorSections (M := M) U
  refine ⟨fun m m' hm ↦ h.1 ?_, fun F ↦ ?_⟩
  · rwa [toOfUnitsTorsor_app_apply, toOfUnitsTorsor_app_apply] at hm
  · obtain ⟨m, hm⟩ := h.2 F
    exact ⟨m, (toOfUnitsTorsor_app_apply m).trans hm⟩

end ToOfUnitsTorsor

end Comparison

end Modules

open Modules

/-- The class of the `𝒪_Xˣ`-torsor `Isom(𝒪_X, L)` of local generators of an invertible
module `L`. -/
noncomputable def Pic.torsorClass (L : X.Pic) :
    _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf)) :=
  haveI := Pic.isInvertible L
  _root_.Quotient.mk _ (generatorsTorsor ((fromSkeleton X.Modules).obj L.val))

lemma Pic.torsorClass_mk (M : X.Modules) [M.IsInvertible] :
    (Pic.mk M).torsorClass = _root_.Quotient.mk _ M.generatorsTorsor := by
  have := Pic.isInvertible (Pic.mk M)
  exact _root_.Quotient.sound (generatorsTorsor_equiv_of_iso (fromSkeletonToSkeletonIso _))

/-- **Line bundles and `𝒪ˣ`-torsors, Zariski version.** For a scheme `X`, the map
`L ↦ Isom(𝒪_X, L)` sending an invertible `𝒪_X`-module to the `𝒪_Xˣ`-torsor of its local
generators is a bijection from the Picard group of `X` onto the set of isomorphism classes of
`𝒪_Xˣ`-torsors on the Zariski site of `X`. Its inverse sends a torsor `T` to the invertible
module `(T × 𝒪_X) / 𝒪_Xˣ` (`AlgebraicGeometry.Scheme.Modules.ofUnitsTorsor`), see
`AlgebraicGeometry.Scheme.picEquivQuotientTorsorUnitsSheaf_symm_mk`. -/
theorem Pic.bijective_torsorClass : Function.Bijective (Pic.torsorClass (X := X)) := by
  refine ⟨fun L L' h ↦ ?_, fun T ↦ ?_⟩
  · have := Pic.isInvertible L
    have := Pic.isInvertible L'
    obtain ⟨e⟩ := nonempty_ofUnitsTorsor_iso (_root_.Quotient.exact h)
    exact Pic.eq_iff_nonempty_iso.2
      ⟨asIso (toOfUnitsTorsor _) ≪≫ e ≪≫ (asIso (toOfUnitsTorsor _)).symm⟩
  · induction T using _root_.Quotient.inductionOn with | h T => ?_
    refine ⟨Pic.mk (ofUnitsTorsor T), ?_⟩
    rw [Pic.torsorClass_mk]
    exact _root_.Quotient.sound (Setoid.symm (equiv_generatorsTorsor_ofUnitsTorsor (T := T)))

variable (X) in
/-- The bijection `L ↦ Isom(𝒪_X, L)` from the Picard group of `X` to the isomorphism classes of
`𝒪_Xˣ`-torsors on the Zariski site (`AlgebraicGeometry.Scheme.Pic.bijective_torsorClass`). -/
noncomputable def picEquivQuotientTorsorUnitsSheaf :
    X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf)) :=
  Equiv.ofBijective _ Pic.bijective_torsorClass

@[simp]
lemma picEquivQuotientTorsorUnitsSheaf_apply (L : X.Pic) :
    X.picEquivQuotientTorsorUnitsSheaf L = L.torsorClass :=
  rfl

/-- The inverse of `L ↦ Isom(𝒪_X, L)` sends a torsor `T` to `(T × 𝒪_X) / 𝒪_Xˣ`. -/
@[simp]
lemma picEquivQuotientTorsorUnitsSheaf_symm_mk (T : Sheaf.Torsor X.unitsSheaf) :
    X.picEquivQuotientTorsorUnitsSheaf.symm (_root_.Quotient.mk _ T) =
      Pic.mk (ofUnitsTorsor T) := by
  rw [Equiv.symm_apply_eq, picEquivQuotientTorsorUnitsSheaf_apply, Pic.torsorClass_mk]
  exact _root_.Quotient.sound (equiv_generatorsTorsor_ofUnitsTorsor (T := T))

/-- Invertible modules up to isomorphism are in bijection with `𝒪_Xˣ`-torsors up to
isomorphism; the bijection is `AlgebraicGeometry.Scheme.picEquivQuotientTorsorUnitsSheaf`. -/
theorem nonempty_pic_equiv_quotient_torsor_unitsSheaf (X : Scheme.{u}) :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf))) :=
  ⟨X.picEquivQuotientTorsorUnitsSheaf⟩

end AlgebraicGeometry.Scheme
