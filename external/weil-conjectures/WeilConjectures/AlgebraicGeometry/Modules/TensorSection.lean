/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products of sections of modules on a scheme

The tensor product `M ⊗ N` of two `𝒪_X`-modules is the sheafification of the tensor product of
the underlying presheaves of modules (`SheafOfModules.tensorObjIsoSheafification`). Sections
`s ∈ Γ(M, U)` and `t ∈ Γ(N, U)` therefore have a tensor product `s ⊗ t ∈ Γ(M ⊗ N, U)`, the image
of `s ⊗ₜ t` under the sheafification map. It is bilinear and compatible with restriction, and the
tensor product of free generators is a free generator: on the presheaf level this is
`TensorProduct.bijective_smul_tmul`, and sheafification is locally injective and locally
surjective.

The forgetful functor from `𝒪_X`-modules to presheaves of modules is right adjoint to the
monoidal sheafification functor, hence lax monoidal (`Adjunction.rightAdjointLaxMonoidal`); its
tensorator `Γ(M, U) ⊗ Γ(N, U) → Γ(M ⊗ N, U)` sends `s ⊗ₜ t` to `tmulSection s t`
(`tensorSectionsMap_tmul`). The coherence axioms of a lax monoidal functor then compute the
action of the structural morphisms of the monoidal category `X.Modules` on such sections.

If `e` is a free generator of `N` on `V`, then on every `W ≤ V` the presheaf tensor product is
already isomorphic to `M` via `s ↦ s ⊗ e|_W`; as the tensorator is locally bijective, this
shows that `s ↦ s ⊗ e|_W` is a bijection `Γ(M, W) ≃ Γ(M ⊗ N, W)`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.tmulSection`: the tensor product `s ⊗ t` of sections.
- `AlgebraicGeometry.Scheme.Modules.tensorSectionsMap`: the linear map
  `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)`, `s ⊗ₜ t ↦ tmulSection s t`.
- `AlgebraicGeometry.Scheme.Modules.unitSectionsEquiv`: the sections of the unit
  `𝟙_ X.Modules` over `U` are `Γ(X, U)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.tmulSection`: the tensor product of free
  generators is a free generator.
- `AlgebraicGeometry.Scheme.Modules.tensorHom_app_tmulSection`,
  `AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tmulSection`,
  `AlgebraicGeometry.Scheme.Modules.associator_hom_app_tmulSection`,
  `AlgebraicGeometry.Scheme.Modules.braiding_hom_app_tmulSection`: the structural morphisms of
  the monoidal category `X.Modules` on elementary tensors.
- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.bijective_tmulSection_right`: tensoring with
  a free generator is bijective on sections.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

variable (M N) in
/-- The unit `M ⊗ₚ N ⟶ a(M ⊗ₚ N)` of the sheafification of the tensor product of the
underlying presheaves of modules. -/
noncomputable abbrev toSheafifyTensor :=
  (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
    (M.val ⊗ N.val)

variable (M N) in
/-- The sheafification of the tensor product of the underlying presheaves of modules. -/
noncomputable abbrev sheafifyTensor : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).obj (M.val ⊗ N.val)

/-- The tensor product `s ⊗ t ∈ Γ(M ⊗ N, U)` of sections `s ∈ Γ(M, U)` and `t ∈ Γ(N, U)`. -/
noncomputable def tmulSection {U : X.Opens} (s : Γ(M, U)) (t : Γ(N, U)) : Γ(M ⊗ N, U) :=
  Hom.app (SheafOfModules.tensorObjIsoSheafification M N).inv U
    ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(X, U)] t))

lemma toSheafifyTensor_map {U V : X.Opens} (i : V ⟶ U) (x : (M.val ⊗ N.val).obj (op U)) :
    (sheafifyTensor M N).presheaf.map i.op ((toSheafifyTensor M N).app (op U) x) =
      (toSheafifyTensor M N).app (op V) ((M.val ⊗ N.val).map i.op x) :=
  (PresheafOfModules.naturality_apply (toSheafifyTensor M N) i.op x).symm

lemma toSheafifyTensor_smul {U : X.Opens} (r : Γ(X, U)) (x : (M.val ⊗ N.val).obj (op U)) :
    (toSheafifyTensor M N).app (op U) (r • x) = r • (toSheafifyTensor M N).app (op U) x :=
  ((toSheafifyTensor M N).app (op U)).hom.map_smul r x

lemma isFreeGenerator_toSheafifyTensor {U : X.Opens} {s : Γ(M, U)} {t : Γ(N, U)}
    (hs : IsFreeGenerator s) (ht : IsFreeGenerator t) :
    IsFreeGenerator (M := sheafifyTensor M N)
      ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(X, U)] t)) := by
  have hP (W : X.Opens) (hW : W ≤ U) : Function.Bijective fun r : Γ(X, W) ↦
      r • (show (M.val ⊗ N.val).obj (op W) from
        (M.val ⊗ N.val).map (homOfLE hW).op (s ⊗ₜ[Γ(X, U)] t)) :=
    TensorProduct.bijective_smul_tmul (hs W hW) (ht W hW)
  have hPmap {V W : X.Opens} (hV : V ≤ U) (i : W ⟶ V) :
      (M.val ⊗ N.val).map i.op ((M.val ⊗ N.val).map (homOfLE hV).op (s ⊗ₜ[Γ(X, U)] t)) =
        (M.val ⊗ N.val).map (homOfLE ((leOfHom i).trans hV)).op (s ⊗ₜ[Γ(X, U)] t) := by
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallyInjective
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  have hinj (V : X.Opens) (h : V ≤ U) : Function.Injective fun r : Γ(X, V) ↦
      r • (sheafifyTensor M N).presheaf.map (homOfLE h).op
        ((toSheafifyTensor M N).app (op U) (s ⊗ₜ[Γ(X, U)] t)) := by
    intro r r' hrr'
    dsimp only at hrr'
    rw [toSheafifyTensor_map, ← toSheafifyTensor_smul, ← toSheafifyTensor_smul] at hrr'
    have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) (X := op V) _ _ hrr'
    refine Scheme.ext_of_mem hS fun Z l hl ↦ (hP Z ((leOfHom l).trans h)).1 ?_
    have : (M.val ⊗ N.val).map l.op (r • (show (M.val ⊗ N.val).obj (op V) from
        (M.val ⊗ N.val).map (homOfLE h).op (s ⊗ₜ[Γ(X, U)] t))) =
        (M.val ⊗ N.val).map l.op (r' • (show (M.val ⊗ N.val).obj (op V) from
          (M.val ⊗ N.val).map (homOfLE h).op (s ⊗ₜ[Γ(X, U)] t))) := hl
    rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul, hPmap] at this
    exact this
  refine isFreeGenerator_of_locally _ hinj fun V h q ↦ ?_
  refine ⟨_, Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (toSheafifyTensor M N)) (U := op V) q,
    fun W i hi ↦ ?_⟩
  obtain ⟨x, hx⟩ := hi
  obtain ⟨a, rfl⟩ := (hP W ((leOfHom i).trans h)).2 x
  refine ⟨a, ?_⟩
  refine hx.symm.trans ?_
  change (toSheafifyTensor M N).app (op W) (a • _) = _
  rw [toSheafifyTensor_smul, toSheafifyTensor_map]

/-- **The tensor product of free generators is a free generator.** -/
lemma IsFreeGenerator.tmulSection {U : X.Opens} {s : Γ(M, U)} {t : Γ(N, U)}
    (hs : IsFreeGenerator s) (ht : IsFreeGenerator t) : IsFreeGenerator (tmulSection s t) :=
  (isFreeGenerator_toSheafifyTensor hs ht).app_hom
    (SheafOfModules.tensorObjIsoSheafification M N).symm

lemma tmulSection_map {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (M ⊗ N).presheaf.map (homOfLE h).op (tmulSection s t) =
      tmulSection (M.presheaf.map (homOfLE h).op s) (N.presheaf.map (homOfLE h).op t) := by
  rw [tmulSection]
  refine (Hom.app_presheaf_map (SheafOfModules.tensorObjIsoSheafification M N).inv
    (homOfLE h) _).symm.trans ?_
  rw [toSheafifyTensor_map]
  rfl

lemma smul_tmulSection {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmulSection (r • s) t = r • tmulSection s t := by
  rw [tmulSection, tmulSection, ← Hom.app_smul, ← toSheafifyTensor_smul]
  rfl

lemma tmulSection_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    tmulSection s (r • t) = r • tmulSection s t := by
  rw [tmulSection, tmulSection, ← Hom.app_smul, ← toSheafifyTensor_smul]
  congr 2
  exact TensorProduct.tmul_smul r s t

section Monoidal

open TensorProduct

/-! ### The tensor product of sections as the tensorator of a lax monoidal functor -/

variable (X) in
/-- The monoidal structure on presheaves of modules over the structure sheaf of `X`: the
pointwise tensor product. -/
@[instance_reducible]
noncomputable def presheafMonoidalCategory :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs
    (MonoidalCategory (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

variable (X) in
/-- The symmetric monoidal structure on presheaves of modules over the structure sheaf of
`X`. -/
@[instance_reducible]
noncomputable def presheafSymmetricCategory :
    letI := presheafMonoidalCategory X
    SymmetricCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs
    (SymmetricCategory (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory

variable (X) in
/-- The sheafification functor from presheaves of modules over the structure sheaf of `X` to
`𝒪_X`-modules. -/
noncomputable abbrev sheafification :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  _root_.PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)

attribute [local instance] SheafOfModules.sheafificationMonoidal
  SheafOfModules.sheafificationBraided

variable (X) in
/-- The monoidal structure on the sheafification functor of `X`. -/
@[instance_reducible]
noncomputable def sheafificationMonoidal : (sheafification X).Monoidal :=
  SheafOfModules.sheafificationMonoidal X.sheaf

variable (X) in
/-- The braided structure on the sheafification functor of `X`. -/
@[instance_reducible]
noncomputable def sheafificationBraided :
    letI := sheafificationMonoidal X
    (sheafification X).Braided :=
  SheafOfModules.sheafificationBraided X.sheaf

attribute [local instance] sheafificationMonoidal sheafificationBraided

variable (X) in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules, in the form which is
right adjoint to `sheafification X`. -/
noncomputable abbrev forgetToPresheafOfModules :
    X.Modules ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  SheafOfModules.forget _ ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 _)

variable (X) in
/-- The sheafification adjunction for presheaves of modules over the structure sheaf of `X`. -/
noncomputable abbrev sheafificationAdjunction :
    sheafification X ⊣ forgetToPresheafOfModules X :=
  _root_.PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)

variable (X) in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules is lax monoidal, being
right adjoint to the monoidal sheafification functor. -/
@[instance_reducible]
noncomputable def forgetToPresheafOfModulesLaxMonoidal :
    (forgetToPresheafOfModules X).LaxMonoidal :=
  (sheafificationAdjunction X).rightAdjointLaxMonoidal

attribute [local instance] forgetToPresheafOfModulesLaxMonoidal

variable {P M' N' : X.Modules} {U : X.Opens}

/-- The tensorator of the lax monoidal functor `forgetToPresheafOfModules X` at `M` and `N`. -/
local notation "μ[" M ", " N "]" => Functor.LaxMonoidal.μ (forgetToPresheafOfModules _) M N

variable (M N U) in
/-- The `Γ(X, U)`-linear map `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)`, the component at `U`
of the tensorator of the lax monoidal functor `forgetToPresheafOfModules X`, i.e. of the
canonical map from the presheaf tensor product to its sheafification `M ⊗ N`. -/
noncomputable def tensorSectionsMap :
    Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(M ⊗ N, U) :=
  (μ[M, N].app (op U)).hom

/-- The tensorator of `forgetToPresheafOfModules X` sends `s ⊗ₜ t` to `tmulSection s t`. -/
lemma tensorSectionsMap_tmul (s : Γ(M, U)) (t : Γ(N, U)) :
    tensorSectionsMap M N U (s ⊗ₜ t) = tmulSection s t :=
  rfl

lemma add_tmulSection (s s' : Γ(M, U)) (t : Γ(N, U)) :
    tmulSection (s + s') t = tmulSection s t + tmulSection s' t := by
  rw [← tensorSectionsMap_tmul, TensorProduct.add_tmul, map_add, tensorSectionsMap_tmul,
    tensorSectionsMap_tmul]

lemma tmulSection_add (s : Γ(M, U)) (t t' : Γ(N, U)) :
    tmulSection s (t + t') = tmulSection s t + tmulSection s t' := by
  rw [← tensorSectionsMap_tmul, TensorProduct.tmul_add, map_add, tensorSectionsMap_tmul,
    tensorSectionsMap_tmul]

@[simp]
lemma zero_tmulSection (t : Γ(N, U)) : tmulSection (0 : Γ(M, U)) t = 0 := by
  rw [← tensorSectionsMap_tmul, TensorProduct.zero_tmul, map_zero]

@[simp]
lemma tmulSection_zero (s : Γ(M, U)) : tmulSection s (0 : Γ(N, U)) = 0 := by
  rw [← tensorSectionsMap_tmul, TensorProduct.tmul_zero, map_zero]

/-- Naturality of the tensor product of sections. -/
lemma tensorHom_app_tmulSection (f : M ⟶ M') (g : N ⟶ N') (s : Γ(M, U)) (t : Γ(N, U)) :
    (f ⊗ₘ g).app U (tmulSection s t) = tmulSection (f.app U s) (g.app U t) :=
  (congr_arg (fun φ ↦ φ.app (op U) (s ⊗ₜ t))
    (Functor.LaxMonoidal.μ_natural (forgetToPresheafOfModules X) f g)).symm

lemma whiskerLeft_app_tmulSection (g : N ⟶ N') (s : Γ(M, U)) (t : Γ(N, U)) :
    (M ◁ g).app U (tmulSection s t) = tmulSection s (g.app U t) :=
  (congr_arg (fun φ ↦ φ.app (op U) (s ⊗ₜ t))
    (Functor.LaxMonoidal.μ_natural_right (forgetToPresheafOfModules X) M g)).symm

lemma whiskerRight_app_tmulSection (f : M ⟶ M') (s : Γ(M, U)) (t : Γ(N, U)) :
    (f ▷ N).app U (tmulSection s t) = tmulSection (f.app U s) t :=
  (congr_arg (fun φ ↦ φ.app (op U) (s ⊗ₜ t))
    (Functor.LaxMonoidal.μ_natural_left (forgetToPresheafOfModules X) f N)).symm

variable (U) in
/-- The sections of the unit `𝟙_ X.Modules = 𝒪_X` over `U` are the functions `Γ(X, U)`. -/
noncomputable def unitSectionsEquiv : Γ(X, U) ≃ₗ[Γ(X, U)] Γ(𝟙_ X.Modules, U) :=
  LinearEquiv.refl _ _

/-- A section of the unit is a multiple of the section `1`. -/
lemma unitSectionsEquiv_eq_smul_one (r : Γ(X, U)) :
    unitSectionsEquiv U r = r • unitSectionsEquiv U 1 := by
  rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]

/-- Restriction of sections of the unit is restriction of functions. -/
lemma presheaf_map_unitSectionsEquiv {V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    (𝟙_ X.Modules).presheaf.map i.op (unitSectionsEquiv U r) =
      unitSectionsEquiv V (X.presheaf.map i.op r) :=
  rfl

/-- The unit of the lax monoidal functor `forgetToPresheafOfModules X` is the identity. -/
lemma ε_forgetToPresheafOfModules_app (r : Γ(X, U)) :
    (Functor.LaxMonoidal.ε (forgetToPresheafOfModules X)).app (op U) r =
      unitSectionsEquiv U r :=
  congr_arg (fun φ ↦ φ.app (op U) r)
    ((sheafificationAdjunction X).right_triangle_components (SheafOfModules.unit _))

/-- The left unitor on elementary tensors: `1 ⊗ s ↦ s`. -/
lemma leftUnitor_hom_app_tmulSection (r : Γ(X, U)) (s : Γ(M, U)) :
    (λ_ M).hom.app U (tmulSection (unitSectionsEquiv U r) s) = r • s := by
  rw [← ε_forgetToPresheafOfModules_app]
  exact (congr_arg (fun φ ↦ φ.app (op U) (r ⊗ₜ s))
    (Functor.LaxMonoidal.left_unitality (forgetToPresheafOfModules X) M)).symm

/-- The right unitor on elementary tensors: `s ⊗ 1 ↦ s`. -/
lemma rightUnitor_hom_app_tmulSection (r : Γ(X, U)) (s : Γ(M, U)) :
    (ρ_ M).hom.app U (tmulSection s (unitSectionsEquiv U r)) = r • s := by
  rw [← ε_forgetToPresheafOfModules_app]
  exact (congr_arg (fun φ ↦ φ.app (op U) (s ⊗ₜ r))
    (Functor.LaxMonoidal.right_unitality (forgetToPresheafOfModules X) M)).symm

/-- The left unitor on elementary tensors, for an arbitrary section of the unit. -/
lemma leftUnitor_hom_app_tmulSection' (a : Γ(𝟙_ X.Modules, U)) (s : Γ(M, U)) :
    (λ_ M).hom.app U (tmulSection a s) = (unitSectionsEquiv U).symm a • s := by
  rw [← leftUnitor_hom_app_tmulSection, LinearEquiv.apply_symm_apply]

/-- The right unitor on elementary tensors, for an arbitrary section of the unit. -/
lemma rightUnitor_hom_app_tmulSection' (s : Γ(M, U)) (a : Γ(𝟙_ X.Modules, U)) :
    (ρ_ M).hom.app U (tmulSection s a) = (unitSectionsEquiv U).symm a • s := by
  rw [← rightUnitor_hom_app_tmulSection, LinearEquiv.apply_symm_apply]

/-- The associator on elementary tensors: `(s ⊗ t) ⊗ w ↦ s ⊗ (t ⊗ w)`. -/
lemma associator_hom_app_tmulSection (s : Γ(M, U)) (t : Γ(N, U)) (w : Γ(P, U)) :
    (α_ M N P).hom.app U (tmulSection (tmulSection s t) w) =
      tmulSection s (tmulSection t w) :=
  congr_arg (fun φ ↦ φ.app (op U) ((s ⊗ₜ t) ⊗ₜ w))
    (Functor.LaxMonoidal.associativity (forgetToPresheafOfModules X) M N P)

/-- The braiding on elementary tensors: `s ⊗ t ↦ t ⊗ s`. -/
lemma braiding_hom_app_tmulSection (s : Γ(M, U)) (t : Γ(N, U)) :
    (β_ M N).hom.app U (tmulSection s t) = tmulSection t s :=
  congr_arg (fun φ ↦ φ.app (op U) (s ⊗ₜ t))
    ((sheafificationAdjunction X).rightAdjointLaxMonoidal_μ_comp_map_braiding M N)

/-- The inverse of an isomorphism of modules undoes it on sections. -/
lemma inv_app_hom_app_apply_of_iso (e : M ≅ N) (z : Γ(M, U)) :
    e.inv.app U (e.hom.app U z) = z := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
  rfl

/-- An isomorphism of modules is bijective on sections. -/
lemma bijective_app_of_iso (e : M ≅ N) (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

/-- The inverse of the left unitor: `s ↦ 1 ⊗ s`. -/
lemma leftUnitor_inv_app (s : Γ(M, U)) :
    (λ_ M).inv.app U s = tmulSection (unitSectionsEquiv U 1) s := by
  conv_lhs => rw [← one_smul Γ(X, U) s, ← leftUnitor_hom_app_tmulSection]
  exact inv_app_hom_app_apply_of_iso _ _

/-- The inverse of the right unitor: `s ↦ s ⊗ 1`. -/
lemma rightUnitor_inv_app (s : Γ(M, U)) :
    (ρ_ M).inv.app U s = tmulSection s (unitSectionsEquiv U 1) := by
  conv_lhs => rw [← one_smul Γ(X, U) s, ← rightUnitor_hom_app_tmulSection]
  exact inv_app_hom_app_apply_of_iso _ _

/-- The inverse of the associator: `s ⊗ (t ⊗ w) ↦ (s ⊗ t) ⊗ w`. -/
lemma associator_inv_app_tmulSection (s : Γ(M, U)) (t : Γ(N, U)) (w : Γ(P, U)) :
    (α_ M N P).inv.app U (tmulSection s (tmulSection t w)) =
      tmulSection (tmulSection s t) w := by
  rw [← associator_hom_app_tmulSection]
  exact inv_app_hom_app_apply_of_iso _ _

variable (M N) in
/-- The map from the presheaf tensor product to `M ⊗ N` is the unit of the sheafification
adjunction followed by an isomorphism. -/
lemma toPresheaf_map_μ :
    (_root_.PresheafOfModules.toPresheaf _).map μ[M, N] =
      CategoryTheory.toSheafify _ _ ≫ (_root_.PresheafOfModules.toPresheaf _).map
        ((forgetToPresheafOfModules X).map (Functor.OplaxMonoidal.δ (sheafification X) _ _ ≫
          ((sheafificationAdjunction X).counit.app M ⊗ₘ
            (sheafificationAdjunction X).counit.app N))) := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit, Functor.map_comp]
  exact congr_arg (· ≫ _)
    (_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _)

variable (M N) in
/-- The comparison isomorphism `a(M ⊗ₚ N) ≅ M ⊗ N`, seen on underlying presheaves. -/
instance isIso_toPresheaf_map_δ_comp_counit :
    IsIso ((_root_.PresheafOfModules.toPresheaf _).map
        ((forgetToPresheafOfModules X).map (Functor.OplaxMonoidal.δ (sheafification X) _ _ ≫
          ((sheafificationAdjunction X).counit.app M ⊗ₘ
            (sheafificationAdjunction X).counit.app N)))) := by
  have : IsIso (sheafificationAdjunction X).counit :=
    (inferInstance : IsIso (_root_.PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 X.ringCatSheaf.obj)).counit)
  infer_instance

variable (M N) in
/-- The map from the presheaf tensor product to `M ⊗ N` becomes an isomorphism after
sheafification. -/
lemma W_toPresheaf_map_μ :
    (Opens.grothendieckTopology X).W ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) := by
  rw [toPresheaf_map_μ]
  exact MorphismProperty.comp_mem _ _ _ ((Opens.grothendieckTopology X).W_toSheafify _)
    (MorphismProperty.of_isIso _ _)

instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) :=
  (W_toPresheaf_map_μ M N).isLocallyInjective

instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) :=
  (W_toPresheaf_map_μ M N).isLocallySurjective

/-- Tensoring with a free generator `e` of `N` on `V` is injective on sections over `W ≤ V`. -/
lemma IsFreeGenerator.injective_tmulSection_right {V : X.Opens} {e : Γ(N, V)}
    (he : IsFreeGenerator e) {W : X.Opens} (h : W ≤ V) :
    Function.Injective fun s : Γ(M, W) ↦
      Modules.tmulSection s (N.presheaf.map (homOfLE h).op e) := by
  intro s s' hss'
  simp only [← tensorSectionsMap_tmul] at hss'
  have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) (X := op W)
    (s ⊗ₜ[Γ(X, W)] N.presheaf.map (homOfLE h).op e : Γ(M, W) ⊗[Γ(X, W)] Γ(N, W))
    (s' ⊗ₜ[Γ(X, W)] N.presheaf.map (homOfLE h).op e : Γ(M, W) ⊗[Γ(X, W)] Γ(N, W)) hss'
  refine (M.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W' f hf ↦ ?_
  apply (TensorProduct.bijective_tmul_right_of_bijective_smul (A := Γ(M, W'))
    (he.map ((leOfHom f).trans h)).bijective).1
  have hf' : M.presheaf.map f.op s ⊗ₜ[Γ(X, W')]
        N.presheaf.map f.op (N.presheaf.map (homOfLE h).op e) =
      M.presheaf.map f.op s' ⊗ₜ[Γ(X, W')]
        N.presheaf.map f.op (N.presheaf.map (homOfLE h).op e) := hf
  rw [presheaf_map_map_apply] at hf'
  exact hf'

/-- Restriction of an elementary tensor with a restriction of a fixed section `e`. -/
lemma presheaf_map_tmulSection_presheaf_map {V W W' : X.Opens} (e : Γ(N, V)) (h : W ≤ V)
    (h' : W' ≤ V) (g : W' ⟶ W) (s : Γ(M, W)) :
    (M ⊗ N).presheaf.map g.op (Modules.tmulSection s (N.presheaf.map (homOfLE h).op e)) =
      Modules.tmulSection (M.presheaf.map g.op s) (N.presheaf.map (homOfLE h').op e) := by
  refine (tmulSection_map (leOfHom g) _ _).trans ?_
  rw [presheaf_map_map_apply]
  rfl

/-- **Local triviality of tensor products.** If `e` is a free generator of `N` on `V`, then
`s ↦ s ⊗ e|_W` is a bijection `Γ(M, W) → Γ(M ⊗ N, W)` for every `W ≤ V`.

The map from the presheaf tensor product to `M ⊗ N` is locally bijective, and on opens
contained in `V` the presheaf tensor product is identified with `M` by `s ↦ s ⊗ e`; one
concludes with the sheaf property of `M` and `M ⊗ N`. -/
lemma IsFreeGenerator.bijective_tmulSection_right {V : X.Opens} {e : Γ(N, V)}
    (he : IsFreeGenerator e) {W : X.Opens} (h : W ≤ V) :
    Function.Bijective fun s : Γ(M, W) ↦
      Modules.tmulSection s (N.presheaf.map (homOfLE h).op e) := by
  refine ⟨he.injective_tmulSection_right h, fun s ↦ ?_⟩
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) (U := op W) s
  have hb (W' : X.Opens) (f : W' ⟶ W) := (TensorProduct.bijective_tmul_right_of_bijective_smul
    (A := Γ(M, W')) (he.map ((leOfHom f).trans h)).bijective).2
  let x : Presieve.FamilyOfElements (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (Presheaf.imageSieve ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) s).arrows :=
    fun W' f hf ↦ Function.surjInv (hb W' f)
      (Presheaf.localPreimage _ s f hf : Γ(M, W') ⊗[Γ(X, W')] Γ(N, W'))
  have hx {W' : X.Opens} (f : W' ⟶ W) (hf) :
      Modules.tmulSection (x f hf) (N.presheaf.map (homOfLE ((leOfHom f).trans h)).op e) =
        (M ⊗ N).presheaf.map f.op s :=
    (tensorSectionsMap_tmul _ _).symm.trans
      ((congr_arg (tensorSectionsMap M N W') (Function.surjInv_eq (hb W' f) _)).trans
        (Presheaf.app_localPreimage _ s f hf))
  have hcompat : x.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    have hZ : Z ≤ V := (leOfHom (g₁ ≫ f₁)).trans h
    have e₁ := presheaf_map_tmulSection_presheaf_map e ((leOfHom f₁).trans h) hZ g₁ (x f₁ hf₁)
    have e₂ := presheaf_map_tmulSection_presheaf_map e ((leOfHom f₂).trans h) hZ g₂ (x f₂ hf₂)
    rw [hx, presheaf_map_map_apply, hcomm] at e₁
    rw [hx, presheaf_map_map_apply] at e₂
    exact he.injective_tmulSection_right hZ (e₁.symm.trans e₂)
  have hM := M.isSheaf_presheaf_comp_forget _ hS
  refine ⟨hM.amalgamate x hcompat,
    ((M ⊗ N).isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W' f hf ↦ ?_⟩
  exact (presheaf_map_tmulSection_presheaf_map e h ((leOfHom f).trans h) f _).trans
    ((congrArg (Modules.tmulSection · _) (hM.valid_glue hcompat f hf)).trans (hx f hf))

/-- **Local triviality of tensor products**, with the free generator on the left: if `e` is a
free generator of `M` on `V`, then `t ↦ e|_W ⊗ t` is a bijection `Γ(N, W) → Γ(M ⊗ N, W)` for
every `W ≤ V`. -/
lemma IsFreeGenerator.bijective_tmulSection_left {V : X.Opens} {e : Γ(M, V)}
    (he : IsFreeGenerator e) {W : X.Opens} (h : W ≤ V) :
    Function.Bijective fun t : Γ(N, W) ↦
      Modules.tmulSection (M.presheaf.map (homOfLE h).op e) t := by
  have : (fun t : Γ(N, W) ↦ Modules.tmulSection (M.presheaf.map (homOfLE h).op e) t) =
      (β_ N M).hom.app W ∘
        fun t : Γ(N, W) ↦ Modules.tmulSection t (M.presheaf.map (homOfLE h).op e) := by
    ext t
    exact (braiding_hom_app_tmulSection _ _).symm
  rw [this]
  exact (bijective_app_of_iso _ W).comp (he.bijective_tmulSection_right h)

end Monoidal

end AlgebraicGeometry.Scheme.Modules
