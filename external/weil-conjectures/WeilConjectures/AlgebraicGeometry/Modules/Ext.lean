/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree

/-!
# Ext groups of sheaves of modules on a scheme

For `𝒪_X`-modules `ℱ` and `𝒢` on a scheme `X`, the group `Ext^i_X(ℱ, 𝒢)` is Mathlib's
`Abelian.Ext`: the morphisms `ℱ ⟶ 𝒢[i]` in the derived category of the abelian category
`X.Modules`. As `X.Modules` has enough injectives, this is the `i`-th right derived functor of
`Hom_{𝒪_X}(ℱ, -)` evaluated at `𝒢`; it is not computed by projective resolutions of `ℱ`, which
need not exist.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.Ext`: the group `Ext^i_X(ℱ, 𝒢)`.
- `AlgebraicGeometry.Scheme.Modules.extUnitToH`: the canonical comparison map
  `Ext^n_X(𝒪_X, M) ⟶ H^n(X, M)` (forget to abelian sheaves, pull back along `ℤ ⟶ 𝒪_X`).
- `AlgebraicGeometry.Scheme.Modules.extUnitAddEquivH`: the canonical isomorphism
  `Ext^n_X(𝒪_X, M) ≃ H^n(X, M)`, natural in `M`.
- `AlgebraicGeometry.Scheme.Modules.extAddEquivH`: the canonical isomorphism
  `Ext^i_X(ℱ, 𝒢) ≃ H^i(X, ℱᵛ ⊗ 𝒢)` for finite locally free `ℱ`, natural in `𝒢`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.contravariantSequence_ext_exact`: the long exact sequence of
  `Ext(-, 𝒢)` attached to a short exact sequence.
- `AlgebraicGeometry.Scheme.Modules.extUnitToH_bijective`: the comparison map is bijective, by
  dimension shifting.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_unit_addEquiv_H`: `Ext^n_X(𝒪_X, M) ≅ H^n(X, M)`,
  by dimension shifting, injective `𝒪_X`-modules being flasque, hence acyclic.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`: for finite locally free `ℱ`,
  `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`.

## Implementation notes

The `Ext` groups need the hypothesis `HasExt.{u} X.Modules`, which holds because `X.Modules` is a
Grothendieck abelian category (`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`); it is
kept as an instance argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [HasExt.{u} X.Modules]

/-- The **Ext groups** `Ext^i_X(ℱ, 𝒢)` of two `𝒪_X`-modules: the morphisms `ℱ ⟶ 𝒢[i]` in the
derived category of `𝒪_X`-modules, equivalently the right derived functors of `Hom_{𝒪_X}(ℱ, -)`
evaluated at `𝒢` (`𝒪_X`-modules have enough injectives but in general not enough projectives).
In degree `0` this is `Hom_{𝒪_X}(ℱ, 𝒢)` (`CategoryTheory.Abelian.Ext.homEquiv₀`). -/
abbrev Ext (ℱ 𝒢 : X.Modules) (i : ℕ) : Type u :=
  Abelian.Ext ℱ 𝒢 i

/-- **The long exact `Ext` sequence.** A short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of
`𝒪_X`-modules gives, for every `𝒢` and `1 + n₀ = n₁`, the exact sequence
`Ext^{n₀}(ℱ₃, 𝒢) → Ext^{n₀}(ℱ₂, 𝒢) → Ext^{n₀}(ℱ₁, 𝒢) → Ext^{n₁}(ℱ₃, 𝒢) → Ext^{n₁}(ℱ₂, 𝒢) →
Ext^{n₁}(ℱ₁, 𝒢)`. The comparison with sheaf cohomology for finite locally free `ℱ` is
`AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`. -/
theorem contravariantSequence_ext_exact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (𝒢 : X.Modules) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Abelian.Ext.contravariantSequence hS 𝒢 n₀ n₁ h).Exact :=
  Abelian.Ext.contravariantSequence_exact hS 𝒢 n₀ n₁ h


section Comparison

/-- Two quotients by the kernels of surjective additive maps are identified by an additive
equivalence of the sources matching the kernels. -/
private noncomputable def addEquivOfSurjective {A₁ A₂ B₁ B₂ : Type*} [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂] (δ₁ : A₁ →+ B₁) (δ₂ : A₂ →+ B₂)
    (h₁ : Function.Surjective δ₁) (h₂ : Function.Surjective δ₂) (e : A₁ ≃+ A₂)
    (he : δ₁.ker.map e.toAddMonoidHom = δ₂.ker) : B₁ ≃+ B₂ :=
  (QuotientAddGroup.quotientKerEquivOfSurjective δ₁ h₁).symm.trans
    ((QuotientAddGroup.congr _ _ e he).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective δ₂ h₂))

/-- The global sections of `M` as morphisms `𝒪_X ⟶ M`. -/
noncomputable def unitHomAddEquiv (M : X.Modules) : (𝟙_ X.Modules ⟶ M) ≃+ Γ(M, ⊤) where
  toFun f := Hom.app f ⊤ (1 : Γ(X, ⊤))
  invFun u := homOfGlobalSection M u
  left_inv f := by
    refine (SheafOfModules.unitHomEquiv M).injective (Subtype.ext (funext fun U ↦ ?_))
    change Hom.app (homOfGlobalSection M (Hom.app f ⊤ (1 : Γ(X, ⊤)))) U.unop (1 : Γ(X, U.unop)) =
      Hom.app f U.unop (1 : Γ(X, U.unop))
    rw [homOfGlobalSection_app_one, ← Hom.app_presheaf_map]
    exact congrArg (Hom.app f U.unop)
      (map_one (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom :)
  right_inv u := by
    change Hom.app (homOfGlobalSection M u) ⊤ (1 : Γ(X, ⊤)) = u
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
  map_add' f g := rfl

omit [HasExt X.Modules] in
lemma unitHomAddEquiv_comp {M N : X.Modules} (f : 𝟙_ X.Modules ⟶ M) (g : M ⟶ N) :
    unitHomAddEquiv N (f ≫ g) = Hom.app g ⊤ (unitHomAddEquiv M f) :=
  rfl

/-- `Ext⁰(𝒪_X, M)` is the group of global sections of `M`. -/
noncomputable def extUnitZeroAddEquiv (M : X.Modules) : Ext (𝟙_ X.Modules) M 0 ≃+ Γ(M, ⊤) :=
  Abelian.Ext.addEquiv₀.trans (unitHomAddEquiv M)

lemma extUnitZeroAddEquiv_comp {M N : X.Modules} (g : M ⟶ N) (x : Ext (𝟙_ X.Modules) M 0) :
    extUnitZeroAddEquiv N (x.comp (Abelian.Ext.mk₀ g) (add_zero 0)) =
      Hom.app g ⊤ (extUnitZeroAddEquiv M x) := by
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective (𝟙_ X.Modules) M).2 x
  rw [Abelian.Ext.mk₀_comp_mk₀]
  have h (P : X.Modules) (h : 𝟙_ X.Modules ⟶ P) :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ h) = h :=
    Abelian.Ext.addEquiv₀.apply_symm_apply h
  simp only [extUnitZeroAddEquiv, AddEquiv.trans_apply, h]
  rfl

omit [HasExt X.Modules] in
/-- `H⁰(X, M) ≅ Γ(M, ⊤)`, naturally. -/
lemma zeroLinearEquiv_map {M N : X.Modules} (g : M ⟶ N) (x : M.H 0) :
    H.zeroLinearEquiv N (H.map g 0 x) = Hom.app g ⊤ (H.zeroLinearEquiv M x) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop) _ x).symm

/-- **`Ext` from the structure sheaf is sheaf cohomology.** For every `𝒪_X`-module `M`,
`Ext^n_X(𝒪_X, M) ≅ H^n(X, M)`: both vanish on injective `𝒪_X`-modules in positive degrees
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_injective`), agree with global sections in
degree `0`, and have long exact sequences, so dimension shifting along an embedding of `M` into
an injective module identifies them. -/
theorem nonempty_ext_unit_addEquiv_H (n : ℕ) (M : X.Modules) :
    Nonempty (Ext (𝟙_ X.Modules) M n ≃+ M.H n) := by
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  induction n generalizing M with
  | zero => exact ⟨(extUnitZeroAddEquiv M).trans (H.zeroLinearEquiv M).toAddEquiv.symm⟩
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hHI := subsingleton_H_of_injective S.X₂ n
    -- the connecting maps
    let δE : Ext (𝟙_ X.Modules) S.X₃ n →+ Ext (𝟙_ X.Modules) S.X₁ (n + 1) :=
      hS.extClass.postcomp (𝟙_ X.Modules) rfl
    have hδE : Function.Surjective δE := fun x ↦
      Abelian.Ext.covariant_sequence_exact₁ _ hS x (Abelian.Ext.eq_zero_of_injective _) rfl
    have hkerE : δE.ker = ((Abelian.Ext.mk₀ S.g).postcomp (𝟙_ X.Modules) (add_zero n)).range := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
      constructor
      · intro hx
        exact Abelian.Ext.covariant_sequence_exact₃ _ hS x rfl hx
      · rintro ⟨y, rfl⟩
        change (y.comp (Abelian.Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
        rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Abelian.Ext.comp_zero]
    have hδH : Function.Surjective (H.δ hS n) := by
      rw [← AddMonoidHom.range_eq_top, ← H.ker_map_f_eq_range_δ hS n]
      exact eq_top_iff.mpr fun x _ ↦ Subsingleton.elim _ _
    have hkerH := H.ker_δ_eq_range_map_g hS n
    rcases n with _ | n
    · -- degree one: the cokernels of `Γ(I) ⟶ Γ(Q)` on both sides
      let e : Ext (𝟙_ X.Modules) S.X₃ 0 ≃+ S.X₃.H 0 :=
        (extUnitZeroAddEquiv S.X₃).trans (H.zeroLinearEquiv S.X₃).toAddEquiv.symm
      refine ⟨addEquivOfSurjective δE (H.δ hS 0) hδE hδH e ?_⟩
      rw [hkerE, hkerH]
      ext z
      simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range]
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        refine ⟨(H.zeroLinearEquiv S.X₂).symm (extUnitZeroAddEquiv S.X₂ y), ?_⟩
        apply (H.zeroLinearEquiv S.X₃).injective
        change _ = (H.zeroLinearEquiv S.X₃) ((H.zeroLinearEquiv S.X₃).symm _)
        rw [LinearEquiv.apply_symm_apply, zeroLinearEquiv_map, LinearEquiv.apply_symm_apply]
        exact (extUnitZeroAddEquiv_comp S.g y).symm
      · rintro ⟨y, rfl⟩
        refine ⟨_, ⟨(extUnitZeroAddEquiv S.X₂).symm (H.zeroLinearEquiv S.X₂ y), rfl⟩, ?_⟩
        apply (H.zeroLinearEquiv S.X₃).injective
        change (H.zeroLinearEquiv S.X₃) ((H.zeroLinearEquiv S.X₃).symm _) = _
        rw [LinearEquiv.apply_symm_apply, zeroLinearEquiv_map]
        exact (extUnitZeroAddEquiv_comp S.g _).trans
          (congrArg _ (AddEquiv.apply_symm_apply _ _))
    · -- higher degrees: both connecting maps are isomorphisms
      obtain ⟨e⟩ := ih S.X₃
      have hEI : Subsingleton (Ext (𝟙_ X.Modules) S.X₂ (n + 1)) :=
        Abelian.Ext.subsingleton_of_injective _ _ n
      have hHI' := subsingleton_H_of_injective S.X₂ n
      refine ⟨addEquivOfSurjective δE (H.δ hS (n + 1)) hδE hδH e ?_⟩
      rw [hkerE, hkerH]
      have h₁ : ((Abelian.Ext.mk₀ S.g).postcomp (𝟙_ X.Modules) (add_zero (n + 1))).range = ⊥ := by
        refine eq_bot_iff.mpr ?_
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y 0, map_zero]
        exact zero_mem _
      have h₂ : (H.map S.g (n + 1)).range = ⊥ := by
        refine eq_bot_iff.mpr ?_
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y 0, map_zero]
        exact zero_mem _
      rw [h₁, h₂, AddSubgroup.map_bot]


/-- The forgetful functor from `𝒪_X`-modules to abelian sheaves is additive. -/
instance additive_toAb : (toAb X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive

variable (X) in
/-- The morphism from the constant sheaf `ℤ` to the underlying abelian sheaf of `𝒪_X` which
corresponds to the global section `1`. -/
noncomputable def constantSheafToUnit :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ (toAb X).obj (𝟙_ X.Modules) :=
  ((constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ _).symm
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm (1 : Γ(X, ⊤)))

/-- The canonical comparison map `Ext^n_X(𝒪_X, M) ⟶ H^n(X, M)`: an `Ext`-class of
`𝒪_X`-modules is mapped along the exact forgetful functor to abelian sheaves, and then
precomposed with the morphism `ℤ ⟶ 𝒪_X` given by the unit section. It is bijective
(`AlgebraicGeometry.Scheme.Modules.extUnitToH_bijective`). -/
noncomputable def extUnitToH (M : X.Modules) (n : ℕ) : Ext (𝟙_ X.Modules) M n →+ M.H n :=
  ((Abelian.Ext.mk₀ (constantSheafToUnit X)).precomp _ (zero_add n)).comp
    ((toAb X).mapExtAddHom (𝟙_ X.Modules) M n :
      Ext (𝟙_ X.Modules) M n →+ Abelian.Ext.{u} _ _ n)

lemma extUnitToH_apply (M : X.Modules) (n : ℕ) (x : Ext (𝟙_ X.Modules) M n) :
    extUnitToH M n x = (Abelian.Ext.mk₀ (constantSheafToUnit X)).comp
      (x.mapExactFunctor (toAb X) : Abelian.Ext.{u} _ _ n)
      (zero_add n) :=
  rfl

/-- The comparison map `AlgebraicGeometry.Scheme.Modules.extUnitToH` is natural in `M`. -/
lemma extUnitToH_comp_mk₀ {M N : X.Modules} (g : M ⟶ N) {n : ℕ}
    (x : Ext (𝟙_ X.Modules) M n) :
    extUnitToH N n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) = H.map g n (extUnitToH M n x) := by
  rw [extUnitToH_apply, extUnitToH_apply, H.map_apply_eq_comp, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- The comparison map `AlgebraicGeometry.Scheme.Modules.extUnitToH` commutes with the
connecting maps of a short exact sequence. -/
lemma extUnitToH_comp_extClass {S : ShortComplex X.Modules} (hS : S.ShortExact) {n : ℕ}
    (x : Ext (𝟙_ X.Modules) S.X₃ n) :
    extUnitToH S.X₁ (n + 1) (x.comp hS.extClass rfl) = H.δ hS n (extUnitToH S.X₃ n x) := by
  rw [extUnitToH_apply, extUnitToH_apply, H.δ_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- In degree `0`, the comparison map `AlgebraicGeometry.Scheme.Modules.extUnitToH` is the
identification of both sides with the global sections. -/
lemma zeroLinearEquiv_extUnitToH (M : X.Modules) (x : Ext (𝟙_ X.Modules) M 0) :
    H.zeroLinearEquiv M (extUnitToH M 0 x) = extUnitZeroAddEquiv M x := by
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  rw [extUnitToH_apply, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  have h₀ : H.zeroLinearEquiv M (Abelian.Ext.mk₀ (constantSheafToUnit X ≫ (toAb X).map f)) =
      AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ _
          (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (constantSheafToUnit X ≫ (toAb X).map f)))) :=
    rfl
  have hc : (constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ _
      (constantSheafToUnit X) = (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm (1 : Γ(X, ⊤)) :=
    Equiv.apply_symm_apply _ _
  rw [h₀, ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, hc, extUnitZeroAddEquiv, AddEquiv.trans_apply,
    ← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact congrArg (Hom.app f ⊤) ((AddCommGrpCat.uliftZMultiplesAddEquiv _).apply_symm_apply _)

/-- **`Ext` from the structure sheaf is sheaf cohomology.** The comparison map
`Ext^n_X(𝒪_X, M) ⟶ H^n(X, M)` is bijective: both sides vanish on injective `𝒪_X`-modules in
positive degrees (`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_injective`), agree with
global sections in degree `0`, and the comparison map is compatible with the long exact
sequences, so dimension shifting gives the claim. -/
theorem extUnitToH_bijective (M : X.Modules) (n : ℕ) : Function.Bijective (extUnitToH M n) := by
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  induction n generalizing M with
  | zero =>
    have h : ⇑(extUnitToH M 0) = (H.zeroLinearEquiv M).symm ∘ extUnitZeroAddEquiv M :=
      funext fun x ↦ by
        rw [Function.comp_apply, ← zeroLinearEquiv_extUnitToH, LinearEquiv.symm_apply_apply]
    rw [h]
    exact (H.zeroLinearEquiv M).symm.bijective.comp (extUnitZeroAddEquiv M).bijective
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hHI := subsingleton_H_of_injective S.X₂ n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Abelian.Ext.mk₀ S.g).postcomp (𝟙_ X.Modules) (add_zero n))
      (hS.extClass.postcomp (𝟙_ X.Modules) rfl) (H.map S.g n) (H.δ hS n)
      (extUnitToH S.X₂ n) (extUnitToH S.X₃ n) (extUnitToH M (n + 1))
      (AddMonoidHom.ext fun x ↦ (extUnitToH_comp_mk₀ S.g x).symm)
      (AddMonoidHom.ext fun x ↦ (extUnitToH_comp_extClass hS x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      (fun y ↦ (AddMonoidHom.mem_ker.symm.trans
        (SetLike.ext_iff.mp (H.ker_δ_eq_range_map_g hS n) y)).trans AddMonoidHom.mem_range)
      (ih S.X₂).2 (ih S.X₃)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS x
        (Abelian.Ext.eq_zero_of_injective _) rfl)
      (by
        rw [← AddMonoidHom.range_eq_top, ← H.ker_map_f_eq_range_δ hS n]
        exact eq_top_iff.mpr fun x _ ↦ Subsingleton.elim _ _)

/-- **`Ext` from the structure sheaf is sheaf cohomology**, canonically:
`Ext^n_X(𝒪_X, M) ≃ H^n(X, M)` via the comparison map
`AlgebraicGeometry.Scheme.Modules.extUnitToH`, which is natural in `M`
(`AlgebraicGeometry.Scheme.Modules.extUnitAddEquivH_comp_mk₀`). -/
noncomputable def extUnitAddEquivH (M : X.Modules) (n : ℕ) :
    Ext (𝟙_ X.Modules) M n ≃+ M.H n :=
  AddEquiv.ofBijective (extUnitToH M n) (extUnitToH_bijective M n)

@[simp]
lemma extUnitAddEquivH_apply (M : X.Modules) (n : ℕ) (x : Ext (𝟙_ X.Modules) M n) :
    extUnitAddEquivH M n x = extUnitToH M n x :=
  rfl

/-- The isomorphism `AlgebraicGeometry.Scheme.Modules.extUnitAddEquivH` is natural in `M`. -/
lemma extUnitAddEquivH_comp_mk₀ {M N : X.Modules} (g : M ⟶ N) {n : ℕ}
    (x : Ext (𝟙_ X.Modules) M n) :
    extUnitAddEquivH N n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) =
      H.map g n (extUnitAddEquivH M n x) :=
  extUnitToH_comp_mk₀ g x

end Comparison


section LocallyFree

/-- `Ext` is invariant under isomorphisms in its second variable. -/
noncomputable def extAddEquivOfIsoRight {A B B' : X.Modules} (e : B ≅ B') (n : ℕ) :
    Ext A B n ≃+ Ext A B' n where
  toFun x := x.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id]
    exact Abelian.Ext.comp_mk₀_id x
  right_inv x := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id]
    exact Abelian.Ext.comp_mk₀_id x
  map_add' x y := Abelian.Ext.add_comp _ _ _ _

/-- Evaluation of `AlgebraicGeometry.Scheme.Modules.extAddEquivOfIsoRight`. -/
lemma extAddEquivOfIsoRight_apply {A B B' : X.Modules} (e : B ≅ B') {n : ℕ} (x : Ext A B n) :
    extAddEquivOfIsoRight e n x = x.comp (Abelian.Ext.mk₀ e.hom) (add_zero n) :=
  rfl

/-- `Ext` is invariant under isomorphisms in its first variable. -/
noncomputable def extAddEquivOfIsoLeft {A A' B : X.Modules} (e : A' ≅ A) (n : ℕ) :
    Ext A B n ≃+ Ext A' B n where
  toFun x := (Abelian.Ext.mk₀ e.hom).comp x (zero_add n)
  invFun x := (Abelian.Ext.mk₀ e.inv).comp x (zero_add n)
  left_inv x := by
    dsimp only
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
    exact Abelian.Ext.mk₀_id_comp x
  right_inv x := by
    dsimp only
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id]
    exact Abelian.Ext.mk₀_id_comp x
  map_add' x y := Abelian.Ext.comp_add _ _ _ _

/-- Evaluation of `AlgebraicGeometry.Scheme.Modules.extAddEquivOfIsoLeft`. -/
lemma extAddEquivOfIsoLeft_apply {A A' B : X.Modules} (e : A' ≅ A) {n : ℕ} (x : Ext A B n) :
    extAddEquivOfIsoLeft e n x = (Abelian.Ext.mk₀ e.hom).comp x (zero_add n) :=
  rfl

/-- For a finite locally free `ℱ`, tensoring with the dual is the internal hom out of `ℱ`. -/
noncomputable def tensorLeftDualIsoIhom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    tensorLeft ℱᵛ ≅ ihom ℱ :=
  NatIso.ofComponents (fun N ↦ asIso (dualTensorHom ℱ N)) fun g ↦
    dualTensorHom_naturality_right ℱ g

end LocallyFree
/-- **Ext of a finite locally free module.** For a finite locally free `𝒪_X`-module `ℱ` and any
`𝒪_X`-module `𝒢`, `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`. Indeed `Hom(ℱ, -) = Γ(X, ℱᵛ ⊗ -)` is the
composite of the exact functor `ℱᵛ ⊗ -` with `Γ(X, -)`. In particular
`Ext^i_X(𝒪_X, 𝒢) = H^i(X, 𝒢)`. -/
theorem nonempty_ext_addEquiv_H (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteLocallyFree] (i : ℕ) :
    Nonempty (Ext ℱ 𝒢 i ≃+ (ℱᵛ ⊗ 𝒢).H i) := by
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  have := IsFiniteLocallyFree.dual ℱ
  have := SheafOfModules.isIso_bidual (R := X.sheaf) ℱ
  -- `ℱ ⊗ -` and `Hom(ℱ, -)` are exact: they are isomorphic to internal homs, respectively
  -- tensor products, out of finite locally free modules
  let eR : tensorLeft ℱᵛ ≅ ihom ℱ := tensorLeftDualIsoIhom ℱ
  let eL : tensorLeft ℱ ≅ ihom ℱᵛ :=
    (tensoringLeft X.Modules).mapIso (asIso (SheafOfModules.bidual (R := X.sheaf) ℱ)) ≪≫
      tensorLeftDualIsoIhom ℱᵛ
  have hadd (A : X.Modules) : (tensorLeft A).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
      (ihom.adjunction A).leftAdjoint_preservesColimits
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft A)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have := hadd ℱ
  have := hadd ℱᵛ
  have : PreservesFiniteLimits (tensorLeft ℱ) := preservesFiniteLimits_of_natIso eL.symm
  have : PreservesFiniteColimits (ihom ℱ) := preservesFiniteColimits_of_natIso eR
  have : (ihom ℱ).Additive := Functor.additive_of_iso eR
  let adj := ihom.adjunction ℱ
  have hbij := adj.mapExtCounit_bijective (𝟙_ X.Modules) 𝒢 i
  obtain ⟨e⟩ := nonempty_ext_unit_addEquiv_H i (ℱᵛ ⊗ 𝒢)
  exact ⟨(extAddEquivOfIsoLeft (ρ_ ℱ) i).trans ((AddEquiv.ofBijective _ hbij).symm.trans
    ((extAddEquivOfIsoRight (eR.app 𝒢).symm i).trans e))⟩


section LocallyFreeCanonical

omit [HasExt X.Modules] in
/-- The category of `𝒪_X`-modules has enough injectives, being a Grothendieck abelian
category. -/
instance enoughInjectives : EnoughInjectives X.Modules :=
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  IsGrothendieckAbelian.enoughInjectives

omit [HasExt X.Modules] in
/-- Tensoring with an `𝒪_X`-module is additive, being a left adjoint. -/
instance additive_tensorLeft (A : X.Modules) : (tensorLeft A).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
    (ihom.adjunction A).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft A)
  exact Functor.additive_of_preservesBinaryBiproducts _

omit [HasExt X.Modules] in
/-- Tensoring with a finite locally free `𝒪_X`-module `ℱ` is left exact: it is isomorphic to the
internal hom out of the dual of `ℱ`. -/
instance preservesFiniteLimits_tensorLeft (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    PreservesFiniteLimits (tensorLeft ℱ) := by
  have := IsFiniteLocallyFree.dual ℱ
  have := SheafOfModules.isIso_bidual (R := X.sheaf) ℱ
  exact preservesFiniteLimits_of_natIso ((tensoringLeft X.Modules).mapIso
    (asIso (SheafOfModules.bidual (R := X.sheaf) ℱ)) ≪≫ tensorLeftDualIsoIhom ℱᵛ).symm

omit [HasExt X.Modules] in
/-- The internal hom out of a finite locally free `𝒪_X`-module `ℱ` is right exact: it is
isomorphic to tensoring with the dual of `ℱ`. -/
instance preservesFiniteColimits_ihom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    PreservesFiniteColimits (ihom ℱ) :=
  preservesFiniteColimits_of_natIso (tensorLeftDualIsoIhom ℱ)

omit [HasExt X.Modules] in
/-- The internal hom out of a finite locally free `𝒪_X`-module is additive. -/
instance additive_ihom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] : (ihom ℱ).Additive :=
  Functor.additive_of_iso (tensorLeftDualIsoIhom ℱ)

/-- **Ext of a finite locally free module.** For a finite locally free `𝒪_X`-module `ℱ` and any
`𝒪_X`-module `𝒢`, the canonical isomorphism `Ext^i_X(ℱ, 𝒢) ≃ H^i(X, ℱᵛ ⊗ 𝒢)`: the composite of
`Ext^i(ℱ, 𝒢) = Ext^i(ℱ ⊗ 𝒪_X, 𝒢) ≃ Ext^i(𝒪_X, Hom(ℱ, 𝒢))` (the `Ext`-adjunction for the exact
adjoint functors `ℱ ⊗ -` and `Hom(ℱ, -)`), of `Hom(ℱ, 𝒢) ≅ ℱᵛ ⊗ 𝒢`, and of the comparison
`AlgebraicGeometry.Scheme.Modules.extUnitAddEquivH`. It is natural in `𝒢`
(`AlgebraicGeometry.Scheme.Modules.extAddEquivH_comp_mk₀`). -/
noncomputable def extAddEquivH (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteLocallyFree] (i : ℕ) :
    Ext ℱ 𝒢 i ≃+ (ℱᵛ ⊗ 𝒢).H i :=
  (extAddEquivOfIsoLeft (ρ_ ℱ) i).trans
    (((ihom.adjunction ℱ).extAddEquiv (𝟙_ X.Modules) 𝒢 i).symm.trans
      ((extAddEquivOfIsoRight ((tensorLeftDualIsoIhom ℱ).app 𝒢).symm i).trans
        (extUnitAddEquivH _ i)))

/-- The isomorphism `AlgebraicGeometry.Scheme.Modules.extAddEquivH` is natural in `𝒢`. -/
lemma extAddEquivH_comp_mk₀ (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] {𝒢 𝒢' : X.Modules}
    (g : 𝒢 ⟶ 𝒢') {i : ℕ} (x : Ext ℱ 𝒢 i) :
    extAddEquivH ℱ 𝒢' i (x.comp (Abelian.Ext.mk₀ g) (add_zero i)) =
      H.map (ℱᵛ ◁ g) i (extAddEquivH ℱ 𝒢 i x) := by
  have hadj (z : Ext (ℱ ⊗ 𝟙_ X.Modules) 𝒢 i) :
      ((ihom.adjunction ℱ).extAddEquiv (𝟙_ X.Modules) 𝒢' i).symm
          (z.comp (Abelian.Ext.mk₀ g) (add_zero i)) =
        (((ihom.adjunction ℱ).extAddEquiv (𝟙_ X.Modules) 𝒢 i).symm z).comp
          (Abelian.Ext.mk₀ ((ihom ℱ).map g)) (add_zero i) := by
    refine ((ihom.adjunction ℱ).extAddEquiv (𝟙_ X.Modules) 𝒢' i).symm_apply_eq.mpr ?_
    refine Eq.trans ?_ ((ihom.adjunction ℱ).mapExtCounit_comp_mk₀ (𝟙_ X.Modules) g _).symm
    exact congrArg (fun y ↦ y.comp (Abelian.Ext.mk₀ g) (add_zero i))
      (((ihom.adjunction ℱ).extAddEquiv (𝟙_ X.Modules) 𝒢 i).apply_symm_apply z).symm
  simp only [extAddEquivH, AddEquiv.trans_apply]
  refine (congrArg (extUnitAddEquivH _ i) ?_).trans (extUnitAddEquivH_comp_mk₀ (ℱᵛ ◁ g) _)
  rw [extAddEquivOfIsoLeft_apply, ← Abelian.Ext.comp_assoc_of_third_deg_zero]
  erw [hadj]
  rw [extAddEquivOfIsoRight_apply, extAddEquivOfIsoRight_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  congr 2
  exact (tensorLeftDualIsoIhom ℱ).inv.naturality g

end LocallyFreeCanonical

end AlgebraicGeometry.Scheme.Modules
