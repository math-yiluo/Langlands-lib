/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Strict-perfect coefficient packages

Source: the Weil conjectures blueprint, proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).

## Main definitions

- `SheafOfModules.StrictPerfectCoefficientPackage`: the chosen degreewise splittings.
- `SheafOfModules.StrictPerfectCoefficientRepresentation`: a bounded localized model.
- `SheafOfModules.IsLocallyStrictPerfectComplex` and `SheafOfModules.IsPerfectOnRingedSite`:
  local perfectness of complexes and perfectness of derived objects.
- `ModuleCat.StrictPerfectCoefficientPackage`: the global ring-module version.
- `ModuleCat.StrictPerfectCoefficientPackage.constant`: its associated constant sheaf package.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Chosen degreewise finite-free splittings, with no chain-map condition.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientPackage (R : Sheaf J RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) where
  /-- Rank of the finite free term in each degree. -/
  N : ℤ → ℕ
  /-- Inclusion into a finite tuple sheaf. -/
  i (r : ℤ) : F.X r ⟶ ∏ᶜ fun _ : Fin (N r) => SheafOfModules.unit R
  /-- Retraction from the same finite tuple sheaf. -/
  p (r : ℤ) : (∏ᶜ fun _ : Fin (N r) => SheafOfModules.unit R) ⟶ F.X r
  /-- Splitting relation, in diagrammatic composition order. -/
  splitting (r : ℤ) : i r ≫ p r = 𝟙 (F.X r)

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

attribute [instance] CategoryTheory.module_overFunctor_preservesZero

/-- Local perfectness: covering sieves admit bounded, finite-free retract models mapping
quasi-isomorphically to the restricted complex. Bounds and ranks vary with the cover member.
Source: Stacks, Tag 08G5, and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsLocallyStrictPerfectComplex (R : Sheaf J CommRingCat.{u})
    (K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (SheafOfModules.{u}
          (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ℤ,
        (∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) ∧
        Nonempty (StrictPerfectCoefficientPackage _ F) ∧
        ∃ α : F ⟶ ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K, QuasiIso α

/-- Perfect objects are exactly the objects represented by locally perfect complexes.
Source: Stacks, Tag 08G5, and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsPerfectOnRingedSite (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (E : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) : Prop :=
  ∃ K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ,
    IsLocallyStrictPerfectComplex R K ∧ Nonempty (E ≅ DerivedCategory.Q.obj K)

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

/-- A global coefficient package for a fixed representative. The standard finite free
module is the module of finite tuples, with its standard basis.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientPackage (F : CochainComplex (ModuleCat.{u} Λ) ℤ) where
  /-- Finite ranks, allowed to be zero. -/
  N : ℤ → ℕ
  /-- Degreewise inclusions. -/
  i (r : ℤ) : F.X r ⟶ ModuleCat.of Λ (Fin (N r) → Λ)
  /-- Degreewise projections. -/
  p (r : ℤ) : ModuleCat.of Λ (Fin (N r) → Λ) ⟶ F.X r
  /-- The projections split the inclusions. -/
  splitting (r : ℤ) : i r ≫ p r = 𝟙 (F.X r)

end ModuleCat

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

/-- Constant presheaves of modules, with identity restriction maps.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def strictPerfectConstantPresheaf :
    ModuleCat.{u} Λ ⥤ PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj M := { obj := fun _ => M, map := fun _ => ModuleCat.ofHom (LinearMap.id) }
  map f := { app := fun _ => f }

/-- Constant presheaves preserve addition componentwise.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: evaluate the two maps at any object; both are the original sum of linear maps. -/
theorem strictPerfectConstantPresheaf_additive :
    (strictPerfectConstantPresheaf (C := C) Λ).Additive := by
  constructor
  intro M N f g
  apply PresheafOfModules.hom_ext
  intro X
  rfl

attribute [instance] strictPerfectConstantPresheaf_additive

/-- The associated constant sheaf of modules over the constant ring sheaf. This applies
module sheafification to the constant presheaf, using the ring-sheafification unit.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantSheaf :
    ModuleCat.{u} Λ ⥤ SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  strictPerfectConstantPresheaf (C := C) Λ ⋙
    PresheafOfModules.sheafification
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

/-- The constant module sheaf functor is additive.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: the constant presheaf functor is additive componentwise. Module sheafification
preserves finite products and the zero object, so it is additive; compose these functors. -/
theorem strictPerfectConstantSheaf_additive : (strictPerfectConstantSheaf J Λ).Additive := by
  have : (PresheafOfModules.sheafification
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).Additive :=
    (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  unfold strictPerfectConstantSheaf
  infer_instance

attribute [instance] strictPerfectConstantSheaf_additive

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

/-- Coordinate evaluation followed by the coefficient-ring sheafification unit is additive.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: addition of tuples is pointwise, so evaluation at `k` sends the sum to
`v k + w k`. Apply preservation of addition by the ring sheafification unit at `X`. -/
theorem strictPerfectConstantCoordinateComponent_map_add (n : ℕ) (k : Fin n)
    (X : Cᵒᵖ) (v w : Fin n → Λ) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X ((v + w) k) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (v k) +
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (w k) := by
  exact map_add _ _ _

/-- Coordinate evaluation followed by the coefficient-ring unit respects scalar multiplication.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: scalar multiplication of tuples is pointwise multiplication by `r`.
The unit preserves multiplication, and restriction of scalars makes the target action
multiplication by the image of `r` under that same unit. -/
theorem strictPerfectConstantCoordinateComponent_map_smul (n : ℕ) (k : Fin n)
    (X : Cᵒᵖ) (r : Λ) (v : Fin n → Λ) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X ((r • v) k) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X r *
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (v k) := by
  exact map_mul _ _ _

/-- A coordinate component, linear for the sheafification unit on coefficient rings.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantCoordinateComponent (n : ℕ) (k : Fin n) (X : Cᵒᵖ) :
    ModuleCat.of Λ (Fin n → Λ) ⟶
      ((PresheafOfModules.restrictScalars
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
          (SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).val).obj X :=
  ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
        (SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).val).obj X)
    { toFun := fun v => (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app X (v k)
      map_add' := strictPerfectConstantCoordinateComponent_map_add J Λ n k X
      map_smul' := strictPerfectConstantCoordinateComponent_map_smul J Λ n k X }

/-- The coordinate components are natural.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: evaluate at a tuple `v`. The left side is the image of `v k` under the ring
sheafification unit at `Y`; the right side is its image at `X` followed by restriction.
These agree by naturality of the ring sheafification unit. -/
theorem strictPerfectConstantCoordinate_naturality (n : ℕ) (k : Fin n)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((strictPerfectConstantPresheaf (C := C) Λ).obj
        (ModuleCat.of Λ (Fin n → Λ))).map f ≫
      (ModuleCat.restrictScalars
        (((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).map f).hom).map
          (strictPerfectConstantCoordinateComponent J Λ n k Y) =
    strictPerfectConstantCoordinateComponent J Λ n k X ≫
      ((PresheafOfModules.restrictScalars
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).obj
          (SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ))).val).map f :=
  by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f) (v k)

/-- A coordinate map, obtained from the constant presheaf coordinate by module sheafification.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantCoordinate (n : ℕ) (k : Fin n) :
    (strictPerfectConstantSheaf J Λ).obj (ModuleCat.of Λ (Fin n → Λ)) ⟶
      SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  (PresheafOfModules.sheafificationHomEquiv
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))).symm
    { app := strictPerfectConstantCoordinateComponent J Λ n k
      naturality := strictPerfectConstantCoordinate_naturality J Λ n k }

/-- The canonical finite-product comparison, with coordinates the sheafified projections.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def strictPerfectConstantFiniteFreeComparison (n : ℕ) :
    (strictPerfectConstantSheaf J Λ).obj (ModuleCat.of Λ (Fin n → Λ)) ⟶
      ∏ᶜ fun _ : Fin n =>
        SheafOfModules.unit ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  Pi.lift (strictPerfectConstantCoordinate J Λ n)

/-- The canonical finite-product comparison is invertible, also in rank zero.
Source: finite-product preservation of sheafification and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: before sheafification the finite tuple module is the product of `n` copies of the
coefficient ring. Sheafification preserves finite products (including the empty product),
and sheafifying the coefficient ring gives the constant ring sheaf. The displayed map is
precisely the comparison induced by these projections. Thus it is an isomorphism. -/
theorem strictPerfectConstantFiniteFreeComparison_isIso (n : ℕ) :
    IsIso (strictPerfectConstantFiniteFreeComparison J Λ n) := by
  let A := (constantSheaf J RingCat.{u}).obj (RingCat.of Λ)
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let P := (strictPerfectConstantPresheaf (C := C) Λ).obj (ModuleCat.of Λ Λ)
  let a : P ⟶ (PresheafOfModules.restrictScalars η).obj (unit A).val :=
    { app := fun X => ModuleCat.ofHom
        (X := P.obj X)
        (Y := ((PresheafOfModules.restrictScalars η).obj (unit A).val).obj X)
        { toFun := η.app X
          map_add' := map_add _
          map_smul' := by
            change ∀ r x : Λ, η.app X (r * x) = η.app X r * η.app X x
            exact (η.app X).hom.map_mul }
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (η.naturality f) x }
  let e : (strictPerfectConstantSheaf J Λ).obj (ModuleCat.of Λ Λ) ⟶ unit A :=
    (PresheafOfModules.sheafificationHomEquiv η).symm a
  let g := (PresheafOfModules.toPresheaf _).map a
  have : Presheaf.IsLocallyInjective J g := by
    constructor
    intro X x y h
    exact Presheaf.equalizerSieve_mem J η x y h
  have : Presheaf.IsLocallySurjective J g := by
    constructor
    intro X x
    exact Presheaf.imageSieve_mem J η x
  let q := (toSheaf A).map e
  have hfac : toSheafify J P.presheaf ≫ q.hom = g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv η
        (P := P) (F := unit A)).apply_symm_apply a)
  have : Presheaf.IsLocallySurjective J (toSheafify J P.presheaf) :=
    (J.W_toSheafify P.presheaf).isLocallySurjective
  have : Presheaf.IsLocallyInjective J q.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J g hfac
  have : Presheaf.IsLocallySurjective J q.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hfac
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).mp
    ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (toSheaf A)
  let G := strictPerfectConstantSheaf J Λ
  let t := G.mapIso (ModuleCat.piIsoPi (fun _ : Fin n => ModuleCat.of Λ Λ)).symm ≪≫
    PreservesProduct.iso G (fun _ : Fin n => ModuleCat.of Λ Λ) ≪≫
      Pi.mapIso (fun _ : Fin n => asIso e)
  have ht : t.hom = strictPerfectConstantFiniteFreeComparison J Λ n := by
    apply Pi.hom_ext
    intro k
    have hk : t.hom ≫ Pi.π _ k =
        G.map (ModuleCat.ofHom (LinearMap.proj k)) ≫ e := by
      simp only [t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
        Pi.mapIso_hom_π, PreservesProduct.iso_hom, piComparison_comp_π_assoc,
        asIso_hom]
      rw [← G.map_comp_assoc, ModuleCat.piIsoPi_inv_kernel_ι]
    rw [hk]
    change G.map (ModuleCat.ofHom (LinearMap.proj k)) ≫ e =
      Pi.lift (strictPerfectConstantCoordinate J Λ n) ≫ Pi.π _ k
    rw [Pi.lift_comp_π]
    let c := (strictPerfectConstantPresheaf (C := C) Λ).map
      (ModuleCat.ofHom (LinearMap.proj k) : ModuleCat.of Λ (Fin n → Λ) ⟶
        ModuleCat.of Λ Λ)
    have hc : c ≫ a =
        { app := strictPerfectConstantCoordinateComponent J Λ n k
          naturality := strictPerfectConstantCoordinate_naturality J Λ n k } := by
      apply PresheafOfModules.hom_ext
      intro X
      rfl
    have h := (PresheafOfModules.sheafificationAdjunction η).homEquiv_naturality_left_symm
      (Y := unit A) c a
    rw [hc] at h
    have heq (M : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))) :
        (PresheafOfModules.sheafificationAdjunction η).homEquiv M (unit A) =
          PresheafOfModules.sheafificationHomEquiv η := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply η f
    rw [heq, heq] at h
    dsimp only [G, strictPerfectConstantSheaf, Functor.comp_map,
      strictPerfectConstantCoordinate, e]
    exact h.symm
  rw [← ht]
  infer_instance

attribute [instance] strictPerfectConstantFiniteFreeComparison_isIso

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

end ModuleCat
