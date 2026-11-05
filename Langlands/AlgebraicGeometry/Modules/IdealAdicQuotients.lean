import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.RingTheory.Ideal.Operations

/-! # Actual ideal multiples and adic quotients of scheme modules -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- A base scalar restricted to an open of the source. -/
def scalar (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
    (DerivedSections.structureRingHom f).hom

lemma scalar_naturality {U V : X.Opensᵒᵖ} (i : U ⟶ V) (a : R) :
    X.presheaf.map i (scalar f U.unop a) = scalar f V.unop a := by
  change (X.presheaf.map i) ((X.presheaf.map
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
    ((DerivedSections.structureRingHom f) a)) = _
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Sectionwise span of products of base-ideal elements and module sections. -/
def multiplePresubmodule (I : Ideal R) (M : X.Modules) :
    PresheafOfModules.Submodule M.val where
  obj U := Submodule.span (X.ringCatSheaf.obj.obj U)
    {x | ∃ a ∈ I, ∃ m : M.val.obj U, x = scalar f U.unop a • m}
  map {U V} i := by
    apply Submodule.span_le.2
    rintro x ⟨a, ha, m, rfl⟩
    change M.val.map i (scalar f U.unop a • m) ∈
      Submodule.span (X.ringCatSheaf.obj.obj V)
        {x | ∃ a ∈ I, ∃ m : M.val.obj V, x = scalar f V.unop a • m}
    rw [M.val.map_smul]
    change X.presheaf.map i (scalar f U.unop a) • M.val.map i m ∈ _
    rw [scalar_naturality]
    exact Submodule.subset_span ⟨a, ha, M.val.map i m, rfl⟩

lemma multiplePresubmodule_mono {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    multiplePresubmodule f I M ≤ multiplePresubmodule f J M := by
  intro U
  apply Submodule.span_mono
  rintro x ⟨a, ha, m, rfl⟩
  exact ⟨a, h ha, m, rfl⟩

/-- The sheaf of local ideal multiples, formed by module sheafification. -/
def multiple (I : Ideal R) (M : X.Modules) : X.Modules :=
  (sheafify X).obj (multiplePresubmodule f I M).toPresheafOfModules

/-- The canonical morphism of the ideal multiple into its ambient module. -/
def inclusion (I : Ideal R) (M : X.Modules) : multiple f I M ⟶ M :=
  (sheafify X).map (multiplePresubmodule f I M).ι ≫
    (sheafifyForgetIso X).hom.app M

instance (I : Ideal R) (M : X.Modules) : Mono (inclusion f I M) := by
  change Mono ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (multiplePresubmodule f I M).ι ≫ ((sheafifyForgetIso X).app M).hom)
  infer_instance

/-- The map of ideal multiples induced by an inclusion of base ideals. -/
def multipleMap {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    multiple f I M ⟶ multiple f J M :=
  (sheafify X).map
    (PresheafOfModules.Submodule.homOfLE (multiplePresubmodule_mono f h M))

@[reassoc (attr := simp)]
lemma multipleMap_inclusion {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    multipleMap f h M ≫ inclusion f J M = inclusion f I M := by
  unfold multipleMap inclusion
  rw [← Category.assoc, ← Functor.map_comp,
    PresheafOfModules.Submodule.homOfLE_ι]

/-- The actual sheaf quotient by the local ideal multiple. -/
def quotient (I : Ideal R) (M : X.Modules) : X.Modules :=
  cokernel (inclusion f I M)

/-- The canonical projection to the ideal quotient. -/
def projection (I : Ideal R) (M : X.Modules) : M ⟶ quotient f I M :=
  cokernel.π (inclusion f I M)

instance (I : Ideal R) (M : X.Modules) : Epi (projection f I M) := by
  unfold projection
  infer_instance

/-- Quotient transition induced by an inclusion of ideals. -/
def quotientMap {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    quotient f I M ⟶ quotient f J M :=
  cokernel.desc (inclusion f I M) (projection f J M) (by
    rw [← multipleMap_inclusion f h M, Category.assoc]
    rw [projection, cokernel.condition, comp_zero])

@[reassoc (attr := simp)]
lemma projection_quotientMap {I J : Ideal R} (h : I ≤ J) (M : X.Modules) :
    projection f I M ≫ quotientMap f h M = projection f J M :=
  cokernel.π_desc _ _ _

@[simp]
lemma quotientMap_refl (I : Ideal R) (M : X.Modules) :
    quotientMap f (le_refl I) M = 𝟙 (quotient f I M) := by
  apply (cancel_epi (projection f I M)).1
  simp

@[reassoc (attr := simp)]
lemma quotientMap_comp {I J K : Ideal R} (hIJ : I ≤ J) (hJK : J ≤ K)
    (M : X.Modules) :
    quotientMap f hIJ M ≫ quotientMap f hJK M =
      quotientMap f (hIJ.trans hJK) M := by
  apply (cancel_epi (projection f I M)).1
  simp

/-- The quotient by the `n`-th power of the base ideal; at zero this is the
quotient by the unit ideal. -/
abbrev adicQuotient (I : Ideal R) (M : X.Modules) (n : ℕ) : X.Modules :=
  quotient f (I ^ n) M

/-- The canonical adic projection. -/
abbrev adicProjection (I : Ideal R) (M : X.Modules) (n : ℕ) :
    M ⟶ adicQuotient f I M n :=
  projection f (I ^ n) M

/-- The transition from the `k`-th quotient to the `n`-th, for `n ≤ k`. -/
abbrev adicTransition (I : Ideal R) (M : X.Modules) {n k : ℕ} (h : n ≤ k) :
    adicQuotient f I M k ⟶ adicQuotient f I M n :=
  quotientMap f (Ideal.pow_le_pow_right h) M

end Langlands.AlgebraicGeometry.Modules.IdealAdic
