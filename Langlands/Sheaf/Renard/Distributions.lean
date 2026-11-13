import Langlands.Sheaf.Renard.VectorSheafScalars
import Langlands.Sheaf.CompactSupport.IndependentUniverses
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Distributions on complex vector sheaves

Renard (9 July 2026), II.2.5 Definition, printed p.42 / PDF p.48.
The full algebraic dual of compactly supported sections carries the transpose
of the locally constant scalar action.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.Distributions

open CategoryTheory TopologicalSpace Opposite
open VectorSheafScalars
open Langlands.Sheaf.CompactSupport

attribute [local instance] IndependentUniverses.forget₂_preservesFilteredColimits
  IndependentUniverses.forget_preservesFilteredColimits

universe u

variable {X : Type u} [TopologicalSpace X] (F : VectorSheaf X)

/-- Renard's compactly supported sections of a vector sheaf. -/
abbrev CompactSection : Type u := IndependentUniverses.submodule F.presheaf

/-- Global locally constant functions read on the largest open. -/
def topScalar : LocallyConstant X ℂ →ₐ[ℂ] LocallyConstant (⊤ : Opens X) ℂ :=
  LocallyConstant.comapₐ ℂ ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem topScalar_apply (f : LocallyConstant X ℂ) (x : (⊤ : Opens X)) :
    topScalar f x = f x := rfl

/-- Locally constant multiplication does not enlarge a section's support. -/
theorem support_smul_subset (f : LocallyConstant X ℂ) (s : F.presheaf.obj (op ⊤)) :
    IndependentUniverses.support F.presheaf (topScalar f • s) ⊆
      IndependentUniverses.support F.presheaf s := by
  intro x hx
  by_contra hs
  have h0 : F.presheaf.Γgerm x s = 0 := by
    simpa [IndependentUniverses.support] using hs
  have h : F.presheaf.Γgerm x (topScalar f • s) =
      f x • F.presheaf.Γgerm x s :=
    germ_lc_smul F (topScalar f) s x trivial
  exact hx (by rw [h, h0, smul_zero])

/-- Locally constant multiplication on compactly supported sections. -/
def compactSmul (f : LocallyConstant X ℂ) (s : CompactSection F) : CompactSection F :=
  ⟨topScalar f • s.val, s.property.of_isClosed_subset
    (IndependentUniverses.isClosed_support F.presheaf _) (support_smul_subset F f s.val)⟩

/-- The full ring of locally constant functions acts on compact sections. -/
instance compactSectionModule : Module (LocallyConstant X ℂ) (CompactSection F) where
  smul := compactSmul F
  one_smul s := Subtype.ext (by
    change topScalar (1 : LocallyConstant X ℂ) • s.val = s.val
    rw [map_one, one_smul])
  mul_smul f g s := Subtype.ext (by
    change topScalar (f * g) • s.val = topScalar f • topScalar g • s.val
    rw [map_mul, mul_smul])
  smul_zero f := Subtype.ext (smul_zero _)
  smul_add f s t := Subtype.ext (smul_add _ _ _)
  add_smul f g s := Subtype.ext (by
    change topScalar (f + g) • s.val = topScalar f • s.val + topScalar g • s.val
    rw [map_add, add_smul])
  zero_smul s := Subtype.ext (by
    change topScalar (0 : LocallyConstant X ℂ) • s.val = 0
    rw [map_zero, zero_smul])

@[simp]
theorem coe_compact_smul (f : LocallyConstant X ℂ) (s : CompactSection F) :
    ((f • s : CompactSection F) : F.presheaf.obj (op ⊤)) = topScalar f • s.val := rfl

/-- The scalar action on compact sections has the source's pointwise germ formula. -/
@[simp]
theorem Γgerm_compact_smul (f : LocallyConstant X ℂ) (s : CompactSection F) (x : X) :
    F.presheaf.Γgerm x (f • s : CompactSection F).val =
      f x • F.presheaf.Γgerm x s.val :=
  germ_lc_smul F (topScalar f) s.val x trivial

instance compactSectionScalarTower :
    IsScalarTower ℂ (LocallyConstant X ℂ) (CompactSection F) where
  smul_assoc c f s := Subtype.ext (by
    change topScalar (c • f) • s.val = c • topScalar f • s.val
    rw [map_smul, smul_assoc])

instance compactSectionSmulCommClass :
    SMulCommClass ℂ (LocallyConstant X ℂ) (CompactSection F) where
  smul_comm c f s := Subtype.ext (by
    change c • topScalar f • s.val = topScalar f • c • s.val
    exact smul_comm c (topScalar f) s.val)

/-- Constant functions act by the original complex scalar structure. -/
@[simp]
theorem compact_constants_smul (c : ℂ) (s : CompactSection F) :
    algebraMap ℂ (LocallyConstant X ℂ) c • s = c • s := by
  apply Subtype.ext
  change topScalar (algebraMap ℂ (LocallyConstant X ℂ) c) • s.val = c • s.val
  rw [(topScalar (X := X)).commutes c, VectorSheafScalars.algebraMap_smul]

/-- Multiplication by a locally constant function is complex-linear. -/
def compactScalarLinear (f : LocallyConstant X ℂ) :
    CompactSection F →ₗ[ℂ] CompactSection F where
  toFun := (f • ·)
  map_add' := smul_add f
  map_smul' c s := (smul_comm c f s).symm

@[simp]
theorem compactScalarLinear_apply (f : LocallyConstant X ℂ) (s : CompactSection F) :
    compactScalarLinear F f s = f • s := rfl

/-- Renard II.2.5: distributions are the full complex algebraic dual. -/
abbrev Distribution := Module.Dual ℂ (CompactSection F)

/-- Renard's transpose action, `(f • T)(s) = T(f • s)`. -/
def distributionSmul (f : LocallyConstant X ℂ) (T : Distribution F) : Distribution F :=
  T.comp (compactScalarLinear F f)

/-- The transpose action is a module action, using commutativity of the scalar ring. -/
instance distributionModule : Module (LocallyConstant X ℂ) (Distribution F) where
  smul := distributionSmul F
  one_smul T := by
    ext s
    change T ((1 : LocallyConstant X ℂ) • s) = T s
    rw [one_smul]
  mul_smul f g T := by
    ext s
    change T ((f * g) • s) = T (g • f • s)
    rw [mul_comm f g, mul_smul]
  smul_zero f := by
    ext s
    rfl
  smul_add f T S := by
    ext s
    rfl
  add_smul f g T := by
    ext s
    change T ((f + g) • s) = T (f • s) + T (g • s)
    rw [add_smul, map_add]
  zero_smul T := by
    ext s
    change T ((0 : LocallyConstant X ℂ) • s) = 0
    rw [zero_smul, map_zero]

/-- The pairing formula in Renard II.2.5's Definition. -/
@[simp]
theorem smul_apply (f : LocallyConstant X ℂ) (T : Distribution F) (s : CompactSection F) :
    (f • T) s = T (f • s) := rfl

instance distributionScalarTower :
    IsScalarTower ℂ (LocallyConstant X ℂ) (Distribution F) where
  smul_assoc c f T := by
    ext s
    change T ((c • f) • s) = c • T (f • s)
    rw [smul_assoc, map_smul]

instance distributionSmulCommClass :
    SMulCommClass ℂ (LocallyConstant X ℂ) (Distribution F) where
  smul_comm c f T := by
    ext s
    rfl

/-- Constant locally constant functions give the usual complex scaling on the dual. -/
@[simp]
theorem constants_smul (c : ℂ) (T : Distribution F) :
    algebraMap ℂ (LocallyConstant X ℂ) c • T = c • T := by
  ext s
  change T (algebraMap ℂ (LocallyConstant X ℂ) c • s) = c • T s
  rw [compact_constants_smul, map_smul]

section Morphisms

variable {F} {G H : VectorSheaf X}

/-- Compact-section maps commute with the full locally constant scalar action. -/
theorem compactSectionMap_smul (φ : F ⟶ G) (f : LocallyConstant X ℂ)
    (s : CompactSection F) :
    IndependentUniverses.map φ.hom (f • s) = f • IndependentUniverses.map φ.hom s :=
  Subtype.ext (app_smul φ (topScalar f) s.val)

/-- The contravariant map on distributions induced by an actual sheaf morphism. -/
def transpose (φ : F ⟶ G) : Distribution G →ₗ[ℂ] Distribution F :=
  (IndependentUniverses.map φ.hom).dualMap

@[simp]
theorem transpose_apply (φ : F ⟶ G) (T : Distribution G) (s : CompactSection F) :
    transpose φ T s = T (IndependentUniverses.map φ.hom s) := rfl

/-- Transposition respects the full locally constant scalar action. -/
theorem transpose_smul (φ : F ⟶ G) (f : LocallyConstant X ℂ) (T : Distribution G) :
    transpose φ (f • T) = f • transpose φ T := by
  ext s
  change T (f • IndependentUniverses.map φ.hom s) = T (IndependentUniverses.map φ.hom (f • s))
  rw [compactSectionMap_smul]

@[simp]
theorem transpose_id (F : VectorSheaf X) :
    transpose (𝟙 F) = LinearMap.id := by
  ext T s
  rfl

@[simp]
theorem transpose_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    transpose (φ ≫ ψ) = (transpose φ).comp (transpose ψ) := by
  ext T s
  rfl

end Morphisms

/-- The complex algebraic dual of compact sections as an actual contravariant functor. -/
def functor : (VectorSheaf X)ᵒᵖ ⥤ ModuleCat.{u} ℂ where
  obj F := ModuleCat.of ℂ (Distribution F.unop)
  map φ := ModuleCat.ofHom (transpose φ.unop)
  map_id F := by
    apply ModuleCat.hom_ext
    exact transpose_id F.unop
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    ext T s
    rfl

end Langlands.Sheaf.Renard.Distributions
