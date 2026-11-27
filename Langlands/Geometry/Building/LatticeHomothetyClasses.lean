import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-! # Lattices in `F^n` and their homothety classes

Let `F` be a field with a valuative relation, `𝒪[F]` its valuation ring and `n` a type.
An `𝒪[F]`-lattice in the column space `n → F` is a finitely generated `𝒪[F]`-submodule whose
`F`-span is `n → F` (Mathlib's `Submodule.IsLattice`). This module constructs

* `ValuationRingLattice F n`, the type of `𝒪[F]`-lattices in `n → F`;
* the homothety relation `M = a L` for some `a ∈ Fˣ`, and the type `LatticeClass F n` of
  homothety classes `[L]`;
* for finite `n`, the action of `GL_n(F)` on lattices by `g · L = {g v | v ∈ L}` (column
  vectors), and the induced action `g · [L] = [g L]` on homothety classes.

For a nonarchimedean local field `F` and `n = Fin 2`, the homothety classes of lattices are the
vertices of the Bruhat–Tits tree of `GL_2(F)` (Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach*, 15.1.23 and Proposition 15.1.31), as the module documentation of Mathlib's
`Mathlib.Algebra.Module.Lattice` also recalls.
-/

noncomputable section

universe u

open scoped Pointwise ValuativeRel Matrix

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] (n : Type)

/-! ### Lattices and their homothety classes -/

/-- An `𝒪[F]`-lattice in the column space `n → F`: an `𝒪[F]`-submodule that is finitely
generated and spans `n → F` over `F` (Mathlib's `Submodule.IsLattice`). -/
@[ext]
structure ValuationRingLattice where
  /-- The underlying `𝒪[F]`-submodule `L ⊆ n → F`. -/
  carrier : Submodule 𝒪[F] (n → F)
  /-- `L` is finitely generated over `𝒪[F]` and spans `n → F` over `F`. -/
  isLattice : carrier.IsLattice F

variable {F n}

/-- Two lattices are homothetic if `M = a L` for some `a ∈ Fˣ`. -/
def ValuationRingLattice.Homothetic (L M : ValuationRingLattice F n) : Prop :=
  ∃ a : Fˣ, M.carrier = a • L.carrier

variable (F n)

/-- Homothety is an equivalence relation on lattices. -/
def ValuationRingLattice.homothetySetoid : Setoid (ValuationRingLattice F n) where
  r := ValuationRingLattice.Homothetic
  iseqv :=
    ⟨fun _ => ⟨1, (one_smul _ _).symm⟩,
      fun {_ _} ⟨a, h⟩ => ⟨a⁻¹, by rw [h, inv_smul_smul]⟩,
      fun {_ _ _} ⟨a, h⟩ ⟨b, h'⟩ => ⟨b * a, by rw [h', h, mul_smul]⟩⟩

/-- The homothety classes `[L]` of `𝒪[F]`-lattices `L` in `n → F`. -/
def LatticeClass : Type u :=
  Quotient (ValuationRingLattice.homothetySetoid F n)

variable {F n}

/-- The homothety class `[L]` of a lattice `L`. -/
def LatticeClass.mk (L : ValuationRingLattice F n) : LatticeClass F n :=
  Quotient.mk'' L

theorem LatticeClass.mk_surjective : Function.Surjective (LatticeClass.mk (F := F) (n := n)) :=
  Quotient.mk''_surjective

theorem LatticeClass.mk_eq_mk_iff {L M : ValuationRingLattice F n} :
    LatticeClass.mk L = LatticeClass.mk M ↔ L.Homothetic M :=
  Quotient.eq''

/-! ### The action of `GL_n(F)` -/

variable (F n) [Fintype n] [DecidableEq n]

/-- The image `g L = {g v | v ∈ L}` of an `𝒪[F]`-submodule `L` of `n → F` under the invertible
matrix `g`, acting on column vectors. -/
def glImage (g : GL n F) (L : Submodule 𝒪[F] (n → F)) : Submodule 𝒪[F] (n → F) :=
  L.map ((Matrix.mulVecLin (g : Matrix n n F)).restrictScalars 𝒪[F])

variable {F n}

theorem coe_glImage (g : GL n F) (L : Submodule 𝒪[F] (n → F)) :
    (glImage F n g L : Set (n → F)) = (fun v => (g : Matrix n n F) *ᵥ v) '' (L : Set (n → F)) :=
  rfl

omit [ValuativeRel F] in
theorem mulVecLin_surjective (g : GL n F) :
    Function.Surjective (Matrix.mulVecLin (g : Matrix n n F)) := fun w =>
  ⟨((g⁻¹ : GL n F) : Matrix n n F) *ᵥ w, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]⟩

/-- The image of a lattice under an invertible matrix is a lattice. -/
theorem isLattice_glImage (g : GL n F) {L : Submodule 𝒪[F] (n → F)} (hL : L.IsLattice F) :
    (glImage F n g L).IsLattice F where
  fg := hL.fg.map _
  span_eq_top := by
    change Submodule.span F ((Matrix.mulVecLin (g : Matrix n n F)) '' (L : Set (n → F))) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.2 (mulVecLin_surjective g)]

theorem glImage_one (L : Submodule 𝒪[F] (n → F)) : glImage F n 1 L = L := by
  apply SetLike.coe_injective
  rw [coe_glImage]
  simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']

theorem glImage_mul (g h : GL n F) (L : Submodule 𝒪[F] (n → F)) :
    glImage F n (g * h) L = glImage F n g (glImage F n h L) := by
  apply SetLike.coe_injective
  rw [coe_glImage, coe_glImage, coe_glImage, Set.image_image]
  congr 1
  funext v
  rw [Units.val_mul, Matrix.mulVec_mulVec]

/-- The image under `g` of the homothetic submodule `a L` is `a (g L)`. -/
theorem glImage_smul (g : GL n F) (a : Fˣ) (L : Submodule 𝒪[F] (n → F)) :
    glImage F n g (a • L) = a • glImage F n g L := by
  apply SetLike.coe_injective
  rw [coe_glImage, Units.smul_def, Units.smul_def, Submodule.coe_pointwise_smul,
    Submodule.coe_pointwise_smul, coe_glImage]
  exact Set.image_smul_comm _ _ _ fun v => Matrix.mulVec_smul _ _ _

/-- `GL_n(F)` acts on the `𝒪[F]`-lattices in `n → F` by `g · L = g L`. -/
instance : MulAction (GL n F) (ValuationRingLattice F n) where
  smul g L := ⟨glImage F n g L.carrier, isLattice_glImage g L.isLattice⟩
  one_smul L := ValuationRingLattice.ext (glImage_one L.carrier)
  mul_smul g h L := ValuationRingLattice.ext (glImage_mul g h L.carrier)

theorem ValuationRingLattice.carrier_smul (g : GL n F) (L : ValuationRingLattice F n) :
    (g • L).carrier = glImage F n g L.carrier :=
  rfl

theorem ValuationRingLattice.Homothetic.smul {L M : ValuationRingLattice F n} (h : L.Homothetic M)
    (g : GL n F) : (g • L).Homothetic (g • M) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [ValuationRingLattice.carrier_smul, ValuationRingLattice.carrier_smul, ha, glImage_smul]

/-- `GL_n(F)` acts on the homothety classes of lattices by `g · [L] = [g L]`. -/
instance : MulAction (GL n F) (LatticeClass F n) where
  smul g := Quotient.map' (g • ·) fun _ _ h => ValuationRingLattice.Homothetic.smul h g
  one_smul x := Quotient.inductionOn' x fun L => congrArg Quotient.mk'' (one_smul _ L)
  mul_smul g h x := Quotient.inductionOn' x fun L => congrArg Quotient.mk'' (mul_smul g h L)

theorem LatticeClass.smul_mk (g : GL n F) (L : ValuationRingLattice F n) :
    g • LatticeClass.mk L = LatticeClass.mk (g • L) :=
  rfl

end Langlands.Geometry.Building
