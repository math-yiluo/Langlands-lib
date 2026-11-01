import Langlands.Algebra.NonUnitalModuleTensor
import Langlands.Algebra.NondegenerateScalars
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Canonical scalars on balanced tensors of original nondegenerate modules

Renard (9 July 2026), I.2.1, printed p. 14. The coefficient module is built on the
published original tensor, and that tensor is identified with an explicit quotient of
the coefficient tensor of the two canonically scalar-equipped factors. The "right factor" is
the right module `X` (an original `Aᵐᵒᵖ`-action) and the "left factor" the left module `Y`.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateTensorScalars

open scoped TensorProduct
open MulOpposite
open NonUnitalModuleTensor (Tensor tmul)

universe uK uA uX uY uZ uX' uY' uX'' uY''

section Opposite

variable {k : Type uK} {A : Type uA} [CommSemiring k] [NonUnitalRing A] [Module k A]

/-- Opposite adapter: the right half of bilinearity on `Aᵐᵒᵖ` is the left half on `A`. -/
theorem opIsScalarTower [SMulCommClass k A A] : IsScalarTower k Aᵐᵒᵖ Aᵐᵒᵖ :=
  ⟨fun c a b => unop_injective (mul_smul_comm c (unop b) (unop a))⟩

/-- Opposite adapter: the left half of bilinearity on `Aᵐᵒᵖ` is the right half on `A`. -/
theorem opSMulCommClass [IsScalarTower k A A] : SMulCommClass k Aᵐᵒᵖ Aᵐᵒᵖ :=
  ⟨fun c a b => unop_injective (smul_mul_assoc c (unop b) (unop a)).symm⟩

end Opposite

attribute [local instance] opIsScalarTower opSMulCommClass

/-- Any action on a subsingleton group is nondegenerate, the zero idempotent fixing everything. -/
theorem isNondegenerate_of_subsingleton {B : Type uA} {M : Type uX} [NonUnitalRing B]
    [AddCommGroup M] [NonUnitalModule B M] [Subsingleton M] : IsNondegenerate B M :=
  fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

section Compatible

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [Semiring k] [NonUnitalRing A] [AddCommGroup X] [AddCommGroup Y]
  [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
  [instY : Module k Y] [commY : SMulCommClass k A Y]

/-- For any coefficient module on `Y` commuting with the original action, `y ↦ c • y` is an
original intertwiner. -/
def compatibleScalarHom (c : k) : NonUnitalModuleHom A Y Y where
  toFun y := c • y
  map_zero' := smul_zero c
  map_add' := smul_add c
  map_smul' a y := smul_comm c a y

theorem compatibleScalarHom_apply (c : k) (y : Y) : compatibleScalarHom k A Y c y = c • y := rfl

/-- The additive scalar endomorphism: the published tensor map of `id_X` and `y ↦ c • y`. -/
def compatibleScalarEnd (c : k) : Tensor A X Y →+ Tensor A X Y :=
  NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (compatibleScalarHom k A Y c)

theorem compatibleScalarEnd_tmul (c : k) (x : X) (y : Y) :
    compatibleScalarEnd k A X Y c (tmul A X Y x y) = tmul A X Y x (c • y) := rfl

theorem compatibleScalarEnd_one :
    compatibleScalarEnd k A X Y 1 = AddMonoidHom.id (Tensor A X Y) :=
  NonUnitalModuleTensor.hom_ext A fun x y => congrArg (tmul A X Y x) (one_smul k y)

theorem compatibleScalarEnd_mul (c d : k) :
    compatibleScalarEnd k A X Y (c * d) =
      (compatibleScalarEnd k A X Y c).comp (compatibleScalarEnd k A X Y d) :=
  NonUnitalModuleTensor.hom_ext A fun x y => congrArg (tmul A X Y x) (mul_smul c d y)

theorem compatibleScalarEnd_add (c d : k) :
    compatibleScalarEnd k A X Y (c + d) =
      compatibleScalarEnd k A X Y c + compatibleScalarEnd k A X Y d :=
  NonUnitalModuleTensor.hom_ext A fun x y =>
    (congrArg (tmul A X Y x) (add_smul c d y)).trans
      (NonUnitalModuleTensor.tmul_add A X Y x (c • y) (d • y))

theorem compatibleScalarEnd_zero : compatibleScalarEnd k A X Y 0 = 0 :=
  NonUnitalModuleTensor.hom_ext A fun x y =>
    (congrArg (tmul A X Y x) (zero_smul k y)).trans (NonUnitalModuleTensor.tmul_zero A X Y x)

/-- The coefficient module on the published original tensor induced by a compatible coefficient
module on the left factor alone, retaining the tensor's group; it is installed only locally. -/
abbrev compatibleModule : Module k (Tensor A X Y) where
  smul c t := compatibleScalarEnd k A X Y c t
  one_smul t := DFunLike.congr_fun (compatibleScalarEnd_one k A X Y) t
  mul_smul c d t := DFunLike.congr_fun (compatibleScalarEnd_mul k A X Y c d) t
  smul_zero c := (compatibleScalarEnd k A X Y c).map_zero
  smul_add c := (compatibleScalarEnd k A X Y c).map_add
  add_smul c d t := DFunLike.congr_fun (compatibleScalarEnd_add k A X Y c d) t
  zero_smul t := DFunLike.congr_fun (compatibleScalarEnd_zero k A X Y) t

theorem compatible_smul_def (c : k) (t : Tensor A X Y) :
    letI := compatibleModule k A X Y
    c • t = compatibleScalarEnd k A X Y c t := rfl

/-- The entire additive scalar endomorphism is the published map of `id_X` and `y ↦ c • y`. -/
theorem compatible_toAddMonoidHom_smul (c : k) :
    letI := compatibleModule k A X Y
    DistribSMul.toAddMonoidHom (Tensor A X Y) c =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (compatibleScalarHom k A Y c) :=
  AddMonoidHom.ext fun _ => rfl

theorem compatible_smul_tmul (c : k) (x : X) (y : Y) :
    letI := compatibleModule k A X Y
    c • tmul A X Y x y = tmul A X Y x (c • y) := rfl

variable {Z : Type uZ} [AddCommGroup Z] [Module k Z]

/-- An additive map out of the tensor commuting with left-factor scalars on pure tensors is
coefficient-linear for the compatible module. -/
def linearOfPure (f : Tensor A X Y →+ Z)
    (hf : ∀ (c : k) (x : X) (y : Y), f (tmul A X Y x (c • y)) = c • f (tmul A X Y x y)) :
    letI := compatibleModule k A X Y
    Tensor A X Y →ₗ[k] Z :=
  letI := compatibleModule k A X Y
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun c t => by
      have h : f.comp (compatibleScalarEnd k A X Y c) =
          (DistribSMul.toAddMonoidHom Z c).comp f :=
        NonUnitalModuleTensor.hom_ext A fun x y => hf c x y
      exact DFunLike.congr_fun h t }

theorem linearOfPure_toAddMonoidHom (f : Tensor A X Y →+ Z)
    (hf : ∀ (c : k) (x : X) (y : Y), f (tmul A X Y x (c • y)) = c • f (tmul A X Y x y)) :
    (linearOfPure k A X Y f hf).toAddMonoidHom = f := rfl

/-- Coefficient-linear maps out of the tensor are determined by their pure-tensor values. -/
theorem compatible_linear_hom_ext
    {f g : letI := compatibleModule k A X Y; Tensor A X Y →ₗ[k] Z}
    (h : ∀ (x : X) (y : Y), f (tmul A X Y x y) = g (tmul A X Y x y)) : f = g := by
  let _ := compatibleModule k A X Y
  exact LinearMap.toAddMonoidHom_injective (NonUnitalModuleTensor.hom_ext A h)

end Compatible

section FactorScalars

variable (k : Type uK) {A : Type uA} {X : Type uX} {Y : Type uY}
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]

/-- The published canonical scalars on the original right factor, over the opposite ring. -/
noncomputable abbrev rightModule (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) :
    Module k X :=
  NondegenerateScalars.module k hA.op hX

/-- The published canonical scalars on the original left factor. -/
noncomputable abbrev leftModule (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    Module k Y :=
  NondegenerateScalars.module k hA hY

theorem rightModule_eq (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) :
    rightModule k hA hX = NondegenerateScalars.module k hA.op hX := rfl

theorem leftModule_eq (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    leftModule k hA hY = NondegenerateScalars.module k hA hY := rfl

/-- The canonical scalar `y ↦ c • y`, an original intertwiner by the published proved
compatibility `NondegenerateScalars.smulCommClass`. -/
noncomputable def scalarHom (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) :
    NonUnitalModuleHom A Y Y :=
  compatibleScalarHom k A Y (instY := leftModule k hA hY)
    (commY := NondegenerateScalars.smulCommClass k hA hY) c

theorem scalarHom_apply (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) (y : Y) :
    letI := leftModule k hA hY
    scalarHom k hA hY c y = c • y := rfl

/-- The canonical scalar `x ↦ c • x` on the right factor, an original right intertwiner. -/
noncomputable def rightScalarHom (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (c : k) : NonUnitalModuleHom Aᵐᵒᵖ X X :=
  compatibleScalarHom k Aᵐᵒᵖ X (instY := rightModule k hA hX)
    (commY := NondegenerateScalars.smulCommClass k hA.op hX) c

theorem rightScalarHom_apply (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (c : k) (x : X) :
    letI := rightModule k hA hX
    rightScalarHom k hA hX c x = c • x := rfl

end FactorScalars

section Biadditive

variable {R : Type uK} {M : Type uX} {N : Type uY} {P : Type uZ} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]

/-- The complete underlying biadditive map of a coefficient-bilinear map. -/
def toBiadditive (b : M →ₗ[R] N →ₗ[R] P) : M →+ N →+ P :=
  LinearMap.toAddMonoidHom'.comp b.toAddMonoidHom

@[simp] theorem toBiadditive_apply (b : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    toBiadditive b m n = b m n := rfl

end Biadditive

section Tensor

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]

/-- The canonical additive scalar endomorphism: the published tensor map of `id_X` and the
canonical intertwiner `y ↦ c • y`. -/
noncomputable def scalarEnd (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) :
    Tensor A X Y →+ Tensor A X Y :=
  NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c)

theorem scalarEnd_tmul (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k)
    (x : X) (y : Y) :
    letI := leftModule k hA hY
    scalarEnd k A X Y hA hY c (tmul A X Y x y) = tmul A X Y x (c • y) := rfl

/-- The canonical coefficient module on the published original tensor, retaining its group:
the compatible module of the published canonical scalars on the left factor. -/
noncomputable abbrev module (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    Module k (Tensor A X Y) :=
  compatibleModule k A X Y (instY := leftModule k hA hY)
    (commY := NondegenerateScalars.smulCommClass k hA hY)

theorem module_eq (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    module k A X Y hA hY = compatibleModule k A X Y (instY := leftModule k hA hY)
      (commY := NondegenerateScalars.smulCommClass k hA hY) := rfl

theorem smul_def (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k)
    (t : Tensor A X Y) :
    letI := module k A X Y hA hY
    c • t = scalarEnd k A X Y hA hY c t := rfl

/-- The entire additive scalar endomorphism is the published map of `id_X` and `y ↦ c • y`. -/
theorem toAddMonoidHom_smul (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) :
    letI := module k A X Y hA hY
    DistribSMul.toAddMonoidHom (Tensor A X Y) c =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c) :=
  AddMonoidHom.ext fun _ => rfl

theorem smul_tmul_right (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k)
    (x : X) (y : Y) :
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    c • tmul A X Y x y = tmul A X Y x (c • y) := rfl

/-- Scalars move between the factors, by a fixing idempotent and original balancing. -/
theorem tmul_smul_left_eq (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (c : k) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    tmul A X Y (c • x) y = tmul A X Y x (c • y) := by
  let _ := rightModule k hA hX
  let _ := leftModule k hA hY
  obtain ⟨e, he⟩ := hX x
  have hcx : c • x = op (c • unop (e : Aᵐᵒᵖ)) • x :=
    NondegenerateScalars.smul_eq k hA.op hX c x e he
  have hy : (c • unop (e : Aᵐᵒᵖ)) • y = c • (unop (e : Aᵐᵒᵖ) • y) :=
    (NondegenerateScalars.smul_action k hA hY c (unop (e : Aᵐᵒᵖ)) y).symm
  have hx : op (unop (e : Aᵐᵒᵖ)) • x = x := he
  calc tmul A X Y (c • x) y = tmul A X Y (op (c • unop (e : Aᵐᵒᵖ)) • x) y := by rw [hcx]
    _ = tmul A X Y x ((c • unop (e : Aᵐᵒᵖ)) • y) :=
      NonUnitalModuleTensor.tmul_balanced A X Y _ x y
    _ = tmul A X Y x (c • (unop (e : Aᵐᵒᵖ) • y)) := by rw [hy]
    _ = scalarEnd k A X Y hA hY c (tmul A X Y x (unop (e : Aᵐᵒᵖ) • y)) := rfl
    _ = scalarEnd k A X Y hA hY c (tmul A X Y (op (unop (e : Aᵐᵒᵖ)) • x) y) := by
      rw [NonUnitalModuleTensor.tmul_balanced A X Y]
    _ = scalarEnd k A X Y hA hY c (tmul A X Y x y) := by rw [hx]
    _ = tmul A X Y x (c • y) := rfl

theorem smul_tmul_left (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (c : k) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := module k A X Y hA hY
    c • tmul A X Y x y = tmul A X Y (c • x) y :=
  (tmul_smul_left_eq k A X Y hA hX hY c x y).symm

/-- The full two-variable formulas `c • tmul x y = tmul (c • x) y = tmul x (c • y)`. -/
theorem smul_tmul_function (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (c : k) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
      (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  ⟨funext fun x => funext fun y => smul_tmul_left k A X Y hA hX hY c x y,
    funext fun x => funext fun y => tmul_smul_left_eq k A X Y hA hX hY c x y⟩

/-- The same scalar endomorphism is the published map of `x ↦ c • x` and `id_Y`. -/
theorem map_rightScalarHom_id (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (c : k) :
    NonUnitalModuleTensor.map A (rightScalarHom k hA hX c) (NonUnitalModuleHom.id A Y) =
      scalarEnd k A X Y hA hY c :=
  NonUnitalModuleTensor.hom_ext A fun x y => tmul_smul_left_eq k A X Y hA hX hY c x y

/-! ### The bilinear pure map and the coefficient-tensor projection -/

/-- The published pure map, refined to an actual coefficient-bilinear map. -/
noncomputable def bilinear (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    X →ₗ[k] Y →ₗ[k] Tensor A X Y :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  LinearMap.mk₂ k (tmul A X Y) (NonUnitalModuleTensor.add_tmul A X Y)
    (fun c x y => tmul_smul_left_eq k A X Y hA hX hY c x y)
    (NonUnitalModuleTensor.tmul_add A X Y) (fun _ _ _ => rfl)

theorem bilinear_apply (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    bilinear k A X Y hA hX hY x y = tmul A X Y x y := rfl

theorem bilinear_function (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    (fun x y => bilinear k A X Y hA hX hY x y) = tmul A X Y := rfl

/-- The complete underlying biadditive map is the published `biadditive`. -/
theorem toBiadditive_bilinear (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    toBiadditive (bilinear k A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  rfl

/-- The actual coefficient-tensor lift `π : X ⊗[k] Y →ₗ[k] Tensor A X Y`. -/
noncomputable def coefficientProjection (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (X ⊗[k] Y) →ₗ[k] Tensor A X Y :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  TensorProduct.lift (bilinear k A X Y hA hX hY)

theorem coefficientProjection_eq_lift (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    coefficientProjection k A X Y hA hX hY = TensorProduct.lift (bilinear k A X Y hA hX hY) :=
  rfl

theorem coefficientProjection_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    coefficientProjection k A X Y hA hX hY (x ⊗ₜ[k] y) = tmul A X Y x y := rfl

/-- Whole-map factorization of the bilinear map through the projection. -/
theorem mk_compr₂_coefficientProjection (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (TensorProduct.mk k X Y).compr₂ (coefficientProjection k A X Y hA hX hY) =
      bilinear k A X Y hA hX hY :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  LinearMap.ext₂ fun _ _ => rfl

theorem coefficientProjection_surjective (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    Function.Surjective (coefficientProjection k A X Y hA hX hY) := by
  let _ := rightModule k hA hX
  let _ := leftModule k hA hY
  let _ := module k A X Y hA hY
  intro t
  obtain ⟨q, rfl⟩ := NonUnitalModuleTensor.projection_surjective A X Y t
  induction q using TensorProduct.inductionOn with
  | tmul x y => exact ⟨x ⊗ₜ[k] y, rfl⟩
  | add q r hq hr =>
    obtain ⟨q', hq'⟩ := hq
    obtain ⟨r', hr'⟩ := hr
    exact ⟨q' + r', by rw [map_add, hq', hr', map_add]⟩

/-! ### The coefficient balancing quotient -/

/-- The actual span `K` of the original balancing differences in the coefficient tensor. -/
noncomputable def coefficientRelations (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    Submodule k (X ⊗[k] Y) :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  Submodule.span k {(op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | (a : A) (x : X) (y : Y)}

theorem coefficientRelations_eq_span (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    coefficientRelations k A X Y hA hX hY =
      Submodule.span k {(op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | (a : A) (x : X) (y : Y)} :=
  rfl

theorem generator_mem_coefficientRelations (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (a : A) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    (op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) ∈ coefficientRelations k A X Y hA hX hY :=
  Submodule.subset_span ⟨a, x, y, rfl⟩

theorem coefficientRelations_le_ker (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    coefficientRelations k A X Y hA hX hY ≤
      LinearMap.ker (coefficientProjection k A X Y hA hX hY) := by
  let _ := rightModule k hA hX
  let _ := leftModule k hA hY
  let _ := module k A X Y hA hY
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, x, y, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact NonUnitalModuleTensor.tmul_balanced A X Y a x y

/-- The forward map `(X ⊗[k] Y) ⧸ K →ₗ[k] Tensor A X Y`, induced by `π`. -/
noncomputable def quotientToTensor (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) →ₗ[k] Tensor A X Y :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  (coefficientRelations k A X Y hA hX hY).liftQ (coefficientProjection k A X Y hA hX hY)
    (coefficientRelations_le_ker k A X Y hA hX hY)

/-- The class of `x ⊗ₜ[k] y`, as an original biadditive map. -/
noncomputable def toQuotientBiadditive (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    X →+ Y →+ ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  toBiadditive ((TensorProduct.mk k X Y).compr₂ (coefficientRelations k A X Y hA hX hY).mkQ)

theorem toQuotientBiadditive_apply (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    toQuotientBiadditive k A X Y hA hX hY x y =
      Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y) := rfl

theorem toQuotientBiadditive_balanced (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    NonUnitalModuleTensor.IsBalanced A (toQuotientBiadditive k A X Y hA hX hY) := by
  let _ := rightModule k hA hX
  let _ := leftModule k hA hY
  intro a x y
  exact (Submodule.Quotient.eq _).mpr (generator_mem_coefficientRelations k A X Y hA hX hY a x y)

/-- An additive map out of the tensor commuting with the canonical left-factor scalars on
pure tensors is coefficient-linear for the canonical module. -/
noncomputable def canonicalLinearOfPure (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    {Z : Type uZ} [AddCommGroup Z] [Module k Z] (f : Tensor A X Y →+ Z)
    (hf : letI := leftModule k hA hY
      ∀ (c : k) (x : X) (y : Y), f (tmul A X Y x (c • y)) = c • f (tmul A X Y x y)) :
    letI := module k A X Y hA hY
    Tensor A X Y →ₗ[k] Z :=
  linearOfPure k A X Y (instY := leftModule k hA hY)
    (commY := NondegenerateScalars.smulCommClass k hA hY) f hf

theorem canonicalLinearOfPure_toAddMonoidHom (hA : IsIdempotented A)
    (hY : IsNondegenerate A Y) {Z : Type uZ} [AddCommGroup Z] [Module k Z]
    (f : Tensor A X Y →+ Z)
    (hf : letI := leftModule k hA hY
      ∀ (c : k) (x : X) (y : Y), f (tmul A X Y x (c • y)) = c • f (tmul A X Y x y)) :
    (canonicalLinearOfPure k A X Y hA hY f hf).toAddMonoidHom = f := rfl

/-- The inverse: the published original lift of the class of `x ⊗ₜ[k] y`, proved linear. -/
noncomputable def tensorToQuotient (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    Tensor A X Y →ₗ[k] ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  canonicalLinearOfPure k A X Y hA hY
    (NonUnitalModuleTensor.lift A (toQuotientBiadditive k A X Y hA hX hY)
      (toQuotientBiadditive_balanced k A X Y hA hX hY))
    (fun c x y => by
      change Submodule.Quotient.mk (x ⊗ₜ[k] (c • y)) = c • Submodule.Quotient.mk (x ⊗ₜ[k] y)
      rw [TensorProduct.tmul_smul, Submodule.Quotient.mk_smul])

theorem quotientToTensor_comp_tensorToQuotient (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientToTensor k A X Y hA hX hY).comp (tensorToQuotient k A X Y hA hX hY) =
      LinearMap.id :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  LinearMap.toAddMonoidHom_injective (NonUnitalModuleTensor.hom_ext A fun _ _ => rfl)

theorem tensorToQuotient_comp_quotientToTensor (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (tensorToQuotient k A X Y hA hX hY).comp (quotientToTensor k A X Y hA hX hY) =
      LinearMap.id :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  Submodule.linearMap_qext _ (TensorProduct.ext' fun _ _ => rfl)

/-- The explicit coefficient-linear equivalence `((X ⊗[k] Y) ⧸ K) ≃ₗ[k] Tensor A X Y`. -/
noncomputable def quotientEquiv (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  LinearEquiv.ofLinearMap (quotientToTensor k A X Y hA hX hY) (tensorToQuotient k A X Y hA hX hY)
    (quotientToTensor_comp_tensorToQuotient k A X Y hA hX hY)
    (tensorToQuotient_comp_quotientToTensor k A X Y hA hX hY)

theorem quotientEquiv_mk_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    quotientEquiv k A X Y hA hX hY
        (Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y)) =
      tmul A X Y x y := rfl

theorem quotientEquiv_symm_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    (quotientEquiv k A X Y hA hX hY).symm (tmul A X Y x y) =
      Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y) := rfl

theorem quotientEquiv_toLinearMap (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientEquiv k A X Y hA hX hY).toLinearMap = quotientToTensor k A X Y hA hX hY := rfl

theorem quotientEquiv_symm_toLinearMap (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientEquiv k A X Y hA hX hY).symm.toLinearMap = tensorToQuotient k A X Y hA hX hY :=
  rfl

/-- The complete underlying additive map of the forward equivalence is the quotient lift. -/
theorem quotientEquiv_toAddMonoidHom (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientEquiv k A X Y hA hX hY).toLinearMap.toAddMonoidHom =
      ((coefficientRelations k A X Y hA hX hY).liftQ (coefficientProjection k A X Y hA hX hY)
        (coefficientRelations_le_ker k A X Y hA hX hY)).toAddMonoidHom := rfl

/-- The complete underlying additive map of the inverse is the published original lift. -/
theorem quotientEquiv_symm_toAddMonoidHom (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
      NonUnitalModuleTensor.lift A (toQuotientBiadditive k A X Y hA hX hY)
        (toQuotientBiadditive_balanced k A X Y hA hX hY) := rfl

theorem quotientEquiv_symm_comp (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.comp
        (quotientEquiv k A X Y hA hX hY).toLinearMap = LinearMap.id :=
  tensorToQuotient_comp_quotientToTensor k A X Y hA hX hY

theorem quotientEquiv_comp_symm (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
        (quotientEquiv k A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  quotientToTensor_comp_tensorToQuotient k A X Y hA hX hY

/-- `π` is the forward equivalence composed with `K.mkQ`. -/
theorem coefficientProjection_eq_comp_mkQ (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    coefficientProjection k A X Y hA hX hY =
      (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
        (coefficientRelations k A X Y hA hX hY).mkQ :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  (Submodule.liftQ_mkQ _ _ _).symm

theorem ker_coefficientProjection (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    LinearMap.ker (coefficientProjection k A X Y hA hX hY) =
      coefficientRelations k A X Y hA hX hY := by
  let _ := rightModule k hA hX
  let _ := leftModule k hA hY
  let _ := module k A X Y hA hY
  rw [coefficientProjection_eq_comp_mkQ k A X Y hA hX hY, LinearEquiv.ker_comp,
    Submodule.ker_mkQ]

/-! ### The coefficient-linear universal lift -/

variable {Z : Type uZ} [AddCommGroup Z] [Module k Z]

/-- The published original lift of a balanced coefficient-bilinear map, proved linear. -/
noncomputable def linearLift (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY; X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) :
    letI := module k A X Y hA hY
    Tensor A X Y →ₗ[k] Z :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  canonicalLinearOfPure k A X Y hA hY (NonUnitalModuleTensor.lift A (toBiadditive b) hb)
    (fun c x y => (b x).map_smul c y)

theorem linearLift_toAddMonoidHom (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY; X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (linearLift k A X Y hA hX hY b hb).toAddMonoidHom =
      NonUnitalModuleTensor.lift A (toBiadditive b) hb := rfl

theorem linearLift_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY; X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) (x : X) (y : Y) :
    linearLift k A X Y hA hX hY b hb (tmul A X Y x y) = b x y := rfl

/-- Coefficient-linear maps out of the tensor are determined by their pure-tensor values. -/
theorem linear_hom_ext (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    {f g : letI := module k A X Y hA hY; Tensor A X Y →ₗ[k] Z}
    (h : ∀ (x : X) (y : Y), f (tmul A X Y x y) = g (tmul A X Y x y)) : f = g :=
  compatible_linear_hom_ext k A X Y (instY := leftModule k hA hY)
    (commY := NondegenerateScalars.smulCommClass k hA hY) h

theorem linearLift_unique (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY; X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := module k A X Y hA hY; Tensor A X Y →ₗ[k] Z)
    (hf : ∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) :
    f = linearLift k A X Y hA hX hY b hb :=
  linear_hom_ext k A X Y hA hY hf

/-- Whole-map factorization of a balanced bilinear map through the bilinear pure map. -/
theorem bilinear_compr₂_linearLift (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY; X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (bilinear k A X Y hA hX hY).compr₂ (linearLift k A X Y hA hX hY b hb) = b :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := module k A X Y hA hY
  LinearMap.ext₂ fun _ _ => rfl

end Tensor

/-! ### Coefficient-linear induced maps -/

section Maps

variable (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
  {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
  [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']

/-- The published tensor map of original intertwiners, proved coefficient-linear. -/
noncomputable def linearMap (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (hY' : IsNondegenerate A Y') (f : NonUnitalModuleHom Aᵐᵒᵖ X X')
    (g : NonUnitalModuleHom A Y Y') :
    letI := module k A X Y hA hY
    letI := module k A X' Y' hA hY'
    Tensor A X Y →ₗ[k] Tensor A X' Y' :=
  letI := module k A X' Y' hA hY'
  canonicalLinearOfPure k A X Y hA hY (NonUnitalModuleTensor.map A f g) fun c x y =>
    congrArg (tmul A X' Y' (f x)) (NondegenerateScalars.map_smul k hA hY hY' g c y)

theorem linearMap_toAddMonoidHom (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (hY' : IsNondegenerate A Y') (f : NonUnitalModuleHom Aᵐᵒᵖ X X')
    (g : NonUnitalModuleHom A Y Y') :
    letI := module k A X Y hA hY
    letI := module k A X' Y' hA hY'
    (linearMap k A hA hY hY' f g).toAddMonoidHom = NonUnitalModuleTensor.map A f g := rfl

theorem linearMap_tmul (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (hY' : IsNondegenerate A Y') (f : NonUnitalModuleHom Aᵐᵒᵖ X X')
    (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y) :
    linearMap k A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) := rfl

theorem linearMap_id (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    letI := module k A X Y hA hY
    linearMap k A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
      LinearMap.id :=
  letI := module k A X Y hA hY
  LinearMap.toAddMonoidHom_injective (NonUnitalModuleTensor.map_id A)

theorem linearMap_comp {X'' : Type uX''} {Y'' : Type uY''} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y'') :
    letI := module k A X Y hA hY
    letI := module k A X' Y' hA hY'
    letI := module k A X'' Y'' hA hY''
    (linearMap k A hA hY' hY'' f' g').comp (linearMap k A hA hY hY' f g) =
      linearMap k A hA hY hY'' (f'.comp f) (g'.comp g) :=
  letI := module k A X Y hA hY
  letI := module k A X' Y' hA hY'
  letI := module k A X'' Y'' hA hY''
  LinearMap.toAddMonoidHom_injective (NonUnitalModuleTensor.map_comp A f g f' g')

/-- Naturality of `π` against the coefficient tensor map of the canonical linear refinements. -/
theorem linearMap_comp_coefficientProjection (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := rightModule k hA hX'
    letI := leftModule k hA hY'
    letI := module k A X Y hA hY
    letI := module k A X' Y' hA hY'
    (linearMap k A hA hY hY' f g).comp (coefficientProjection k A X Y hA hX hY) =
      (coefficientProjection k A X' Y' hA hX' hY').comp
        (TensorProduct.map (NondegenerateScalars.toLinearMap k hA.op hX hX' f)
          (NondegenerateScalars.toLinearMap k hA hY hY' g)) :=
  letI := rightModule k hA hX
  letI := leftModule k hA hY
  letI := rightModule k hA hX'
  letI := leftModule k hA hY'
  letI := module k A X Y hA hY
  letI := module k A X' Y' hA hY'
  TensorProduct.ext' fun _ _ => rfl

end Maps

/-! ### Renard's complex case -/

section Complex

variable (A : Type uA) (X : Type uX) (Y : Type uY)
  [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]

variable {A X Y} in
/-- Renard's complex scalars on the original right factor: the published complex module over
the opposite algebra. -/
noncomputable abbrev complexRightModule (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) :
    Module ℂ X :=
  rightModule ℂ hA hX

variable {A X Y} in
/-- Renard's complex scalars on the original left factor. -/
noncomputable abbrev complexLeftModule (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    Module ℂ Y :=
  leftModule ℂ hA hY

variable {A X Y} in
theorem complexRightModule_eq (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) :
    complexRightModule hA hX = NondegenerateScalars.complexModule hA.op hX := rfl

variable {A X Y} in
theorem complexLeftModule_eq (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    complexLeftModule hA hY = NondegenerateScalars.complexModule hA hY := rfl

/-- Renard's complex vector structure on the original tensor of nondegenerate modules. -/
noncomputable abbrev complexModule (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    Module ℂ (Tensor A X Y) :=
  module ℂ A X Y hA hY

theorem complexModule_eq (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    complexModule A X Y hA hY = module ℂ A X Y hA hY := rfl

/-- The entire complex scalar endomorphism is the published map of `id_X` and `y ↦ c • y`. -/
theorem complex_toAddMonoidHom_smul (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (c : ℂ) :
    letI := complexModule A X Y hA hY
    DistribSMul.toAddMonoidHom (Tensor A X Y) c =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom ℂ hA hY c) :=
  toAddMonoidHom_smul ℂ A X Y hA hY c

theorem complex_smul_tmul_right (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : ℂ)
    (x : X) (y : Y) :
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    c • tmul A X Y x y = tmul A X Y x (c • y) := rfl

theorem complex_smul_tmul_left (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (c : ℂ) (x : X) (y : Y) :
    letI := complexRightModule hA hX
    letI := complexModule A X Y hA hY
    c • tmul A X Y x y = tmul A X Y (c • x) y :=
  smul_tmul_left ℂ A X Y hA hX hY c x y

/-- The complex two-variable formulas `c • tmul x y = tmul (c • x) y = tmul x (c • y)`. -/
theorem complex_smul_tmul_function (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (c : ℂ) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
      (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  smul_tmul_function ℂ A X Y hA hX hY c

/-- The published pure map as an actual complex-bilinear map. -/
noncomputable def complexBilinear (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    X →ₗ[ℂ] Y →ₗ[ℂ] Tensor A X Y :=
  bilinear ℂ A X Y hA hX hY

theorem complexBilinear_apply (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    complexBilinear A X Y hA hX hY x y = tmul A X Y x y := rfl

theorem toBiadditive_complexBilinear (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    toBiadditive (complexBilinear A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  rfl

/-- The complex coefficient-tensor projection `X ⊗[ℂ] Y →ₗ[ℂ] Tensor A X Y`. -/
noncomputable def complexProjection (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (X ⊗[ℂ] Y) →ₗ[ℂ] Tensor A X Y :=
  coefficientProjection ℂ A X Y hA hX hY

theorem complexProjection_eq_lift (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    complexProjection A X Y hA hX hY = TensorProduct.lift (complexBilinear A X Y hA hX hY) :=
  rfl

theorem complexProjection_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    complexProjection A X Y hA hX hY (x ⊗ₜ[ℂ] y) = tmul A X Y x y := rfl

theorem complexProjection_surjective (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    Function.Surjective (complexProjection A X Y hA hX hY) :=
  coefficientProjection_surjective ℂ A X Y hA hX hY

/-- The span of the original balancing differences in `X ⊗[ℂ] Y`. -/
noncomputable def complexRelations (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    Submodule ℂ (X ⊗[ℂ] Y) :=
  coefficientRelations ℂ A X Y hA hX hY

theorem complexRelations_eq_span (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    complexRelations A X Y hA hX hY =
      Submodule.span ℂ {(op a • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (a • y) | (a : A) (x : X) (y : Y)} :=
  rfl

/-- The explicit complex-linear equivalence `((X ⊗[ℂ] Y) ⧸ K) ≃ₗ[ℂ] Tensor A X Y`. -/
noncomputable def complexQuotientEquiv (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    ((X ⊗[ℂ] Y) ⧸ complexRelations A X Y hA hX hY) ≃ₗ[ℂ] Tensor A X Y :=
  quotientEquiv ℂ A X Y hA hX hY

theorem complexQuotientEquiv_mk_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    complexQuotientEquiv A X Y hA hX hY
        (Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y)) =
      tmul A X Y x y := rfl

theorem complexQuotientEquiv_symm_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) (x : X) (y : Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    (complexQuotientEquiv A X Y hA hX hY).symm (tmul A X Y x y) =
      Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y) := rfl

theorem complexQuotientEquiv_symm_comp (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.comp
        (complexQuotientEquiv A X Y hA hX hY).toLinearMap = LinearMap.id :=
  quotientEquiv_symm_comp ℂ A X Y hA hX hY

theorem complexQuotientEquiv_comp_symm (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
        (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  quotientEquiv_comp_symm ℂ A X Y hA hX hY

theorem complexQuotientEquiv_toAddMonoidHom (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (complexQuotientEquiv A X Y hA hX hY).toLinearMap.toAddMonoidHom =
      ((complexRelations A X Y hA hX hY).liftQ (complexProjection A X Y hA hX hY)
        (coefficientRelations_le_ker ℂ A X Y hA hX hY)).toAddMonoidHom := rfl

theorem complexQuotientEquiv_symm_toAddMonoidHom (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
      NonUnitalModuleTensor.lift A (toQuotientBiadditive ℂ A X Y hA hX hY)
        (toQuotientBiadditive_balanced ℂ A X Y hA hX hY) := rfl

theorem complexProjection_eq_comp_mkQ (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    complexProjection A X Y hA hX hY =
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
        (complexRelations A X Y hA hX hY).mkQ :=
  coefficientProjection_eq_comp_mkQ ℂ A X Y hA hX hY

theorem ker_complexProjection (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    LinearMap.ker (complexProjection A X Y hA hX hY) = complexRelations A X Y hA hX hY :=
  ker_coefficientProjection ℂ A X Y hA hX hY

variable {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]

/-- The complex-linear lift of a balanced complex-bilinear map. -/
noncomputable def complexLinearLift (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY; X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) :
    letI := complexModule A X Y hA hY
    Tensor A X Y →ₗ[ℂ] Z :=
  linearLift ℂ A X Y hA hX hY b hb

theorem complexLinearLift_toAddMonoidHom (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY; X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (complexLinearLift A X Y hA hX hY b hb).toAddMonoidHom =
      NonUnitalModuleTensor.lift A (toBiadditive b) hb := rfl

theorem complexLinearLift_tmul (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY; X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) (x : X) (y : Y) :
    complexLinearLift A X Y hA hX hY b hb (tmul A X Y x y) = b x y := rfl

theorem complexLinearLift_unique (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY; X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := complexModule A X Y hA hY; Tensor A X Y →ₗ[ℂ] Z)
    (hf : ∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) :
    f = complexLinearLift A X Y hA hX hY b hb :=
  linearLift_unique ℂ A X Y hA hX hY b hb f hf

end Complex

section ComplexMaps

variable (A : Type uA) {X : Type uX} {Y : Type uY}
  [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
  {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
  [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']

/-- The published tensor map of original intertwiners, proved complex-linear. -/
noncomputable def complexLinearMap (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (hY' : IsNondegenerate A Y') (f : NonUnitalModuleHom Aᵐᵒᵖ X X')
    (g : NonUnitalModuleHom A Y Y') :
    letI := complexModule A X Y hA hY
    letI := complexModule A X' Y' hA hY'
    Tensor A X Y →ₗ[ℂ] Tensor A X' Y' :=
  linearMap ℂ A hA hY hY' f g

theorem complexLinearMap_toAddMonoidHom (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (hY' : IsNondegenerate A Y') (f : NonUnitalModuleHom Aᵐᵒᵖ X X')
    (g : NonUnitalModuleHom A Y Y') :
    letI := complexModule A X Y hA hY
    letI := complexModule A X' Y' hA hY'
    (complexLinearMap A hA hY hY' f g).toAddMonoidHom = NonUnitalModuleTensor.map A f g := rfl

theorem complexLinearMap_tmul (hA : IsIdempotented A) (hY : IsNondegenerate A Y)
    (hY' : IsNondegenerate A Y') (f : NonUnitalModuleHom Aᵐᵒᵖ X X')
    (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y) :
    complexLinearMap A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) := rfl

theorem complexLinearMap_id (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    letI := complexModule A X Y hA hY
    complexLinearMap A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
      LinearMap.id :=
  linearMap_id ℂ A hA hY

theorem complexLinearMap_comp {X'' : Type uX''} {Y'' : Type uY''} [AddCommGroup X'']
    [AddCommGroup Y''] [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y'') :
    letI := complexModule A X Y hA hY
    letI := complexModule A X' Y' hA hY'
    letI := complexModule A X'' Y'' hA hY''
    (complexLinearMap A hA hY' hY'' f' g').comp (complexLinearMap A hA hY hY' f g) =
      complexLinearMap A hA hY hY'' (f'.comp f) (g'.comp g) :=
  linearMap_comp ℂ A hA hY hY' hY'' f g f' g'

/-- Naturality of the complex projection against the published complex linear refinements. -/
theorem complexLinearMap_comp_complexProjection (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexRightModule hA hX'
    letI := complexLeftModule hA hY'
    letI := complexModule A X Y hA hY
    letI := complexModule A X' Y' hA hY'
    (complexLinearMap A hA hY hY' f g).comp (complexProjection A X Y hA hX hY) =
      (complexProjection A X' Y' hA hX' hY').comp
        (TensorProduct.map (NondegenerateScalars.complexToLinearMap hA.op hX hX' f)
          (NondegenerateScalars.complexToLinearMap hA hY hY' g)) :=
  linearMap_comp_coefficientProjection ℂ A hA hX hY hX' hY' f g

end ComplexMaps

/-! ### Subsingleton factors -/

section SubsingletonFactors

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]

/-- A subsingleton right factor is nondegenerate; the tensor and the quotient are subsingletons
and `K` is everything. -/
example [Subsingleton X] (hA : IsIdempotented A) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA (isNondegenerate_of_subsingleton (B := Aᵐᵒᵖ) (M := X))
    letI := leftModule k hA hY
    Subsingleton (Tensor A X Y) ∧
      Subsingleton ((X ⊗[k] Y) ⧸
        coefficientRelations k A X Y hA isNondegenerate_of_subsingleton hY) ∧
      coefficientRelations k A X Y hA isNondegenerate_of_subsingleton hY = ⊤ := by
  let _ := rightModule k hA (isNondegenerate_of_subsingleton (B := Aᵐᵒᵖ) (M := X))
  let _ := leftModule k hA hY
  refine ⟨(coefficientProjection_surjective k A X Y hA
    (isNondegenerate_of_subsingleton (B := Aᵐᵒᵖ) (M := X)) hY).subsingleton, inferInstance, ?_⟩
  exact eq_top_iff.mpr fun q _ => by
    rw [Subsingleton.elim q 0]
    exact Submodule.zero_mem _

/-- A subsingleton left factor is nondegenerate; the tensor and the quotient are subsingletons
and `K` is everything. -/
example [Subsingleton Y] (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) :
    letI := rightModule k hA hX
    letI := leftModule k hA (isNondegenerate_of_subsingleton (B := A) (M := Y))
    Subsingleton (Tensor A X Y) ∧
      Subsingleton ((X ⊗[k] Y) ⧸
        coefficientRelations k A X Y hA hX isNondegenerate_of_subsingleton) ∧
      coefficientRelations k A X Y hA hX isNondegenerate_of_subsingleton = ⊤ := by
  let _ := rightModule k hA hX
  let _ := leftModule k hA (isNondegenerate_of_subsingleton (B := A) (M := Y))
  refine ⟨(coefficientProjection_surjective k A X Y hA hX
    (isNondegenerate_of_subsingleton (B := A) (M := Y))).subsingleton, inferInstance, ?_⟩
  exact eq_top_iff.mpr fun q _ => by
    rw [Subsingleton.elim q 0]
    exact Submodule.zero_mem _

/-- Over a subsingleton algebra every original action is zero and only subsingleton groups are
nondegenerate; the construction still applies to them. -/
example [Subsingleton A] [Subsingleton X] [Subsingleton Y] :
    letI := module k A X Y (fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, fun _ _ => Subsingleton.elim _ _⟩)
      (isNondegenerate_of_subsingleton (B := A) (M := Y))
    ∀ (c : k) (t : Tensor A X Y), c • t = t := by
  intro c t
  have : Subsingleton (Tensor A X Y) :=
    (NonUnitalModuleTensor.projection_surjective A X Y).subsingleton
  exact Subsingleton.elim _ _

end SubsingletonFactors

/-! ### The regular integer example -/

section RegularInteger

/-- On the regular integer tensor the default integer action `c • t` (from the additive group)
is the canonical scalar endomorphism, since any two integer modules coincide. -/
example :
    letI := NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ
    letI := @NonUnitalModule.ofModule ℤ ℤ _ _ Semiring.toModule
    ∀ (hY : IsNondegenerate ℤ ℤ) (c : ℤ) (t : Tensor ℤ ℤ ℤ),
      c • t = scalarEnd ℤ ℤ ℤ ℤ (IsIdempotented.of_ring ℤ) hY c t := by
  let _ := NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ
  let _ := @NonUnitalModule.ofModule ℤ ℤ _ _ Semiring.toModule
  intro hY c t
  have h : AddCommGroup.toIntModule (Tensor ℤ ℤ ℤ) =
      module ℤ ℤ ℤ ℤ (IsIdempotented.of_ring ℤ) hY := Subsingleton.elim _ _
  exact congrArg (fun M : Module ℤ (Tensor ℤ ℤ ℤ) => M.toSMul.smul c t) h

/-- The right and left regular actions of `A = ℤ` on `X = Y = ℤ`, with `k = ℤ`: `tmul 1 1 ≠ 0`
and the canonical scalar formula `c • tmul 1 1 = tmul c 1 = tmul 1 c` is visible. The canonical
scalars are installed as the scalar action explicitly, since `c • t` for `c : ℤ` otherwise
elaborates to the additive group's default integer action (equal to it by the previous example). -/
example :
    letI := NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ
    letI := @NonUnitalModule.ofModule ℤ ℤ _ _ Semiring.toModule
    ∀ (_hX : IsNondegenerate ℤᵐᵒᵖ ℤ) (hY : IsNondegenerate ℤ ℤ),
      letI : SMul ℤ (Tensor ℤ ℤ ℤ) := (module ℤ ℤ ℤ ℤ (IsIdempotented.of_ring ℤ) hY).toSMul
      tmul ℤ ℤ ℤ 1 1 ≠ 0 ∧
        ∀ c : ℤ, c • tmul ℤ ℤ ℤ 1 1 = tmul ℤ ℤ ℤ c 1 ∧ c • tmul ℤ ℤ ℤ 1 1 = tmul ℤ ℤ ℤ 1 c := by
  let _ := NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ
  let _ := @NonUnitalModule.ofModule ℤ ℤ _ _ Semiring.toModule
  intro hX hY
  let _ : SMul ℤ (Tensor ℤ ℤ ℤ) := (module ℤ ℤ ℤ ℤ (IsIdempotented.of_ring ℤ) hY).toSMul
  have hcy (c : ℤ) : scalarHom ℤ (IsIdempotented.of_ring ℤ) hY c 1 = c :=
    (NondegenerateScalars.smul_eq ℤ (IsIdempotented.of_ring ℤ) hY c 1
      ⟨1, IsIdempotentElem.one⟩ (one_mul 1)).trans (by
        show c • (1 : ℤ) * 1 = c
        simp)
  have hcx (c : ℤ) : rightScalarHom ℤ (IsIdempotented.of_ring ℤ) hX c 1 = c :=
    (NondegenerateScalars.smul_eq ℤ (IsIdempotented.of_ring ℤ).op hX c 1
      ⟨1, IsIdempotentElem.one⟩ (mul_one 1)).trans (by
        show (1 : ℤ) * MulOpposite.unop (c • (1 : ℤᵐᵒᵖ)) = c
        simp)
  let b : ℤ →+ ℤ →+ ℤ :=
    { toFun x :=
        { toFun y := x * y
          map_zero' := mul_zero x
          map_add' := mul_add x }
      map_zero' := AddMonoidHom.ext zero_mul
      map_add' x x' := AddMonoidHom.ext fun y => add_mul x x' y }
  have hb : NonUnitalModuleTensor.IsBalanced ℤ b := fun a x y => mul_assoc x a y
  refine ⟨fun ht => ?_, fun c => ⟨?_, ?_⟩⟩
  · have h := congrArg (NonUnitalModuleTensor.lift ℤ b hb) ht
    rw [NonUnitalModuleTensor.lift_tmul, map_zero] at h
    exact one_ne_zero h
  · have h : tmul ℤ ℤ ℤ (rightScalarHom ℤ (IsIdempotented.of_ring ℤ) hX c 1) 1 =
        tmul ℤ ℤ ℤ 1 (scalarHom ℤ (IsIdempotented.of_ring ℤ) hY c 1) :=
      tmul_smul_left_eq ℤ ℤ ℤ ℤ (IsIdempotented.of_ring ℤ) hX hY c 1 1
    show tmul ℤ ℤ ℤ 1 (scalarHom ℤ (IsIdempotented.of_ring ℤ) hY c 1) = tmul ℤ ℤ ℤ c 1
    rw [← h, hcx c]
  · show tmul ℤ ℤ ℤ 1 (scalarHom ℤ (IsIdempotented.of_ring ℤ) hY c 1) = tmul ℤ ℤ ℤ 1 c
    rw [hcy c]

/-- The regular actions are nondegenerate, the unit fixing every vector. -/
example :
    letI := NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ
    letI := @NonUnitalModule.ofModule ℤ ℤ _ _ Semiring.toModule
    IsNondegenerate ℤᵐᵒᵖ ℤ ∧ IsNondegenerate ℤ ℤ :=
  ⟨fun x => ⟨⟨1, IsIdempotentElem.one⟩, mul_one x⟩,
    fun y => ⟨⟨1, IsIdempotentElem.one⟩, one_mul y⟩⟩

/-- On the regular integer tensor, the canonical scalars agree with the competing integer
module `AddCommGroup.toIntModule`, as do all integer modules. -/
example :
    letI := NonUnitalModule.ofModule ℤᵐᵒᵖ ℤ
    letI := @NonUnitalModule.ofModule ℤ ℤ _ _ Semiring.toModule
    ∀ hY : IsNondegenerate ℤ ℤ,
      module ℤ ℤ ℤ ℤ (IsIdempotented.of_ring ℤ) hY = AddCommGroup.toIntModule _ :=
  fun _ => Subsingleton.elim _ _

end RegularInteger

/-! ### Explicit choices under competing structures -/

noncomputable section

section CompetingCoefficientModules

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
  [competingX : Module k X] [competingY : Module k Y] [competingT : Module k (Tensor A X Y)]

/-- Under competing coefficient modules on `X`, `Y` and the tensor, the installed structures are
exactly the published canonical ones and the constructed tensor module. -/
example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    (inferInstance : Module k X) = NondegenerateScalars.module k hA.op hX ∧
      (inferInstance : Module k Y) = NondegenerateScalars.module k hA hY ∧
      (inferInstance : Module k (Tensor A X Y)) = module k A X Y hA hY :=
  ⟨rfl, rfl, rfl⟩

example (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) (t : Tensor A X Y) :
    letI := module k A X Y hA hY
    c • t = NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c) t :=
  rfl

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (c : k) (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    c • tmul A X Y x y = tmul A X Y (c • x) y ∧ tmul A X Y (c • x) y = tmul A X Y x (c • y) :=
  ⟨smul_tmul_left k A X Y hA hX hY c x y, tmul_smul_left_eq k A X Y hA hX hY c x y⟩

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    X →ₗ[k] Y →ₗ[k] Tensor A X Y :=
  bilinear k A X Y hA hX hY

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    coefficientRelations k A X Y hA hX hY =
      Submodule.span k {(op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | (a : A) (x : X) (y : Y)} :=
  coefficientRelations_eq_span k A X Y hA hX hY

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  quotientEquiv k A X Y hA hX hY

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    (quotientEquiv k A X Y hA hX hY).symm (tmul A X Y x y) =
      Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y) :=
  quotientEquiv_symm_tmul k A X Y hA hX hY x y

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := rightModule k hA hX
    letI := leftModule k hA hY
    letI := module k A X Y hA hY
    LinearMap.ker (coefficientProjection k A X Y hA hX hY) =
      coefficientRelations k A X Y hA hX hY :=
  ker_coefficientProjection k A X Y hA hX hY

end CompetingCoefficientModules

section CompetingComplexModules

set_option linter.overlappingInstances false

variable (A : Type uA) (X : Type uX) (Y : Type uY)
  [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
  [competingX : Module ℂ X] [competingY : Module ℂ Y] [competingT : Module ℂ (Tensor A X Y)]

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    (inferInstance : Module ℂ X) = NondegenerateScalars.complexModule hA.op hX ∧
      (inferInstance : Module ℂ Y) = NondegenerateScalars.complexModule hA hY ∧
      (inferInstance : Module ℂ (Tensor A X Y)) = module ℂ A X Y hA hY :=
  ⟨rfl, rfl, rfl⟩

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (c : ℂ) (x : X) (y : Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    c • tmul A X Y x y = tmul A X Y (c • x) y ∧ c • tmul A X Y x y = tmul A X Y x (c • y) :=
  ⟨complex_smul_tmul_left A X Y hA hX hY c x y, complex_smul_tmul_right A X Y hA hY c x y⟩

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) :
    letI := complexRightModule hA hX
    letI := complexLeftModule hA hY
    letI := complexModule A X Y hA hY
    ((X ⊗[ℂ] Y) ⧸ complexRelations A X Y hA hX hY) ≃ₗ[ℂ] Tensor A X Y :=
  complexQuotientEquiv A X Y hA hX hY

end CompetingComplexModules

section CompetingTargetModule

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
  (Z : Type uZ) [AddCommGroup Z] [originalZ : Module k Z] [competingZ : Module k Z]

example (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY; letI := originalZ;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)) :
    letI := originalZ
    letI := module k A X Y hA hY
    Tensor A X Y →ₗ[k] Z :=
  @linearLift k A X Y _ _ _ _ _ _ _ _ _ Z _ originalZ hA hX hY b hb

end CompetingTargetModule

section CompetingCoefficientRing

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) [originalRing : CommRing k] [NonUnitalRing A]
  [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] [competingRing : CommRing k]

example :
    letI := originalRing
    ∀ (X : Type uX) (Y : Type uY) [AddCommGroup X] [AddCommGroup Y]
      [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
      (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  fun X Y => @quotientEquiv k A X Y originalRing _ _ _ _

end CompetingCoefficientRing

section CompetingAmbient

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) [CommRing k] [originalAmbient : NonUnitalRing A]
  [originalScalars : Module k A] [originalTower : IsScalarTower k A A]
  [originalComm : SMulCommClass k A A]
  [competingAmbient : NonUnitalRing A] [competingScalars : Module k A]

example :
    letI := originalAmbient
    letI := originalScalars
    ∀ (X : Type uX) (Y : Type uY) [AddCommGroup X] [AddCommGroup Y]
      [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
      (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  fun X Y => @quotientEquiv k A X Y _ originalAmbient originalScalars originalTower originalComm

example :
    letI := originalAmbient
    letI := originalScalars
    ∀ {X : Type uX} {Y : Type uY} [AddCommGroup X] [AddCommGroup Y]
      [NonUnitalModule Aᵐᵒᵖ X] [NonUnitalModule A Y]
      {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
      [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
      (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
      (_f : NonUnitalModuleHom Aᵐᵒᵖ X X') (_g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      Tensor A X Y →ₗ[k] Tensor A X' Y' :=
  fun {X} {Y} => @linearMap k A X Y _ originalAmbient originalScalars originalTower originalComm

end CompetingAmbient

section CompetingGroups

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [originalXGroup : AddCommGroup X] [originalYGroup : AddCommGroup Y]
  [originalRight : NonUnitalModule Aᵐᵒᵖ X] [originalLeft : NonUnitalModule A Y]
  [competingXGroup : AddCommGroup X] [competingYGroup : AddCommGroup Y]

example :
    letI := originalXGroup
    letI := originalYGroup
    ∀ (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  @quotientEquiv k A X Y _ _ _ _ _ originalXGroup originalYGroup originalRight originalLeft

example :
    letI := originalXGroup
    letI := originalYGroup
    IsIdempotented A → IsNondegenerate A Y → Module k (Tensor A X Y) :=
  @module k A X Y _ _ _ _ _ originalXGroup originalYGroup originalRight originalLeft

end CompetingGroups

section CompetingActions

set_option linter.overlappingInstances false

variable (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
  [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
  [AddCommGroup X] [AddCommGroup Y]
  [originalRight : NonUnitalModule Aᵐᵒᵖ X] [originalLeft : NonUnitalModule A Y]
  [competingRight : NonUnitalModule Aᵐᵒᵖ X] [competingLeft : NonUnitalModule A Y]

example :
    letI := originalRight
    letI := originalLeft
    ∀ (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  @quotientEquiv k A X Y _ _ _ _ _ _ _ originalRight originalLeft

example :
    letI := originalRight
    letI := originalLeft
    ∀ (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      X →ₗ[k] Y →ₗ[k] Tensor A X Y :=
  @bilinear k A X Y _ _ _ _ _ _ _ originalRight originalLeft

end CompetingActions

end

/-! ### Complete unapplied interfaces at independent universes -/

noncomputable section

set_option linter.unusedVariables false

section ArbitraryUniverses

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      Module k (Tensor A X Y) :=
  @module

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k),
      Tensor A X Y →+ Tensor A X Y :=
  @scalarEnd

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) (t : Tensor A X Y),
      letI := module k A X Y hA hY
      c • t = scalarEnd k A X Y hA hY c t :=
  @smul_def

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k),
      letI := module k A X Y hA hY
      DistribSMul.toAddMonoidHom (Tensor A X Y) c =
        NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c) :=
  @toAddMonoidHom_smul

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (c : k),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
        (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  @smul_tmul_function

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      X →ₗ[k] Y →ₗ[k] Tensor A X Y :=
  @bilinear

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      bilinear k A X Y hA hX hY x y = tmul A X Y x y :=
  @bilinear_apply

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      toBiadditive (bilinear k A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  @toBiadditive_bilinear

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (X ⊗[k] Y) →ₗ[k] Tensor A X Y :=
  @coefficientProjection

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      coefficientProjection k A X Y hA hX hY = TensorProduct.lift (bilinear k A X Y hA hX hY) :=
  @coefficientProjection_eq_lift

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      coefficientProjection k A X Y hA hX hY (x ⊗ₜ[k] y) = tmul A X Y x y :=
  @coefficientProjection_tmul

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (TensorProduct.mk k X Y).compr₂ (coefficientProjection k A X Y hA hX hY) =
        bilinear k A X Y hA hX hY :=
  @mk_compr₂_coefficientProjection

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      Function.Surjective (coefficientProjection k A X Y hA hX hY) :=
  @coefficientProjection_surjective

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      Submodule k (X ⊗[k] Y) :=
  @coefficientRelations

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      coefficientRelations k A X Y hA hX hY =
        Submodule.span k {(op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | (a : A) (x : X) (y : Y)} :=
  @coefficientRelations_eq_span

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  @quotientEquiv

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      quotientEquiv k A X Y hA hX hY
          (Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y)) =
        tmul A X Y x y :=
  @quotientEquiv_mk_tmul

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      (quotientEquiv k A X Y hA hX hY).symm (tmul A X Y x y) =
        Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y) :=
  @quotientEquiv_symm_tmul

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.comp
          (quotientEquiv k A X Y hA hX hY).toLinearMap = LinearMap.id :=
  @quotientEquiv_symm_comp

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
          (quotientEquiv k A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  @quotientEquiv_comp_symm

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).toLinearMap.toAddMonoidHom =
        ((coefficientRelations k A X Y hA hX hY).liftQ (coefficientProjection k A X Y hA hX hY)
          (coefficientRelations_le_ker k A X Y hA hX hY)).toAddMonoidHom :=
  @quotientEquiv_toAddMonoidHom

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toQuotientBiadditive k A X Y hA hX hY)
          (toQuotientBiadditive_balanced k A X Y hA hX hY) :=
  @quotientEquiv_symm_toAddMonoidHom

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      coefficientProjection k A X Y hA hX hY =
        (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
          (coefficientRelations k A X Y hA hX hY).mkQ :=
  @coefficientProjection_eq_comp_mkQ

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      LinearMap.ker (coefficientProjection k A X Y hA hX hY) =
        coefficientRelations k A X Y hA hX hY :=
  @ker_coefficientProjection

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := module k A X Y hA hY
      Tensor A X Y →ₗ[k] Z :=
  @linearLift

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (linearLift k A X Y hA hX hY b hb).toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toBiadditive b) hb :=
  @linearLift_toAddMonoidHom

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (x : X) (y : Y),
      linearLift k A X Y hA hX hY b hb (tmul A X Y x y) = b x y :=
  @linearLift_tmul

example : ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := module k A X Y hA hY; Tensor A X Y →ₗ[k] Z),
      (∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) →
        f = linearLift k A X Y hA hX hY b hb :=
  @linearLift_unique

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      Tensor A X Y →ₗ[k] Tensor A X' Y' :=
  @linearMap

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      (linearMap k A hA hY hY' f g).toAddMonoidHom =
        NonUnitalModuleTensor.map A f g :=
  @linearMap_toAddMonoidHom

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y),
      linearMap k A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) :=
  @linearMap_tmul

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      letI := module k A X Y hA hY
      linearMap k A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
        LinearMap.id :=
  @linearMap_id

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    {X'' : Type uX''} {Y'' : Type uY''} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y''),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      letI := module k A X'' Y'' hA hY''
      (linearMap k A hA hY' hY'' f' g').comp (linearMap k A hA hY hY' f g) =
        linearMap k A hA hY hY'' (f'.comp f) (g'.comp g) :=
  @linearMap_comp

example : ∀ (k : Type uK) (A : Type uA) {X : Type uX} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := rightModule k hA hX'
      letI := leftModule k hA hY'
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      (linearMap k A hA hY hY' f g).comp (coefficientProjection k A X Y hA hX hY) =
        (coefficientProjection k A X' Y' hA hX' hY').comp
          (TensorProduct.map (NondegenerateScalars.toLinearMap k hA.op hX hX' f)
            (NondegenerateScalars.toLinearMap k hA hY hY' g)) :=
  @linearMap_comp_coefficientProjection

example : ∀ (k : Type uK) {A : Type uA} {X : Type uX}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X),
      rightModule k hA hX = NondegenerateScalars.module k hA.op hX :=
  @rightModule_eq

example : ∀ (k : Type uK) {A : Type uA} {Y : Type uY}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      leftModule k hA hY = NondegenerateScalars.module k hA hY :=
  @leftModule_eq

end ArbitraryUniverses

section UniversesOneZero

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      Module k (Tensor A X Y) :=
  @module

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k),
      Tensor A X Y →+ Tensor A X Y :=
  @scalarEnd

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) (t : Tensor A X Y),
      letI := module k A X Y hA hY
      c • t = scalarEnd k A X Y hA hY c t :=
  @smul_def

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k),
      letI := module k A X Y hA hY
      DistribSMul.toAddMonoidHom (Tensor A X Y) c =
        NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c) :=
  @toAddMonoidHom_smul

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (c : k),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
        (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  @smul_tmul_function

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      X →ₗ[k] Y →ₗ[k] Tensor A X Y :=
  @bilinear

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      bilinear k A X Y hA hX hY x y = tmul A X Y x y :=
  @bilinear_apply

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      toBiadditive (bilinear k A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  @toBiadditive_bilinear

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (X ⊗[k] Y) →ₗ[k] Tensor A X Y :=
  @coefficientProjection

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      coefficientProjection k A X Y hA hX hY = TensorProduct.lift (bilinear k A X Y hA hX hY) :=
  @coefficientProjection_eq_lift

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      coefficientProjection k A X Y hA hX hY (x ⊗ₜ[k] y) = tmul A X Y x y :=
  @coefficientProjection_tmul

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (TensorProduct.mk k X Y).compr₂ (coefficientProjection k A X Y hA hX hY) =
        bilinear k A X Y hA hX hY :=
  @mk_compr₂_coefficientProjection

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      Function.Surjective (coefficientProjection k A X Y hA hX hY) :=
  @coefficientProjection_surjective

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      Submodule k (X ⊗[k] Y) :=
  @coefficientRelations

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      coefficientRelations k A X Y hA hX hY =
        Submodule.span k {(op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | (a : A) (x : X) (y : Y)} :=
  @coefficientRelations_eq_span

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  @quotientEquiv

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      quotientEquiv k A X Y hA hX hY
          (Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y)) =
        tmul A X Y x y :=
  @quotientEquiv_mk_tmul

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      (quotientEquiv k A X Y hA hX hY).symm (tmul A X Y x y) =
        Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y) :=
  @quotientEquiv_symm_tmul

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.comp
          (quotientEquiv k A X Y hA hX hY).toLinearMap = LinearMap.id :=
  @quotientEquiv_symm_comp

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
          (quotientEquiv k A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  @quotientEquiv_comp_symm

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).toLinearMap.toAddMonoidHom =
        ((coefficientRelations k A X Y hA hX hY).liftQ (coefficientProjection k A X Y hA hX hY)
          (coefficientRelations_le_ker k A X Y hA hX hY)).toAddMonoidHom :=
  @quotientEquiv_toAddMonoidHom

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toQuotientBiadditive k A X Y hA hX hY)
          (toQuotientBiadditive_balanced k A X Y hA hX hY) :=
  @quotientEquiv_symm_toAddMonoidHom

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      coefficientProjection k A X Y hA hX hY =
        (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
          (coefficientRelations k A X Y hA hX hY).mkQ :=
  @coefficientProjection_eq_comp_mkQ

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      LinearMap.ker (coefficientProjection k A X Y hA hX hY) =
        coefficientRelations k A X Y hA hX hY :=
  @ker_coefficientProjection

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := module k A X Y hA hY
      Tensor A X Y →ₗ[k] Z :=
  @linearLift

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (linearLift k A X Y hA hX hY b hb).toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toBiadditive b) hb :=
  @linearLift_toAddMonoidHom

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (x : X) (y : Y),
      linearLift k A X Y hA hX hY b hb (tmul A X Y x y) = b x y :=
  @linearLift_tmul

example : ∀ (k : Type 1) (A : Type 0) (X : Type 1) (Y : Type 0)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := module k A X Y hA hY; Tensor A X Y →ₗ[k] Z),
      (∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) →
        f = linearLift k A X Y hA hX hY b hb :=
  @linearLift_unique

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      Tensor A X Y →ₗ[k] Tensor A X' Y' :=
  @linearMap

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      (linearMap k A hA hY hY' f g).toAddMonoidHom =
        NonUnitalModuleTensor.map A f g :=
  @linearMap_toAddMonoidHom

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y),
      linearMap k A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) :=
  @linearMap_tmul

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      letI := module k A X Y hA hY
      linearMap k A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
        LinearMap.id :=
  @linearMap_id

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    {X'' : Type 0} {Y'' : Type 1} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y''),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      letI := module k A X'' Y'' hA hY''
      (linearMap k A hA hY' hY'' f' g').comp (linearMap k A hA hY hY' f g) =
        linearMap k A hA hY hY'' (f'.comp f) (g'.comp g) :=
  @linearMap_comp

example : ∀ (k : Type 1) (A : Type 0) {X : Type 1} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := rightModule k hA hX'
      letI := leftModule k hA hY'
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      (linearMap k A hA hY hY' f g).comp (coefficientProjection k A X Y hA hX hY) =
        (coefficientProjection k A X' Y' hA hX' hY').comp
          (TensorProduct.map (NondegenerateScalars.toLinearMap k hA.op hX hX' f)
            (NondegenerateScalars.toLinearMap k hA hY hY' g)) :=
  @linearMap_comp_coefficientProjection

example : ∀ (k : Type 1) {A : Type 0} {X : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X),
      rightModule k hA hX = NondegenerateScalars.module k hA.op hX :=
  @rightModule_eq

example : ∀ (k : Type 1) {A : Type 0} {Y : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      leftModule k hA hY = NondegenerateScalars.module k hA hY :=
  @leftModule_eq

end UniversesOneZero

section UniversesZeroOne

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      Module k (Tensor A X Y) :=
  @module

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k),
      Tensor A X Y →+ Tensor A X Y :=
  @scalarEnd

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k) (t : Tensor A X Y),
      letI := module k A X Y hA hY
      c • t = scalarEnd k A X Y hA hY c t :=
  @smul_def

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : k),
      letI := module k A X Y hA hY
      DistribSMul.toAddMonoidHom (Tensor A X Y) c =
        NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom k hA hY c) :=
  @toAddMonoidHom_smul

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (c : k),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
        (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  @smul_tmul_function

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      X →ₗ[k] Y →ₗ[k] Tensor A X Y :=
  @bilinear

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      bilinear k A X Y hA hX hY x y = tmul A X Y x y :=
  @bilinear_apply

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      toBiadditive (bilinear k A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  @toBiadditive_bilinear

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (X ⊗[k] Y) →ₗ[k] Tensor A X Y :=
  @coefficientProjection

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      coefficientProjection k A X Y hA hX hY = TensorProduct.lift (bilinear k A X Y hA hX hY) :=
  @coefficientProjection_eq_lift

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      coefficientProjection k A X Y hA hX hY (x ⊗ₜ[k] y) = tmul A X Y x y :=
  @coefficientProjection_tmul

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (TensorProduct.mk k X Y).compr₂ (coefficientProjection k A X Y hA hX hY) =
        bilinear k A X Y hA hX hY :=
  @mk_compr₂_coefficientProjection

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      Function.Surjective (coefficientProjection k A X Y hA hX hY) :=
  @coefficientProjection_surjective

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      Submodule k (X ⊗[k] Y) :=
  @coefficientRelations

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      coefficientRelations k A X Y hA hX hY =
        Submodule.span k {(op a • x) ⊗ₜ[k] y - x ⊗ₜ[k] (a • y) | (a : A) (x : X) (y : Y)} :=
  @coefficientRelations_eq_span

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      ((X ⊗[k] Y) ⧸ coefficientRelations k A X Y hA hX hY) ≃ₗ[k] Tensor A X Y :=
  @quotientEquiv

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      quotientEquiv k A X Y hA hX hY
          (Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y)) =
        tmul A X Y x y :=
  @quotientEquiv_mk_tmul

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      (quotientEquiv k A X Y hA hX hY).symm (tmul A X Y x y) =
        Submodule.Quotient.mk (p := coefficientRelations k A X Y hA hX hY) (x ⊗ₜ[k] y) :=
  @quotientEquiv_symm_tmul

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.comp
          (quotientEquiv k A X Y hA hX hY).toLinearMap = LinearMap.id :=
  @quotientEquiv_symm_comp

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
          (quotientEquiv k A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  @quotientEquiv_comp_symm

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).toLinearMap.toAddMonoidHom =
        ((coefficientRelations k A X Y hA hX hY).liftQ (coefficientProjection k A X Y hA hX hY)
          (coefficientRelations_le_ker k A X Y hA hX hY)).toAddMonoidHom :=
  @quotientEquiv_toAddMonoidHom

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (quotientEquiv k A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toQuotientBiadditive k A X Y hA hX hY)
          (toQuotientBiadditive_balanced k A X Y hA hX hY) :=
  @quotientEquiv_symm_toAddMonoidHom

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      coefficientProjection k A X Y hA hX hY =
        (quotientEquiv k A X Y hA hX hY).toLinearMap.comp
          (coefficientRelations k A X Y hA hX hY).mkQ :=
  @coefficientProjection_eq_comp_mkQ

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      LinearMap.ker (coefficientProjection k A X Y hA hX hY) =
        coefficientRelations k A X Y hA hX hY :=
  @ker_coefficientProjection

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := module k A X Y hA hY
      Tensor A X Y →ₗ[k] Z :=
  @linearLift

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := module k A X Y hA hY
      (linearLift k A X Y hA hX hY b hb).toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toBiadditive b) hb :=
  @linearLift_toAddMonoidHom

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (x : X) (y : Y),
      linearLift k A X Y hA hX hY b hb (tmul A X Y x y) = b x y :=
  @linearLift_tmul

example : ∀ (k : Type 0) (A : Type 1) (X : Type 0) (Y : Type 1)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module k Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := rightModule k hA hX; letI := leftModule k hA hY;
      X →ₗ[k] Y →ₗ[k] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := module k A X Y hA hY; Tensor A X Y →ₗ[k] Z),
      (∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) →
        f = linearLift k A X Y hA hX hY b hb :=
  @linearLift_unique

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      Tensor A X Y →ₗ[k] Tensor A X' Y' :=
  @linearMap

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      (linearMap k A hA hY hY' f g).toAddMonoidHom =
        NonUnitalModuleTensor.map A f g :=
  @linearMap_toAddMonoidHom

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y),
      linearMap k A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) :=
  @linearMap_tmul

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      letI := module k A X Y hA hY
      linearMap k A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
        LinearMap.id :=
  @linearMap_id

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    {X'' : Type 1} {Y'' : Type 0} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y''),
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      letI := module k A X'' Y'' hA hY''
      (linearMap k A hA hY' hY'' f' g').comp (linearMap k A hA hY hY' f g) =
        linearMap k A hA hY hY'' (f'.comp f) (g'.comp g) :=
  @linearMap_comp

example : ∀ (k : Type 0) (A : Type 1) {X : Type 0} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := rightModule k hA hX
      letI := leftModule k hA hY
      letI := rightModule k hA hX'
      letI := leftModule k hA hY'
      letI := module k A X Y hA hY
      letI := module k A X' Y' hA hY'
      (linearMap k A hA hY hY' f g).comp (coefficientProjection k A X Y hA hX hY) =
        (coefficientProjection k A X' Y' hA hX' hY').comp
          (TensorProduct.map (NondegenerateScalars.toLinearMap k hA.op hX hX' f)
            (NondegenerateScalars.toLinearMap k hA hY hY' g)) :=
  @linearMap_comp_coefficientProjection

example : ∀ (k : Type 0) {A : Type 1} {X : Type 0}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X),
      rightModule k hA hX = NondegenerateScalars.module k hA.op hX :=
  @rightModule_eq

example : ∀ (k : Type 0) {A : Type 1} {Y : Type 1}
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A]
    [SMulCommClass k A A] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      leftModule k hA hY = NondegenerateScalars.module k hA hY :=
  @leftModule_eq

end UniversesZeroOne

section ComplexArbitraryUniverses

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      Module ℂ (Tensor A X Y) :=
  @complexModule

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : ℂ),
      letI := complexModule A X Y hA hY
      DistribSMul.toAddMonoidHom (Tensor A X Y) c =
        NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom ℂ hA hY c) :=
  @complex_toAddMonoidHom_smul

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (c : ℂ),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
        (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  @complex_smul_tmul_function

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      X →ₗ[ℂ] Y →ₗ[ℂ] Tensor A X Y :=
  @complexBilinear

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      complexBilinear A X Y hA hX hY x y = tmul A X Y x y :=
  @complexBilinear_apply

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      toBiadditive (complexBilinear A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  @toBiadditive_complexBilinear

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (X ⊗[ℂ] Y) →ₗ[ℂ] Tensor A X Y :=
  @complexProjection

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      complexProjection A X Y hA hX hY = TensorProduct.lift (complexBilinear A X Y hA hX hY) :=
  @complexProjection_eq_lift

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexProjection A X Y hA hX hY (x ⊗ₜ[ℂ] y) = tmul A X Y x y :=
  @complexProjection_tmul

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      Function.Surjective (complexProjection A X Y hA hX hY) :=
  @complexProjection_surjective

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      Submodule ℂ (X ⊗[ℂ] Y) :=
  @complexRelations

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexRelations A X Y hA hX hY =
        Submodule.span ℂ {(op a • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (a • y) | (a : A) (x : X) (y : Y)} :=
  @complexRelations_eq_span

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      ((X ⊗[ℂ] Y) ⧸ complexRelations A X Y hA hX hY) ≃ₗ[ℂ] Tensor A X Y :=
  @complexQuotientEquiv

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexQuotientEquiv A X Y hA hX hY
          (Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y)) =
        tmul A X Y x y :=
  @complexQuotientEquiv_mk_tmul

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm (tmul A X Y x y) =
        Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y) :=
  @complexQuotientEquiv_symm_tmul

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.comp
          (complexQuotientEquiv A X Y hA hX hY).toLinearMap = LinearMap.id :=
  @complexQuotientEquiv_symm_comp

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
          (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  @complexQuotientEquiv_comp_symm

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.toAddMonoidHom =
        ((complexRelations A X Y hA hX hY).liftQ (complexProjection A X Y hA hX hY)
          (coefficientRelations_le_ker ℂ A X Y hA hX hY)).toAddMonoidHom :=
  @complexQuotientEquiv_toAddMonoidHom

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toQuotientBiadditive ℂ A X Y hA hX hY)
          (toQuotientBiadditive_balanced ℂ A X Y hA hX hY) :=
  @complexQuotientEquiv_symm_toAddMonoidHom

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      complexProjection A X Y hA hX hY =
        (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
          (complexRelations A X Y hA hX hY).mkQ :=
  @complexProjection_eq_comp_mkQ

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      LinearMap.ker (complexProjection A X Y hA hX hY) =
        complexRelations A X Y hA hX hY :=
  @ker_complexProjection

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := complexModule A X Y hA hY
      Tensor A X Y →ₗ[ℂ] Z :=
  @complexLinearLift

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexLinearLift A X Y hA hX hY b hb).toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toBiadditive b) hb :=
  @complexLinearLift_toAddMonoidHom

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (x : X) (y : Y),
      complexLinearLift A X Y hA hX hY b hb (tmul A X Y x y) = b x y :=
  @complexLinearLift_tmul

example : ∀ (A : Type uA) (X : Type uX) (Y : Type uY)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := complexModule A X Y hA hY; Tensor A X Y →ₗ[ℂ] Z),
      (∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) →
        f = complexLinearLift A X Y hA hX hY b hb :=
  @complexLinearLift_unique

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      Tensor A X Y →ₗ[ℂ] Tensor A X' Y' :=
  @complexLinearMap

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      (complexLinearMap A hA hY hY' f g).toAddMonoidHom =
        NonUnitalModuleTensor.map A f g :=
  @complexLinearMap_toAddMonoidHom

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y),
      complexLinearMap A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) :=
  @complexLinearMap_tmul

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      letI := complexModule A X Y hA hY
      complexLinearMap A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
        LinearMap.id :=
  @complexLinearMap_id

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    {X'' : Type uX''} {Y'' : Type uY''} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y''),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      letI := complexModule A X'' Y'' hA hY''
      (complexLinearMap A hA hY' hY'' f' g').comp (complexLinearMap A hA hY hY' f g) =
        complexLinearMap A hA hY hY'' (f'.comp f) (g'.comp g) :=
  @complexLinearMap_comp

example : ∀ (A : Type uA) {X : Type uX} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type uX'} {Y' : Type uY'} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexRightModule hA hX'
      letI := complexLeftModule hA hY'
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      (complexLinearMap A hA hY hY' f g).comp (complexProjection A X Y hA hX hY) =
        (complexProjection A X' Y' hA hX' hY').comp
          (TensorProduct.map (NondegenerateScalars.complexToLinearMap hA.op hX hX' f)
            (NondegenerateScalars.complexToLinearMap hA hY hY' g)) :=
  @complexLinearMap_comp_complexProjection

example : ∀ {A : Type uA} {X : Type uX}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X),
      complexRightModule hA hX = NondegenerateScalars.complexModule hA.op hX :=
  @complexRightModule_eq

example : ∀ {A : Type uA} {Y : Type uY}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      complexLeftModule hA hY = NondegenerateScalars.complexModule hA hY :=
  @complexLeftModule_eq

end ComplexArbitraryUniverses

section ComplexUniversesZeroOne

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      Module ℂ (Tensor A X Y) :=
  @complexModule

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : ℂ),
      letI := complexModule A X Y hA hY
      DistribSMul.toAddMonoidHom (Tensor A X Y) c =
        NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom ℂ hA hY c) :=
  @complex_toAddMonoidHom_smul

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (c : ℂ),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
        (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  @complex_smul_tmul_function

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      X →ₗ[ℂ] Y →ₗ[ℂ] Tensor A X Y :=
  @complexBilinear

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      complexBilinear A X Y hA hX hY x y = tmul A X Y x y :=
  @complexBilinear_apply

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      toBiadditive (complexBilinear A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  @toBiadditive_complexBilinear

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (X ⊗[ℂ] Y) →ₗ[ℂ] Tensor A X Y :=
  @complexProjection

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      complexProjection A X Y hA hX hY = TensorProduct.lift (complexBilinear A X Y hA hX hY) :=
  @complexProjection_eq_lift

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexProjection A X Y hA hX hY (x ⊗ₜ[ℂ] y) = tmul A X Y x y :=
  @complexProjection_tmul

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      Function.Surjective (complexProjection A X Y hA hX hY) :=
  @complexProjection_surjective

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      Submodule ℂ (X ⊗[ℂ] Y) :=
  @complexRelations

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexRelations A X Y hA hX hY =
        Submodule.span ℂ {(op a • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (a • y) | (a : A) (x : X) (y : Y)} :=
  @complexRelations_eq_span

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      ((X ⊗[ℂ] Y) ⧸ complexRelations A X Y hA hX hY) ≃ₗ[ℂ] Tensor A X Y :=
  @complexQuotientEquiv

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexQuotientEquiv A X Y hA hX hY
          (Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y)) =
        tmul A X Y x y :=
  @complexQuotientEquiv_mk_tmul

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm (tmul A X Y x y) =
        Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y) :=
  @complexQuotientEquiv_symm_tmul

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.comp
          (complexQuotientEquiv A X Y hA hX hY).toLinearMap = LinearMap.id :=
  @complexQuotientEquiv_symm_comp

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
          (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  @complexQuotientEquiv_comp_symm

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.toAddMonoidHom =
        ((complexRelations A X Y hA hX hY).liftQ (complexProjection A X Y hA hX hY)
          (coefficientRelations_le_ker ℂ A X Y hA hX hY)).toAddMonoidHom :=
  @complexQuotientEquiv_toAddMonoidHom

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toQuotientBiadditive ℂ A X Y hA hX hY)
          (toQuotientBiadditive_balanced ℂ A X Y hA hX hY) :=
  @complexQuotientEquiv_symm_toAddMonoidHom

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      complexProjection A X Y hA hX hY =
        (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
          (complexRelations A X Y hA hX hY).mkQ :=
  @complexProjection_eq_comp_mkQ

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      LinearMap.ker (complexProjection A X Y hA hX hY) =
        complexRelations A X Y hA hX hY :=
  @ker_complexProjection

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := complexModule A X Y hA hY
      Tensor A X Y →ₗ[ℂ] Z :=
  @complexLinearLift

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexLinearLift A X Y hA hX hY b hb).toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toBiadditive b) hb :=
  @complexLinearLift_toAddMonoidHom

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (x : X) (y : Y),
      complexLinearLift A X Y hA hX hY b hb (tmul A X Y x y) = b x y :=
  @complexLinearLift_tmul

example : ∀ (A : Type 0) (X : Type 1) (Y : Type 0)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 1} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := complexModule A X Y hA hY; Tensor A X Y →ₗ[ℂ] Z),
      (∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) →
        f = complexLinearLift A X Y hA hX hY b hb :=
  @complexLinearLift_unique

example : ∀ (A : Type 0) {X : Type 1} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      Tensor A X Y →ₗ[ℂ] Tensor A X' Y' :=
  @complexLinearMap

example : ∀ (A : Type 0) {X : Type 1} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      (complexLinearMap A hA hY hY' f g).toAddMonoidHom =
        NonUnitalModuleTensor.map A f g :=
  @complexLinearMap_toAddMonoidHom

example : ∀ (A : Type 0) {X : Type 1} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y),
      complexLinearMap A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) :=
  @complexLinearMap_tmul

example : ∀ (A : Type 0) {X : Type 1} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      letI := complexModule A X Y hA hY
      complexLinearMap A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
        LinearMap.id :=
  @complexLinearMap_id

example : ∀ (A : Type 0) {X : Type 1} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    {X'' : Type 0} {Y'' : Type 1} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y''),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      letI := complexModule A X'' Y'' hA hY''
      (complexLinearMap A hA hY' hY'' f' g').comp (complexLinearMap A hA hY hY' f g) =
        complexLinearMap A hA hY hY'' (f'.comp f) (g'.comp g) :=
  @complexLinearMap_comp

example : ∀ (A : Type 0) {X : Type 1} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 0} {Y' : Type 1} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexRightModule hA hX'
      letI := complexLeftModule hA hY'
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      (complexLinearMap A hA hY hY' f g).comp (complexProjection A X Y hA hX hY) =
        (complexProjection A X' Y' hA hX' hY').comp
          (TensorProduct.map (NondegenerateScalars.complexToLinearMap hA.op hX hX' f)
            (NondegenerateScalars.complexToLinearMap hA hY hY' g)) :=
  @complexLinearMap_comp_complexProjection

example : ∀ {A : Type 0} {X : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X),
      complexRightModule hA hX = NondegenerateScalars.complexModule hA.op hX :=
  @complexRightModule_eq

example : ∀ {A : Type 0} {Y : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      complexLeftModule hA hY = NondegenerateScalars.complexModule hA hY :=
  @complexLeftModule_eq

end ComplexUniversesZeroOne

section ComplexUniversesOneZero

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      Module ℂ (Tensor A X Y) :=
  @complexModule

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (c : ℂ),
      letI := complexModule A X Y hA hY
      DistribSMul.toAddMonoidHom (Tensor A X Y) c =
        NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ X) (scalarHom ℂ hA hY c) :=
  @complex_toAddMonoidHom_smul

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y) (c : ℂ),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (fun x y => c • tmul A X Y x y) = (fun x y => tmul A X Y (c • x) y) ∧
        (fun x y => tmul A X Y (c • x) y) = (fun x y => tmul A X Y x (c • y)) :=
  @complex_smul_tmul_function

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      X →ₗ[ℂ] Y →ₗ[ℂ] Tensor A X Y :=
  @complexBilinear

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      complexBilinear A X Y hA hX hY x y = tmul A X Y x y :=
  @complexBilinear_apply

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      toBiadditive (complexBilinear A X Y hA hX hY) = NonUnitalModuleTensor.biadditive A X Y :=
  @toBiadditive_complexBilinear

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (X ⊗[ℂ] Y) →ₗ[ℂ] Tensor A X Y :=
  @complexProjection

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      complexProjection A X Y hA hX hY = TensorProduct.lift (complexBilinear A X Y hA hX hY) :=
  @complexProjection_eq_lift

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexProjection A X Y hA hX hY (x ⊗ₜ[ℂ] y) = tmul A X Y x y :=
  @complexProjection_tmul

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      Function.Surjective (complexProjection A X Y hA hX hY) :=
  @complexProjection_surjective

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      Submodule ℂ (X ⊗[ℂ] Y) :=
  @complexRelations

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexRelations A X Y hA hX hY =
        Submodule.span ℂ {(op a • x) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (a • y) | (a : A) (x : X) (y : Y)} :=
  @complexRelations_eq_span

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      ((X ⊗[ℂ] Y) ⧸ complexRelations A X Y hA hX hY) ≃ₗ[ℂ] Tensor A X Y :=
  @complexQuotientEquiv

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      complexQuotientEquiv A X Y hA hX hY
          (Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y)) =
        tmul A X Y x y :=
  @complexQuotientEquiv_mk_tmul

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (x : X) (y : Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm (tmul A X Y x y) =
        Submodule.Quotient.mk (p := complexRelations A X Y hA hX hY) (x ⊗ₜ[ℂ] y) :=
  @complexQuotientEquiv_symm_tmul

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.comp
          (complexQuotientEquiv A X Y hA hX hY).toLinearMap = LinearMap.id :=
  @complexQuotientEquiv_symm_comp

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
          (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap = LinearMap.id :=
  @complexQuotientEquiv_comp_symm

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).toLinearMap.toAddMonoidHom =
        ((complexRelations A X Y hA hX hY).liftQ (complexProjection A X Y hA hX hY)
          (coefficientRelations_le_ker ℂ A X Y hA hX hY)).toAddMonoidHom :=
  @complexQuotientEquiv_toAddMonoidHom

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexQuotientEquiv A X Y hA hX hY).symm.toLinearMap.toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toQuotientBiadditive ℂ A X Y hA hX hY)
          (toQuotientBiadditive_balanced ℂ A X Y hA hX hY) :=
  @complexQuotientEquiv_symm_toAddMonoidHom

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      complexProjection A X Y hA hX hY =
        (complexQuotientEquiv A X Y hA hX hY).toLinearMap.comp
          (complexRelations A X Y hA hX hY).mkQ :=
  @complexProjection_eq_comp_mkQ

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      LinearMap.ker (complexProjection A X Y hA hX hY) =
        complexRelations A X Y hA hX hY :=
  @ker_complexProjection

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := complexModule A X Y hA hY
      Tensor A X Y →ₗ[ℂ] Z :=
  @complexLinearLift

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y)),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexModule A X Y hA hY
      (complexLinearLift A X Y hA hX hY b hb).toAddMonoidHom =
        NonUnitalModuleTensor.lift A (toBiadditive b) hb :=
  @complexLinearLift_toAddMonoidHom

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (x : X) (y : Y),
      complexLinearLift A X Y hA hX hY b hb (tmul A X Y x y) = b x y :=
  @complexLinearLift_tmul

example : ∀ (A : Type 1) (X : Type 0) (Y : Type 1)
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {Z : Type 0} [AddCommGroup Z] [Module ℂ Z]
    (hA : IsIdempotented A)
    (hX : IsNondegenerate Aᵐᵒᵖ X)
    (hY : IsNondegenerate A Y)
    (b : letI := complexRightModule hA hX; letI := complexLeftModule hA hY;
      X →ₗ[ℂ] Y →ₗ[ℂ] Z)
    (hb : ∀ (a : A) (x : X) (y : Y), b (op a • x) y = b x (a • y))
    (f : letI := complexModule A X Y hA hY; Tensor A X Y →ₗ[ℂ] Z),
      (∀ (x : X) (y : Y), f (tmul A X Y x y) = b x y) →
        f = complexLinearLift A X Y hA hX hY b hb :=
  @complexLinearLift_unique

example : ∀ (A : Type 1) {X : Type 0} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      Tensor A X Y →ₗ[ℂ] Tensor A X' Y' :=
  @complexLinearMap

example : ∀ (A : Type 1) {X : Type 0} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      (complexLinearMap A hA hY hY' f g).toAddMonoidHom =
        NonUnitalModuleTensor.map A f g :=
  @complexLinearMap_toAddMonoidHom

example : ∀ (A : Type 1) {X : Type 0} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y') (x : X) (y : Y),
      complexLinearMap A hA hY hY' f g (tmul A X Y x y) = tmul A X' Y' (f x) (g y) :=
  @complexLinearMap_tmul

example : ∀ (A : Type 1) {X : Type 0} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      letI := complexModule A X Y hA hY
      complexLinearMap A hA hY hY (NonUnitalModuleHom.id Aᵐᵒᵖ X) (NonUnitalModuleHom.id A Y) =
        LinearMap.id :=
  @complexLinearMap_id

example : ∀ (A : Type 1) {X : Type 0} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    {X'' : Type 1} {Y'' : Type 0} [AddCommGroup X''] [AddCommGroup Y'']
    [NonUnitalModule Aᵐᵒᵖ X''] [NonUnitalModule A Y'']
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y) (hY' : IsNondegenerate A Y')
    (hY'' : IsNondegenerate A Y'')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y')
    (f' : NonUnitalModuleHom Aᵐᵒᵖ X' X'') (g' : NonUnitalModuleHom A Y' Y''),
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      letI := complexModule A X'' Y'' hA hY''
      (complexLinearMap A hA hY' hY'' f' g').comp (complexLinearMap A hA hY hY' f g) =
        complexLinearMap A hA hY hY'' (f'.comp f) (g'.comp g) :=
  @complexLinearMap_comp

example : ∀ (A : Type 1) {X : Type 0} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [AddCommGroup Y] [NonUnitalModule Aᵐᵒᵖ X]
    [NonUnitalModule A Y]
    {X' : Type 1} {Y' : Type 0} [AddCommGroup X'] [AddCommGroup Y']
    [NonUnitalModule Aᵐᵒᵖ X'] [NonUnitalModule A Y']
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y)
    (hX' : IsNondegenerate Aᵐᵒᵖ X') (hY' : IsNondegenerate A Y')
    (f : NonUnitalModuleHom Aᵐᵒᵖ X X') (g : NonUnitalModuleHom A Y Y'),
      letI := complexRightModule hA hX
      letI := complexLeftModule hA hY
      letI := complexRightModule hA hX'
      letI := complexLeftModule hA hY'
      letI := complexModule A X Y hA hY
      letI := complexModule A X' Y' hA hY'
      (complexLinearMap A hA hY hY' f g).comp (complexProjection A X Y hA hX hY) =
        (complexProjection A X' Y' hA hX' hY').comp
          (TensorProduct.map (NondegenerateScalars.complexToLinearMap hA.op hX hX' f)
            (NondegenerateScalars.complexToLinearMap hA hY hY' g)) :=
  @complexLinearMap_comp_complexProjection

example : ∀ {A : Type 1} {X : Type 0}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X),
      complexRightModule hA hX = NondegenerateScalars.complexModule hA.op hX :=
  @complexRightModule_eq

example : ∀ {A : Type 1} {Y : Type 1}
    [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hY : IsNondegenerate A Y),
      complexLeftModule hA hY = NondegenerateScalars.complexModule hA hY :=
  @complexLeftModule_eq

end ComplexUniversesOneZero

end

end Langlands.Algebra.NondegenerateTensorScalars
