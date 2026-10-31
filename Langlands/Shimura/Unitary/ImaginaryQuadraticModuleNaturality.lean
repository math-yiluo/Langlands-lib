import Langlands.Shimura.Unitary.ImaginaryQuadraticModule

/-! # Semilinear naturality of the actual imaginary quadratic module decomposition -/

noncomputable section

open NumberField Algebra
open scoped TensorProduct

set_option autoImplicit false

universe u v w w' w'' z z' z''

namespace Langlands.Shimura.ImaginaryQuadratic

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  (R : Type w) [CommRing R] [Algebra K R] [Algebra ℚ R]
  [IsScalarTower ℚ K R]
  (R' : Type w') [CommRing R'] [Algebra K R'] [Algebra ℚ R']
  [IsScalarTower ℚ K R']
  (M : Type z) [AddCommGroup M] [Module R M] [Module ℚ M]
  [IsScalarTower ℚ R M]
  (M' : Type z') [AddCommGroup M'] [Module R' M'] [Module ℚ M']
  [IsScalarTower ℚ R' M']
  (ρ : L →+* Module.End R M) (ρ' : L →+* Module.End R' M')
  (f : R →ₐ[K] R') (F : M →ₛₗ[f.toRingHom] M')
  (hF : ∀ (t : L) (m : M), F (ρ t m) = ρ' t (F m))

omit [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ R] [IsScalarTower ℚ K R]
  [Algebra ℚ R'] [IsScalarTower ℚ K R'] in
/-- Coefficient-algebra maps preserve the selected natural or conjugate character. -/
theorem factorCharacter_naturality (conjugate : Bool) (t : L) :
    f (factorCharacter L K R conjugate t) = factorCharacter L K R' conjugate t := by
  cases conjugate <;> simp [factorCharacter, f.commutes]

omit [IsCMField L] [IsQuadraticExtension ℚ L] [Algebra L K] in
include hF in
/-- An actual semilinear field-action intertwiner also intertwines the induced tensor action. -/
theorem tensorAction_naturality (a : R ⊗[ℚ] L) (m : M) :
    F (tensorAction L R M ρ a m) =
      tensorAction L R' M' ρ' (coefficientMap L K R R' f a) (F m) := by
  induction a using TensorProduct.inductionOn with
  | tmul r t =>
    simp only [tensorAction_tmul, LinearMap.smul_apply, coefficientMap_tmul,
      F.map_smulₛₗ, hF t m]
    rfl
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]

include hF in
/-- Semilinear intertwiners commute with the constructed actual projectors. -/
theorem moduleProjector_naturality (conjugate : Bool) (m : M) :
    F (moduleProjector L K R M ρ conjugate m) =
      moduleProjector L K R' M' ρ' conjugate (F m) := by
  unfold moduleProjector
  rw [tensorAction_naturality L K R R' M M' ρ ρ' f F hF,
    coefficientMap_factorIdempotent]

omit [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ R] [IsScalarTower ℚ K R]
  [Algebra ℚ R'] [IsScalarTower ℚ K R'] [Module ℚ M] [IsScalarTower ℚ R M]
  [Module ℚ M'] [IsScalarTower ℚ R' M'] in
include hF in
/-- The complete simultaneous scalar eigencondition is preserved by a semilinear intertwiner. -/
theorem map_mem_eigenmodule (conjugate : Bool) {m : M}
    (hm : m ∈ eigenmodule L K R M ρ conjugate) :
    F m ∈ eigenmodule L K R' M' ρ' conjugate := by
  intro t
  rw [← hF t m, hm t, F.map_smulₛₗ]
  change f (factorCharacter L K R conjugate t) • F m = _
  rw [factorCharacter_naturality L K R R' f]

/-- The actual semilinear map induced on a simultaneous scalar eigensubmodule. -/
def eigenmoduleMap (conjugate : Bool) :
    eigenmodule L K R M ρ conjugate →ₛₗ[f.toRingHom]
      eigenmodule L K R' M' ρ' conjugate where
  toFun m := ⟨F m.val, map_mem_eigenmodule L K R R' M M' ρ ρ' f F hF conjugate m.property⟩
  map_add' x y := Subtype.ext (F.map_add x.val y.val)
  map_smul' r m := Subtype.ext (F.map_smulₛₗ r m.val)

omit [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ R] [IsScalarTower ℚ K R]
  [Algebra ℚ R'] [IsScalarTower ℚ K R'] [Module ℚ M] [IsScalarTower ℚ R M]
  [Module ℚ M'] [IsScalarTower ℚ R' M'] in
@[simp]
theorem eigenmoduleMap_val (conjugate : Bool) (m : eigenmodule L K R M ρ conjugate) :
    (eigenmoduleMap L K R R' M M' ρ ρ' f F hF conjugate m).val = F m.val := rfl

/-- The constructed module decomposition commutes with every semilinear intertwiner. -/
theorem eigenmoduleEquiv_naturality (m : M) :
    eigenmoduleEquiv L K R' M' ρ' (F m) =
      (eigenmoduleMap L K R R' M M' ρ ρ' f F hF false
          (eigenmoduleEquiv L K R M ρ m).1,
        eigenmoduleMap L K R R' M M' ρ ρ' f F hF true
          (eigenmoduleEquiv L K R M ρ m).2) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    exact (moduleProjector_naturality L K R R' M M' ρ ρ' f F hF _ m).symm

omit [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ R] [IsScalarTower ℚ K R]
  [Module ℚ M] [IsScalarTower ℚ R M] in
@[simp]
theorem eigenmoduleMap_id (conjugate : Bool) :
    eigenmoduleMap L K R R M M ρ ρ (AlgHom.id K R) LinearMap.id
        (fun _ _ => rfl) conjugate = LinearMap.id := by
  ext m
  rfl

variable (R'' : Type w'') [CommRing R''] [Algebra K R''] [Algebra ℚ R'']
  [IsScalarTower ℚ K R'']
  (M'' : Type z'') [AddCommGroup M''] [Module R'' M''] [Module ℚ M'']
  [IsScalarTower ℚ R'' M'']
  (ρ'' : L →+* Module.End R'' M'')
  (g : R' →ₐ[K] R'') (G : M' →ₛₗ[g.toRingHom] M'')
  (hG : ∀ (t : L) (m : M'), G (ρ' t m) = ρ'' t (G m))

omit [IsQuadraticExtension ℚ L] [CharZero K] [Algebra ℚ R] [IsScalarTower ℚ K R]
  [Algebra ℚ R'] [IsScalarTower ℚ K R'] [Algebra ℚ R''] [IsScalarTower ℚ K R'']
  [Module ℚ M] [IsScalarTower ℚ R M]
  [Module ℚ M'] [IsScalarTower ℚ R' M'] [Module ℚ M''] [IsScalarTower ℚ R'' M''] in
/-- Restricting a composite semilinear intertwiner is the composite of its restrictions. -/
theorem eigenmoduleMap_comp (conjugate : Bool) :
    (eigenmoduleMap L K R' R'' M' M'' ρ' ρ'' g G hG conjugate).comp
        (eigenmoduleMap L K R R' M M' ρ ρ' f F hF conjugate) =
      eigenmoduleMap L K R R'' M M'' ρ ρ'' (g.comp f) (G.comp F)
        (fun t m => by
          change G (F (ρ t m)) = ρ'' t (G (F m))
          rw [hF, hG]) conjugate := by
  ext m
  rfl

end Langlands.Shimura.ImaginaryQuadratic
