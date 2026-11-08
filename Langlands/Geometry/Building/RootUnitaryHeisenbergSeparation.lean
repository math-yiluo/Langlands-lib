import Langlands.Algebra.NormEquivariantBilinear
import Langlands.Geometry.Building.RootUnitaryHeisenbergAdditivity
import Langlands.GroupScheme.Rational.RootHeisenbergCocycleLie

/-! # Heisenberg field data with trace compatibility from separating character values

The published structure `HeisenbergUnitaryData` asks for the cocycle of a Heisenberg normal
form, written in field coordinates, to be additive in its second argument and trace compatible.
This module derives both properties from other data. Additivity holds automatically. Trace
compatibility follows when the cocycle is `k`-bilinear in the coordinates and products of two
embeddings of the extension field separate the pairs `{π, π ∘ σ}` on the values of the
character on `Z(k)`. The centralizer action makes the cocycle norm equivariant at these values,
and `Langlands.Algebra.NormEquivariantBilinear.add_eq_trace_mul` turns this into trace
compatibility.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U U₂ : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {jZ : Z ⟶ G} {a : characterLattice S}
  {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
  {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

section Additivity

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] {C : DoubleRootCommutatorPairing i a hj hj₂}

/-- The cocycle of a Heisenberg normal form is multiplicative in its first argument. -/
theorem HeisenbergNormalForm.cocycle_lift_mul_left (M : HeisenbergNormalForm C)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) {T : Over (Spec (CommRingCat.of k))}
    (x x' y : T ⟶ C.V.X) :
    lift (x * x') y ≫ M.cocycle = (lift x y ≫ M.cocycle) * (lift x' y ≫ M.cocycle) := by
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  obtain ⟨m, e', he'⟩ := weightVectorCoordinatesOfNoHigherRoots hS i h2a
    (hasNoHigherRoots_two_nsmul hhigh) hj₂
  have hb := (M.isBilinearVectorPairing_cocycle hS ha he he' T x x' y y 1).1
  apply (e' T).injective
  rw [map_mul]
  exact hb

/-- In any additive coordinates of `V(k)` and `U_{2a}(k)`, the cocycle is additive in its
first argument. -/
theorem HeisenbergNormalForm.form_add_left_of_cocycle_eq (M : HeisenbergNormalForm C)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)
    {E : Type*} [AddCommGroup E] {H : AddSubgroup E}
    (first : Multiplicative E ≃* rationalPoints C.V) (second : Multiplicative H ≃* rationalPoints U₂)
    (form : E → E → E)
    (cocycle_eq : ∀ x y : E,
      (Multiplicative.toAdd
        (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
          M.cocycle))).1 = form x y)
    (x x' y : E) : form (x + x') y = form x y + form x' y := by
  rw [← cocycle_eq, ← cocycle_eq, ← cocycle_eq, ofAdd_add, map_mul,
    HeisenbergNormalForm.cocycle_lift_mul_left M hS ha hhigh, map_mul, toAdd_mul]
  rfl

end Additivity

section Homogeneity

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom] [IsAffineHom U₂.X.hom]
  {C : DoubleRootCommutatorPairing i a hj hj₂} [IsAffineHom C.V.X.hom]
  (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)

include hS ha hhigh in
/-- **Homogeneity in the first argument.** Let `first` and `second` be coordinates of `V(k)` and
`U_{2a}(k)` by a `k`-module `E` and a subgroup `H` stable under `k`. Assume their images in the
weight spaces of `a` and `2 • a` depend `k`-linearly on the coordinates. Then the cocycle in
these coordinates is `k`-homogeneous in its first argument. -/
theorem HeisenbergNormalForm.form_smul_left_of_lie (M : HeisenbergNormalForm C)
    {E : Type*} [AddCommGroup E] [Module k E] {H : AddSubgroup E}
    (first : Multiplicative E ≃* rationalPoints C.V) (second : Multiplicative H ≃* rationalPoints U₂)
    (form : E → E → E)
    (cocycle_eq : ∀ x y : E,
      (Multiplicative.toAdd
        (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
          M.cocycle))).1 = form x y)
    (hH : ∀ (c : k) (w : H), c • (w : E) ∈ H)
    (hfirst : ∀ (c : k) (x : E),
      (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul (first (Multiplicative.ofAdd (c • x)))) :
          Additive (lieKernel G k)) =
        c • (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul (first (Multiplicative.ofAdd x))) :
          Additive (lieKernel G k)))
    (hsecond : ∀ (c : k) (w w' : H), (w' : E) = c • (w : E) →
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (second (Multiplicative.ofAdd w'))) :
          Additive (lieKernel G k)) =
        c • (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (second (Multiplicative.ofAdd w))) :
          Additive (lieKernel G k)))
    (c : k) (x y : E) : form (c • x) y = c • form x y := by
  set w := Multiplicative.toAdd (second.symm
    (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫ M.cocycle)) with hw
  have hW : lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫ M.cocycle =
      second (Multiplicative.ofAdd w) := by
    rw [hw, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective (fun u : rationalPoints U₂ =>
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul u) : Additive (lieKernel G k))) :=
    Subtype.val_injective.comp
      ((doubleRootPointLieEquiv hS ha hhigh hj₂).injective.comp Additive.ofMul.injective)
  have key : lift (first (Multiplicative.ofAdd (c • x))) (first (Multiplicative.ofAdd y)) ≫
      M.cocycle = second (Multiplicative.ofAdd ⟨c • (w : E), hH c w⟩) := by
    apply hinj
    change (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul _) : Additive (lieKernel G k)) =
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul _) : Additive (lieKernel G k))
    rw [hsecond c w ⟨c • (w : E), hH c w⟩ rfl, ← hW]
    exact DoubleRootCommutatorPairing.doubleRootPointLieEquiv_cocycle_smul_left hS ha hhigh M c
      _ _ _ (hfirst c x)
  rw [← cocycle_eq, ← cocycle_eq, key, MulEquiv.symm_apply_apply, toAdd_ofAdd]

include hS ha hhigh in
/-- **Homogeneity in the second argument.** The same as `form_smul_left_of_lie`, for the second
argument. -/
theorem HeisenbergNormalForm.form_smul_right_of_lie (M : HeisenbergNormalForm C)
    {E : Type*} [AddCommGroup E] [Module k E] {H : AddSubgroup E}
    (first : Multiplicative E ≃* rationalPoints C.V) (second : Multiplicative H ≃* rationalPoints U₂)
    (form : E → E → E)
    (cocycle_eq : ∀ x y : E,
      (Multiplicative.toAdd
        (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
          M.cocycle))).1 = form x y)
    (hH : ∀ (c : k) (w : H), c • (w : E) ∈ H)
    (hfirst : ∀ (c : k) (x : E),
      (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul (first (Multiplicative.ofAdd (c • x)))) :
          Additive (lieKernel G k)) =
        c • (C.rootQuotientPointLieEquiv hS ha hhigh (Additive.ofMul (first (Multiplicative.ofAdd x))) :
          Additive (lieKernel G k)))
    (hsecond : ∀ (c : k) (w w' : H), (w' : E) = c • (w : E) →
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (second (Multiplicative.ofAdd w'))) :
          Additive (lieKernel G k)) =
        c • (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul (second (Multiplicative.ofAdd w))) :
          Additive (lieKernel G k)))
    (c : k) (x y : E) : form x (c • y) = c • form x y := by
  set w := Multiplicative.toAdd (second.symm
    (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫ M.cocycle)) with hw
  have hW : lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫ M.cocycle =
      second (Multiplicative.ofAdd w) := by
    rw [hw, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective (fun u : rationalPoints U₂ =>
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul u) : Additive (lieKernel G k))) :=
    Subtype.val_injective.comp
      ((doubleRootPointLieEquiv hS ha hhigh hj₂).injective.comp Additive.ofMul.injective)
  have key : lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd (c • y))) ≫
      M.cocycle = second (Multiplicative.ofAdd ⟨c • (w : E), hH c w⟩) := by
    apply hinj
    change (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul _) : Additive (lieKernel G k)) =
      (doubleRootPointLieEquiv hS ha hhigh hj₂ (Additive.ofMul _) : Additive (lieKernel G k))
    rw [hsecond c w ⟨c • (w : E), hH c w⟩ rfl, ← hW]
    exact DoubleRootCommutatorPairing.doubleRootPointLieEquiv_cocycle_smul_right hS ha hhigh M c
      _ _ _ (hfirst c y)
  rw [← cocycle_eq, ← cocycle_eq, key, MulEquiv.symm_apply_apply, toAdd_ofAdd]

end Homogeneity

/-- **Field data with separating character values.** The data of `HeisenbergUnitaryData`
without its fields `form_add` and `form_trace`. Instead, the cocycle in coordinates is
`k`-linear in each argument, and there is a field `splitting` receiving as many `k`-embeddings
of the extension as its degree, such that products of two embeddings separate the pairs
`{π, π ∘ σ}` on the values of the character on `Z(k)`. Here `σ` is the conjugation of the
extension over `base`. -/
structure HeisenbergUnitarySeparationData (C : DoubleRootCommutatorPairing i a hj hj₂)
    {hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ Z.X) (t : T ⟶ S.X),
      (AutomorphicAction.conjugation jZ).act z (t ≫ i.hom.hom) = t ≫ i.hom.hom}
    (N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation jZ) hfix)
    (s : S.toGrp ⟶ Z) where
  /-- The field over which the quadratic unitary group is defined. -/
  base : Type u
  /-- The separable quadratic extension of `base` carrying the coordinates. -/
  extension : Type u
  [baseField : Field base]
  [field : Field extension]
  [baseAlgebra : Algebra k base]
  [quadraticAlgebra : Algebra base extension]
  [algebra : Algebra k extension]
  [scalarTower : IsScalarTower k base extension]
  [quadratic : Algebra.IsQuadraticExtension base extension]
  [quadraticSeparable : Algebra.IsSeparable base extension]
  [finite : FiniteDimensional k extension]
  [separable : Algebra.IsSeparable k extension]
  /-- Coordinates of the rational points of the quotient. -/
  first : Multiplicative extension ≃* rationalPoints C.V
  /-- Coordinates of the rational points of the doubled root group. -/
  second : Multiplicative (SU3Root.Parameters.traceZero (SU3Root.fieldInvolution base extension)) ≃*
    rationalPoints U₂
  /-- The cocycle in these coordinates. -/
  form : extension → extension → extension
  cocycle_eq : ∀ x y : extension,
    (Multiplicative.toAdd
      (second.symm (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫
        N.cocycle))).1 = form x y
  form_smul_left : ∀ (c : k) (x y : extension), form (c • x) y = c • form x y
  form_smul_right : ∀ (c : k) (x y : extension), form x (c • y) = c • form x y
  form_nonsymm : ∃ x y : extension, form x y ≠ form y x
  /-- The character of `Z_extension` through which the centralizer scales the coordinates. -/
  character : rationalCharacters (GaloisPointComparison.baseChanged k extension Z)
  restriction :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k extension)).map s)
        character =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k extension)
        ((rationalCharacters.equivCharacterLattice S).symm a)
  first_act : ∀ (z : rationalPoints Z) (x : extension),
    (C.torusQuotientAction (AutomorphicAction.conjugation jZ) hfix).act z
        (first (Multiplicative.ofAdd x)) =
      first (Multiplicative.ofAdd ((rationalCharacterEval character
        (GaloisPointComparison.rationalExtend k extension Z z) : extension) * x))
  second_act : ∀ (z : rationalPoints Z)
    (w w' : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution base extension)),
    (w' : extension) = (rationalCharacterEval character
        (GaloisPointComparison.rationalExtend k extension Z z) : extension) *
      SU3Root.conjugation base extension (rationalCharacterEval character
        (GaloisPointComparison.rationalExtend k extension Z z) : extension) * w →
    (rootActionOfFixesTorus (AutomorphicAction.conjugation jZ) i hfix (2 • a) j₂ hj₂).act z
        (second (Multiplicative.ofAdd w)) =
      second (Multiplicative.ofAdd w')
  /-- A field receiving the `k`-embeddings of the extension. -/
  splitting : Type u
  [splittingField : Field splitting]
  [splittingAlgebra : Algebra k splitting]
  /-- There are as many `k`-embeddings of the extension into `splitting` as its degree. -/
  card_embeddings : Nat.card (extension →ₐ[k] splitting) = Module.finrank k extension
  /-- Products of two embeddings separate the pairs `{π, π ∘ σ}` on the character values. -/
  separation : ∀ π τ ρ : extension →ₐ[k] splitting,
    (∀ c ∈ Set.range (fun z : rationalPoints Z =>
        (rationalCharacterEval character (GaloisPointComparison.rationalExtend k extension Z z) :
          extension)),
      τ c * ρ c =
        π c * π ((SU3Root.conjugation base extension).toAlgHom.restrictScalars k c)) →
      (τ = π ∧ ρ = π.comp ((SU3Root.conjugation base extension).toAlgHom.restrictScalars k)) ∨
        (τ = π.comp ((SU3Root.conjugation base extension).toAlgHom.restrictScalars k) ∧ ρ = π)

attribute [instance] HeisenbergUnitarySeparationData.baseField
  HeisenbergUnitarySeparationData.field HeisenbergUnitarySeparationData.baseAlgebra
  HeisenbergUnitarySeparationData.quadraticAlgebra HeisenbergUnitarySeparationData.algebra
  HeisenbergUnitarySeparationData.scalarTower HeisenbergUnitarySeparationData.quadratic
  HeisenbergUnitarySeparationData.quadraticSeparable HeisenbergUnitarySeparationData.finite
  HeisenbergUnitarySeparationData.separable HeisenbergUnitarySeparationData.splittingField
  HeisenbergUnitarySeparationData.splittingAlgebra

namespace HeisenbergUnitarySeparationData

variable {C : DoubleRootCommutatorPairing i a hj hj₂}
  {hfix : ∀ (T : Over (Spec (CommRingCat.of k))) (z : T ⟶ Z.X) (t : T ⟶ S.X),
    (AutomorphicAction.conjugation jZ).act z (t ≫ i.hom.hom) = t ≫ i.hom.hom}
  {N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation jZ) hfix}
  {s : S.toGrp ⟶ Z} (R : HeisenbergUnitarySeparationData C N s)

/-- The value of the character at a rational point of `Z`. -/
def value (z : rationalPoints Z) : R.extension :=
  (rationalCharacterEval R.character (GaloisPointComparison.rationalExtend k R.extension Z z) :
    R.extension)

/-- The norm of a character value scales trace-zero elements within the trace-zero elements. -/
theorem norm_mul_mem_traceZero (z : rationalPoints Z)
    (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension)) :
    R.value z * SU3Root.conjugation R.base R.extension (R.value z) * (w : R.extension) ∈
      SU3Root.Parameters.traceZero (SU3Root.fieldInvolution R.base R.extension) := by
  have h : (w : R.extension) + SU3Root.conjugation R.base R.extension (w : R.extension) = 0 :=
    w.property
  change _ + SU3Root.conjugation R.base R.extension _ = 0
  rw [map_mul, map_mul, SU3Root.conjugation_involutive]
  linear_combination (R.value z * SU3Root.conjugation R.base R.extension (R.value z)) * h

/-- **Norm equivariance.** At a character value, the cocycle in coordinates scales by the
norm. -/
theorem form_norm (z : rationalPoints Z) (x y : R.extension) :
    R.form (R.value z * x) (R.value z * y) =
      R.value z * SU3Root.conjugation R.base R.extension (R.value z) * R.form x y := by
  set w := Multiplicative.toAdd (R.second.symm
    (lift (R.first (Multiplicative.ofAdd x)) (R.first (Multiplicative.ofAdd y)) ≫ N.cocycle))
    with hw
  have hact := R.second_act z w ⟨_, R.norm_mul_mem_traceZero z w⟩ rfl
  have hW : lift (R.first (Multiplicative.ofAdd x)) (R.first (Multiplicative.ofAdd y)) ≫
      N.cocycle = R.second (Multiplicative.ofAdd w) := by
    rw [hw, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rw [← R.cocycle_eq, ← R.cocycle_eq, value, ← R.first_act, ← R.first_act,
    N.cocycle_act_torus, hW, hact, MulEquiv.symm_apply_apply, toAdd_ofAdd,
    MulEquiv.symm_apply_apply, toAdd_ofAdd]
  rfl

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i)

include hS ha hhigh in
theorem form_add_left (x x' y : R.extension) : R.form (x + x') y = R.form x y + R.form x' y :=
  HeisenbergNormalForm.form_add_left_of_cocycle_eq N.toHeisenbergNormalForm hS ha hhigh
    R.first R.second R.form R.cocycle_eq x x' y

include hS ha hhigh in
theorem form_add_right (x y y' : R.extension) : R.form x (y + y') = R.form x y + R.form x y' :=
  HeisenbergNormalForm.form_add_of_cocycle_eq N.toHeisenbergNormalForm hS ha hhigh
    R.first R.second R.form R.cocycle_eq x y y'

/-- The cocycle in coordinates as a `k`-bilinear map. -/
def bilinear : R.extension →ₗ[k] R.extension →ₗ[k] R.extension :=
  LinearMap.mk₂ k R.form (R.form_add_left hS ha hhigh) R.form_smul_left
    (R.form_add_right hS ha hhigh) R.form_smul_right

include hS ha hhigh in
/-- **Trace compatibility.** -/
theorem form_trace (f x y : R.extension) :
    R.form (f * x) y + R.form x (f * y) =
      (f + SU3Root.conjugation R.base R.extension f) * R.form x y := by
  have h := Langlands.Algebra.NormEquivariantBilinear.add_eq_trace_mul R.card_embeddings
    ((SU3Root.conjugation R.base R.extension).toAlgHom.restrictScalars k) _
    (R.bilinear hS ha hhigh) (by
      rintro e ⟨z, rfl⟩ x y
      exact R.form_norm z x y) R.separation f x y
  exact h

/-- **The field data of `HeisenbergUnitaryData`.** -/
def toHeisenbergUnitaryData : HeisenbergUnitaryData C N s where
  base := R.base
  extension := R.extension
  first := R.first
  second := R.second
  form := R.form
  cocycle_eq := R.cocycle_eq
  form_add := R.form_add_right hS ha hhigh
  form_trace := R.form_trace hS ha hhigh
  form_nonsymm := R.form_nonsymm
  character := R.character
  restriction := R.restriction
  first_act := R.first_act
  second_act := R.second_act

end HeisenbergUnitarySeparationData

end Langlands.Geometry.Building
