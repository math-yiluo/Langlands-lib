import Langlands.AbelianScheme.PrimeToP
import Langlands.AbelianScheme.LieRationalDeterminant

/-! # The relative Lie functor on `ℤ_(p)`-localized homomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped TensorProduct
open Langlands.Scheme.Modules

universe u v w

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}} (p : ℕ) [Fact p.Prime]

/-- If every natural number prime to `p` is invertible in the global regular functions of `S`,
then `ℤ_(p)` maps uniquely into them. -/
def primeLocalGlobalScalars (h : ∀ n : ℕ, n.Coprime p → IsUnit (n : Γ(S, ⊤))) :
    PrimeLocalIntegers p →+* Γ(S, ⊤) :=
  PrimeLocalIntegers.lift h

/-- Conversely, a ring homomorphism from `ℤ_(p)` makes every natural number prime to `p`
invertible on `S`. -/
theorem isUnit_natCast_of_primeLocal (a : PrimeLocalIntegers p →+* Γ(S, ⊤)) {n : ℕ}
    (hn : n.Coprime p) : IsUnit (n : Γ(S, ⊤)) := by
  simpa using (PrimeLocalIntegers.isUnit_natCast p hn).map a

variable (a : PrimeLocalIntegers p →+* Γ(S, ⊤))

/-- The Lie functor extended to the localized category, using the scalars `a`. -/
def primeToPLieFunctor : PrimeToPCategory p S ⥤ S.Modules := by
  letI := linearOfGlobalScalars a
  exact CoefficientExtension.lift (PrimeLocalIntegers p) (lieFunctor S)

instance primeToPLieFunctor_additive : (primeToPLieFunctor p a).Additive := by
  let := linearOfGlobalScalars a
  exact inferInstanceAs
    (CoefficientExtension.lift (PrimeLocalIntegers p) (lieFunctor S)).Additive

/-- The differential of a `ℤ_(p)`-localized homomorphism of abelian schemes. -/
def lieMapP {A B : AbelianScheme S} (f : HomP p A B) : A.Lie ⟶ B.Lie :=
  (primeToPLieFunctor p a).map
    (X := CoefficientExtension.of A) (Y := CoefficientExtension.of B) f

/-- On a pure tensor, the differential is the global scalar times the actual differential. -/
@[simp]
theorem lieMapP_tmul {A B : AbelianScheme S} (r : PrimeLocalIntegers p) (f : A ⟶ B) :
    lieMapP p a (r ⊗ₜ[ℤ] f) = a r • lieMap f := rfl

@[simp]
theorem lieMapP_homToHomP {A B : AbelianScheme S} (f : A ⟶ B) :
    lieMapP p a (homToHomP p f) = lieMap f := by
  rw [homToHomP_apply, lieMapP_tmul, map_one, one_smul]

@[simp]
theorem lieMapP_idP (A : AbelianScheme S) : lieMapP p a (idP p A) = 𝟙 A.Lie :=
  (primeToPLieFunctor p a).map_id (CoefficientExtension.of A)

@[simp]
theorem lieMapP_compP {A B C : AbelianScheme S} (f : HomP p A B) (g : HomP p B C) :
    lieMapP p a (compP p A B C f g) = lieMapP p a f ≫ lieMapP p a g :=
  (primeToPLieFunctor p a).map_comp
    (X := CoefficientExtension.of A) (Y := CoefficientExtension.of B)
    (Z := CoefficientExtension.of C) f g

@[simp]
theorem lieMapP_add {A B : AbelianScheme S} (f g : HomP p A B) :
    lieMapP p a (f + g) = lieMapP p a f + lieMapP p a g :=
  (primeToPLieFunctor p a).map_add

/-- The differential is semilinear along `a` for the localized scalars. -/
theorem lieMapP_smul {A B : AbelianScheme S} (r : PrimeLocalIntegers p) (f : HomP p A B) :
    lieMapP p a (r • f) = a r • lieMapP p a f := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => rw [smul_add, lieMapP_add, lieMapP_add, hf, hg, smul_add]
  | tmul s f =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, lieMapP_tmul, lieMapP_tmul, map_mul, mul_smul]

/-- Compose an action on localized endomorphisms with the differential. -/
def liePOrderAction (A : AbelianScheme S) {O : Type v} [Ring O] (α : O →+* EndP p A) :
    O →+* CategoryTheory.End A.Lie where
  toFun b := CategoryTheory.End.of (lieMapP p a (α b).asHom)
  map_zero' := by
    rw [map_zero]
    exact congrArg CategoryTheory.End.of ((primeToPLieFunctor p a).map_zero _ _)
  map_one' := by rw [map_one]; exact congrArg CategoryTheory.End.of (lieMapP_idP p a A)
  map_add' b c := by
    rw [map_add]; exact congrArg CategoryTheory.End.of (lieMapP_add p a _ _)
  map_mul' b c := by
    rw [map_mul]; exact congrArg CategoryTheory.End.of (lieMapP_compP p a _ _)

@[simp]
theorem liePOrderAction_apply (A : AbelianScheme S) {O : Type v} [Ring O]
    (α : O →+* EndP p A) (b : O) :
    liePOrderAction p a A α b = CategoryTheory.End.of (lieMapP p a (α b).asHom) := rfl

/-- For an action through actual endomorphisms, this is the published integral Lie action. -/
theorem liePOrderAction_integral (A : AbelianScheme S) {O : Type v} [Ring O]
    (α : O →+* CategoryTheory.End A) :
    liePOrderAction p a A ((endToEndP p A).comp α) = (lieEndAction A).comp α := by
  ext b : 1
  apply CategoryTheory.End.ext
  exact lieMapP_homToHomP p a (α b).asHom

/-- Over a base whose global scalars are a rational algebra, the localized differential is the
published rational differential of the image in the rational category. Any two ring maps out of
`ℤ_(p)` agree, so no compatibility of `a` with the rational structure is assumed. -/
theorem lieMapP_eq_lieMap0 {R : CommRingCat.{u}} [Algebra ℚ R] (q : S ⟶ Spec R)
    {A B : AbelianScheme S} (f : HomP p A B) :
    lieMapP p a f = lieMap0 q (homPToHom0 p A B f) := by
  have ha : a = ((scalarsFromBase q).comp (algebraMap ℚ R)).comp
      (PrimeLocalIntegers.toRat p) := PrimeLocalIntegers.ringHom_ext _ _
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => rw [lieMapP_add, hf, hg, map_add, lieMap0_add]
  | tmul r f =>
    rw [lieMapP_tmul, homPToHom0_tmul]
    let := rationalLinearOverBase q
    rw [lieMap0_tmul, ha]
    rfl

/-- Consequently the localized Lie action is the rational Lie action of the image action. -/
theorem liePOrderAction_eq_rational {R : CommRingCat.{u}} [Algebra ℚ R] (q : S ⟶ Spec R)
    (A : AbelianScheme S) {O : Type v} [Ring O] (α : O →+* EndP p A) :
    liePOrderAction p a A α = lieRationalOrderAction q A ((endPToEnd0 p A).comp α) := by
  ext b : 1
  apply CategoryTheory.End.ext
  exact lieMapP_eq_lieMap0 p a q (α b).asHom

/-! ## Local section determinants -/

variable {O : Type v} [Ring O] {ι : Type w} [Fintype ι]

/-- Restrict the localized Lie action to a genuine open. -/
def liePLocalOrderAction (A : AbelianScheme S) (α : O →+* EndP p A) (U : S.Opens) :
    O →+* CategoryTheory.End (A.Lie.over U) where
  toFun b := CategoryTheory.End.of ((liePOrderAction p a A α b).asHom.over U)
  map_zero' := by rw [map_zero]; rfl
  map_one' := by rw [map_one]; rfl
  map_add' b c := by rw [map_add]; rfl
  map_mul' b c := by rw [map_mul]; rfl

/-- The localized action on the actual sections of the Lie module over `V`. -/
def liePSectionOrderAction (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} (V : Over U) :
    O →+* Module.End Γ(S, V.left) Γ(A.Lie, V.left) :=
  (localSectionEndomorphism A.Lie V).comp (liePLocalOrderAction p a A α U)

@[simp]
theorem liePSectionOrderAction_apply (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} (V : Over U) (b : O) (x : Γ(A.Lie, V.left)) :
    liePSectionOrderAction p a A α V b x = (lieMapP p a (α b).asHom).app V.left x :=
  rfl

/-- Kottwitz's determinant polynomial `det(X₁b₁ + ⋯ + X_tb_t ; Lie A)` of a finite family in
the acting ring, computed on a finite free chart of the Lie module. -/
def liePSectionDeterminant (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (b : ι → O) (V : Over U) : MvPolynomial ι Γ(S, V.left) :=
  localSectionDeterminant e (fun i => liePLocalOrderAction p a A α U (b i)) V

/-- Any finite basis of the same section module computes the same polynomial. -/
theorem liePSectionDeterminant_eq_basis (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (b : ι → O) (V : Over U) {J : Type u} [Fintype J] [DecidableEq J]
    (c : Module.Basis J Γ(S, V.left) Γ(A.Lie, V.left)) :
    liePSectionDeterminant p a A α e b V =
      Langlands.Shimura.HodgeDeterminant.polynomial c
        (fun i => liePSectionOrderAction p a A α V (b i)) :=
  localSectionDeterminant_eq_basis e _ V c

/-- The polynomial restricts along the structure-sheaf restriction maps. -/
theorem liePSectionDeterminant_restrict (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (b : ι → O) {V W : Over U} (j : V ⟶ W) :
    MvPolynomial.map (S.presheaf.map j.left.op).hom (liePSectionDeterminant p a A α e b W) =
      liePSectionDeterminant p a A α e b V :=
  localSectionDeterminant_restrict e _ j

/-- Evaluation is the determinant of the corresponding linear combination on sections. -/
theorem eval_liePSectionDeterminant (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (b : ι → O) (V : Over U) (x : ι → Γ(S, V.left)) :
    eval x (liePSectionDeterminant p a A α e b V) =
      LinearMap.det (∑ i, x i • liePSectionOrderAction p a A α V (b i)) :=
  eval_localSectionDeterminant e _ V x

/-- For an action through actual endomorphisms, the polynomial is the published one. -/
theorem liePSectionDeterminant_integral (A : AbelianScheme S)
    (α : O →+* CategoryTheory.End A) {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (b : ι → O) (V : Over U) :
    liePSectionDeterminant p a A ((endToEndP p A).comp α) e b V =
      lieSectionDeterminant A α e b V := by
  unfold liePSectionDeterminant lieSectionDeterminant
  congr 2
  ext i : 1
  apply CategoryTheory.End.ext
  change ((liePOrderAction p a A ((endToEndP p A).comp α) (b i)).asHom.over U) =
    ((lieOrderAction A α (b i)).asHom.over U)
  rw [liePOrderAction_integral]
  rfl

/-- Over a rational algebra base, the polynomial is the published rational one. -/
theorem liePSectionDeterminant_eq_rational {R : CommRingCat.{u}} [Algebra ℚ R]
    (q : S ⟶ Spec R) (A : AbelianScheme S) (α : O →+* EndP p A)
    {U : S.Opens} {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ A.Lie.over U)
    (b : ι → O) (V : Over U) :
    liePSectionDeterminant p a A α e b V =
      lieRationalSectionDeterminant q A ((endPToEnd0 p A).comp α) e b V := by
  unfold liePSectionDeterminant lieRationalSectionDeterminant
  congr 2
  ext i : 1
  apply CategoryTheory.End.ext
  change ((liePOrderAction p a A α (b i)).asHom.over U) =
    ((lieRationalOrderAction q A ((endPToEnd0 p A).comp α) (b i)).asHom.over U)
  rw [liePOrderAction_eq_rational p a q]

end Langlands.AbelianScheme
