import Langlands.GroupScheme.SplitComponent.LatticeFunctor
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.OrzechProperty

/-! # Images of homomorphisms from lattice tori

Let `α : Hom(Λ, -ˣ) ⟶ F'` be a natural homomorphism into a group functor corepresented by `B'`,
classified by `ψ : B' → R[Λ]`. Comparing the comultiplications shows that the range of `ψ`
contains `c • [m]` for every coefficient `c` of every element of the range at `m`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.SplitComponent

open Corepresented.LinearEmbedding

section Coefficients

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

/-- The coefficient of `[m]`, as a linear functional on `R[Λ]`. -/
def coeffAt (m : Λ) : AddMonoidAlgebra R Λ →ₗ[R] R :=
  Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

omit [AddCommGroup Λ] in
@[simp] theorem coeffAt_apply (m : Λ) (x : AddMonoidAlgebra R Λ) : coeffAt m x = x.coeff m := rfl

/-- The slice `x ⊗ y ↦ coeff_m(y) • x`. -/
def sliceAt (m : Λ) : AddMonoidAlgebra R Λ ⊗[R] AddMonoidAlgebra R Λ →ₗ[R] AddMonoidAlgebra R Λ :=
  (TensorProduct.rid R _).toLinearMap ∘ₗ (coeffAt m).lTensor _

theorem sliceAt_tmul (m : Λ) (x y : AddMonoidAlgebra R Λ) :
    sliceAt m (x ⊗ₜ[R] y) = y.coeff m • x := by
  simp [sliceAt]

theorem sliceAt_comul (m : Λ) (x : AddMonoidAlgebra R Λ) :
    sliceAt m ((comul (latticeCorep R Λ)).hom x) = x.coeff m • AddMonoidAlgebra.single m 1 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, add_smul]
  | single n c =>
    have hs : (AddMonoidAlgebra.single n c : AddMonoidAlgebra R Λ) =
        c • AddMonoidAlgebra.single n 1 := by
      rw [AddMonoidAlgebra.smul_single', mul_one]
    rw [hs, map_smul, map_smul, comul_latticeCorep_single, sliceAt_tmul,
      AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_single, smul_assoc]
    by_cases h : n = m
    · subst h
      simp
    · simp [h]

variable {F' : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B' : CommAlgCat.{u} R}
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

/-- For a homomorphism from a lattice torus with classifying map `ψ`, the coefficient of `[m]`
in `ψ h`, times `[m]`, is again in the range of `ψ`. -/
theorem coeff_smul_single_eq (α : latticeFunctor R Λ ⟶ F') (h : B') (m : Λ) :
    ((classify (latticeCorep R Λ) d α).hom h).coeff m • AddMonoidAlgebra.single m (1 : R) =
      (classify (latticeCorep R Λ) d α).hom (TensorProduct.rid R B'
        ((coeffAt m ∘ₗ (classify (latticeCorep R Λ) d α).hom.toLinearMap).lTensor B'
          ((comul d).hom h))) := by
  set ψ := classify (latticeCorep R Λ) d α
  rw [← sliceAt_comul]
  have hc := congrArg (fun q : B' ⟶ sq (latticeAlgebra R Λ) => q.hom h)
    (classify_comul (latticeCorep R Λ) d α)
  simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply] at hc
  change sliceAt m ((comul (latticeCorep R Λ)).hom (ψ.hom h)) = _
  rw [hc]
  generalize (comul d).hom h = t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [pair_tmul]
    simp [sliceAt, inl, inr, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add, map_add]

end Coefficients

/-! ### Tensor products of test algebras -/

section Tensor

variable {R : CommRingCat.{u}}

/-- The tensor product of two test algebras. -/
abbrev tens (A A' : CommAlgCat.{u} R) : CommAlgCat.{u} R := CommAlgCat.of R (A ⊗[R] A')

/-- The left inclusion into a tensor product. -/
def jl (A A' : CommAlgCat.{u} R) : A ⟶ tens A A' :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeLeft

/-- The right inclusion into a tensor product. -/
def jr (A A' : CommAlgCat.{u} R) : A' ⟶ tens A A' :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeRight

/-- The algebra map out of a tensor product determined by two algebra maps. -/
def lift2 {A A' S : CommAlgCat.{u} R} (f : A ⟶ S) (g : A' ⟶ S) : tens A A' ⟶ S :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift f.hom g.hom fun _ _ => Commute.all _ _)

@[simp] theorem lift2_tmul {A A' S : CommAlgCat.{u} R} (f : A ⟶ S) (g : A' ⟶ S) (x : A)
    (y : A') : (lift2 f g).hom (x ⊗ₜ[R] y) = f.hom x * g.hom y := by
  simp [lift2]

@[simp] theorem jl_lift2 {A A' S : CommAlgCat.{u} R} (f : A ⟶ S) (g : A' ⟶ S) :
    jl A A' ≫ lift2 f g = f := by
  ext x
  simp [jl, lift2]

@[simp] theorem jr_lift2 {A A' S : CommAlgCat.{u} R} (f : A ⟶ S) (g : A' ⟶ S) :
    jr A A' ≫ lift2 f g = g := by
  ext x
  simp [jr, lift2]

theorem pair_comp {B S T : CommAlgCat.{u} R} (f g : B ⟶ S) (h : S ⟶ T) :
    pair f g ≫ h = pair (f ≫ h) (g ≫ h) := by
  ext x <;> simp [pair]

/-- Cancellation of an algebra map with injective underlying function. -/
theorem cancel_injective {X Y Z : CommAlgCat.{u} R} {f g : X ⟶ Y} {p : Y ⟶ Z}
    (hp : Function.Injective p.hom) (h : f ≫ p = g ≫ p) : f = g := by
  ext x
  exact hp (congrArg (fun q : X ⟶ Z => q.hom x) h)

end Tensor

/-! ### Central natural homomorphisms -/

section Central

variable {R : CommRingCat.{u}} {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B B' : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

/-- A natural homomorphism is central when its values commute with every point of the target. -/
def IsCentralNat (α : F ⟶ F') : Prop :=
  ∀ (S : CommAlgCat.{u} R) (x : F.obj S) (y : F'.obj S), Commute (α.app S x) y

theorem IsCentralNat.comp {F'' : CommAlgCat.{u} R ⥤ GrpCat.{u}} {α : F' ⟶ F''}
    (hα : IsCentralNat α) (β : F ⟶ F') : IsCentralNat (β ≫ α) :=
  fun S x y => hα S (β.app S x) y

/-- The universal commutation identity for an algebra map `ψ : B' → B`: the classified point
over `B ⊗ B'` commutes with the universal point of `F'`. -/
def CentralIdentity (ψ : B' ⟶ B) : Prop :=
  comul d ≫ pair (ψ ≫ jl B B') (jr B B') = comul d ≫ pair (jr B B') (ψ ≫ jl B B')

theorem isCentralNat_iff (α : F ⟶ F') :
    IsCentralNat α ↔ CentralIdentity d (classify e d α) := by
  constructor
  · intro h
    have hc := (h (tens B B') (pt e (jl B B')) (pt d (jr B B'))).eq
    rw [app_eq e d α, cls_pt, pt_mul, ← cls_pt d (jr B B'), pt_cls, pt_mul,
      cls_pt] at hc
    exact d.homEquiv.injective hc
  · intro h S x y
    let q : tens B B' ⟶ S := lift2 (cls e x) (cls d y)
    have h1 : pair (classify e d α ≫ cls e x) (cls d y) =
        pair (classify e d α ≫ jl B B') (jr B B') ≫ q := by
      rw [pair_comp, Category.assoc, jl_lift2, jr_lift2]
    have h2 : pair (cls d y) (classify e d α ≫ cls e x) =
        pair (jr B B') (classify e d α ≫ jl B B') ≫ q := by
      rw [pair_comp, Category.assoc, jl_lift2, jr_lift2]
    change α.app S x * y = y * α.app S x
    rw [app_eq e d α, ← pt_cls d y, pt_mul, pt_mul, h1, h2, ← Category.assoc,
      ← Category.assoc, h]

end Central

end Langlands.GroupScheme.SplitComponent
