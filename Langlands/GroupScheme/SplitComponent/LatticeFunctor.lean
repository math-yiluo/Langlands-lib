import Langlands.GroupScheme.CorepresentedLinearEmbedding
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # Lattice tori as corepresented group functors

For a commutative ring `R` and an abelian group `Λ`, the functor `A ↦ Hom(Λ, Aˣ)` on commutative
`R`-algebras is corepresented by the group algebra `R[Λ]`. For corepresented group functors,
natural homomorphisms are classified by algebra maps between the representing algebras.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.SplitComponent

open Corepresented.LinearEmbedding

/-! ### Natural homomorphisms of corepresented group functors -/

section Classify

variable {R : CommRingCat.{u}} {F F' F'' : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B B' B'' : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')
  (c : (F'' ⋙ forget GrpCat).CorepresentableBy B'')

/-- The algebra map classifying a natural homomorphism: the image of the universal point. -/
def classify (α : F ⟶ F') : B' ⟶ B := Corepresented.classify e d α

/-- A natural homomorphism is determined by its classifying map. -/
theorem app_eq (α : F ⟶ F') {S : CommAlgCat.{u} R} (x : F.obj S) :
    α.app S x = pt d (classify e d α ≫ cls e x) := by
  simpa only [pt, cls, classify, Equiv.apply_symm_apply] using
    Corepresented.app_homEquiv e d α (e.homEquiv.symm x)

/-- The classifying map classifies the image of the universal point. -/
theorem pt_classify (α : F ⟶ F') : pt d (classify e d α) = α.app B (pt e (𝟙 B)) :=
  pt_cls d _

/-- Natural homomorphisms with the same classifying map are equal. -/
theorem nat_ext {α β : F ⟶ F'} (h : classify e d α = classify e d β) : α = β := by
  ext S x
  rw [app_eq e d α, app_eq e d β, h]

/-- Classifying maps compose contravariantly. -/
theorem classify_comp (α : F ⟶ F') (β : F' ⟶ F'') :
    classify e c (α ≫ β) = classify d c β ≫ classify e d α := by
  change cls c (β.app B (α.app B (pt e (𝟙 B)))) = _
  rw [app_eq d c β, cls_pt, classify]
  rfl

/-- The multiplicativity of a natural homomorphism, on its classifying map. -/
theorem classify_comul (α : F ⟶ F') :
    classify e d α ≫ comul e =
      comul d ≫ pair (classify e d α ≫ inl B) (classify e d α ≫ inr B) :=
  Corepresented.classify_comul e d α

/-- A natural homomorphism from an algebra map compatible with the comultiplications. -/
def ofClassify (ψ : B' ⟶ B)
    (hψ : ψ ≫ comul e = comul d ≫ pair (ψ ≫ inl B) (ψ ≫ inr B)) : F ⟶ F' where
  app S := GrpCat.ofHom (MonoidHom.mk' (fun x => pt d (ψ ≫ cls e x)) fun x y => by
    change pt d (ψ ≫ cls e (x * y)) = pt d (ψ ≫ cls e x) * pt d (ψ ≫ cls e y)
    rw [cls_mul, ← Category.assoc, hψ, pt_mul, Category.assoc]
    congr 2
    ext z <;> simp [pair, inl, inr])
  naturality S T g := by
    ext x
    change pt d (ψ ≫ cls e (F.map g x)) = F'.map g (pt d (ψ ≫ cls e x))
    rw [cls_map, ← pt_comp, Category.assoc]

/-- The natural homomorphism built from `ψ` is classified by `ψ`. -/
theorem classify_ofClassify (ψ : B' ⟶ B)
    (hψ : ψ ≫ comul e = comul d ≫ pair (ψ ≫ inl B) (ψ ≫ inr B)) :
    classify e d (ofClassify e d ψ hψ) = ψ := by
  change cls d (pt d (ψ ≫ cls e (pt e (𝟙 B)))) = ψ
  rw [cls_pt, cls_pt, Category.comp_id]

/-- The antipode: the algebra map classifying the inverse of the universal point. -/
def antipode : B ⟶ B := Corepresented.antipode e

/-- Inverses are classified through the antipode. -/
theorem cls_inv {S : CommAlgCat.{u} R} (x : F.obj S) : cls e x⁻¹ = antipode e ≫ cls e x :=
  Corepresented.homEquiv_symm_inv e x

/-- A natural homomorphism commutes with the antipodes. -/
theorem classify_antipode (α : F ⟶ F') :
    classify e d α ≫ antipode e = antipode d ≫ classify e d α :=
  Corepresented.classify_antipode e d α

end Classify

/-! ### Lattice tori -/

section Lattice

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-- The group algebra `R[Λ]`, as a commutative `R`-algebra. -/
abbrev latticeAlgebra : CommAlgCat.{u} R := Diagonalizable.algebra R Λ

/-- The functor `A ↦ Hom(Λ, Aˣ)` of characters of `Λ` with values in units. -/
def latticeFunctor : CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  Diagonalizable.functor R Λ

/-- The universal character `m ↦ [m]` of `Λ` in the units of `R[Λ]`. -/
def univChar : Multiplicative Λ →* (AddMonoidAlgebra R Λ)ˣ :=
  Diagonalizable.monomialUnits R Λ

/-- The universal character sends `m` to `[m]`. -/
theorem univChar_val (m : Λ) :
    (univChar R Λ (Multiplicative.ofAdd m) : AddMonoidAlgebra R Λ) =
      AddMonoidAlgebra.single m 1 := rfl

variable {R Λ} in
/-- A point of the lattice functor, viewed as a character. -/
abbrev asChar {A : CommAlgCat.{u} R} (χ : (latticeFunctor R Λ ⋙ forget GrpCat).obj A) :
    Multiplicative Λ →* Aˣ := χ

variable {R Λ} in
/-- Algebra maps out of `R[Λ]` agree when they agree on the basis `[m]`. -/
theorem latticeAlgHom_ext {A : Type u} [CommRing A] [Algebra R A]
    {φ₁ φ₂ : AddMonoidAlgebra R Λ →ₐ[R] A}
    (h : ∀ m, φ₁ (AddMonoidAlgebra.single m 1) = φ₂ (AddMonoidAlgebra.single m 1)) :
    φ₁ = φ₂ :=
  (AddMonoidAlgebra.lift R A Λ).symm.injective (MonoidHom.ext fun m => h m.toAdd)

variable {R Λ} in
/-- Morphisms out of `R[Λ]` in `CommAlgCat` agree when they agree on the basis `[m]`. -/
theorem latticeHom_ext {A : CommAlgCat.{u} R} {f g : latticeAlgebra R Λ ⟶ A}
    (h : ∀ m, f.hom (AddMonoidAlgebra.single m 1) = g.hom (AddMonoidAlgebra.single m 1)) :
    f = g :=
  CommAlgCat.hom_ext (latticeAlgHom_ext h)

/-- `R[Λ]` corepresents the characters of `Λ`. -/
def latticeCorep :
    (latticeFunctor R Λ ⋙ forget GrpCat).CorepresentableBy (latticeAlgebra R Λ) :=
  Diagonalizable.grpCorepresentation R Λ

variable {R Λ}

/-- The character classified by `f : R[Λ] → A` sends `m` to `f [m]`. -/
theorem pt_latticeCorep_val {A : CommAlgCat.{u} R} (f : latticeAlgebra R Λ ⟶ A) (m : Λ) :
    (asChar (pt (latticeCorep R Λ) f) (Multiplicative.ofAdd m) : A) =
      f.hom (AddMonoidAlgebra.single m 1) := rfl

/-- The algebra map classifying a character `χ` sends `[m]` to `χ m`. -/
theorem cls_latticeCorep_single {A : CommAlgCat.{u} R}
    (χ : (latticeFunctor R Λ ⋙ forget GrpCat).obj A) (m : Λ) :
    (cls (latticeCorep R Λ) χ).hom (AddMonoidAlgebra.single m 1) =
      (asChar χ (Multiplicative.ofAdd m) : A) := by
  change AddMonoidAlgebra.lift R A Λ ((Units.coeHom A).comp χ) (AddMonoidAlgebra.single m 1) = _
  simp
  rfl

/-- The comultiplication of `R[Λ]` is `[m] ↦ [m] ⊗ [m]`. -/
theorem comul_latticeCorep_single (m : Λ) :
    (comul (latticeCorep R Λ)).hom (AddMonoidAlgebra.single m (1 : R)) =
      AddMonoidAlgebra.single m 1 ⊗ₜ[R] AddMonoidAlgebra.single m 1 := by
  rw [comul, cls_latticeCorep_single]
  change (asChar (pt (latticeCorep R Λ) (inl _)) (Multiplicative.ofAdd m)).val *
    (asChar (pt (latticeCorep R Λ) (inr _)) (Multiplicative.ofAdd m)).val = _
  rw [pt_latticeCorep_val, pt_latticeCorep_val]
  simp [inl, inr]

/-- The antipode of `R[Λ]` is `[m] ↦ [-m]`. -/
theorem antipode_latticeCorep_single (m : Λ) :
    (antipode (latticeCorep R Λ)).hom (AddMonoidAlgebra.single m (1 : R)) =
      AddMonoidAlgebra.single (-m) 1 :=
  Diagonalizable.antipode_single R Λ m 1

/-- Restriction of characters along a homomorphism of lattices. -/
def latticeMap {Λ' : Type u} [AddCommGroup Λ'] (l : Λ →+ Λ') :
    latticeFunctor R Λ' ⟶ latticeFunctor R Λ :=
  Diagonalizable.restrict R l

/-- Restriction along `l` is classified by `[m] ↦ [l m]`. -/
theorem classify_latticeMap_single {Λ' : Type u} [AddCommGroup Λ'] (l : Λ →+ Λ') (m : Λ) :
    (classify (latticeCorep R Λ') (latticeCorep R Λ) (latticeMap l)).hom
      (AddMonoidAlgebra.single m 1) = (AddMonoidAlgebra.single (l m) 1 : AddMonoidAlgebra R Λ') := by
  change (cls (latticeCorep R Λ)
    ((latticeMap l).app _ (pt (latticeCorep R Λ') (𝟙 _)))).hom
      (AddMonoidAlgebra.single m 1) = _
  rw [cls_latticeCorep_single]
  rfl

end Lattice

end Langlands.GroupScheme.SplitComponent
