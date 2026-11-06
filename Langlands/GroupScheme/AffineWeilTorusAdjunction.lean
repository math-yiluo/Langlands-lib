import Langlands.GroupScheme.AffineWeilRestriction
import Langlands.GroupScheme.SplitComponent.SchemeBridge
import Mathlib.RingTheory.Unramified.Finite

/-! # Character functors and the Weil restriction point functor

For an algebra `A → B`, a group scheme `G` over `B` and an abelian group `Λ`, natural
homomorphisms from the character functor `latticeFunctor A Λ` into the restricted point functor
`AffineWeil.pointFunctor A B G` and natural homomorphisms from `latticeFunctor B Λ` into the
affine-point functor of `G` are exchanged by restriction of scalars and the multiplication map,
and by the right tensor inclusion. For general `Λ` the character functor is the diagonalizable
group of `Λ`; it is a split torus when `Λ` is finite free.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineWeil

open SplitComponent

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Restriction of scalars from `B`-algebras to `A`-algebras. -/
@[reducible] def restrictScalars :
    CommAlgCat.{u} (CommRingCat.of B) ⥤ CommAlgCat.{u} (CommRingCat.of A) where
  obj C :=
    letI : Algebra A C := Algebra.compHom C (algebraMap A B)
    CommAlgCat.of (CommRingCat.of A) C
  map {C D} g :=
    letI : Algebra A C := Algebra.compHom C (algebraMap A B)
    letI : Algebra A D := Algebra.compHom D (algebraMap A B)
    CommAlgCat.ofHom
      { g.hom.toRingHom with commutes' := fun a => g.hom.commutes (algebraMap A B a) }

section Multiplication

variable {B} in
/-- The multiplication `B ⊗[A] C → C` of a `B`-algebra `C`, an algebra map over `B`. -/
def multiplication (C : CommAlgCat.{u} (CommRingCat.of B)) :
    (tensorFunctor A B).obj ((restrictScalars A B).obj C) ⟶ C :=
  letI : Algebra A C := Algebra.compHom C (algebraMap A B)
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (Algebra.ofId B C) (AlgHom.id A C)
    fun _ _ => Commute.all _ _)

variable {B} in
@[simp] theorem multiplication_tmul (C : CommAlgCat.{u} (CommRingCat.of B)) (b : B) (c : C) :
    (multiplication A C).hom (b ⊗ₜ[A] c) = algebraMap B C b * c := by
  simp [multiplication]
  rfl

variable {B} in
/-- The multiplication maps are natural in the `B`-algebra. -/
theorem multiplication_naturality {C D : CommAlgCat.{u} (CommRingCat.of B)} (g : C ⟶ D) :
    (tensorFunctor A B).map ((restrictScalars A B).map g) ≫ multiplication A D =
      multiplication A C ≫ g := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply]
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    change (multiplication A D).hom (b ⊗ₜ[A] g.hom c) =
      g.hom ((multiplication A C).hom (b ⊗ₜ c))
    rw [multiplication_tmul, multiplication_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]

variable {B} in
theorem multiplication_tensorMap_tmul {C' : CommAlgCat.{u} (CommRingCat.of A)}
    {C : CommAlgCat.{u} (CommRingCat.of B)} (g : C' ⟶ (restrictScalars A B).obj C) (b : B)
    (c : C') :
    (multiplication A C).hom (((tensorFunctor A B).map g).hom (b ⊗ₜ[A] c)) =
      algebraMap B C b * g.hom c := by
  change (multiplication A C).hom (b ⊗ₜ[A] g.hom c) = _
  rw [multiplication_tmul]

end Multiplication

section SeparableLift

variable (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The multiplication `B ⊗[A] C → C`, over `B`. -/
abbrev tensorMul : B ⊗[A] C →ₐ[B] C :=
  Algebra.TensorProduct.lift (Algebra.ofId B C) (AlgHom.id A C) fun _ _ => Commute.all _ _

variable [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]

/-- Multiplying by the separability element only sees the product of a tensor. -/
theorem mul_elem_eq (u : B ⊗[A] B) :
    u * Algebra.FormallyUnramified.elem A B =
      (Algebra.TensorProduct.lmul' A u ⊗ₜ[A] (1 : B)) * Algebra.FormallyUnramified.elem A B := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    have h : x ⊗ₜ[A] y = (x ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, mul_assoc, Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) (S := B), ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← h,
      Algebra.TensorProduct.lmul'_apply_tmul]
  | add x y hx hy => rw [add_mul, hx, hy, ← add_mul, map_add, TensorProduct.add_tmul]

/-- The separability element is idempotent. -/
theorem elem_mul_elem :
    Algebra.FormallyUnramified.elem A B * Algebra.FormallyUnramified.elem A B =
      Algebra.FormallyUnramified.elem A B := by
  rw [mul_elem_eq, Algebra.FormallyUnramified.lmul_elem (R := A) (S := B),
    ← Algebra.TensorProduct.one_def,
    one_mul]

/-- The separability idempotent of `B ⊗[A] C`. -/
def sepIdempotent : B ⊗[A] C :=
  Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom A B C)
    (Algebra.FormallyUnramified.elem A B)

theorem sepIdempotent_mul_self :
    sepIdempotent A B C * sepIdempotent A B C = sepIdempotent A B C := by
  rw [sepIdempotent, ← map_mul, elem_mul_elem]

omit [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] in
theorem tensorMul_map (x : B ⊗[A] B) :
    tensorMul A B C (Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom A B C) x) =
      algebraMap B C (Algebra.TensorProduct.lmul' A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorMul_sepIdempotent : tensorMul A B C (sepIdempotent A B C) = 1 := by
  rw [sepIdempotent, tensorMul_map, Algebra.FormallyUnramified.lmul_elem (R := A) (S := B),
    map_one]

theorem one_tmul_mul_sepIdempotent (b : B) :
    ((1 : B) ⊗ₜ[A] algebraMap B C b) * sepIdempotent A B C =
      (b ⊗ₜ[A] (1 : C)) * sepIdempotent A B C := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom A B C))
    (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) b)
  rw [map_mul, map_mul] at h
  simpa [sepIdempotent] using h

/-- Over a formally unramified essentially finite type algebra, every algebra map into `C`
lifts through the multiplication map. -/
theorem exists_tensorMul_comp_eq {O : Type u} [CommRing O] [Algebra B O]
    (f : O →ₐ[B] C) (z : O →ₐ[B] B ⊗[A] C) :
    ∃ f' : O →ₐ[B] B ⊗[A] C, (tensorMul A B C).comp f' = f := by
  set e := sepIdempotent A B C with he_def
  have he : e * e = e := sepIdempotent_mul_self A B C
  have hcomm (b : B) : e * ((1 : B) ⊗ₜ[A] algebraMap B C b) = (b ⊗ₜ[A] (1 : C)) * e := by
    rw [mul_comm]
    exact one_tmul_mul_sepIdempotent A B C b
  refine ⟨
    { toFun := fun o => e * ((1 : B) ⊗ₜ[A] f o) + (1 - e) * z o
      map_one' := by
        simp only [map_one, ← Algebra.TensorProduct.one_def]
        ring
      map_mul' := fun o o' => by
        simp only [map_mul]
        rw [← one_mul (1 : B), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        linear_combination
          (-(((1 : B) ⊗ₜ[A] f o) * ((1 : B) ⊗ₜ[A] f o') - ((1 : B) ⊗ₜ[A] f o) * z o' -
            z o * ((1 : B) ⊗ₜ[A] f o') + z o * z o')) * he
      map_zero' := by simp
      map_add' := fun o o' => by
        simp only [map_add, TensorProduct.tmul_add]
        ring
      commutes' := fun b => by
        simp only [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply]
        rw [hcomm]
        ring }, ?_⟩
  ext o
  simp only [AlgHom.coe_comp, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, map_add, map_mul, map_sub, map_one, Algebra.TensorProduct.lift_tmul,
    AlgHom.id_apply, he_def, tensorMul_sepIdempotent]
  simp

end SeparableLift

section Points

open Langlands.AlgebraicGeometry.PointTopology

variable {B} (G : GroupScheme (Spec (CommRingCat.of B)))

/-- Over a formally unramified essentially finite type algebra, every point of an affine group
scheme lifts through the multiplication map `B ⊗[A] C → C`. -/
theorem exists_affinePointMap_multiplication_eq [IsAffine G.X.left]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (C : CommAlgCat.{u} (CommRingCat.of B)) (y : G.affinePoints C) :
    ∃ y' : G.affinePoints ((tensorFunctor A B).obj ((restrictScalars A B).obj C)),
      G.affinePointMap (multiplication A C) y' = y := by
  let _ : Algebra A C := Algebra.compHom C (algebraMap A B)
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let f := (affineSchemePointEquiv B G.X C y).toAlgHom
  let z := (affineSchemePointEquiv B G.X (B ⊗[A] C)
    (1 : G.affinePoints ((tensorFunctor A B).obj ((restrictScalars A B).obj C)))).toAlgHom
  obtain ⟨f', hf'⟩ := exists_tensorMul_comp_eq A B C f z
  refine ⟨(affineSchemePointEquiv B G.X (B ⊗[A] C)).symm (AlgPoint.ofAlgHom f'), ?_⟩
  apply (affineSchemePointEquiv B G.X C).injective
  change affineSchemePointEquiv B G.X C (ringTestMap B (tensorMul A B C) ≫
    (affineSchemePointEquiv B G.X (B ⊗[A] C)).symm (AlgPoint.ofAlgHom f')) = _
  have h := coordinatePoint_changeRing B G.X (tensorMul A B C)
    ((affineSchemePointEquiv B G.X (B ⊗[A] C)).symm (AlgPoint.ofAlgHom f'))
  rw [Equiv.apply_symm_apply] at h
  change AlgPoint.toAlgHom _ = (tensorMul A B C).comp f' at h
  rw [hf'] at h
  exact h

end Points

section Transformations

variable {B} (G : GroupScheme (Spec (CommRingCat.of B))) {Λ : Type u} [AddCommGroup Λ]

variable (B Λ) in
/-- Characters valued in a `B`-algebra are characters valued in its restriction to `A`. -/
def latticeRestrict : latticeFunctor (CommRingCat.of B) Λ ⟶
    restrictScalars A B ⋙ latticeFunctor (CommRingCat.of A) Λ where
  app _ := GrpCat.ofHom (MonoidHom.id _)
  naturality _ _ _ := rfl

/-- The multiplication map `B ⊗[A] C → C` on points of `G`. -/
def multiplicationTrans : restrictScalars A B ⋙ pointFunctor A B G ⟶ G.affinePointFunctor where
  app C := GrpCat.ofHom (G.affinePointMap (multiplication A C))
  naturality C D g := by
    apply GrpCat.hom_ext
    change (G.affinePointMap (multiplication A D)).comp
        (G.affinePointMap ((tensorFunctor A B).map ((restrictScalars A B).map g))) =
      (G.affinePointMap g).comp (G.affinePointMap (multiplication A C))
    rw [← GroupScheme.affinePointMap_comp, ← GroupScheme.affinePointMap_comp,
      multiplication_naturality]

/-- A natural homomorphism from the character functor over `A` into the restricted point
functor gives one from the character functor over `B` into the points of `G`: evaluate on the
restricted algebra, then apply the multiplication map `B ⊗[A] C → C`. -/
def counitTrans (α : latticeFunctor (CommRingCat.of A) Λ ⟶ pointFunctor A B G) :
    latticeFunctor (CommRingCat.of B) Λ ⟶ G.affinePointFunctor :=
  latticeRestrict A B Λ ≫ Functor.whiskerLeft (restrictScalars A B) α ≫ multiplicationTrans A G

theorem counitTrans_app (α : latticeFunctor (CommRingCat.of A) Λ ⟶ pointFunctor A B G)
    (C : CommAlgCat.{u} (CommRingCat.of B)) (χ : (latticeFunctor (CommRingCat.of B) Λ).obj C) :
    (counitTrans A G α).app C χ = G.affinePointMap (multiplication A C)
      (α.app ((restrictScalars A B).obj C) ((latticeRestrict A B Λ).app C χ)) := rfl

/-- Changing the `B`-algebra after the multiplication map is changing it before. -/
theorem affinePointMap_multiplication_app
    (α : latticeFunctor (CommRingCat.of A) Λ ⟶ pointFunctor A B G)
    {C D : CommAlgCat.{u} (CommRingCat.of B)} (g : C ⟶ D)
    (χ : (latticeFunctor (CommRingCat.of A) Λ).obj ((restrictScalars A B).obj C)) :
    G.affinePointMap g (G.affinePointMap (multiplication A C) (α.app _ χ)) =
      G.affinePointMap (multiplication A D)
        (α.app _ ((latticeFunctor (CommRingCat.of A) Λ).map ((restrictScalars A B).map g) χ)) := by
  have key : (G.affinePointMap g).comp (G.affinePointMap (multiplication A C)) =
      (G.affinePointMap (multiplication A D)).comp
        (G.affinePointMap ((tensorFunctor A B).map ((restrictScalars A B).map g))) := by
    rw [← GroupScheme.affinePointMap_comp, ← GroupScheme.affinePointMap_comp,
      multiplication_naturality]
  have h := ConcreteCategory.congr_hom (α.naturality ((restrictScalars A B).map g)) χ
  calc G.affinePointMap g (G.affinePointMap (multiplication A C) (α.app _ χ))
      = ((G.affinePointMap g).comp (G.affinePointMap (multiplication A C))) (α.app _ χ) := rfl
    _ = ((G.affinePointMap (multiplication A D)).comp
          (G.affinePointMap ((tensorFunctor A B).map ((restrictScalars A B).map g))))
          (α.app _ χ) := by rw [key]
    _ = _ := congrArg (G.affinePointMap (multiplication A D)) h.symm

/-- An algebra map into a restricted algebra, followed by multiplication, acts through the
lattice characters. -/
theorem affinePointMap_tensorMap_multiplication
    (α : latticeFunctor (CommRingCat.of A) Λ ⟶ pointFunctor A B G)
    {C' : CommAlgCat.{u} (CommRingCat.of A)} {C : CommAlgCat.{u} (CommRingCat.of B)}
    (h : C' ⟶ (restrictScalars A B).obj C) (χ : (latticeFunctor (CommRingCat.of A) Λ).obj C') :
    G.affinePointMap ((tensorFunctor A B).map h ≫ multiplication A C) (α.app C' χ) =
      G.affinePointMap (multiplication A C)
        (α.app _ ((latticeFunctor (CommRingCat.of A) Λ).map h χ)) := by
  have hn := ConcreteCategory.congr_hom (α.naturality h) χ
  calc G.affinePointMap ((tensorFunctor A B).map h ≫ multiplication A C) (α.app C' χ)
      = G.affinePointMap (multiplication A C)
          (G.affinePointMap ((tensorFunctor A B).map h) (α.app C' χ)) := by
        rw [GroupScheme.affinePointMap_comp]
        rfl
    _ = _ := congrArg (G.affinePointMap (multiplication A C)) hn.symm

/-- Centrality passes from the restricted point functor to `G` over a formally unramified
essentially finite type algebra. -/
theorem isCentralNat_counitTrans [IsAffine G.X.left]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    {α : latticeFunctor (CommRingCat.of A) Λ ⟶ pointFunctor A B G} (hα : IsCentralNat α) :
    IsCentralNat (counitTrans A G α) := by
  intro C χ y
  obtain ⟨y', rfl⟩ := exists_affinePointMap_multiplication_eq A G C y
  exact (hα _ ((latticeRestrict A B Λ).app C χ) y').map (G.affinePointMap (multiplication A C))

variable (B) in
/-- Characters valued in `C` become characters valued in `B ⊗[A] C`. -/
def latticeUnit : latticeFunctor (CommRingCat.of A) Λ ⟶
    tensorFunctor A B ⋙ latticeFunctor (CommRingCat.of B) Λ where
  app C := GrpCat.ofHom (MonoidHom.compHom
    (Units.map (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toMonoidHom))
  naturality C D g := by
    ext χ
    refine MonoidHom.ext fun m => Units.ext ?_
    change (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (g.hom ((asChar χ m : Cˣ) : C)) : B ⊗[A] D) =
      Algebra.TensorProduct.lTensor B g.hom
        ((Algebra.TensorProduct.includeRight ((asChar χ m : Cˣ) : C)))
    simp [Algebra.TensorProduct.includeRight_apply]

/-- A natural homomorphism from the character functor over `B` into the points of `G` gives one
from the character functor over `A` into the restricted point functor, through the right tensor
inclusion. -/
def unitTrans (I : latticeFunctor (CommRingCat.of B) Λ ⟶ G.affinePointFunctor) :
    latticeFunctor (CommRingCat.of A) Λ ⟶ pointFunctor A B G :=
  latticeUnit A B ≫ Functor.whiskerLeft (tensorFunctor A B) I

theorem unitTrans_app (I : latticeFunctor (CommRingCat.of B) Λ ⟶ G.affinePointFunctor)
    (C : CommAlgCat.{u} (CommRingCat.of A)) (χ : (latticeFunctor (CommRingCat.of A) Λ).obj C) :
    (unitTrans A G I).app C χ = I.app ((tensorFunctor A B).obj C)
      ((latticeUnit A B).app C χ) := rfl

/-- Centrality passes from `G` to the restricted point functor. -/
theorem isCentralNat_unitTrans {I : latticeFunctor (CommRingCat.of B) Λ ⟶ G.affinePointFunctor}
    (hI : IsCentralNat I) : IsCentralNat (unitTrans A G I) :=
  fun _ _ y => hI _ _ y

end Transformations

end Langlands.GroupScheme.AffineWeil
