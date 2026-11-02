import Langlands.GroupScheme.Reductive.Basic
import Mathlib.RingTheory.Bialgebra.Basic

/-! # The coordinate bialgebra of a corepresented group functor and its matrix embeddings -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.AffineLinearEmbedding

open Algebra.TensorProduct (includeLeft includeRight productMap)

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The point of `F` classified by an algebra map out of the representing algebra. -/
def pt {A : CommAlgCat.{u} R} (f : B →ₐ[R] A) : F.obj A :=
  e.homEquiv (CommAlgCat.ofHom f)

theorem pt_injective {A : CommAlgCat.{u} R} {f g : B →ₐ[R] A} (h : pt e f = pt e g) :
    f = g :=
  congrArg CommAlgCat.Hom.hom (e.homEquiv.injective h)

@[simp] theorem pt_homEquiv_symm {A : CommAlgCat.{u} R} (x : F.obj A) :
    pt e (e.homEquiv.symm x).hom = x := by
  rw [pt, CommAlgCat.ofHom_hom, Equiv.apply_symm_apply]

theorem pt_comp {A A' : CommAlgCat.{u} R} (f : B →ₐ[R] A) (g : A →ₐ[R] A') :
    pt e (g.comp f) = F.map (CommAlgCat.ofHom g) (pt e f) :=
  e.homEquiv_comp (CommAlgCat.ofHom g) (CommAlgCat.ofHom f)

/-- The comultiplication of the representing algebra: the algebra map classifying the product
of the two universal points over `B ⊗ B`. -/
def comul : B →ₐ[R] B ⊗[R] B :=
  (e.homEquiv.symm
    (pt e (A := CommAlgCat.of R (B ⊗[R] B)) includeLeft *
      pt e (A := CommAlgCat.of R (B ⊗[R] B)) includeRight)).hom

/-- The counit of the representing algebra: the algebra map classifying the identity point. -/
def counit : B →ₐ[R] R :=
  (e.homEquiv.symm (1 : F.obj (CommAlgCat.of R R))).hom

theorem pt_comul :
    pt e (comul e) = pt e (A := CommAlgCat.of R (B ⊗[R] B)) includeLeft *
      pt e (A := CommAlgCat.of R (B ⊗[R] B)) includeRight :=
  pt_homEquiv_symm e _

/-- Composing the comultiplication with an algebra map out of `B ⊗ B` multiplies points. -/
theorem pt_comp_comul {A : CommAlgCat.{u} R} (l : B ⊗[R] B →ₐ[R] A) {f g : B →ₐ[R] A}
    (hf : l.comp includeLeft = f) (hg : l.comp includeRight = g) :
    pt e (l.comp (comul e)) = pt e f * pt e g := by
  rw [pt_comp e (A := CommAlgCat.of R (B ⊗[R] B)) (comul e) l, pt_comul, map_mul,
    ← pt_comp e (A := CommAlgCat.of R (B ⊗[R] B)) includeLeft l,
    ← pt_comp e (A := CommAlgCat.of R (B ⊗[R] B)) includeRight l, hf, hg]

/-- Convolution of algebra maps corresponds to multiplication of points. -/
theorem pt_productMap_comp_comul {A : CommAlgCat.{u} R} (f g : B →ₐ[R] A) :
    pt e ((productMap f g).comp (comul e)) = pt e f * pt e g :=
  pt_comp_comul e _ (Algebra.TensorProduct.productMap_left f g)
    (Algebra.TensorProduct.productMap_right f g)

/-- Algebra maps factoring through the counit classify the identity point. -/
theorem pt_comp_counit {A : CommAlgCat.{u} R} (g : R →ₐ[R] A) :
    pt e (g.comp (counit e)) = 1 := by
  rw [pt_comp e (A := CommAlgCat.of R R) (counit e) g, counit, pt_homEquiv_symm, map_one]

theorem homEquiv_symm_mul {A : CommAlgCat.{u} R} (x y : F.obj A) :
    (e.homEquiv.symm (x * y)).hom =
      (productMap (e.homEquiv.symm x).hom (e.homEquiv.symm y).hom).comp (comul e) := by
  apply pt_injective e
  rw [pt_productMap_comp_comul, pt_homEquiv_symm, pt_homEquiv_symm, pt_homEquiv_symm]

theorem homEquiv_symm_one (A : CommAlgCat.{u} R) :
    (e.homEquiv.symm (1 : F.obj A)).hom = (Algebra.ofId R A).comp (counit e) := by
  apply pt_injective e
  rw [pt_homEquiv_symm, pt_comp_counit]

theorem homEquiv_symm_map {A A' : CommAlgCat.{u} R} (g : A ⟶ A') (x : F.obj A) :
    (e.homEquiv.symm (F.map g x)).hom = g.hom.comp (e.homEquiv.symm x).hom := by
  apply pt_injective e
  rw [pt_homEquiv_symm, pt_comp, pt_homEquiv_symm, CommAlgCat.ofHom_hom]

/-- Coassociativity, from associativity of the group law on points. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul e) (AlgHom.id R B)).comp (comul e)) =
      (Algebra.TensorProduct.map (AlgHom.id R B) (comul e)).comp (comul e) := by
  apply pt_injective e (A := CommAlgCat.of R (B ⊗[R] (B ⊗[R] B)))
  rw [← AlgHom.comp_assoc,
    pt_comp_comul e _
      (f := ((Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp includeLeft).comp (comul e))
      (g := includeRight.comp includeRight)
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]),
    pt_comp_comul e _ (f := includeLeft) (g := includeRight.comp includeLeft)
      (AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]) (AlgHom.ext fun b => by simp),
    pt_comp_comul e _ (f := includeLeft) (g := includeRight.comp (comul e))
      (AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]) (AlgHom.ext fun b => by simp),
    pt_comp_comul e (A := CommAlgCat.of R (B ⊗[R] (B ⊗[R] B)))
      (includeRight : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B)) rfl rfl, mul_assoc]

/-- Left counitality, from the left unit law on points. -/
theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit e) (AlgHom.id R B)).comp (comul e) =
      (Algebra.TensorProduct.lid R B).symm := by
  apply pt_injective e (A := CommAlgCat.of R (R ⊗[R] B))
  rw [pt_comp_comul e _ (f := includeLeft.comp (counit e)) (g := includeRight)
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp),
    pt_comp_counit, one_mul]
  exact congrArg (pt e) (AlgHom.ext fun b => by simp)

/-- Right counitality, from the right unit law on points. -/
theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R B) (counit e)).comp (comul e) =
      (Algebra.TensorProduct.rid R R B).symm := by
  apply pt_injective e (A := CommAlgCat.of R (B ⊗[R] R))
  rw [pt_comp_comul e _ (f := includeLeft) (g := includeRight.comp (counit e))
      (AlgHom.ext fun b => by simp) (AlgHom.ext fun b => by simp),
    pt_comp_counit, mul_one]
  exact congrArg (pt e) (AlgHom.ext fun b => by simp)

/-- The bialgebra structure on the representing algebra of a corepresented group functor. -/
abbrev bialgebra : Bialgebra R B :=
  Bialgebra.ofAlgHom (comul e) (counit e) (comul_coassoc e) (comul_rTensor_counit e)
    (comul_lTensor_counit e)

section Matrix

variable {N : ℕ} (M : Matrix (Fin N) (Fin N) B)
  (hcomul : ∀ i j, comul e (M i j) = ∑ l, M i l ⊗ₜ[R] M l j)
  (hcounit : ∀ i j, counit e (M i j) = (1 : Matrix (Fin N) (Fin N) R) i j)

/-- The matrix of a point: the entries of `M` evaluated at the classifying algebra map. -/
def matrixHom (A : CommAlgCat.{u} R) : F.obj A →* Matrix (Fin N) (Fin N) A where
  toFun x := M.map (e.homEquiv.symm x).hom
  map_one' := by
    ext i j
    rw [homEquiv_symm_one, Matrix.map_apply, AlgHom.comp_apply, hcounit, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  map_mul' x y := by
    ext i j
    simp only [homEquiv_symm_mul, Matrix.map_apply, AlgHom.comp_apply, hcomul, map_sum,
      Algebra.TensorProduct.productMap_apply_tmul, Matrix.mul_apply]

include hcomul hcounit in
theorem matrixHom_apply (A : CommAlgCat.{u} R) (x : F.obj A) (i j : Fin N) :
    matrixHom e M hcomul hcounit A x i j = (e.homEquiv.symm x).hom (M i j) := rfl

/-- The natural transformation from `F` to invertible matrices given by `M`. -/
def toGL : F ⟶ GeneralLinear.functor (Fin N) R where
  app A := GrpCat.ofHom (matrixHom e M hcomul hcounit A).toHomUnits
  naturality A A' g := by
    ext x : 2
    apply Units.ext
    ext i j
    change (e.homEquiv.symm (F.map g x)).hom (M i j) = g.hom ((e.homEquiv.symm x).hom (M i j))
    rw [homEquiv_symm_map, AlgHom.comp_apply]

/-- The group-scheme homomorphism into the general linear group given by `M`. -/
def toGLHom : Corepresented.groupScheme F e ⟶ GeneralLinear.groupScheme (Fin N) R :=
  Corepresented.groupSchemeMap e (GeneralLinear.corepresentableBy (Fin N) R)
    (toGL e M hcomul hcounit)

/-- If the entries of `M` generate the representing algebra, the homomorphism is a closed
immersion. -/
theorem isClosedSubgroup_toGLHom
    (hgen : Algebra.adjoin R (Set.range fun p : Fin N × Fin N => M p.1 p.2) = ⊤) :
    IsClosedSubgroup (toGLHom e M hcomul hcounit) := by
  set g : Matrix.GeneralLinearGroup (Fin N) B := (toGL e M hcomul hcounit).app B (e.homEquiv (𝟙 B))
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (GeneralLinear.classify (R := R) g).toRingHom))
  apply IsClosedImmersion.spec_of_surjective
  have hg : ∀ i j, g i j = M i j := fun i j => by
    change (e.homEquiv.symm (e.homEquiv (𝟙 B))).hom (M i j) = M i j
    rw [Equiv.symm_apply_apply]
    rfl
  have hle : Algebra.adjoin R (Set.range fun p : Fin N × Fin N => M p.1 p.2) ≤
      (GeneralLinear.classify (R := R) g).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨_, (GeneralLinear.classify_entry g i j).trans (hg i j)⟩
  intro b
  obtain ⟨c, hc⟩ := hle (hgen ▸ Algebra.mem_top : b ∈ Algebra.adjoin R _)
  exact ⟨c, hc⟩

end Matrix

end Langlands.GroupScheme.AffineLinearEmbedding
