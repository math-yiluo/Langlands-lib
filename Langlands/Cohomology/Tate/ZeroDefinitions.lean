import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.Ring.ULift

/-!
# Degree-zero Tate cohomology and its norm quotient

All cohomology objects in this file are Mathlib's `tateCohomology`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open groupCohomology groupHomology

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The actual group norm, with its codomain restricted to invariant vectors. -/
def normToInvariants (A : Rep R G) : A →ₗ[R] A.ρ.invariants :=
  A.ρ.norm.codRestrict _ (fun a g => A.ρ.self_norm_apply g a)

/-- The actual norm image, considered as a submodule of the invariant vectors. -/
def normImage (A : Rep R G) : Submodule R A.ρ.invariants :=
  (normToInvariants A).range

/-- The explicit invariant-vector quotient used to describe degree-zero Tate cohomology. -/
abbrev InvariantsModNorm (A : Rep R G) :=
  A.ρ.invariants ⧸ normImage A

/-- The part of the Tate complex in degrees `-1, 0, 1`, expressed on coefficients. -/
abbrev zeroShortComplex (A : Rep R G) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk A.norm.toModuleCatHom (d₀₁ A) (Rep.norm_comp_d_eq_zero A)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison with the actual three terms of Mathlib's Tate complex. -/
def zeroShortComplexIso (A : Rep R G) :
    (tateComplex A).sc 0 ≅ zeroShortComplex A := by
  refine (tateComplex A).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫ ?_
  change ShortComplex.mk A.tateNorm ((inhomogeneousCochains A).d 0 1) _ ≅ _
  exact ShortComplex.isoMk (chainsIso₀ A) (cochainsIso₀ A) (cochainsIso₁ A)
    (by simp [Rep.tateNorm]) (comp_d₀₁_eq A)

set_option backward.isDefEq.respectTransparency false in
/-- A proved kernel/cokernel presentation by invariants modulo norms. -/
def zeroHomologyData (A : Rep R G) : (zeroShortComplex A).LeftHomologyData where
  K := ModuleCat.of R A.ρ.invariants
  H := ModuleCat.of R (InvariantsModNorm A)
  i := ModuleCat.ofHom A.ρ.invariants.subtype
  π := ModuleCat.ofHom (normImage A).mkQ
  wi := subtype_comp_d₀₁ A
  hi := (groupCohomology.shortComplexH0_exact A).fIsKernel
  wπ := by
    have h :
        (groupCohomology.shortComplexH0_exact A).fIsKernel.lift
          (KernelFork.ofι _ (zeroShortComplex A).zero) =
          ModuleCat.ofHom (normToInvariants A) := by
      apply (cancel_mono (groupCohomology.shortComplexH0 A).f).1
      exact (groupCohomology.shortComplexH0_exact A).fIsKernel.fac
        (KernelFork.ofι _ (zeroShortComplex A).zero) WalkingParallelPair.zero
    rw [h]
    exact ModuleCat.hom_ext (LinearMap.range_mkQ_comp _)
  hπ := by
    have h :
        (groupCohomology.shortComplexH0_exact A).fIsKernel.lift
          (KernelFork.ofι _ (zeroShortComplex A).zero) =
          ModuleCat.ofHom (normToInvariants A) := by
      apply (cancel_mono (groupCohomology.shortComplexH0 A).f).1
      exact (groupCohomology.shortComplexH0_exact A).fIsKernel.fac
        (KernelFork.ofι _ (zeroShortComplex A).zero) WalkingParallelPair.zero
    exact CokernelCofork.isColimitOfIsColimitOfIff'
      (ModuleCat.cokernelIsColimit (ModuleCat.ofHom (normToInvariants A))) _
      (by intros; simp only [h])

/-- Degree-zero Tate cohomology is the invariant-vector quotient by the actual norm image. -/
def zeroEquiv (A : Rep R G) :
    tateCohomology A 0 ≅ ModuleCat.of R (InvariantsModNorm A) :=
  ShortComplex.homologyMapIso (zeroShortComplexIso A) ≪≫
    (zeroHomologyData A).homologyIso

/-- The class in actual Tate cohomology of an invariant vector. -/
def zeroClass (A : Rep R G) : A.ρ.invariants →ₗ[R] tateCohomology A 0 :=
  (zeroEquiv A).inv.hom.comp (normImage A).mkQ

/-- A coefficient pairing, with the actual bilinear map and its equivariance. -/
structure Pairing (A B C : Rep R G) where
  bilinear : A →ₗ[R] B →ₗ[R] C
  equivariant : ∀ (g : G) (a : A) (b : B),
    bilinear (A.ρ g a) (B.ρ g b) = C.ρ g (bilinear a b)

variable {A B C : Rep R G}

/-- An equivariant coefficient pairing restricts to invariant vectors. -/
def Pairing.onInvariants (φ : Pairing A B C) :
    A.ρ.invariants →ₗ[R] B.ρ.invariants →ₗ[R] C.ρ.invariants where
  toFun a :=
    { toFun b := ⟨φ.bilinear a b, fun g => by
        rw [← φ.equivariant, a.property g, b.property g]⟩
      map_add' b b' := Subtype.ext (by simp)
      map_smul' r b := Subtype.ext (by simp) }
  map_add' a a' := by ext b; simp
  map_smul' r a := by ext b; simp

/-- Moving a norm out of the first argument when the second is invariant. -/
lemma Pairing.norm_left (φ : Pairing A B C) (a : A) (b : B.ρ.invariants) :
    φ.bilinear (A.ρ.norm a) b = C.ρ.norm (φ.bilinear a b) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simpa only [b.property g] using φ.equivariant g a b

/-- Moving a norm out of the second argument when the first is invariant. -/
lemma Pairing.norm_right (φ : Pairing A B C) (a : A.ρ.invariants) (b : B) :
    φ.bilinear a (B.ρ.norm b) = C.ρ.norm (φ.bilinear a b) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simpa only [a.property g] using φ.equivariant g a b

/-- The class of the coefficient pairing on invariant vectors. -/
def Pairing.onInvariantClasses (φ : Pairing A B C) :
    A.ρ.invariants →ₗ[R] B.ρ.invariants →ₗ[R] InvariantsModNorm C where
  toFun a := (normImage C).mkQ.comp (φ.onInvariants a)
  map_add' a a' := by ext b; simp
  map_smul' r a := by ext b; simp

/-- A norm in the first argument has zero class. -/
lemma Pairing.normImage_le_ker_left (φ : Pairing A B C) :
    normImage A ≤ φ.onInvariantClasses.ker := by
  rintro _ ⟨a, rfl⟩
  ext b
  apply (Submodule.Quotient.mk_eq_zero (normImage C)).mpr
  refine ⟨φ.bilinear a b, ?_⟩
  apply Subtype.ext
  exact (φ.norm_left a b).symm

/-- A norm in the second argument has zero class. -/
lemma Pairing.normImage_le_ker_right (φ : Pairing A B C) :
    normImage B ≤ φ.onInvariantClasses.flip.ker := by
  rintro _ ⟨b, rfl⟩
  ext a
  apply (Submodule.Quotient.mk_eq_zero (normImage C)).mpr
  refine ⟨φ.bilinear a b, ?_⟩
  apply Subtype.ext
  exact (φ.norm_right a b).symm

/-- The normalized degree-zero product on the explicit norm quotients. -/
def Pairing.quotientProduct (φ : Pairing A B C) :
    InvariantsModNorm A →ₗ[R] InvariantsModNorm B →ₗ[R] InvariantsModNorm C :=
  LinearMap.liftQ₂ (normImage A) (normImage B) φ.onInvariantClasses
    φ.normImage_le_ker_left φ.normImage_le_ker_right

/-- The normalized degree-zero product on Mathlib's actual Tate cohomology. -/
def cupZero (φ : Pairing A B C) :
    tateCohomology A 0 →ₗ[R] tateCohomology B 0 →ₗ[R] tateCohomology C 0 where
  toFun a := (zeroEquiv C).inv.hom.comp
    ((φ.quotientProduct ((zeroEquiv A).hom a)).comp (zeroEquiv B).hom.hom)
  map_add' a a' := by ext b; simp
  map_smul' r a := by ext b; simp

/-- Integers lifted to the carrier universe of the group and its coefficients. -/
abbrev IntegralScalar : Type u := ULift.{u} ℤ

/-- The specified identification of the lifted scalar ring with the integers. -/
def integralScalarEquiv : IntegralScalar.{u} ≃+* ℤ := ULift.ringEquiv

/-- The actual trivial integral representation in the required carrier universe. -/
abbrev integralTrivial (G : Type u) [Group G] : Rep IntegralScalar.{u} G :=
  Rep.trivial IntegralScalar G IntegralScalar

end Langlands.Tate
