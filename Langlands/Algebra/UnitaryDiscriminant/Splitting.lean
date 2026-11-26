import Langlands.Algebra.UnitaryDiscriminant.Class
import Langlands.Algebra.CentralSimple.FiniteGaloisSplitting
import Mathlib.FieldTheory.Normal.Closure

/-! # Finite Galois splittings and the discriminant class without a supplied chart -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

/-- A finite Galois matrix splitting of an `L`-algebra `B` over an extension `field` of `F`
containing `L`: the kind of trivialization used by `discriminantClass`. -/
structure GaloisSplitting (F L : Type u) [Field F] [Field L] [Algebra F L]
    (B : Type v) [Ring B] [Algebra L B] (n : ℕ) where
  /-- The splitting field. -/
  field : Type u
  [instField : Field field]
  [instAlgebraBase : Algebra F field]
  [instAlgebraCenter : Algebra L field]
  [instTower : IsScalarTower F L field]
  [instFinite : FiniteDimensional F field]
  [instGalois : IsGalois F field]
  /-- The matrix chart over the splitting field. -/
  chart : field ⊗[L] B ≃ₐ[field] Matrix (Fin n) (Fin n) field

attribute [instance] GaloisSplitting.instField GaloisSplitting.instAlgebraBase
  GaloisSplitting.instAlgebraCenter GaloisSplitting.instTower GaloisSplitting.instFinite
  GaloisSplitting.instGalois

section Construction

variable (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L]
  (B : Type u) [Ring B] [Algebra L B] [FiniteDimensional L B] [Algebra.IsCentral L B]
  [IsSimpleRing B]

/-- `B` as a bundled central simple `L`-algebra. -/
def bundledCSA : CSA.{u, u} L where
  toAlgCat := AlgCat.of L B
  isCentral := ‹_›
  isSimple := ‹_›
  fin_dim := ‹_›

/-- The matrix size of the Library's chosen splitting chart is determined by the dimension. -/
theorem reducedDegree_eq_of_finrank {n : ℕ} (hB : Module.finrank L B = n ^ 2) :
    CentralSimple.reducedDegree L B = n := by
  have h := (CentralSimple.finiteGaloisSplittingChart_spec L B).2
  rw [hB, sq] at h
  exact (Nat.mul_self_inj.mp h).symm

/-- A finite Galois splitting of `B` over an extension of `F` containing `L`. The Library's
finite Galois splitting field `E` of `B` over `L` is embedded in an algebraic closure of `F`, and
the splitting field is the normal closure of `E` over `F` there. -/
def galoisSplitting {n : ℕ} (hB : Module.finrank L B = n ^ 2) : GaloisSplitting F L B n :=
  letI E := CentralSimple.finiteGaloisSplittingField L B
  letI : Algebra F E := ((algebraMap L E).comp (algebraMap F L)).toAlgebra
  haveI : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional F E := Module.Finite.trans L E
  haveI : Algebra.IsSeparable F E := Algebra.IsSeparable.trans F L E
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let φ : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  letI : Algebra E (AlgebraicClosure F) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F E (AlgebraicClosure F) := IsScalarTower.of_algHom φ
  letI N := ↥(IntermediateField.normalClosure F E (AlgebraicClosure F))
  letI : Algebra L N := ((algebraMap E N).comp (algebraMap L E)).toAlgebra
  haveI : IsScalarTower L E N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply F E N x]
    rfl)
  { field := N
    chart := (BrauerComparison.enlargedSplittingChart (A := bundledCSA L B) N
        (CentralSimple.finiteGaloisSplittingChart L B)).trans
      (Matrix.reindexAlgEquiv N N (finCongr (reducedDegree_eq_of_finrank L B hB))) }

/-- Every finite-dimensional central simple `L`-algebra of dimension `n²` has a finite Galois
matrix splitting of size `n` over an extension of `F` containing `L`. -/
theorem exists_galoisSplitting {n : ℕ} (hB : Module.finrank L B = n ^ 2) :
    Nonempty (GaloisSplitting F L B n) :=
  ⟨galoisSplitting F L B hB⟩

end Construction

section Class

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [Algebra.IsQuadraticExtension F L]
  [Algebra.IsSeparable F L]
  {B : Type u} [Ring B] [Algebra L B] [FiniteDimensional L B] [Algebra.IsCentral L B]
  [IsSimpleRing B]
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {τ : B → B} (hτ : IsUnitaryInvolution ι τ)

/-- The discriminant Brauer class of a central simple `L`-algebra `B` of degree `2m` with unitary
involution `τ`, computed in the finite Galois splitting `galoisSplitting F L B hB`. -/
def discriminantClassOf {m : ℕ} (hB : Module.finrank L B = (2 * m) ^ 2) :
    BrauerGroup.{u, u} F :=
  discriminantClass hι hτ (galoisSplitting F L B hB).chart

theorem discriminantClassOf_eq {m : ℕ} (hB : Module.finrank L B = (2 * m) ^ 2) :
    discriminantClassOf hι hτ hB = discriminantClass hι hτ (galoisSplitting F L B hB).chart :=
  rfl

/-- The discriminant class of `(B, τ)` is killed by two. -/
theorem two_nsmul_discriminantClassOf {m : ℕ} (hB : Module.finrank L B = (2 * m) ^ 2) :
    2 • discriminantClassOf hι hτ hB = 0 :=
  two_nsmul_discriminantClass hι hτ _

end Class

end Langlands.UnitaryDiscriminant
