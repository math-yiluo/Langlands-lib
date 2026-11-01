import Langlands.AlgebraicGeometry.ImaginaryQuadraticEigensheafNaturality
import Langlands.Shimura.PEL.HarrisTaylorLieEigensheaf

/-! # Actual natural and conjugate splitting of the relative Lie sheaf -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.Shimura.ImaginaryQuadratic
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L]
  {K : Type} [Field K] [NumberField K] [Algebra L K]
  {S : AlgebraicGeometry.Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of K))
  {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]

omit [IsQuadraticExtension ℚ L] [NumberField K] in
/-- The generic natural/conjugate characters are the actual structure characters. -/
theorem sheafFactorCharacter_eq_imaginaryLieCharacter (conjugate : Bool) :
    letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
    letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
    letI : IsScalarTower ℚ K Γ(S, ⊤) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    sheafFactorCharacter L K conjugate = imaginaryLieCharacter L s conjugate := by
  cases conjugate <;> rfl

variable (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

/-- The actual projection from the relative Lie sheaf to its full central eigensubsheaf. -/
def lieEigenProjection (conjugate : Bool) : B.Lie ⟶ lieEigensheaf L s B i conjugate := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  simpa only [lieEigensheaf, sheafFactorCharacter_eq_imaginaryLieCharacter L s] using
    sheafEigenProjection L K B.Lie (imaginaryLieAction L s B i) conjugate

/-- The actual relative Lie sheaf splits into its natural and conjugate central eigensheaves. -/
def lieEigenIso :
    B.Lie ≅ lieEigensheaf L s B i false ⨯ lieEigensheaf L s B i true := by
  letI : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  letI : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  letI : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  simpa only [lieEigensheaf, sheafFactorCharacter_eq_imaginaryLieCharacter L s] using
    sheafEigenIso L K B.Lie (imaginaryLieAction L s B i)

@[simp]
theorem lieEigenIso_hom :
    (lieEigenIso L s B i).hom =
      prod.lift (lieEigenProjection L s B i false) (lieEigenProjection L s B i true) := by
  rfl

@[simp]
theorem lieEigenIso_inv :
    (lieEigenIso L s B i).inv =
      prod.fst ≫ lieEigensheafι L s B i false +
        prod.snd ≫ lieEigensheafι L s B i true := by
  rfl

/-- The projection is equivariant for the full actual rational algebra action. -/
theorem lieEigenProjection_intertwines (conjugate : Bool) (a : A) :
    lieRationalOrderAction s B i.toRingHom a ≫ lieEigenProjection L s B i conjugate =
      lieEigenProjection L s B i conjugate ≫ lieEigensheafAction L s B i conjugate a := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  cases conjugate
  · exact sheafEigenProjection_naturality L K (imaginaryLieAction L s B i)
      (imaginaryLieAction L s B i) (lieRationalOrderAction s B i.toRingHom a)
      (fun r => imaginaryLieAction_commutes L s B i r a) false
  · exact sheafEigenProjection_naturality L K (imaginaryLieAction L s B i)
      (imaginaryLieAction L s B i) (lieRationalOrderAction s B i.toRingHom a)
      (fun r => imaginaryLieAction_commutes L s B i r a) true

/-- The product splitting intertwines the full algebra action with its two restrictions. -/
theorem lieEigenIso_intertwines (a : A) :
    lieRationalOrderAction s B i.toRingHom a ≫ (lieEigenIso L s B i).hom =
      (lieEigenIso L s B i).hom ≫
        prod.map (lieEigensheafAction L s B i false a)
          (lieEigensheafAction L s B i true a) := by
  apply prod.hom_ext
  · simpa only [lieEigenIso_hom, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using
      lieEigenProjection_intertwines L s B i false a
  · simpa only [lieEigenIso_hom, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using
      lieEigenProjection_intertwines L s B i true a

variable {B} {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
  (f : Hom0 B B')
  (hf : ∀ a : A, comp0 B B B' (i a) f = comp0 B B' B' f (i' a))

/-- The projections commute with actual equivariant rational differentials. -/
theorem lieEigenProjection_naturality (conjugate : Bool) :
    lieMap0 s f ≫ lieEigenProjection L s B' i' conjugate =
      lieEigenProjection L s B i conjugate ≫ lieEigensheafMap L s i i' f hf conjugate := by
  let : Algebra K Γ(S, ⊤) := (secHom s ⊤).hom.toAlgebra
  let : Algebra ℚ Γ(S, ⊤) := Algebra.compHom Γ(S, ⊤) (algebraMap ℚ K)
  let : IsScalarTower ℚ K Γ(S, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  cases conjugate
  · exact sheafEigenProjection_naturality L K (imaginaryLieAction L s B i)
      (imaginaryLieAction L s B' i') (lieMap0 s f)
      (imaginaryLieMap_intertwines L s i i' f hf) false
  · exact sheafEigenProjection_naturality L K (imaginaryLieAction L s B i)
      (imaginaryLieAction L s B' i') (lieMap0 s f)
      (imaginaryLieMap_intertwines L s i i' f hf) true

/-- The actual splitting is natural for equivariant rational homomorphisms. -/
theorem lieEigenIso_naturality :
    lieMap0 s f ≫ (lieEigenIso L s B' i').hom =
      (lieEigenIso L s B i).hom ≫
        prod.map (lieEigensheafMap L s i i' f hf false)
          (lieEigensheafMap L s i i' f hf true) := by
  apply prod.hom_ext
  · simpa only [lieEigenIso_hom, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc] using
      lieEigenProjection_naturality L s i i' f hf false
  · simpa only [lieEigenIso_hom, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc] using
      lieEigenProjection_naturality L s i i' f hf true

end Langlands.Shimura.HarrisTaylor
