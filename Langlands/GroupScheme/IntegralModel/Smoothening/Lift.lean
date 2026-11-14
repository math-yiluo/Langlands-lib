import Langlands.GroupScheme.IntegralModel.Smoothening.Hopf
import Langlands.GroupScheme.IntegralModel.Smoothening.SmoothSections
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Lifting morphisms from smooth schemes to the spectrum of the integral functions

Let `R` be a Henselian discrete valuation ring with algebraically closed residue
field and fraction field `K`, `A` a commutative `R`-algebra and
`B = integralFunctions R K A`. For every smooth scheme `Y` over `Spec R`,
composition with `Spec B → Spec A` is a bijection from morphisms `Y → Spec B` to
morphisms `Y → Spec A` over `Spec R`. When `A` is a Hopf algebra, the same holds
for homomorphisms from a smooth group scheme. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.Smoothening

variable {R : Type u} [CommRing R]

section Instances

/-- The unit of the cartesian monoidal structure on schemes over `Spec R` is smooth. -/
instance smooth_tensorUnit_hom : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of R))))

/-- A product of smooth schemes over `Spec R` is smooth. -/
instance smooth_tensorObj_hom (X Y : Over (Spec (CommRingCat.of R))) [Smooth X.hom]
    [Smooth Y.hom] : Smooth (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

end Instances

/-- `R`-algebra maps from `C` to the global functions of a scheme `Y` over `Spec R`
are the morphisms from `(algΓ R).obj Y` to `op C`. -/
def algHomEquiv (Y : Over (Spec (CommRingCat.of R))) (C : CommAlgCat.{u} R) :
    (C →ₐ[R] ((algΓ (CommRingCat.of R)).obj Y).unop) ≃
      ((algΓ (CommRingCat.of R)).obj Y ⟶ op C) where
  toFun φ := (ConcreteCategory.ofHom (C := CommAlgCat.{u} R) φ :
    C ⟶ ((algΓ (CommRingCat.of R)).obj Y).unop).op
  invFun x := x.unop.hom
  left_inv _ := rfl
  right_inv _ := rfl

variable [IsDomain R] {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type u} [CommRing A]

section Algebra

variable [Algebra R A]

variable (R K A) in
/-- The morphism `Spec B → Spec A` over `Spec R` induced by `incl : A → B`. -/
abbrev specIncl :
    (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (integralFunctions R K A))) ⟶
      (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A)) :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom (incl R K A)).op

variable [IsDiscreteValuationRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]

/-- On the global functions `D` of a smooth scheme over `Spec R`, restriction along
`incl` is a bijection from algebra maps `B → D` to algebra maps `A → D`. -/
theorem comp_incl_bijective (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom] :
    Function.Bijective
      (fun φ : integralFunctions R K A →ₐ[R] ((algΓ (CommRingCat.of R)).obj Y).unop =>
        φ.comp (incl R K A)) := by
  refine ⟨fun φ₁ φ₂ h => algHom_ext_incl h, fun ψ => ?_⟩
  refine ⟨extend (B := integralFunctions R K A) ψ fun a s hs h => ?_, extend_comp_incl _ _⟩
  exact exists_eq_smul_of_smooth Y hs (ψ a) fun χ => dvd_of_exists_smul_eq h (χ.comp ψ)

/-- For a smooth scheme `Y` over `Spec R`, composition with `specIncl` is a bijection
from morphisms `Y → Spec B` to morphisms `Y → Spec A` over `Spec R`. -/
theorem bijective_comp_specIncl (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom] :
    Function.Bijective (fun g : Y ⟶ (algSpec (CommRingCat.of R)).obj
        (op (CommAlgCat.of R (integralFunctions R K A))) => g ≫ specIncl R K A) := by
  let adj := algΓAlgSpecAdjunction (CommRingCat.of R)
  let eB := (algHomEquiv Y (CommAlgCat.of R (integralFunctions R K A))).trans
    (adj.homEquiv _ _)
  let eA := (algHomEquiv Y (CommAlgCat.of R A)).trans (adj.homEquiv _ _)
  have key : ∀ φ, eB φ ≫ specIncl R K A = eA (φ.comp (incl R K A)) := by
    intro φ
    simp only [eB, eA, Equiv.trans_apply]
    rw [← adj.homEquiv_naturality_right]
    rfl
  have h : (fun g : Y ⟶ (algSpec (CommRingCat.of R)).obj
        (op (CommAlgCat.of R (integralFunctions R K A))) => g ≫ specIncl R K A) =
      eA ∘ (fun φ => φ.comp (incl R K A)) ∘ eB.symm := by
    funext g
    obtain ⟨φ, rfl⟩ := eB.surjective g
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact key φ
  rw [h]
  exact eA.bijective.comp ((comp_incl_bijective Y).comp eB.symm.bijective)

end Algebra

section Group

variable [HopfAlgebra R A]

variable (R K A) in
/-- The group scheme `Spec B` of the integral functions. -/
abbrev specB [IsDiscreteValuationRing R] : GroupScheme (Spec (CommRingCat.of R)) :=
  (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R (integralFunctions R K A)))

variable (R A) in
/-- The group scheme `Spec A`. -/
abbrev specA : GroupScheme (Spec (CommRingCat.of R)) :=
  (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R A))

variable [IsDiscreteValuationRing R]

variable (R K A) in
/-- The homomorphism `Spec B → Spec A` induced by the Hopf algebra map `incl`. -/
def specInclHom : specB R K A ⟶ specA R A :=
  (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom inclBialgHom).op

theorem specInclHom_hom_hom : (specInclHom R K A).hom.hom = specIncl R K A :=
  rfl

variable [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]

/-- Every homomorphism from a smooth group scheme over `Spec R` to `Spec A` factors
uniquely through `Spec B`. -/
theorem existsUnique_lift (H : GroupScheme (Spec (CommRingCat.of R))) [Smooth H.X.hom]
    (f : H ⟶ specA R A) : ∃! f' : H ⟶ specB R K A, f' ≫ specInclHom R K A = f := by
  have bij : ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Bijective (fun g : Y ⟶ (specB R K A).X => g ≫ (specInclHom R K A).hom.hom) :=
    fun Y _ => bijective_comp_specIncl (K := K) (A := A) Y
  obtain ⟨g, hg⟩ := (bij H.X).2 f.hom.hom
  simp only at hg
  have hg' : IsMonHom g := by
    constructor
    · apply (bij (𝟙_ _)).1
      simp only [Category.assoc, hg, IsMonHom.one_hom]
    · apply (bij (H.X ⊗ H.X)).1
      simp only [Category.assoc, hg, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]
  refine ⟨Grp.homMk g, ?_, fun f'' hf'' => ?_⟩
  · ext
    exact congrArg (fun x => x.left) hg
  · have h1 : f''.hom.hom = g := (bij H.X).1 (show f''.hom.hom ≫ _ = g ≫ _ by
      rw [hg]
      exact congrArg (fun x => x.hom.hom) hf'')
    ext
    exact congrArg (fun x => x.left) h1

end Group

end Langlands.GroupScheme.IntegralModel.Smoothening
