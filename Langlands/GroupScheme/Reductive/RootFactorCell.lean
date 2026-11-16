import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.GroupScheme.Rational.OrderedProductBaseChange
import Langlands.GroupScheme.KernelOrderedProductChart
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Reductive.RelativeCommutatorDescent

/-! # Actual ordered factor cells and their coordinate comparisons -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootFactorCell

open LocalSplitCell RelativeRoot

variable (R : CommRingCat.{u}) (m : ℕ)

/-- The product of `m` additive groups has its actual scalar coordinates. -/
def piGaCoordinates (Z : Over (Spec R)) :
    (Z ⟶ (∏ᶜ fun _ : Fin m => VectorGroup.groupScheme R 1).X) ≃*
      Multiplicative (Fin m → Γ(Z.left, ⊤)) where
  toFun x := Multiplicative.ofAdd (fun i =>
    (VectorGroup.coordinates R 1 Z (x ≫ (Pi.π (fun _ : Fin m => VectorGroup.groupScheme R 1) i).hom.hom)).toAdd 0)
  invFun c := (finiteProductPointsEquiv (fun _ : Fin m => VectorGroup.groupScheme R 1) Z).symm
    (fun i => VectorGroup.scalarPoint R Z (c.toAdd i))
  left_inv x := by
    apply (finiteProductPointsEquiv (fun _ : Fin m => VectorGroup.groupScheme R 1) Z).injective
    funext i
    rw [finiteProductPointsEquiv_apply, finiteProductPointsEquiv_symm_π]
    change VectorGroup.scalarPoint R Z
      ((VectorGroup.coordinates R 1 Z
        (x ≫ (Pi.π (fun _ : Fin m => VectorGroup.groupScheme R 1) i).hom.hom)).toAdd 0) =
      x ≫ (Pi.π (fun _ : Fin m => VectorGroup.groupScheme R 1) i).hom.hom
    exact VectorGroup.scalarPoint_coordinate (R := R) Z _
  right_inv c := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, finiteProductPointsEquiv_symm_π, VectorGroup.coordinates_scalarPoint]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, MonObj.mul_comp, VectorGroup.coordinates_mul]
    rfl

/-- The scalar product coordinates commute with restriction of tests. -/
theorem piGaCoordinates_naturality {Z W : Over (Spec R)} (a : W ⟶ Z)
    (x : Z ⟶ (∏ᶜ fun _ : Fin m => VectorGroup.groupScheme R 1).X) :
    piGaCoordinates R m W (a ≫ x) = Multiplicative.ofAdd
      (fun i => a.left.appTop ((piGaCoordinates R m Z x).toAdd i)) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [piGaCoordinates, toAdd_ofAdd, VectorGroup.coordinates_comp]
  rfl

/-- The standard vector group is the categorical product of its additive coordinates. -/
def vectorPiGaIso : VectorGroup.groupScheme R m ≅
    ∏ᶜ fun _ : Fin m => VectorGroup.groupScheme R 1 :=
  isoOfPointModels (fun Z => Multiplicative (Fin m → Γ(Z.left, ⊤)))
    (fun a =>
      { toFun := fun x => Multiplicative.ofAdd (fun i => a.left.appTop (x.toAdd i))
        map_one' := by
          apply Multiplicative.toAdd.injective
          funext i
          exact map_zero a.left.appTop.hom
        map_mul' := fun x y => by
          apply Multiplicative.toAdd.injective
          funext i
          exact map_add a.left.appTop.hom _ _ })
    (VectorGroup.coordinates R m) (piGaCoordinates R m)
    (fun a x => by
      apply Multiplicative.toAdd.injective
      exact VectorGroup.coordinates_comp a x)
    (fun a x => piGaCoordinates_naturality R m a x)

end Langlands.GroupScheme.RootFactorCell

namespace Langlands.GroupScheme.RootFactorCell

open LocalSplitCell RelativeRoot

variable (R : CommRingCat.{u}) (m : ℕ)

/-- The vector/product isomorphism sends each projection to its scalar coordinate. -/
theorem vectorPiGaIso_hom_π (Z : Over (Spec R))
    (x : Z ⟶ (VectorGroup.groupScheme R m).X) (i : Fin m) :
    x ≫ (vectorPiGaIso R m).hom.hom.hom ≫
        (Pi.π (fun _ : Fin m => VectorGroup.groupScheme R 1) i).hom.hom =
      VectorGroup.scalarPoint R Z ((VectorGroup.coordinates R m Z x).toAdd i) := by
  have h : piGaCoordinates R m Z (x ≫ (vectorPiGaIso R m).hom.hom.hom) =
      VectorGroup.coordinates R m Z x :=
    isoOfPointModels_hom _ _ _ _
      (fun a x => by
        apply Multiplicative.toAdd.injective
        exact VectorGroup.coordinates_comp a x)
      (fun a x => piGaCoordinates_naturality R m a x) Z x
  have hc := congrArg (fun c => c.toAdd i) h
  calc
    _ = VectorGroup.scalarPoint R Z
        ((VectorGroup.coordinates R 1 Z
          (x ≫ (vectorPiGaIso R m).hom.hom.hom ≫
            (Pi.π (fun _ : Fin m => VectorGroup.groupScheme R 1) i).hom.hom)).toAdd 0) :=
      (VectorGroup.scalarPoint_coordinate (R := R) Z _).symm
    _ = _ := congrArg (VectorGroup.scalarPoint R Z) hc

/-- Chosen additive coordinates on actual factors give their actual vector-product iso. -/
def vectorProductIso (A : Fin m → GroupScheme (Spec R))
    (e : ∀ i, VectorGroup.groupScheme R 1 ≅ A i) :
    VectorGroup.groupScheme R m ≅ ∏ᶜ A :=
  vectorPiGaIso R m ≪≫ Pi.mapIso e

/-- Its factor projections are the chosen additive coordinate maps. -/
theorem vectorProductIso_hom_π (A : Fin m → GroupScheme (Spec R))
    (e : ∀ i, VectorGroup.groupScheme R 1 ≅ A i) (Z : Over (Spec R))
    (x : Z ⟶ (VectorGroup.groupScheme R m).X) (i : Fin m) :
    x ≫ (vectorProductIso R m A e).hom.hom.hom ≫ (Pi.π A i).hom.hom =
      VectorGroup.scalarPoint R Z ((VectorGroup.coordinates R m Z x).toAdd i) ≫
        (e i).hom.hom.hom := by
  have h := congrArg (fun f => f.hom.hom) (Pi.map_π (fun i => (e i).hom) i)
  change (Pi.mapIso e).hom.hom.hom ≫ (Pi.π A i).hom.hom =
    (Pi.π (fun _ : Fin m => VectorGroup.groupScheme R 1) i).hom.hom ≫
      (e i).hom.hom.hom at h
  simp only [vectorProductIso, Iso.trans_hom, Grp.comp_hom_hom, Category.assoc]
  rw [h]
  simpa only [Category.assoc] using congrArg (fun p => p ≫ (e i).hom.hom.hom)
    (vectorPiGaIso_hom_π R m Z x i)

section Cell

variable {S : Scheme.{u}} {m n : ℕ} (A : Fin m → GroupScheme S)
    (D : GroupScheme S) (B : Fin n → GroupScheme S)

/-- The actual source group of a negative-factor, torus, positive-factor cell. -/
abbrev sourceGroup : GroupScheme S := ((∏ᶜ A) ⊗ D) ⊗ (∏ᶜ B)

variable {G : GroupScheme S}

/-- The ordered multiplication of the actual factors, with the torus in the middle. -/
def multiplication (jA : ∀ i, A i ⟶ G) (jD : D ⟶ G) (jB : ∀ i, B i ⟶ G) :
    (sourceGroup A D B).X ⟶ G.X :=
  (fst _ _ ≫ fst _ _ ≫ orderedMultiplication jA) *
    (fst _ _ ≫ snd _ _ ≫ jD.hom.hom) * (snd _ _ ≫ orderedMultiplication jB)

/-- Finite products of smooth actual factors are smooth, independently of the base universe. -/
theorem smooth_finiteProduct (hA : ∀ i, Smooth (A i).X.hom) : Smooth (∏ᶜ A).X.hom := by
  let e : ULift.{u} (Fin m) ≃ Fin m := Equiv.ulift
  exact smooth_of_over_iso
    ((Grp.forget (Over S)).mapIso (Pi.reindex e A)).symm
    (smooth_pi (A ∘ e) (fun r => hA (e r)))

/-- The actual cell source is smooth when all its factors are smooth. -/
theorem smooth_sourceGroup (hA : ∀ i, Smooth (A i).X.hom)
    (hD : Smooth D.X.hom) (hB : ∀ i, Smooth (B i).X.hom) :
    Smooth (sourceGroup A D B).X.hom :=
  smooth_tensor _ _ (smooth_tensor _ _ (smooth_finiteProduct A hA) hD)
    (smooth_finiteProduct B hB)

end Cell

end Langlands.GroupScheme.RootFactorCell

namespace Langlands.GroupScheme.RootFactorCell

open RelativeRoot RelativeDerived

variable {S : Scheme.{u}} {m n : ℕ} {G D : GroupScheme S}
    {A : Fin m → GroupScheme S} {B : Fin n → GroupScheme S}

/-- A point of an ordered multiplication chart is locally a commutator if
every value of every factor is. -/
theorem locallyCommutator_orderedMultiplication (j : ∀ i, A i ⟶ G)
    (hj : ∀ i (Z : Over S) (x : Z ⟶ (A i).X), LocallyCommutator (x ≫ (j i).hom.hom))
    (Z : Over S) (x : Z ⟶ (∏ᶜ A).X) :
    LocallyCommutator (x ≫ orderedMultiplication j) := by
  rw [comp_orderedMultiplication, orderedPoints]
  apply (locallyCommutatorSubgroup (G := G) Z).list_prod_mem
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  exact hj i Z _

/-- The actual ordered cell takes the identity point to the identity. -/
theorem one_comp_multiplication (jA : ∀ i, A i ⟶ G) (jD : D ⟶ G) (jB : ∀ i, B i ⟶ G)
    (Z : Over S) :
    (1 : Z ⟶ (sourceGroup A D B).X) ≫ multiplication A D B jA jD jB = 1 := by
  simp only [multiplication, MonObj.comp_mul, ← Category.assoc, MonObj.one_comp,
    one_comp_orderedMultiplication, one_mul]

/-- Its image contains the full unit section. -/
theorem range_unit_subset_multiplication (jA : ∀ i, A i ⟶ G)
    (jD : D ⟶ G) (jB : ∀ i, B i ⟶ G) :
    Set.range η[G.X].left ⊆ Set.range (multiplication A D B jA jD jB).left := by
  have h : η[(sourceGroup A D B).X] ≫ multiplication A D B jA jD jB = η[G.X] := by
    have h := one_comp_multiplication jA jD jB (𝟙_ (Over S))
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h
  rintro _ ⟨s, rfl⟩
  exact ⟨η[(sourceGroup A D B).X].left s,
    congrArg (fun f => f.left s) h⟩

/-- Actual cell values are local commutators when the factors and middle
torus all have that property. -/
theorem locallyCommutator_multiplication (jA : ∀ i, A i ⟶ G)
    (jD : D ⟶ G) (jB : ∀ i, B i ⟶ G)
    (hA : ∀ i (Z : Over S) (x : Z ⟶ (A i).X), LocallyCommutator (x ≫ (jA i).hom.hom))
    (hD : ∀ (Z : Over S) (x : Z ⟶ D.X), LocallyCommutator (x ≫ jD.hom.hom))
    (hB : ∀ i (Z : Over S) (x : Z ⟶ (B i).X), LocallyCommutator (x ≫ (jB i).hom.hom))
    (Z : Over S) (x : Z ⟶ (sourceGroup A D B).X) :
    LocallyCommutator (x ≫ multiplication A D B jA jD jB) := by
  simp only [multiplication, MonObj.comp_mul]
  exact ((locallyCommutator_orderedMultiplication jA hA Z (x ≫ fst _ _ ≫ fst _ _)).mul
    (hD Z (x ≫ fst _ _ ≫ snd _ _))).mul
      (locallyCommutator_orderedMultiplication jB hB Z (x ≫ snd _ _))

end Langlands.GroupScheme.RootFactorCell
