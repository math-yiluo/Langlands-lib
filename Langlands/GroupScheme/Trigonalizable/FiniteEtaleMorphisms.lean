import Langlands.GroupScheme.Trigonalizable.FiniteEtaleEvaluation
import Langlands.GroupScheme.Torus.EtaleMultiplicativeTypeOrderForward

/-! # Morphisms from a finite étale scheme by geometric evaluation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.EtaleExtensionSplit

set_option backward.isDefEq.respectTransparency false

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private abbrev F (k : Type u) [Field k] := algSpec (CommRingCat.of k)
private abbrev ff (k : Type u) [Field k] := algSpec.fullyFaithful (R := CommRingCat.of k)

/-- The test scheme given by the actual scalar extension. -/
abbrev geometricTest (k L : Type u) [Field k] [Field L] [Algebra k L] :=
  (F k).obj (op (CommAlgCat.of k L))

/-- The test morphism induced by an automorphism of geometric scalars. -/
def conjugationTest (σ : L ≃ₐ[k] L) : geometricTest k L ⟶ geometricTest k L :=
  (F k).map (CommAlgCat.ofHom σ.toAlgHom).op

private abbrev affIso (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    X ≅ (F k).obj (op (CommAlgCat.of k (AffineCoordinateRing k X))) :=
  affineSchemeOverIso k X

private def pointCoordinates (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    (geometricTest k L ⟶ X) ≃ (AffineCoordinateRing k X →ₐ[k] L) where
  toFun x := ((ff k).preimage (x ≫ (affIso X).hom)).unop.hom
  invFun x := (F k).map (CommAlgCat.ofHom x).op ≫ (affIso X).inv
  left_inv x := by simp
  right_inv a := by simp

private def homCoordinates {X Y : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [IsAffine Y.left] :
    (X ⟶ Y) ≃ (AffineCoordinateRing k Y →ₐ[k] AffineCoordinateRing k X) where
  toFun f := ((ff k).preimage ((affIso X).inv ≫ f ≫ (affIso Y).hom)).unop.hom
  invFun a := (affIso X).hom ≫ (F k).map (CommAlgCat.ofHom a).op ≫ (affIso Y).inv
  left_inv f := by simp
  right_inv a := by simp

private theorem pointCoordinates_comp {X Y : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [IsAffine Y.left] (x : geometricTest k L ⟶ X) (f : X ⟶ Y) :
    pointCoordinates Y (x ≫ f) = (pointCoordinates X x).comp (homCoordinates f) := by
  apply (pointCoordinates Y).symm.injective
  let a := pointCoordinates X x
  let b := homCoordinates f
  have hcomp : (pointCoordinates Y).symm (a.comp b) =
      (pointCoordinates X).symm a ≫ homCoordinates.symm b := by
    change (F k).map (CommAlgCat.ofHom (a.comp b)).op ≫ (affIso Y).inv =
      ((F k).map (CommAlgCat.ofHom a).op ≫ (affIso X).inv) ≫
        (affIso X).hom ≫ (F k).map (CommAlgCat.ofHom b).op ≫ (affIso Y).inv
    rw [show (CommAlgCat.ofHom (a.comp b)).op =
      (CommAlgCat.ofHom a).op ≫ (CommAlgCat.ofHom b).op from rfl, Functor.map_comp]
    simp
  change (pointCoordinates Y).symm (pointCoordinates Y (x ≫ f)) = _
  rw [Equiv.symm_apply_apply, hcomp]
  simp [a, b]

private theorem pointCoordinates_conjugate {X : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] (σ : L ≃ₐ[k] L) (x : geometricTest k L ⟶ X) :
    pointCoordinates X (conjugationTest σ ≫ x) = σ.toAlgHom.comp (pointCoordinates X x) := by
  apply (pointCoordinates X).symm.injective
  let a := pointCoordinates X x
  have hcomp : (pointCoordinates X).symm (σ.toAlgHom.comp a) =
      conjugationTest σ ≫ (pointCoordinates X).symm a := by
    change (F k).map (CommAlgCat.ofHom (σ.toAlgHom.comp a)).op ≫ (affIso X).inv =
      (F k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
        (F k).map (CommAlgCat.ofHom a).op ≫ (affIso X).inv
    rw [show (CommAlgCat.ofHom (σ.toAlgHom.comp a)).op =
      (CommAlgCat.ofHom σ.toAlgHom).op ≫ (CommAlgCat.ofHom a).op from rfl,
      Functor.map_comp, Category.assoc]
  change (pointCoordinates X).symm (pointCoordinates X (conjugationTest σ ≫ x)) = _
  rw [Equiv.symm_apply_apply, hcomp]
  simp [a]

variable [IsSepClosed L]

/-- Equality of morphisms with affine target and finite étale source can be tested
on geometric points of the source; the target need not be étale. -/
theorem geometric_hom_ext {X Y : Over (Spec (CommRingCat.of k))}
    [IsAffine X.left] [Etale X.hom] [IsAffine Y.left] {f g : X ⟶ Y}
    (h : ∀ x : geometricTest k L ⟶ X, x ≫ f = x ≫ g) : f = g := by
  let : Algebra.Etale k (AffineCoordinateRing k X) :=
    EtaleMultiplicativeTypeOrder.coordinate_etale k X
  apply homCoordinates.injective
  ext b
  apply eq_of_geometric_evaluation k L (AffineCoordinateRing k X)
  intro x
  let y := (pointCoordinates X).symm x
  have hy := congrArg (pointCoordinates Y) (h y)
  rw [pointCoordinates_comp, pointCoordinates_comp] at hy
  simpa only [y, Equiv.apply_symm_apply, AlgHom.comp_apply] using DFunLike.congr_fun hy b

/-- An equivariant function on geometric points of a finite étale source into
an affine target is induced by an actual morphism over the base field. -/
theorem exists_hom_of_equivariant [IsGalois k L]
    {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [Etale X.hom] [IsAffine Y.left]
    (f : (geometricTest k L ⟶ X) → (geometricTest k L ⟶ Y))
    (hf : ∀ (σ : L ≃ₐ[k] L) x, f (conjugationTest σ ≫ x) = conjugationTest σ ≫ f x) :
    ∃ g : X ⟶ Y, ∀ x : geometricTest k L ⟶ X, x ≫ g = f x := by
  let : Algebra.Etale k (AffineCoordinateRing k X) :=
    EtaleMultiplicativeTypeOrder.coordinate_etale k X
  let eX := pointCoordinates (L := L) X
  let eY := pointCoordinates (L := L) Y
  have hcoord (σ : L ≃ₐ[k] L) (x : AffineCoordinateRing k X →ₐ[k] L) :
      eY (f (eX.symm (σ.toAlgHom.comp x))) = σ.toAlgHom.comp (eY (f (eX.symm x))) := by
    have hx : eX.symm (σ.toAlgHom.comp x) = conjugationTest σ ≫ eX.symm x := by
      apply eX.injective
      rw [Equiv.apply_symm_apply, show eX (conjugationTest σ ≫ eX.symm x) =
        σ.toAlgHom.comp (eX (eX.symm x)) from pointCoordinates_conjugate σ _]
      rw [Equiv.apply_symm_apply]
    rw [hx, hf]
    exact pointCoordinates_conjugate σ _
  obtain ⟨a, ha⟩ := exists_algHom_of_equivariant k L (AffineCoordinateRing k X)
    (fun x => eY (f (eX.symm x))) hcoord
  refine ⟨homCoordinates.symm a, fun x => eY.injective ?_⟩
  change pointCoordinates Y (x ≫ homCoordinates.symm a) = eY (f x)
  rw [pointCoordinates_comp, Equiv.apply_symm_apply, ha]
  exact congrArg (eY ∘ f) (eX.symm_apply_apply x)

end Langlands.GroupScheme.EtaleExtensionSplit
