import Langlands.GroupScheme.Torus.PointsTensor
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.GaloisCocycle
import Langlands.ClassFieldTheory.Local.Cohomology

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct MonoidalCategory

namespace Langlands.GroupScheme.TorusPointsTensorGalois

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual commutative group scheme obtained by extending coefficients. -/
abbrev baseChanged (T : CommGroupScheme (Spec (CommRingCat.of k))) :=
  (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T

/-- Field units, written additively, are the actual identity-test Gm points. -/
def unitsPointEquiv :
    Additive Lˣ ≃ₗ[ULift.{u} ℤ]
      Additive (Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶
        (Gm (Spec (CommRingCat.of L))).X) :=
  (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))).symm.toAdditive.toIntLinearEquiv.restrictScalars
    (ULift.{u} ℤ)

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The canonical tensor evaluation, read as actual coefficient points. -/
def coefficientEvaluation :
    Additive Lˣ ⊗[ULift.{u} ℤ] cocharacterLattice (baseChanged k L T) →ₗ[ULift.{u} ℤ]
      Additive (affinePoints T.toGrp (CommAlgCat.of k L)) :=
  ((GaloisPointComparison.baseChangeCoeffEquiv k L T.toGrp).toAdditive.toIntLinearEquiv.restrictScalars
      (ULift.{u} ℤ)).toLinearMap ∘ₗ
    TorusPointsTensor.tensorEvaluation (baseChanged k L T)
      (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ∘ₗ
    (TensorProduct.congr (unitsPointEquiv L)
      (LinearEquiv.refl (ULift.{u} ℤ) _)).toLinearMap

@[simp] theorem coefficientEvaluation_tmul (x : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν) =
      Additive.ofMul (GaloisPointComparison.baseChangeCoeffEquiv k L T.toGrp
        ((unitsPointEquiv L x).toMul ≫ (CommGroupScheme.groupHom ν).hom.hom)) := rfl

/-- The tensor and coefficient points are equivalent when the actual base change is split. -/
def coefficientPointEquiv (hT : IsSplitTorus (baseChanged k L T).toGrp) :
    Additive Lˣ ⊗[ULift.{u} ℤ] cocharacterLattice (baseChanged k L T) ≃ₗ[ULift.{u} ℤ]
      Additive (affinePoints T.toGrp (CommAlgCat.of k L)) :=
  (TensorProduct.congr (unitsPointEquiv L) (LinearEquiv.refl (ULift.{u} ℤ) _)).trans
    ((TorusPointsTensor.tensorPointEquiv L (baseChanged k L T) hT
        (Over.mk (𝟙 (Spec (CommRingCat.of L))))).trans
      ((GaloisPointComparison.baseChangeCoeffEquiv k L T.toGrp).toAdditive.toIntLinearEquiv.restrictScalars
        (ULift.{u} ℤ)))

@[simp] theorem coefficientPointEquiv_apply (hT : IsSplitTorus (baseChanged k L T).toGrp)
    (t : Additive Lˣ ⊗[ULift.{u} ℤ] cocharacterLattice (baseChanged k L T)) :
    coefficientPointEquiv k L T hT t = coefficientEvaluation k L T t := rfl

/-- The coefficient automorphism, as a map from the test scheme with changed structure. -/
def changedTestArrow (σ : L ≃ₐ[k] L) :
    (Over.map (galoisBaseMap k L σ)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
  Over.homMk (galoisBaseMap k L σ) (by simp)

/-- Pullback of a unit point along `Spec σ` gives the usual automorphism of field units. -/
theorem unitPoint_galois (σ : L ≃ₐ[k] L) (x : Additive Lˣ) :
    (Gm.pointsEquiv _ ((Over.map (galoisBaseMap k L σ)).obj
        (Over.mk (𝟙 (Spec (CommRingCat.of L)))))).symm
      (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of L))))
        (unitsPointEquiv L (Additive.ofMul (Units.map σ.toMonoidHom x.toMul))).toMul) =
      changedTestArrow k L σ ≫ (unitsPointEquiv L x).toMul := by
  apply (Gm.pointsEquiv _ _).injective
  rw [MulEquiv.apply_symm_apply, Gm.pointsEquiv_naturality]
  apply (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.toMulEquiv).injective
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      (Gm.pointsEquiv _ _ (unitsPointEquiv L
        (Additive.ofMul (Units.map σ.toMonoidHom x.toMul))).toMul).val =
    (((Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of L)).hom)
        (Gm.pointsEquiv _ _ (unitsPointEquiv L x).toMul).val)
  rw [Scheme.ΓSpecIso_naturality]
  change (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))
      (unitsPointEquiv L (Additive.ofMul (Units.map σ.toMonoidHom x.toMul))).toMul : L) =
    σ (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of L)))
      (unitsPointEquiv L x).toMul : L)
  simp [unitsPointEquiv]

/-- Transported evaluation has the expected underlying map of schemes. -/
theorem transportEvaluation_left
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (χ : (Gm (Spec (CommRingCat.of L))).toGrp ⟶
      (Over.pullback (algebraBaseMap k L)).mapGrp.obj G)
    (σ : L ≃ₐ[k] L) (x : Additive Lˣ) :
    (unitsPointEquiv L (Additive.ofMul (Units.map σ.toMonoidHom x.toMul))).toMul.left ≫
        (transportCocharacter (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) G χ).hom.hom.left ≫
          Limits.pullback.fst G.X.hom (algebraBaseMap k L) =
      galoisBaseMap k L σ ≫ (unitsPointEquiv L x).toMul.left ≫
        χ.hom.hom.left ≫ Limits.pullback.fst G.X.hom (algebraBaseMap k L) := by
  have h := transportCocharacter_points (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G χ
    (Over.mk (𝟙 (Spec (CommRingCat.of L))))
    (unitsPointEquiv L (Additive.ofMul (Units.map σ.toMonoidHom x.toMul))).toMul
  rw [unitPoint_galois k L σ x] at h
  simpa only [baseChangePointsEquiv_left, Over.comp_left, Category.id_comp,
    Category.assoc, descentTestIso, changedTestArrow,
    Over.isoMk_hom_left, Over.homMk_left, Iso.refl_hom] using congrArg (fun f => f.left) h

/-- The algebra-point automorphism is the same underlying spectrum map. -/
theorem algSpec_galois_left (σ : L ≃ₐ[k] L) :
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op).left =
      galoisBaseMap k L σ := rfl

/-- The underlying map of a pure evaluation is the projected cocharacter composite. -/
theorem coefficientEvaluation_tmul_left (x : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν)).toMul.left =
      (unitsPointEquiv L x).toMul.left ≫
        (CommGroupScheme.groupHom ν).hom.hom.left ≫
          Limits.pullback.fst T.X.hom (algebraBaseMap k L) := by
  rw [coefficientEvaluation_tmul, toMul_ofMul,
    GaloisPointComparison.baseChangeCoeffEquiv_left, Over.comp_left, Category.assoc]

/-- Actual coefficient evaluation is compatible with the diagonal Galois action. -/
theorem coefficientEvaluation_galois_tmul (σ : L ≃ₐ[k] L) (x : Additive Lˣ)
    (ν : cocharacterLattice (baseChanged k L T)) :
    coefficientEvaluation k L T
        (Additive.ofMul (Units.map σ.toMonoidHom x.toMul) ⊗ₜ[ULift.{u} ℤ]
          cocharacterLattice.galoisRepresentation k L T σ ν) =
      Additive.ofMul (GaloisPoint.conjugate k L T.toGrp σ
        (coefficientEvaluation k L T (x ⊗ₜ[ULift.{u} ℤ] ν)).toMul) := by
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  simp only [toMul_ofMul, coefficientEvaluation_tmul_left,
    cocharacterLattice.galoisRepresentation_apply, cocharacterLattice.groupHom_transport,
    GaloisPoint.conjugate, affinePointMap_apply, Over.comp_left, algSpec_galois_left]
  exact transportEvaluation_left k L T.toGrp (CommGroupScheme.groupHom ν) σ x

/-- The actual cocharacter lattice with transport action and lifted integer scalars. -/
def latticeRepresentation : Rep.{u} (ULift.{u} ℤ) (L ≃ₐ[k] L) :=
  Rep.of
    { toFun σ := (cocharacterLattice.galoisRepresentation k L T σ).restrictScalars (ULift.{u} ℤ)
      map_one' := by
        ext ν
        exact LinearMap.congr_fun (map_one (cocharacterLattice.galoisRepresentation k L T)) ν
      map_mul' σ τ := by
        ext ν
        exact LinearMap.congr_fun (map_mul (cocharacterLattice.galoisRepresentation k L T) σ τ) ν }

/-- For an actually split base change, tensor evaluation is an isomorphism of Galois
representations on the actual field units, cocharacters, and coefficient points. -/
def tensorPointIso (hT : IsSplitTorus (baseChanged k L T).toGrp) :
    Langlands.ClassFieldTheory.Local.unitsRepresentation k L ⊗ latticeRepresentation k L T ≅
      GaloisCocycle.pointRepresentation (G := T.toGrp) (k := k) (L := L) :=
  Rep.mkIso (Representation.Equiv.mk (coefficientPointEquiv k L T hT) (fun σ => by
    apply TensorProduct.ext'
    intro x ν
    change coefficientPointEquiv k L T hT
        (TensorProduct.map
          ((Langlands.ClassFieldTheory.Local.unitsRepresentation k L).ρ σ)
          ((latticeRepresentation k L T).ρ σ) (x ⊗ₜ[ULift.{u} ℤ] ν)) = _
    rw [TensorProduct.map_tmul, coefficientPointEquiv_apply]
    exact coefficientEvaluation_galois_tmul k L T σ x ν))

end Langlands.GroupScheme.TorusPointsTensorGalois
