import Langlands.GroupScheme.Chevalley.ExteriorLine
import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Chevalley.MatrixExterior

/-! # The actual adjoint determinant line inside an ambient exterior representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Chevalley

section LinearAlgebra

variable {R : Type*} [CommRing R]
  {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {d : ℕ}

/-- An intertwiner carries the top exterior vector of a basis to a determinant
eigenvector of the ambient endomorphism, over every coefficient ring. -/
theorem exteriorPower_map_image_basis
    (b : Basis (Fin d) R V) (j : V →ₗ[R] W)
    (f : V →ₗ[R] V) (e : W →ₗ[R] W)
    (he : ∀ x, e (j x) = j (f x)) :
    exteriorPower.map d e (exteriorPower.ιMulti R d (fun i => j (b i))) =
      LinearMap.det f • exteriorPower.ιMulti R d (fun i => j (b i)) := by
  let a := (exteriorPower.ιMulti R d).compLinearMap j
  have h := congrArg (fun z : V [⋀^Fin d]→ₗ[R] (⋀[R]^d W) => z (f ∘ b))
    (alternatingMap_eq_det_smul b a)
  simp only [AlternatingMap.smulRight_apply, Basis.det_comp, Basis.det_self, mul_one] at h
  simpa only [a, AlternatingMap.compLinearMap_apply, Function.comp_apply,
    exteriorPower.map_apply_ιMulti, Function.comp_def, he] using h

end LinearAlgebra

/-- The algebraic exterior representation has the exterior matrix over the
coefficient algebra itself on every affine test. -/
theorem exteriorRepresentation_affineMatrix
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {N d : ℕ}
    (ρ : MatrixRepresentation G (Fin N)) (A : CommAlgCat.{u} R)
    (x : G.affinePoints A) :
    (exteriorRepresentation N d R ρ).affineMatrix A x =
      exteriorGL N d A (ρ.affineMatrix A x) := by
  rw [MatrixRepresentation.affineMatrix_apply, exteriorRepresentation,
    Grp.comp_hom_hom, ← Category.assoc]
  exact Corepresented.groupSchemeMap_affinePoints
    (GeneralLinear.corepresentableBy (Fin N) R)
    (GeneralLinear.corepresentableBy (Set.powersetCard (Fin N) d) R)
    (exteriorNat N d R) (x ≫ ρ.hom.hom)

/-- The exterior representation acts by the exterior linear map, expressed
in the standard exterior basis. -/
theorem exteriorRepresentation_affineAction
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {N d : ℕ}
    (ρ : MatrixRepresentation G (Fin N)) (A : CommAlgCat.{u} R)
    (x : G.affinePoints A) (v : ⋀[A]^d (Fin N → A)) :
    (exteriorRepresentation N d R ρ).affineAction A x
        ((matrixExteriorBasis N d A).equivFun v) =
      (matrixExteriorBasis N d A).equivFun
        (exteriorPower.map d (ρ.affineAction A x).toLinearMap v) := by
  rw [MatrixRepresentation.affineAction_apply, exteriorRepresentation_affineMatrix,
    exteriorGL_val]
  exact LinearMap.toMatrix_mulVec_repr
    (matrixExteriorBasis N d A) (matrixExteriorBasis N d A) _ v

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.Dynamic

variable {R : CommRingCat.{u}} {G P U : GroupScheme (Spec R)}
  {χ : (Gm (Spec R)).toGrp ⟶ G}
  {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP)
  (hU : (unipotent χ).IsRepresentedBy iU)
  [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]

/-- The actual Lie inclusion intertwines parabolic conjugation on `Lie U`
with the ambient adjoint action. -/
theorem targetMapLinear_parabolicAdjoint
    {A : Type u} [CommRing A] [Algebra R A]
    (p : Lie.AffinePoints P A) (x : Additive (lieKernel U A)) :
    Lie.targetMapLinear iU A ((parabolicAdjointAction hP hU).differential p x) =
      adjoint G A (p ≫ iP.hom.hom) (Lie.targetMapLinear iU A x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (parabolicAdjointAction hP hU).act (Lie.constant P p) x.toMul.val ≫
      iU.hom.hom =
    (Lie.constant G (p ≫ iP.hom.hom)) * (x.toMul.val ≫ iU.hom.hom) *
      (Lie.constant G (p ≫ iP.hom.hom))⁻¹
  rw [parabolicAdjointAction_act_comp]
  simp only [Lie.constant, Lie.affineMap_apply, Category.assoc]

variable {N d : ℕ} (cG : Lie.FiniteCoordinates G N) (cU : Lie.FiniteCoordinates U d)

/-- The ambient adjoint representation's exterior power of degree `dim Lie U`. -/
def adjointExteriorRepresentation :
    MatrixRepresentation G (Set.powersetCard (Fin N) d) :=
  Chevalley.exteriorRepresentation N d R (Lie.adjointRepresentation cG)

/-- The actual Lie inclusion written in the two natural finite coordinate systems. -/
def lieInclusionCoordinates (iU : U ⟶ G) (A : CommAlgCat.{u} R) :
    (Fin d → A) →ₗ[A] (Fin N → A) :=
  (cG.equiv A).toLinearMap ∘ₗ Lie.targetMapLinear iU A ∘ₗ
    (cU.equiv A).symm.toLinearMap

/-- The actual Lie inclusion in natural coordinates commutes with every
homomorphism of coefficient algebras. -/
theorem lieInclusionCoordinates_naturality {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) (x : Fin d → A) :
    lieInclusionCoordinates cG cU iU B (fun i => f.hom (x i)) =
      fun i => f.hom (lieInclusionCoordinates cG cU iU A x i) := by
  have hx : (cU.equiv B).symm (fun i => f.hom (x i)) =
      lieKernelMapLinear U f.hom ((cU.equiv A).symm x) := by
    apply (cU.equiv B).injective
    rw [LinearEquiv.apply_symm_apply, cU.naturality, LinearEquiv.apply_symm_apply]
  change cG.equiv B (Lie.targetMapLinear iU B
      ((cU.equiv B).symm (fun i => f.hom (x i)))) = _
  rw [hx, lieKernelTargetLinear_map, cG.naturality]
  rfl

/-- The decomposable exterior vector of the included `Lie U` basis. -/
def adjointExteriorVector (iU : U ⟶ G) (A : CommAlgCat.{u} R) :
    ⋀[A]^d (Fin N → A) :=
  exteriorPower.ιMulti A d
    (fun i => lieInclusionCoordinates cG cU iU A (Pi.basisFun A (Fin d) i))

/-- Monomorphisms give injective actual Lie inclusion coordinates. -/
theorem lieInclusionCoordinates_injective [Mono iU.hom.hom]
    (A : CommAlgCat.{u} R) :
    Function.Injective (lieInclusionCoordinates cG cU iU A) :=
  (cG.equiv A).injective.comp
    ((Lie.targetMapLinear_injective iU A).comp (cU.equiv A).symm.injective)

/-- Over a field the actual top exterior vector is nonzero, including in
degree zero. -/
theorem adjointExteriorVector_ne_zero [Mono iU.hom.hom]
    (A : CommAlgCat.{u} R) (hA : IsField A) :
    adjointExteriorVector cG cU iU A ≠ 0 := by
  let := hA.toField
  let w := Chevalley.exteriorLineVector (Pi.basisFun A (Fin d)) (Function.Embedding.refl _)
  have hw : w ≠ 0 := by
    intro h
    have hh := congrArg
      (Chevalley.exteriorLineFunctional (Pi.basisFun A (Fin d))
        (Function.Embedding.refl _)) h
    exact one_ne_zero (by
      simpa only [w, Chevalley.exteriorLineFunctional_apply, map_zero] using hh)
  have hj := exteriorPower.map_injective_field (n := d)
    (lieInclusionCoordinates_injective cG cU (iU := iU) A)
  have he : exteriorPower.map d (lieInclusionCoordinates cG cU iU A) w =
      adjointExteriorVector cG cU iU A := by
    simp only [w, Chevalley.exteriorLineVector, exteriorPower.map_apply_ιMulti,
      adjointExteriorVector, Function.comp_def, Function.Embedding.refl_apply]
  intro h
  apply hw
  apply hj
  rw [he, h, map_zero]

/-- The actual determinant vector in the finite matrix coordinates of the
ambient exterior representation. -/
def adjointExteriorCoordinates (iU : U ⟶ G) (A : CommAlgCat.{u} R) :
    Set.powersetCard (Fin N) d → A :=
  (Chevalley.matrixExteriorBasis N d A).equivFun (adjointExteriorVector cG cU iU A)

/-- The exterior coordinates are the minors of the actual Lie inclusion. -/
theorem adjointExteriorCoordinates_apply (A : CommAlgCat.{u} R)
    (s : Set.powersetCard (Fin N) d) :
    adjointExteriorCoordinates cG cU iU A s =
      (Matrix.of fun i j : Fin d => lieInclusionCoordinates cG cU iU A
        (Pi.basisFun A (Fin d) i) (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
  simp only [adjointExteriorCoordinates, Basis.equivFun_apply,
    Chevalley.matrixExteriorBasis, exteriorPower.basis_repr_apply,
    adjointExteriorVector, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/-- The coordinate vector is defined over the base and commutes with every
coefficient map, including nonreduced test algebras. -/
theorem adjointExteriorCoordinates_naturality {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) :
    adjointExteriorCoordinates cG cU iU B =
      fun s => f.hom (adjointExteriorCoordinates cG cU iU A s) := by
  funext s
  rw [adjointExteriorCoordinates_apply, adjointExteriorCoordinates_apply,
    AlgHom.map_det]
  congr 1
  ext i j
  have hb : (Pi.basisFun B (Fin d) i) =
      fun l => f.hom (Pi.basisFun A (Fin d) i l) := by
    funext l
    by_cases hl : l = i <;> simp [Pi.basisFun_apply, hl]
  change lieInclusionCoordinates cG cU iU B (Pi.basisFun B (Fin d) i)
      (Set.powersetCard.ofFinEmbEquiv.symm s j) =
    f.hom (lieInclusionCoordinates cG cU iU A (Pi.basisFun A (Fin d) i)
      (Set.powersetCard.ofFinEmbEquiv.symm s j))
  rw [hb, lieInclusionCoordinates_naturality]

theorem adjointExteriorCoordinates_ne_zero [Mono iU.hom.hom]
    (A : CommAlgCat.{u} R) (hA : IsField A) :
    adjointExteriorCoordinates cG cU iU A ≠ 0 := by
  intro h
  apply adjointExteriorVector_ne_zero cG cU (iU := iU) A hA
  exact (Chevalley.matrixExteriorBasis N d A).equivFun.injective
    (h.trans (map_zero _).symm)

/-- In finite coordinates the actual Lie inclusion intertwines the same actions. -/
theorem lieInclusionCoordinates_parabolicAdjoint (A : CommAlgCat.{u} R)
    (p : P.affinePoints A) (x : Fin d → A) :
    (Lie.adjointRepresentation cG).affineAction A (p ≫ iP.hom.hom)
        (lieInclusionCoordinates cG cU iU A x) =
      lieInclusionCoordinates cG cU iU A
        ((parabolicAdjointAction hP hU).coordinateAction cU A p x) := by
  change (Lie.adjointRepresentation cG).affineAction A (p ≫ iP.hom.hom)
      (cG.equiv A (Lie.targetMapLinear iU A ((cU.equiv A).symm x))) =
    cG.equiv A (Lie.targetMapLinear iU A
      ((cU.equiv A).symm
        (cU.equiv A ((parabolicAdjointAction hP hU).differential p
          ((cU.equiv A).symm x)))))
  rw [Lie.adjointRepresentation_affineAction, LinearEquiv.symm_apply_apply,
    targetMapLinear_parabolicAdjoint hP hU]

/-- The ambient exterior action on this vector has exactly the actual Lie
determinant eigenvalue, on every affine test algebra. -/
theorem adjointExteriorVector_action (A : CommAlgCat.{u} R) (p : P.affinePoints A) :
    exteriorPower.map d
        ((Lie.adjointRepresentation cG).affineAction A (p ≫ iP.hom.hom)).toLinearMap
        (adjointExteriorVector cG cU iU A) =
      (LinearEquiv.det ((parabolicAdjointAction hP hU).differential p) : A) •
        adjointExteriorVector cG cU iU A := by
  have h := Chevalley.exteriorPower_map_image_basis (Pi.basisFun A (Fin d))
    (lieInclusionCoordinates cG cU iU A)
    ((parabolicAdjointAction hP hU).coordinateAction cU A p).toLinearMap
    ((Lie.adjointRepresentation cG).affineAction A (p ≫ iP.hom.hom)).toLinearMap
    (lieInclusionCoordinates_parabolicAdjoint hP hU cG cU A p)
  have hd :
      LinearMap.det ((parabolicAdjointAction hP hU).coordinateAction cU A p).toLinearMap =
        (LinearEquiv.det ((parabolicAdjointAction hP hU).differential p) : A) := by
    rw [← LinearEquiv.coe_det]
    exact congrArg Units.val
      (LinearEquiv.det_conj ((parabolicAdjointAction hP hU).differential p) (cU.equiv A))
  simpa only [hd, adjointExteriorVector] using h

variable [IsAffine P.X.left]

/-- The scalar in the exterior line is the published actual algebraic
parabolic adjoint determinant character. -/
theorem adjointExteriorVector_character_action
    (A : CommAlgCat.{u} R) (p : P.affinePoints A) :
    exteriorPower.map d
        ((Lie.adjointRepresentation cG).affineAction A (p ≫ iP.hom.hom)).toLinearMap
        (adjointExteriorVector cG cU iU A) =
      (@Units.val A _ (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
        (p ≫ (adjointDeterminantCharacter hP hU cU).toMul.hom.hom))) •
        adjointExteriorVector cG cU iU A := by
  rw [adjointDeterminantCharacter_affinePoints]
  exact adjointExteriorVector_action hP hU cG cU A p

/-- On every affine test algebra the actual exterior matrix acts on the
constructed coordinate vector by the actual determinant character. -/
theorem adjointExteriorCoordinates_character_action
    (A : CommAlgCat.{u} R) (p : P.affinePoints A) :
    (adjointExteriorRepresentation cG (d := d)).affineAction A
        (p ≫ iP.hom.hom) (adjointExteriorCoordinates cG cU iU A) =
      (@Units.val A _ (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom
        (p ≫ (adjointDeterminantCharacter hP hU cU).toMul.hom.hom))) •
        adjointExteriorCoordinates cG cU iU A := by
  simp only [adjointExteriorCoordinates, adjointExteriorRepresentation,
    Chevalley.exteriorRepresentation_affineAction,
    adjointExteriorVector_character_action hP hU cG cU, map_smul]

end Langlands.GroupScheme.Dynamic
