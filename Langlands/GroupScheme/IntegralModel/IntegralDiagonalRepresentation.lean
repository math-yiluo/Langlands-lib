import Langlands.GroupScheme.IntegralLinearEmbedding.Comodule
import Langlands.GroupScheme.IntegralLinearEmbedding.Diagonalization
import Langlands.GroupScheme.IntegralModel.LocalIntegralSeparation
import Langlands.GroupScheme.IntegralModel.IwasawaCellLinear
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange

/-! # A diagonal integral matrix representation of a local integral model -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology GaloisPointComparison AffineLinearEmbedding

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} (M : IntegralModel ↥𝒪[F] F G)

private instance repModelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- The coordinate algebra of the model, as an object of `CommAlgCat`. -/
abbrev coordAlg : CommAlgCat (CommRingCat.of ↥𝒪[F]) :=
  CommAlgCat.of (CommRingCat.of ↥𝒪[F]) (AffineCoordinateRing ↥𝒪[F] M.group.X)

/-- The spectrum of the coordinate algebra is the model. -/
def coordIso : (algSpec (CommRingCat.of ↥𝒪[F])).obj (op M.coordAlg) ≅ M.group.X :=
  (affineSchemeOverIso ↥𝒪[F] M.group.X).symm

/-- The corepresentation of the points of the model by its coordinate algebra. -/
abbrev coordCorep :=
  corepresentableBy M.group M.coordIso

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The algebra map classifying an affine point is its coordinate evaluation. -/
theorem coordCorep_homEquiv_symm_apply (A : Type u) [CommRing A] [Algebra ↥𝒪[F] A]
    (x : (algSpec (CommRingCat.of ↥𝒪[F])).obj
      (op (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) A)) ⟶ M.group.X)
    (a : AffineCoordinateRing ↥𝒪[F] M.group.X) :
    (M.coordCorep.homEquiv.symm x).hom a = affineSchemePointEquiv ↥𝒪[F] M.group.X A x a := by
  have h : CommRingCat.ofHom (M.coordCorep.homEquiv.symm x).hom.toRingHom =
      CommRingCat.ofHom (affineSchemePointEquiv ↥𝒪[F] M.group.X A x).toAlgHom.toRingHom := by
    apply Spec.map_injective
    rw [affineSchemePointEquiv_spec]
    have h1 := congrArg (fun f => f.left)
      (algSpec.fullyFaithful.map_preimage (x ≫ M.coordIso.inv))
    exact h1
  exact congrArg (fun f => f.hom a) h

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme.AffineLinearEmbedding

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) {B : CommAlgCat.{u} R}
  (j : (algSpec R).obj (op B) ≅ G.X)

theorem yonedaGrp_preimage_hom_hom {X Y : Grp (Over (Spec R))}
    (φ : yonedaGrp.obj X ⟶ yonedaGrp.obj Y) :
    (yonedaGrpFullyFaithful.preimage φ).hom.hom = φ.app (op X.X) (𝟙 X.X) := by
  conv_rhs => rw [← yonedaGrpFullyFaithful.map_preimage φ]
  exact (Category.id_comp _).symm

theorem modelIso_hom_hom_hom : (modelIso G j).hom.hom.hom = j.hom := by
  change (yonedaGrpFullyFaithful.preimage _).hom.hom = _
  rw [yonedaGrp_preimage_hom_hom]
  exact Category.id_comp j.hom

theorem modelIso_inv_hom_hom : (modelIso G j).inv.hom.hom = j.inv := by
  rw [← cancel_mono j.hom, Iso.inv_hom_id, ← modelIso_hom_hom_hom, ← Grp.comp_hom_hom,
    Iso.inv_hom_id]
  rfl

/-- The corepresentation recovers an affine point of `G` from the corresponding point of the
model. -/
theorem affinePointsEquiv_comp_inv (S : CommAlgCat R) (x : (algSpec R).obj (op S) ⟶ G.X) :
    Corepresented.affinePointsEquiv G.affinePointFunctor (corepresentableBy G j) S
      (x ≫ j.inv) = x := by
  rw [Corepresented.affinePointsEquiv_apply]
  change (algSpec R).map (algSpec.fullyFaithful.preimage (x ≫ j.inv)).unop.op ≫ j.hom = x
  rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

variable {N : ℕ} (M : Matrix (Fin N) (Fin N) B)
  (hcomul : ∀ i j', comul (corepresentableBy G j) (M i j') = ∑ l, M i l ⊗ₜ[R] M l j')
  (hcounit : ∀ i j', counit (corepresentableBy G j) (M i j') = (1 : Matrix (Fin N) (Fin N) R) i j')

/-- The matrix representation of `G` attached to matrix coefficients. -/
abbrev modelRep : MatrixRepresentation G (Fin N) :=
  (modelIso G j).inv ≫ toGLHom (corepresentableBy G j) M hcomul hcounit

/-- Its matrices are the matrix coefficients evaluated at the classifying algebra map. -/
theorem modelRep_affineMatrix_apply (S : CommAlgCat R) (x : (algSpec R).obj (op S) ⟶ G.X)
    (i j' : Fin N) :
    ((modelRep G j M hcomul hcounit).affineMatrix S x : Matrix (Fin N) (Fin N) S) i j' =
      ((corepresentableBy G j).homEquiv.symm x).hom (M i j') := by
  rw [MatrixRepresentation.affineMatrix_apply, Grp.comp_hom_hom, ← Category.assoc,
    modelIso_inv_hom_hom]
  have h := Corepresented.groupSchemeMap_affinePoints (corepresentableBy G j)
    (GeneralLinear.corepresentableBy (Fin N) R) (toGL (corepresentableBy G j) M hcomul hcounit)
    (x ≫ j.inv)
  rw [affinePointsEquiv_comp_inv] at h
  have h2 := congrArg (fun A : (GeneralLinear.functor (Fin N) R).obj S =>
    ((show GL (Fin N) S from A) : Matrix (Fin N) (Fin N) S) i j') h
  exact h2

end Langlands.GroupScheme.AffineLinearEmbedding

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology GaloisPointComparison AffineLinearEmbedding

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} (M : IntegralModel ↥𝒪[F] F G)

private instance repModelAffine' : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- Matrix coefficients over `𝒪[F]` whose entries generate the model coordinate ring. -/
theorem exists_integral_matrixCoefficients (hG : IsConnectedReductive G) :
    ∃ (N : ℕ) (Mat : Matrix (Fin N) (Fin N) M.coordAlg)
      (_ : ∀ i j, comul M.coordCorep (Mat i j) = ∑ l, Mat i l ⊗ₜ[CommRingCat.of ↥𝒪[F]] Mat l j)
      (_ : ∀ i j, counit M.coordCorep (Mat i j) =
        (1 : Matrix (Fin N) (Fin N) (CommRingCat.of ↥𝒪[F])) i j),
      Algebra.adjoin (CommRingCat.of ↥𝒪[F]) (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) =
        ⊤ := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := (bialgebra M.coordCorep).toCoalgebra
  have : IsDomain (CommRingCat.of ↥𝒪[F]) := inferInstanceAs (IsDomain ↥𝒪[F])
  have : IsPrincipalIdealRing (CommRingCat.of ↥𝒪[F]) := inferInstanceAs (IsPrincipalIdealRing ↥𝒪[F])
  have : Module.Flat (CommRingCat.of ↥𝒪[F]) M.coordAlg := M.flat_affineCoordinateRing
  have hsep : ∀ b : M.coordAlg, b ≠ 0 →
      ∃ f : Module.Dual (CommRingCat.of ↥𝒪[F]) M.coordAlg, f b ≠ 0 := by
    intro b hb
    obtain ⟨s, hs⟩ := M.exists_integralSection_apply_ne_zero hG hb
    exact ⟨(affineSchemePointEquiv ↥𝒪[F] M.group.X ↥𝒪[F]
      (rationalPointEquiv ↥𝒪[F] M.group.X s)).toAlgHom.toLinearMap, hs⟩
  obtain ⟨S, hS⟩ := (inferInstance :
    Algebra.FiniteType ↥𝒪[F] (AffineCoordinateRing ↥𝒪[F] M.group.X)).out
  obtain ⟨N, Mat, hcomul, hcounit, hspan⟩ :=
    IntegralLinearEmbedding.exists_matrix_coefficients (R := CommRingCat.of ↥𝒪[F])
      (B := M.coordAlg) hsep S
  refine ⟨N, Mat, hcomul, hcounit, ?_⟩
  rw [eq_top_iff, ← hS]
  exact Algebra.adjoin_le fun b hb => Algebra.span_le_adjoin _ _ (hspan hb)

section Generic

variable {N : ℕ}

/-- The base change to `F` of a representation of the model, as a representation of `G`. -/
def genericRep (ρ₁ : MatrixRepresentation M.group (Fin N)) : MatrixRepresentation G (Fin N) :=
  M.genericIso.inv ≫ (GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).map ρ₁ ≫
    (GeneralLinear.baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] F)).hom

/-- The `F`-valued point of the model underlying a rational point of `G`. -/
abbrev modelPoint (g : rationalPoints G) :
    (algSpec (CommRingCat.of ↥𝒪[F])).obj (op (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F)) ⟶
      M.group.X :=
  M.genericModelPointEquiv F (rationalCoeffEquiv F G g)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem baseChange_map_left_fst {H₁ H₂ : GroupScheme (Spec (CommRingCat.of ↥𝒪[F]))}
    (f : H₁ ⟶ H₂) :
    ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).map f).hom.hom.left ≫
        pullback.fst H₂.X.hom (Spec.algebraMap ↥𝒪[F] F) =
      pullback.fst H₁.X.hom (Spec.algebraMap ↥𝒪[F] F) ≫ f.hom.hom.left := by
  change ((Over.pullback (Spec.algebraMap ↥𝒪[F] F)).map f.hom.hom).left ≫ _ = _
  simp

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rationalPoints_map_genericRep (ρ₁ : MatrixRepresentation M.group (Fin N))
    (g : rationalPoints G) :
    rationalPoints.map (M.genericRep ρ₁) g =
      (g ≫ M.genericIso.inv.hom.hom ≫
        ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).map ρ₁).hom.hom) ≫
        (GeneralLinear.baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] F)).hom.hom.hom := by
  rw [rationalPoints.map_apply]
  simp only [genericRep, Grp.comp_hom_hom, Category.assoc]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
set_option maxHeartbeats 400000 in
/-- Entries of a base-changed point of `GL_N`. -/
theorem baseChangeIso_entry {T : Over (Spec (CommRingCat.of F))}
    (x : T ⟶ ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj
      (GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F]))).X) (i j : Fin N) :
    (x ≫ (GeneralLinear.baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] F)).hom.hom.hom).left.appTop
        (GeneralLinear.entrySection (Fin N) (CommRingCat.of F) i j) =
      (x.left ≫ pullback.fst _ (Spec.algebraMap ↥𝒪[F] F)).appTop
        (GeneralLinear.entrySection (Fin N) (CommRingCat.of ↥𝒪[F]) i j) := by
  have h := GeneralLinear.pointsEquiv_comp_baseChangeIso_hom (n := Fin N)
    (Spec.algebraMap ↥𝒪[F] F) x
  rw [← GeneralLinear.pointsEquiv_apply_apply, h, GeneralLinear.pointsEquiv_apply_apply]
  rfl

set_option maxHeartbeats 400000 in
/-- Entries of an affine point of `GL_N`, through the global-section comparison. -/
theorem affinePointsEquiv_entry {R : CommRingCat.{u}} (S : CommAlgCat.{u} R)
    (y : (algSpec R).obj (op S) ⟶ (GeneralLinear.groupScheme (Fin N) R).X) (i j : Fin N) :
    ((GeneralLinear.affinePointsEquiv (Fin N) R S y : GL (Fin N) S) : Matrix (Fin N) (Fin N) S)
        i j =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom
        (y.left.appTop (GeneralLinear.entrySection (Fin N) R i j)) := by
  have h := GeneralLinear.pointsEquiv_eq_affinePointsEquiv S y
  rw [← GeneralLinear.pointsEquiv_apply_apply, h]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    ((Corepresented.affineSectionsIso S).inv.hom.toRingHom
      ((GeneralLinear.affinePointsEquiv (Fin N) R S y : GL (Fin N) S) i j))
  rw [Corepresented.affineSectionsIso_inv_ringHom]
  exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of S)) _).symm

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem modelPoint_comp_left (ρ₁ : MatrixRepresentation M.group (Fin N))
    (g : rationalPoints G) :
    (M.modelPoint g ≫ ρ₁.hom.hom).left =
      (g ≫ M.genericIso.inv.hom.hom ≫
        ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).map ρ₁).hom.hom).left ≫
        pullback.fst _ (Spec.algebraMap ↥𝒪[F] F) := by
  change (M.modelPoint g).left ≫ ρ₁.hom.hom.left = _
  rw [genericModelPointEquiv_left, rationalCoeffEquiv_left]
  simp only [Over.comp_left, Category.assoc]
  congr 2
  exact (baseChange_map_left_fst ρ₁).symm

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
set_option maxHeartbeats 40000 in
/-- **Matrices of the generic representation** are the matrices of the model representation at
the underlying `F`-valued point. -/
theorem genericRep_rationalPointsEquiv (ρ₁ : MatrixRepresentation M.group (Fin N))
    (g : rationalPoints G) :
    GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
        (rationalPoints.map (M.genericRep ρ₁) g) =
      ρ₁.affineMatrix (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) (M.modelPoint g) := by
  apply Units.ext
  ext i j
  rw [GeneralLinear.rationalPointsEquiv_apply_apply]
  rw [rationalPoints_map_genericRep]
  rw [baseChangeIso_entry]
  rw [MatrixRepresentation.affineMatrix_apply]
  rw [affinePointsEquiv_entry]
  rw [modelPoint_comp_left]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The generic cocharacter followed by the generic representation is the base change of the
model cocharacter followed by the model representation. -/
theorem genericCocharacter_comp_genericRep
    (χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group)
    (ρ₁ : MatrixRepresentation M.group (Fin N)) :
    M.genericCocharacter χ ≫ M.genericRep ρ₁ =
      Dynamic.baseChangeCocharacter (Spec.algebraMap ↥𝒪[F] F) (χ ≫ ρ₁) ≫
        (GeneralLinear.baseChangeIso (Fin N) (Spec.algebraMap ↥𝒪[F] F)).hom := by
  simp only [genericCocharacter, genericRep, Dynamic.baseChangeCocharacter, Category.assoc,
    Iso.hom_inv_id_assoc, Functor.map_comp]

end Generic

section Conjugation

variable {N : ℕ}

/-- Conjugating a matrix representation by a rational matrix point conjugates its matrices. -/
theorem affineMatrix_comp_innerIso {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}
    (ρ : MatrixRepresentation H (Fin N)) (B : GL (Fin N) R) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ H.X) :
    MatrixRepresentation.affineMatrix (G := H) (n := Fin N)
        (ρ ≫ ((GeneralLinear.groupScheme (Fin N) R).innerIso
          (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint B)).hom) S x =
      Matrix.GeneralLinearGroup.map (algebraMap R S) B * ρ.affineMatrix S x *
        (Matrix.GeneralLinearGroup.map (algebraMap R S) B)⁻¹ := by
  rw [MatrixRepresentation.affineMatrix_apply, MatrixRepresentation.affineMatrix_apply,
    Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, map_mul, map_mul, map_inv,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_constant_rationalMatrixPoint]

/-- Conjugation by the image of an invertible matrix preserves the image of `GL_n`. -/
theorem conj_mem_range_map_iff {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K)
    {n : Type} [Fintype n] [DecidableEq n] (B : GL n R) (A : GL n K) :
    Matrix.GeneralLinearGroup.map f B * A * (Matrix.GeneralLinearGroup.map f B)⁻¹ ∈
        (Matrix.GeneralLinearGroup.map (n := n) f).range ↔
      A ∈ (Matrix.GeneralLinearGroup.map (n := n) f).range := by
  have hB : Matrix.GeneralLinearGroup.map f B ∈
      (Matrix.GeneralLinearGroup.map (n := n) f).range := ⟨B, rfl⟩
  rw [Subgroup.mul_mem_cancel_right _ (inv_mem hB), Subgroup.mul_mem_cancel_left _ hB]

end Conjugation

section Integrality

variable {N : ℕ} (Mat : Matrix (Fin N) (Fin N) M.coordAlg)
  (hcomul : ∀ i j, comul M.coordCorep (Mat i j) =
    ∑ l, Mat i l ⊗ₜ[CommRingCat.of ↥𝒪[F]] Mat l j)
  (hcounit : ∀ i j, counit M.coordCorep (Mat i j) =
    (1 : Matrix (Fin N) (Fin N) (CommRingCat.of ↥𝒪[F])) i j)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The entries of the model representation at an `F`-valued point are the coordinate values of
the matrix coefficients. -/
theorem modelRep_entry (x : (algSpec (CommRingCat.of ↥𝒪[F])).obj
      (op (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F)) ⟶ M.group.X) (i j : Fin N) :
    ((modelRep M.group M.coordIso Mat hcomul hcounit).affineMatrix
        (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) x : Matrix (Fin N) (Fin N) F) i j =
      affineSchemePointEquiv ↥𝒪[F] M.group.X F x (Mat i j) := by
  rw [modelRep_affineMatrix_apply]
  exact M.coordCorep_homEquiv_symm_apply F x (Mat i j)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- On a point coming from an `𝒪[F]`-point, the matrix of the model representation is integral. -/
theorem modelRep_affineMatrix_changeRing (p : RingPoint ↥𝒪[F] M.group.X ↥𝒪[F]) :
    (modelRep M.group M.coordIso Mat hcomul hcounit).affineMatrix
        (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) (p.changeRing (Algebra.ofId ↥𝒪[F] F)) ∈
      (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap ↥𝒪[F] F)).range := by
  have h := MatrixRepresentation.affineMatrix_naturality
    (modelRep M.group M.coordIso Mat hcomul hcounit)
    (CommAlgCat.ofHom (Algebra.ofId (CommRingCat.of ↥𝒪[F]) F) :
      CommAlgCat.of (CommRingCat.of ↥𝒪[F]) (CommRingCat.of ↥𝒪[F]) ⟶
        CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) p
  exact ⟨_, h.symm⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- **Integrality is detected by the model representation** when its matrix coefficients
generate the coordinate ring. -/
theorem mem_integralPoints_iff_modelRep
    (hadj : Algebra.adjoin (CommRingCat.of ↥𝒪[F])
      (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) = ⊤)
    (g : rationalPoints G) :
    g ∈ M.integralPoints ↔
      (modelRep M.group M.coordIso Mat hcomul hcounit).affineMatrix
          (CommAlgCat.of (CommRingCat.of ↥𝒪[F]) F) (M.modelPoint g) ∈
        (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap ↥𝒪[F] F)).range := by
  constructor
  · rintro ⟨s, rfl⟩
    have h := M.genericModelPointEquiv_integralPointMap s
    change M.modelPoint (M.integralPointMap s) = _ at h
    rw [h]
    exact modelRep_affineMatrix_changeRing M Mat hcomul hcounit _
  · rintro ⟨C, hC⟩
    rw [mem_integralPoints_iff_genericCoordinates]
    intro a
    rw [← genericModelPointEquiv_evaluation]
    let φ := (affineSchemePointEquiv ↥𝒪[F] M.group.X F (M.modelPoint g)).toAlgHom
    have hgen : ∀ b ∈ Set.range fun p : Fin N × Fin N => Mat p.1 p.2,
        b ∈ (⊥ : Subalgebra ↥𝒪[F] F).comap φ := by
      rintro _ ⟨⟨i, j⟩, rfl⟩
      rw [Subalgebra.mem_comap, Algebra.mem_bot]
      refine ⟨C i j, ?_⟩
      have h1 := congrArg (fun A : GL (Fin N) F => (A : Matrix (Fin N) (Fin N) F) i j) hC
      simp only [Matrix.GeneralLinearGroup.map_apply] at h1
      rw [h1, modelRep_entry]
      rfl
    have hle : Algebra.adjoin ↥𝒪[F] (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) ≤
        (⊥ : Subalgebra ↥𝒪[F] F).comap φ := Algebra.adjoin_le hgen
    have ha : a ∈ Algebra.adjoin ↥𝒪[F] (Set.range fun p : Fin N × Fin N => Mat p.1 p.2) := by
      change a ∈ Algebra.adjoin (CommRingCat.of ↥𝒪[F]) _
      rw [hadj]
      trivial
    have := hle ha
    rw [Subalgebra.mem_comap, Algebra.mem_bot] at this
    exact this

end Integrality

/-- **The integral diagonal representation.** -/
theorem integralDiagonalRepresentation : IntegralDiagonalRepresentationStatement.{u} := by
  intro F _ _ _ _ G hG M _ χ
  obtain ⟨N, Mat, hcomul, hcounit, hadj⟩ := M.exists_integral_matrixCoefficients hG
  obtain ⟨B, e, hB⟩ :=
    GeneralLinear.exists_innerIso_comp_eq_diagonalCocharacter_of_isPrincipalIdealRing ↥𝒪[F]
      (χ ≫ modelRep M.group M.coordIso Mat hcomul hcounit)
  refine ⟨N, M.genericRep (modelRep M.group M.coordIso Mat hcomul hcounit ≫
    ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of ↥𝒪[F])).innerIso
      (GeneralLinear.CocharacterDiagonal.rationalMatrixPoint
        (R := CommRingCat.of ↥𝒪[F]) B)).hom), e, ?_, ?_⟩
  · rw [genericCocharacter_comp_genericRep, ← Category.assoc, hB,
      GeneralLinear.baseChangeCocharacter_diagonalCocharacter]
  · intro g
    rw [genericRep_rationalPointsEquiv, affineMatrix_comp_innerIso]
    exact (M.mem_integralPoints_iff_modelRep Mat hcomul hcounit hadj g).trans
      (conj_mem_range_map_iff _ B _).symm

end Langlands.GroupScheme.IntegralModel
