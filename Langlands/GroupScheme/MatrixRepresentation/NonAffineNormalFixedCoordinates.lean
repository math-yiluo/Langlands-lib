import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.MatrixRepresentation.SchemeAction
import Langlands.GroupScheme.ElementaryOrbitLimit
import Langlands.GroupScheme.Reductive.UnipotentExtension

/-! # Fixed coordinates of normal subgroups without affineness -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

/-- Equality of global sections can be detected on all affine relative tests. -/
theorem section_eq_of_affine_tests
    {T : Over (Spec (CommRingCat.of k))} {s t : Γ(T.left, ⊤)}
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (a : (algSpec (CommRingCat.of k)).obj (op A) ⟶ T),
      a.left.appTop s = a.left.appTop t) : s = t := by
  have he : coefficientPoint T (fun _ : Unit => s) =
      coefficientPoint T (fun _ : Unit => t) := by
    apply OrbitLimit.hom_ext_of_algebraSpec
    intro A _ _ a
    apply coefficientCoordinates_injective
    rw [coefficientCoordinates_comp, coefficientCoordinates_comp,
      coefficientCoordinates_coefficientPoint, coefficientCoordinates_coefficientPoint]
    funext r
    exact h (CommAlgCat.of (CommRingCat.of k) A) a
  simpa only [coefficientCoordinates_coefficientPoint] using
    congrFun (congrArg coefficientCoordinates he) ()

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Fixedness on all affine tests implies fixedness on every scheme test. -/
theorem isFixedVector_of_affine_tests (ρ : MatrixRepresentation G n) (v : n → k)
    (h : ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
      (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X),
      (ρ.affineMatrix A x : Matrix n n A) *ᵥ (fun i => algebraMap k A (v i)) =
        (fun i => algebraMap k A (v i))) :
    ρ.IsFixedVector v := by
  intro T x
  funext r
  apply section_eq_of_affine_tests
  intro A a
  have hf := (affine_fixed_iff ρ A (a ≫ x) v).2 (h A (a ≫ x))
  have hn := ρ.pointMatrix_naturality a x
  have hs : (fun i => a.left.appTop (scalarMap T (v i))) =
      (fun i => scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v i)) := by
    funext i
    exact scalarMap_naturality a _
  rw [a.left.appTop.hom.map_mulVec]
  change ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)).map a.left.appTop.hom *ᵥ
    (fun j => a.left.appTop (scalarMap T (v j)))) r = _
  rw [hs, scalarMap_naturality a]
  rw [hn] at hf
  exact congrFun hf r

/-- Normality puts every linear coefficient of an affine translate in the
original all-test fixed subspace, without an affine model of the subgroup. -/
theorem normal_fixed_coefficient_of_affine_tests
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    {v : n → k} (hv : (ρ.restrict i).IsFixedVector v)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (ℓ : A →ₗ[k] k) :
    (ρ.restrict i).IsFixedVector
      (fun a => ℓ (((ρ.affineMatrix A g : Matrix n n A) *ᵥ
        (fun b => algebraMap k A (v b))) a)) := by
  apply isFixedVector_of_affine_tests
  intro B h
  let D := CommAlgCat.of (CommRingCat.of k) (A ⊗[k] B)
  let a : A ⟶ D := CommAlgCat.ofHom Algebra.TensorProduct.includeLeft
  let b : B ⟶ D := CommAlgCat.ofHom Algebra.TensorProduct.includeRight
  let gD := (algSpec (CommRingCat.of k)).map a.op ≫ g
  let hD := (algSpec (CommRingCat.of k)).map b.op ≫ h
  have ht := normal_fixed_affine ρ i hN hv D gD hD
  have hg : ρ.affineMatrix D gD =
      Matrix.GeneralLinearGroup.map a.hom.toRingHom (ρ.affineMatrix A g) :=
    ρ.affineMatrix_naturality a g
  have hh : ρ.affineMatrix D (hD ≫ i.hom.hom) =
      Matrix.GeneralLinearGroup.map b.hom.toRingHom
        ((ρ.restrict i).affineMatrix B h) := by
    dsimp only [hD]
    rw [Category.assoc, affineMatrix_naturality, affineMatrix_restrict]
  rw [hg, hh] at ht
  have hvec :
      ((Matrix.GeneralLinearGroup.map a.hom.toRingHom (ρ.affineMatrix A g) :
        GL n D) : Matrix n n D) *ᵥ (fun r => algebraMap k D (v r)) =
      (fun r => a.hom
        (((ρ.affineMatrix A g : Matrix n n A) *ᵥ
          (fun s => algebraMap k A (v s))) r)) := by
    funext r
    change (((ρ.affineMatrix A g : Matrix n n A).map a.hom.toRingHom) *ᵥ
      (fun s => algebraMap k D (v s))) r =
        a.hom.toRingHom
          (((ρ.affineMatrix A g : Matrix n n A) *ᵥ
            (fun s => algebraMap k A (v s))) r)
    rw [a.hom.toRingHom.map_mulVec]
    congr 2
  rw [hvec] at ht
  exact fixed_tensor_coefficients
    ((ρ.restrict i).affineMatrix B h : Matrix n n B)
    ((ρ.affineMatrix A g : Matrix n n A) *ᵥ (fun r => algebraMap k A (v r))) ht ℓ

/-- Split coordinates spanning the fixed subspace of a normal subgroup
are stable on every relative scheme test. -/
theorem normal_fixed_coordinates_of_affine_tests
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (B : Matrix n m k) (C : Matrix m n k)
    (hcols : ∀ s, (ρ.restrict i).IsFixedVector (fun r => B r s))
    (hproj : ∀ v, (ρ.restrict i).IsFixedVector v → (B * C) *ᵥ v = v) :
    ρ.IsStableCoordinates B C := by
  have ha (A : CommAlgCat.{u} (CommRingCat.of k))
      (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
      (ρ.affineMatrix A g : Matrix n n A) * B.map (algebraMap k A) =
        B.map (algebraMap k A) *
          (C.map (algebraMap k A) * (ρ.affineMatrix A g : Matrix n n A) *
            B.map (algebraMap k A)) := by
    have he : (ρ.affineMatrix A g : Matrix n n A) * B.map (algebraMap k A) =
        (B * C).map (algebraMap k A) *
          ((ρ.affineMatrix A g : Matrix n n A) * B.map (algebraMap k A)) := by
      ext r s
      have hs := projection_mulVec_eq_of_coefficients (B * C)
        ((ρ.affineMatrix A g : Matrix n n A) *ᵥ
          (fun a => algebraMap k A (B a s)))
        (fun ℓ => hproj _ (normal_fixed_coefficient_of_affine_tests
          ρ i hN (hcols s) A g ℓ))
      exact (congrFun hs r).symm
    rw [Matrix.map_mul] at he
    simpa only [Matrix.mul_assoc] using he
  intro T x
  ext r s
  apply section_eq_of_affine_tests
  intro A a
  let e : A →+* Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) :=
    (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have h₀ := congrArg (fun M : Matrix n m A => M.map e) (ha A (a ≫ x))
  simp only [Matrix.map_mul, Matrix.map_map] at h₀
  have hB : B.map (e ∘ algebraMap k A) =
      B.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  have hC : C.map (e ∘ algebraMap k A) =
      C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  rw [hB, hC] at h₀
  have hM := congrArg (fun U : GL n Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) =>
    (U : Matrix n n Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤))) (ρ.pointMatrix_naturality a x)
  rw [pointMatrix_eq_affineMatrix] at hM
  change (ρ.affineMatrix A (a ≫ x) : Matrix n n A).map e =
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)).map a.left.appTop.hom at hM
  rw [hM] at h₀
  have hB' : (B.map (scalarMap T)).map a.left.appTop.hom =
      B.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact scalarMap_naturality a _
  have hC' : (C.map (scalarMap T)).map a.left.appTop.hom =
      C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact scalarMap_naturality a _
  change (((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
    B.map (scalarMap T)).map a.left.appTop.hom) r s =
    ((B.map (scalarMap T) * (C.map (scalarMap T) *
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T))).map
      a.left.appTop.hom) r s
  rw [Matrix.map_mul, hB']
  have h₁ := congrFun (congrFun h₀ r) s
  simpa only [Matrix.map_mul, hB', hC'] using h₁

/-- The actual fixed-subspace representation of a normal subgroup, with
supplied split coordinates and no affine-source assumptions. -/
def normalFixedCoordinates
    (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hcols : ∀ s, (ρ.restrict i).IsFixedVector (fun r => B r s))
    (hproj : ∀ v, (ρ.restrict i).IsFixedVector v → (B * C) *ᵥ v = v) :
    MatrixRepresentation G m :=
  ρ.restrictCoordinates B C hCB
    (normal_fixed_coordinates_of_affine_tests ρ i hN B C hcols hproj)

end Langlands.GroupScheme.MatrixRepresentation
