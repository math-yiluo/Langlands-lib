import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Chevalley.ExteriorLine

/-! # Exterior powers of actual matrix representations -/

noncomputable section

open Module CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix Classical

namespace Langlands.GroupScheme.Chevalley

variable (N d : ℕ) (A : Type*) [CommRing A]

/-- The exterior-power basis of the standard finite free module. -/
def matrixExteriorBasis :
    Basis (Set.powersetCard (Fin N) d) A (⋀[A]^d (Fin N → A)) :=
  (Pi.basisFun A (Fin N)).exteriorPower d

/-- Exterior powers, expressed in their finite basis, give a multiplicative matrix map. -/
def exteriorMatrixHom :
    GL (Fin N) A →* Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) A where
  toFun g := LinearMap.toMatrix (matrixExteriorBasis N d A) (matrixExteriorBasis N d A)
    (exteriorPower.map d (Matrix.toLin' (g : Matrix (Fin N) (Fin N) A)))
  map_one' := by
    simp [Matrix.toLin'_one, exteriorPower.map_id]
  map_mul' g h := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.toLin'_mul, exteriorPower.map_comp,
      LinearMap.toMatrix_comp (matrixExteriorBasis N d A) (matrixExteriorBasis N d A)
        (matrixExteriorBasis N d A)]

/-- The resulting matrices are invertible because the source is a group. -/
def exteriorGL : GL (Fin N) A →* GL (Set.powersetCard (Fin N) d) A :=
  (exteriorMatrixHom N d A).toHomUnits

theorem exteriorGL_val (g : GL (Fin N) A) :
    (exteriorGL N d A g :
      Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) A) =
      LinearMap.toMatrix (matrixExteriorBasis N d A) (matrixExteriorBasis N d A)
        (exteriorPower.map d (Matrix.toLin' (g : Matrix (Fin N) (Fin N) A))) := rfl

/-- The entries are the actual determinant polynomials in the original matrix entries. -/
theorem exteriorGL_apply (g : GL (Fin N) A)
    (s t : Set.powersetCard (Fin N) d) :
    exteriorGL N d A g s t =
      (Matrix.of fun i j : Fin d =>
        g (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (Set.powersetCard.ofFinEmbEquiv.symm t i)).det := by
  rw [show exteriorGL N d A g s t =
    LinearMap.toMatrix (matrixExteriorBasis N d A) (matrixExteriorBasis N d A)
      (exteriorPower.map d (Matrix.toLin' (g : Matrix (Fin N) (Fin N) A))) s t from rfl]
  rw [LinearMap.toMatrix_apply]
  simp only [matrixExteriorBasis, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Function.comp_apply]
  congr 1
  ext i j
  simp [Basis.coord_apply, Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single]

variable {N d A}

/-- Exterior matrices commute with every homomorphism of coefficient rings. -/
theorem exteriorGL_naturality {A' : Type*} [CommRing A'] (f : A →+* A')
    (g : GL (Fin N) A) :
    exteriorGL N d A' (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (exteriorGL N d A g) := by
  apply Units.ext
  ext s t
  rw [exteriorGL_apply]
  change _ = f (exteriorGL N d A g s t)
  rw [exteriorGL_apply, RingHom.map_det]
  rfl

/-- The distinguished exterior basis vector detects preservation of the selected
coordinate subspace, by a unit-scalar equation in actual matrix coordinates. -/
theorem exteriorGL_basisLine_iff (s : Fin d ↪o Fin N) (g : GL (Fin N) A) :
    (∃ u : Aˣ,
      (exteriorGL N d A g :
        Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) A) *ᵥ
          Pi.single (Set.powersetCard.ofFinEmbEquiv s) 1 =
        (u : A) • Pi.single (Set.powersetCard.ofFinEmbEquiv s) 1) ↔
      ∀ v : Fin N → A, v ∈ coordinateSpan (Pi.basisFun A (Fin N)) s.toEmbedding →
        (g : Matrix (Fin N) (Fin N) A) *ᵥ v ∈
          coordinateSpan (Pi.basisFun A (Fin N)) s.toEmbedding := by
  let b := matrixExteriorBasis N d A
  let t := Set.powersetCard.ofFinEmbEquiv s
  let e : (Fin N → A) ≃ₗ[A] (Fin N → A) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv A _ (Matrix.GeneralLinearGroup.toLin g)
  have hl : b t = exteriorLineVector (Pi.basisFun A (Fin N)) s.toEmbedding := by
    simp [b, t, matrixExteriorBasis, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, exteriorLineVector, Function.comp_def]
  have he : e.toLinearMap = Matrix.toLin' (g : Matrix (Fin N) (Fin N) A) := rfl
  have hm (a : A) :
      (exteriorGL N d A g :
        Matrix (Set.powersetCard (Fin N) d) (Set.powersetCard (Fin N) d) A) *ᵥ
          Pi.single t 1 = a • Pi.single t 1 ↔
        exteriorPower.map d e.toLinearMap (b t) = a • b t := by
    rw [exteriorGL_val, ← he]
    have hdelta (j : Set.powersetCard (Fin N) d) :
        (Pi.single t (1 : A) : _ → A) j = (Finsupp.single t (1 : A)) j := by
      by_cases hj : j = t
      · subst j
        simp
      · simp [hj]
    constructor
    · intro h
      apply b.repr.injective
      ext j
      have hj := congrFun h j
      simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
        LinearMap.toMatrix_apply, Pi.smul_apply, smul_eq_mul] at hj
      change b.repr (exteriorPower.map d e.toLinearMap (b t)) j =
        a * (Pi.single t (1 : A) : _ → A) j at hj
      simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
      rw [← hdelta j]
      exact hj
    · intro h
      funext j
      have hj := congrArg (fun v => b.repr v j) h
      simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul] at hj
      simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
        LinearMap.toMatrix_apply, Pi.smul_apply, smul_eq_mul]
      change b.repr (exteriorPower.map d e.toLinearMap (b t)) j =
        a * (Pi.single t (1 : A) : _ → A) j
      rw [hdelta j]
      exact hj
  constructor
  · rintro ⟨u, hu⟩
    apply (preserves_coordinateSpan_iff (Pi.basisFun A (Fin N)) s.toEmbedding e).mpr
    refine ⟨u, ?_⟩
    rw [← hl]
    exact (hm u).mp hu
  · intro hg
    obtain ⟨u, hu⟩ :=
      (preserves_coordinateSpan_iff (Pi.basisFun A (Fin N)) s.toEmbedding e).mp hg
    refine ⟨u, (hm u).mpr ?_⟩
    rwa [hl]

universe u

variable (R : CommRingCat.{u}) (N d)

/-- Exterior power is a natural homomorphism of the actual general linear functors. -/
def exteriorNat :
    GeneralLinear.functor (Fin N) R ⟶
      GeneralLinear.functor (Set.powersetCard (Fin N) d) R where
  app A := GrpCat.ofHom (exteriorGL N d A)
  naturality A A' f := by
    ext g : 2
    exact exteriorGL_naturality f.hom.toRingHom g

/-- The corresponding actual group-scheme homomorphism. -/
def exteriorGroupHom :
    GeneralLinear.groupScheme (Fin N) R ⟶
      GeneralLinear.groupScheme (Set.powersetCard (Fin N) d) R :=
  Corepresented.groupSchemeMap (GeneralLinear.corepresentableBy (Fin N) R)
    (GeneralLinear.corepresentableBy (Set.powersetCard (Fin N) d) R) (exteriorNat N d R)

/-- The exterior power of an actual finite matrix representation. -/
def exteriorRepresentation {G : GroupScheme (Spec R)} (ρ : MatrixRepresentation G (Fin N)) :
    MatrixRepresentation G (Set.powersetCard (Fin N) d) :=
  ρ ≫ exteriorGroupHom N d R

/-- The exterior representation has exactly the exterior matrix on every scheme test. -/
theorem exteriorRepresentation_pointMatrix {G : GroupScheme (Spec R)}
    (ρ : MatrixRepresentation G (Fin N)) (T : Over (Spec R)) (x : T ⟶ G.X) :
    (exteriorRepresentation N d R ρ).pointMatrix T x =
      exteriorGL N d Γ(T.left, ⊤) (ρ.pointMatrix T x) := by
  exact Corepresented.groupSchemeMap_points
    (GeneralLinear.corepresentableBy (Fin N) R)
    (GeneralLinear.corepresentableBy (Set.powersetCard (Fin N) d) R)
    (exteriorNat N d R) (x ≫ ρ.hom.hom)

end Langlands.GroupScheme.Chevalley
