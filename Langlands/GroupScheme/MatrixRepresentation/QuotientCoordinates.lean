import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation

/-! # Actual quotient representations in split coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section Coordinates

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Split quotient coordinates intertwine the ambient action on every test. -/
def IsQuotientCoordinates (ρ : MatrixRepresentation G n)
    (Q : Matrix m n R) (D : Matrix n m R) : Prop :=
  ∀ (T : Over (Spec R)) (x : T ⟶ G.X),
    Q.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) =
      (Q.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
        D.map (scalarMap T)) * Q.map (scalarMap T)

variable (ρ : MatrixRepresentation G n) (Q : Matrix m n R) (D : Matrix n m R)
  (hQD : Q * D = 1) (hquot : ρ.IsQuotientCoordinates Q D)

/-- The induced action in split quotient coordinates. -/
def quotientMatrixHom (T : Over (Spec R)) :
    (T ⟶ G.X) →* Matrix m m Γ(T.left, ⊤) where
  toFun x := Q.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
    D.map (scalarMap T)
  map_one' := by
    rw [map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one,
      ← Matrix.map_mul, hQD, Matrix.map_one _ (map_zero _) (map_one _)]
  map_mul' x y := by
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul]
    calc
      _ = (Q.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤))) *
          ((ρ.pointMatrix T y : Matrix n n Γ(T.left, ⊤)) * D.map (scalarMap T)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        have h := congrArg
          (fun A => A * ((ρ.pointMatrix T y : Matrix n n Γ(T.left, ⊤)) *
            D.map (scalarMap T))) (hquot T x)
        simpa only [Matrix.mul_assoc] using h

/-- The quotient matrices commute with pullback on scheme tests. -/
theorem quotientMatrixHom_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    quotientMatrixHom ρ Q D hQD hquot T' (a ≫ x) =
      (quotientMatrixHom ρ Q D hQD hquot T x).map a.left.appTop.hom := by
  change Q.map (scalarMap T') * (ρ.pointMatrix T' (a ≫ x) : Matrix n n Γ(T'.left, ⊤)) *
    D.map (scalarMap T') =
      (Q.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
        D.map (scalarMap T)).map a.left.appTop.hom
  rw [pointMatrix_naturality, Matrix.map_mul, Matrix.map_mul]
  change Q.map (scalarMap T') *
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)).map a.left.appTop.hom *
      D.map (scalarMap T') = _
  have hQ : Q.map (scalarMap T') =
      (Q.map (scalarMap T)).map a.left.appTop.hom := by
    ext i j
    exact (scalarMap_naturality a _).symm
  have hD : D.map (scalarMap T') =
      (D.map (scalarMap T)).map a.left.appTop.hom := by
    ext i j
    exact (scalarMap_naturality a _).symm
  rw [hQ, hD]

/-- The quotient action as an actual natural family of general-linear points. -/
def quotientPoints (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme m R).X) :=
  (GeneralLinear.pointsEquiv m R T).symm.toMonoidHom.comp
    (quotientMatrixHom ρ Q D hQD hquot T).toHomUnits

/-- The quotient point action is natural. -/
theorem quotientPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    quotientPoints ρ Q D hQD hquot T' (a ≫ x) =
      a ≫ quotientPoints ρ Q D hQD hquot T x := by
  apply (GeneralLinear.pointsEquiv m R T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [quotientPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change (quotientMatrixHom ρ Q D hQD hquot T').toHomUnits (a ≫ x) =
    Matrix.GeneralLinearGroup.map a.left.appTop.hom
      ((quotientMatrixHom ρ Q D hQD hquot T).toHomUnits x)
  apply Units.ext
  exact quotientMatrixHom_naturality ρ Q D hQD hquot a x

/-- The actual representation on the chosen quotient coordinates. -/
def quotientCoordinates : MatrixRepresentation G m :=
  homOfPoints (quotientPoints ρ Q D hQD hquot)
    (quotientPoints_naturality ρ Q D hQD hquot)

/-- The quotient representation realizes the prescribed matrices on all tests. -/
theorem quotientCoordinates_pointMatrix (T : Over (Spec R)) (x : T ⟶ G.X) :
    (quotientCoordinates ρ Q D hQD hquot).pointMatrix T x =
      (quotientMatrixHom ρ Q D hQD hquot T).toHomUnits x := by
  rw [pointMatrix_apply, quotientCoordinates, comp_homOfPoints]
  exact (GeneralLinear.pointsEquiv m R T).apply_symm_apply _

/-- The quotient projection intertwines the actual actions on every test. -/
theorem quotientCoordinates_intertwines (T : Over (Spec R)) (x : T ⟶ G.X) :
    Q.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) =
      ((quotientCoordinates ρ Q D hQD hquot).pointMatrix T x :
        Matrix m m Γ(T.left, ⊤)) * Q.map (scalarMap T) := by
  rw [quotientCoordinates_pointMatrix]
  exact hquot T x

end Coordinates

section StableKernel

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A stable kernel makes any split quotient coordinates equivariant. -/
theorem IsStableSubspace.isQuotientCoordinates [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)}
    (hV : IsStableSubspace ρ V) (Q : Matrix m n k) (D : Matrix n m k)
    (hQD : Q * D = 1) (hker : LinearMap.ker Q.mulVecLin = V) :
    ρ.IsQuotientCoordinates Q D := by
  classical
  obtain ⟨r, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B C hcols hproj
  have hQB : Q * B = 0 := by
    ext i j
    change (Q *ᵥ (fun a => B a j)) i = 0
    exact congrFun
      (show Q *ᵥ (fun a => B a j) = 0 from
        (show (fun a => B a j) ∈ LinearMap.ker Q.mulVecLin from hker ▸ hcols j)) i
  let P := 1 - D * Q
  have hQP : Q * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQD,
      Matrix.one_mul, sub_self]
  have hBCP : B * C * P = P := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec]
    apply hproj
    rw [← hker]
    change Q *ᵥ (P *ᵥ Pi.single j 1) = 0
    rw [Matrix.mulVec_mulVec, hQP, Matrix.zero_mulVec]
  intro T x
  let f := scalarMap T
  let M : Matrix n n Γ(T.left, ⊤) := ρ.pointMatrix T x
  have hQP' : Q.map f * B.map f = 0 := by
    rw [← Matrix.map_mul, hQB, Matrix.map_zero _ (map_zero _)]
  have hBCP' : B.map f * C.map f * P.map f = P.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hBCP]
  have hMP : M * P.map f = B.map f * (C.map f * M * P.map f) := by
    calc
      _ = M * (B.map f * C.map f * P.map f) := by rw [hBCP']
      _ = (M * B.map f) * (C.map f * P.map f) := by
        simp only [Matrix.mul_assoc]
      _ = (B.map f * (C.map f * M * B.map f)) *
          (C.map f * P.map f) := by rw [hstable T x]
      _ = _ := by
        calc
          _ = B.map f * (C.map f * M * (B.map f * C.map f * P.map f)) := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [hBCP']
  have hQMP : Q.map f * M * P.map f = 0 := by
    rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, hQP', Matrix.zero_mul]
  have hP : P.map f = 1 - D.map f * Q.map f := by
    simp only [P, Matrix.map_sub _ (map_sub _), Matrix.map_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hP, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc] at hQMP
  simpa only [M, f, Matrix.mul_assoc] using sub_eq_zero.mp hQMP

/-- Every finite-dimensional vector-space quotient has split finite coordinates. -/
theorem exists_quotient_split_coordinates (V : Submodule k (n → k)) :
    ∃ (d : ℕ) (Q : Matrix (Fin d) n k) (D : Matrix n (Fin d) k),
      Q * D = 1 ∧ LinearMap.ker Q.mulVecLin = V := by
  classical
  let b := Module.finBasis k ((n → k) ⧸ V)
  let q : (n → k) →ₗ[k] (Fin (Module.finrank k ((n → k) ⧸ V)) → k) :=
    b.equivFun.toLinearMap.comp V.mkQ
  have hq : Function.Surjective q :=
    b.equivFun.surjective.comp V.mkQ_surjective
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hq)
  refine ⟨_, LinearMap.toMatrix' q, LinearMap.toMatrix' s, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hs, LinearMap.toMatrix'_id]
  · ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearMap.toMatrix'_mulVec]
    change b.equivFun (V.mkQ v) = 0 ↔ v ∈ V
    rw [LinearEquiv.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero V

/-- An actual representation of the quotient by a stable subspace, with its
split surjective projection and exact kernel. -/
structure QuotientRepresentation (ρ : MatrixRepresentation G n)
    (V : Submodule k (n → k)) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  projection : Matrix (Fin dimension) n k
  sectionMap : Matrix n (Fin dimension) k
  right_inverse : projection * sectionMap = 1
  ker_projection : LinearMap.ker projection.mulVecLin = V
  intertwines : Intertwines ρ representation projection

/-- The recorded split quotient projection is surjective. -/
theorem QuotientRepresentation.projection_surjective
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)}
    (q : QuotientRepresentation ρ V) :
    Function.Surjective q.projection.mulVecLin := by
  intro v
  refine ⟨q.sectionMap *ᵥ v, ?_⟩
  change q.projection *ᵥ (q.sectionMap *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, q.right_inverse, Matrix.one_mulVec]

/-- The constructed quotient is an actual subquotient in the published sense. -/
theorem QuotientRepresentation.isSubquotientOf
    {N : ℕ} {ρ : MatrixRepresentation G (Fin N)}
    {V : Submodule k (Fin N → k)} (q : QuotientRepresentation ρ V) :
    q.representation.IsSubquotientOf ρ := by
  refine ⟨N, ρ, 1, q.projection, ?_, ?_, q.intertwines,
    q.projection_surjective⟩
  · intro A x
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  · intro v w h
    simpa only [Matrix.mulVecLin_apply, Matrix.one_mulVec] using h

/-- Every stable subspace of an affine group's representation admits its actual
finite-dimensional quotient representation, including zero-dimensional cases. -/
theorem nonempty_quotientRepresentation [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (V : Submodule k (n → k))
    (hV : IsStableSubspace ρ V) : Nonempty (QuotientRepresentation ρ V) := by
  obtain ⟨d, Q, D, hQD, hker⟩ := exists_quotient_split_coordinates V
  have hquot := hV.isQuotientCoordinates Q D hQD hker
  let σ := quotientCoordinates ρ Q D hQD hquot
  refine ⟨⟨d, σ, Q, D, hQD, hker, ?_⟩⟩
  intro A x
  have h := quotientCoordinates_intertwines ρ Q D hQD hquot
    ((algSpec (CommRingCat.of k)).obj (op A)) x
  let e := Corepresented.affineSectionsAlgEquiv A
  have hQ : (Q.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A)))).map
      e.toRingHom = Q.map (algebraMap k A) := by
    ext i j
    exact e.commutes _
  have he {a : Type} [Fintype a] [DecidableEq a] (τ : MatrixRepresentation G a) :
      (τ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) x :
        Matrix a a Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)).map
          e.toRingHom = (τ.affineMatrix A x : Matrix a a A) := by
    rw [pointMatrix_eq_affineMatrix]
    ext i j
    exact e.apply_symm_apply _
  have hh := congrArg (fun M : Matrix (Fin d) n
    Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) => M.map e.toRingHom) h
  erw [Matrix.map_mul (f := e.toRingHom),
    Matrix.map_mul (f := e.toRingHom)] at hh
  erw [hQ, he ρ, he σ] at hh
  exact hh

end StableKernel

end Langlands.GroupScheme.MatrixRepresentation
