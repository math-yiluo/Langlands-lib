import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Derived.CentralIntersection.LinearAlgebra

/-! # Block-determinant characters and eigenvalues of central derived points

For a matrix representation `ρ` of a group scheme `G` and an idempotent coefficient matrix `π`
commuting with every matrix of `ρ`, the map `g ↦ det (ρ(g) π + (1 - π))` is a character of `G`.
Applied to the spectral projector of a central point of an actual derived subgroup, this shows
that every eigenvalue of the point is a root of unity of order at most the dimension. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.CentralIntersection

section Block

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- The structure map of a test scheme, as a morphism to the base viewed as an object over
itself. -/
def toBase (T : Over (Spec R)) : T ⟶ Over.mk (𝟙 (Spec R)) :=
  Over.homMk T.hom

/-- Pulling a rational point back to a test scheme multiplies coefficients by the structure
map. -/
theorem pointMatrix_toBase (ρ : MatrixRepresentation G n) (T : Over (Spec R))
    (x : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    (ρ.pointMatrix T (toBase T ≫ x) : Matrix n n Γ(T.left, ⊤)) =
      (scalarMap T).mapMatrix (ρ.rationalMatrix x : Matrix n n R) := by
  rw [MatrixRepresentation.pointMatrix_naturality]
  ext i j
  change (toBase T).left.appTop.hom
      ((ρ.pointMatrix (Over.mk (𝟙 (Spec R))) x :
        Matrix n n Γ((Over.mk (𝟙 (Spec R))).left, ⊤)) i j) =
    ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom
      ((Scheme.ΓSpecIso R).hom ((ρ.pointMatrix (Over.mk (𝟙 (Spec R))) x :
        Matrix n n Γ((Over.mk (𝟙 (Spec R))).left, ⊤)) i j))
  rw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  rfl

/-- On rational points, the structure map is the inverse of `Γ(Spec R) ≅ R`. -/
theorem scalarMap_base (c : R) :
    (Scheme.ΓSpecIso R).hom (scalarMap (Over.mk (𝟙 (Spec R))) c) = c := by
  change (Scheme.ΓSpecIso R).hom
    (((Scheme.ΓSpecIso R).inv ≫ (𝟙 (Spec R) : Spec R ⟶ Spec R).appTop).hom c) = c
  rw [Scheme.Hom.id_appTop, Category.comp_id, Iso.inv_hom_id_apply]

variable (ρ : MatrixRepresentation G n) (π : Matrix n n R)

/-- The block matrix `ρ(g) π + (1 - π)` of a point `g` over a test scheme `T`. -/
def blockMatrix (T : Over (Spec R)) (g : T ⟶ G.X) : Matrix n n Γ(T.left, ⊤) :=
  (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) * (scalarMap T).mapMatrix π +
    (1 - (scalarMap T).mapMatrix π)

variable {ρ π}

/-- Coefficient pullback along a test morphism transports block matrices. -/
theorem blockMatrix_naturality {T T' : Over (Spec R)} (a : T' ⟶ T) (g : T ⟶ G.X) :
    blockMatrix ρ π T' (a ≫ g) = a.left.appTop.hom.mapMatrix (blockMatrix ρ π T g) := by
  have hπ : (scalarMap T').mapMatrix π = a.left.appTop.hom.mapMatrix ((scalarMap T).mapMatrix π) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (scalarMap_naturality a (π i j)).symm
  rw [blockMatrix, blockMatrix, MatrixRepresentation.pointMatrix_naturality, hπ]
  simp only [map_add, map_mul, map_sub, map_one]
  rfl

variable (hπ : IsIdempotentElem π)
  (hcomm : ∀ (T : Over (Spec R)) (g : T ⟶ G.X),
    Commute ((scalarMap T).mapMatrix π) (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)))
include hπ hcomm

/-- Block matrices multiply like the points they come from. -/
theorem blockMatrix_mul (T : Over (Spec R)) (g h : T ⟶ G.X) :
    blockMatrix ρ π T (g * h) = blockMatrix ρ π T g * blockMatrix ρ π T h := by
  set p := (scalarMap T).mapMatrix π with hpdef
  have hp : IsIdempotentElem p := hπ.map _
  set A := (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤))
  set B := (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))
  have hB : p * B = B * p := hcomm T h
  have h1 : A * p * (B * p) = A * B * p := by
    rw [mul_assoc A p, ← mul_assoc p B p, hB, mul_assoc B p p, hp.eq, ← mul_assoc]
  have h2 : A * p * (1 - p) = 0 := by
    rw [mul_sub, mul_one, mul_assoc, hp.eq, sub_self]
  have h3 : (1 - p) * (B * p) = 0 := by
    rw [sub_mul, one_mul, ← mul_assoc, hB, mul_assoc, hp.eq, sub_self]
  have h4 : (1 - p) * (1 - p) = 1 - p := hp.one_sub.eq
  simp only [blockMatrix, map_mul, Units.val_mul]
  rw [← hpdef, add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add]

/-- The block matrices of the points over `T`, as a monoid homomorphism. -/
def blockMonoidHom (T : Over (Spec R)) : (T ⟶ G.X) →* Matrix n n Γ(T.left, ⊤) where
  toFun := blockMatrix ρ π T
  map_one' := by
    rw [blockMatrix, map_one, Units.val_one, one_mul, add_sub_cancel]
  map_mul' := blockMatrix_mul hπ hcomm T

/-- The block determinant `g ↦ det (ρ(g) π + (1 - π))` on the points over `T`, valued in the
points of `𝔾_m`. -/
def blockDetPoints (T : Over (Spec R)) : (T ⟶ G.X) →* (T ⟶ (Gm (Spec R)).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
    (Matrix.GeneralLinearGroup.det.comp (blockMonoidHom hπ hcomm T).toHomUnits)

theorem blockDetPoints_val (T : Over (Spec R)) (g : T ⟶ G.X) :
    (Gm.pointsEquiv (Spec R) T (blockDetPoints hπ hcomm T g) : Γ(T.left, ⊤)) =
      (blockMatrix ρ π T g).det := by
  simp [blockDetPoints, blockMonoidHom]

theorem blockDetPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T) (g : T ⟶ G.X) :
    blockDetPoints hπ hcomm T' (a ≫ g) = a ≫ blockDetPoints hπ hcomm T g := by
  apply (Gm.pointsEquiv (Spec R) T').injective
  apply Units.ext
  rw [blockDetPoints_val, Gm.pointsEquiv_naturality, Units.coe_map, blockDetPoints_val,
    blockMatrix_naturality]
  exact (RingHom.map_det _ _).symm

/-- The block-determinant character `g ↦ det (ρ(g) π + (1 - π))` of `G`. -/
def blockCharacter : G ⟶ (Gm (Spec R)).toGrp :=
  homOfPoints (blockDetPoints hπ hcomm) (blockDetPoints_naturality hπ hcomm)

theorem comp_blockCharacter (T : Over (Spec R)) (g : T ⟶ G.X) :
    g ≫ (blockCharacter hπ hcomm).hom.hom = blockDetPoints hπ hcomm T g :=
  comp_homOfPoints _ _ T g

end Block

section Commute

variable {K B : Type*} [Field K] [Ring B] {n : Type*} [Fintype n] [DecidableEq n]

/-- If a ring homomorphism sends scalar matrices to elements commuting with `b`, then the image
of every polynomial in a matrix `A` commutes with `b` once the image of `A` does. -/
theorem commute_map_aeval (F : Matrix n n K →+* B)
    {b : B} (hF : ∀ c : K, Commute (F (algebraMap K (Matrix n n K) c)) b)
    {A : Matrix n n K} (h : Commute (F A) b) (P : K[X]) : Commute (F (aeval A P)) b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    exact hp.add_left hq
  | monomial k c =>
    rw [aeval_monomial, map_mul, map_pow]
    exact (hF c).mul_left (h.pow_left k)

end Commute

section Eigenvalues

variable {K : Type u} [Field K] [IsAlgClosed K]
  {G D : GroupScheme (Spec (CommRingCat.of K))} {n : Type} [Fintype n] [DecidableEq n]

/-- Every eigenvalue of a central rational point of an actual derived subgroup, in any matrix
representation, is a root of unity of order at most the dimension. -/
theorem exists_pow_eq_one_of_isRoot_charpoly {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (ρ : MatrixRepresentation G n) (y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ D.X)
    (hy : y ≫ d.hom.hom ∈ (center G).carrier _) {c : K}
    (hc : (ρ.rationalMatrix (y ≫ d.hom.hom) : Matrix n n K).charpoly.IsRoot c) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ Fintype.card n ∧ c ^ a = 1 := by
  set x := y ≫ d.hom.hom with hxdef
  set A₀ := (ρ.rationalMatrix x : Matrix n n K) with hA₀
  obtain ⟨P, hπ, a, ha1, han, hdet⟩ := exists_blockProjector A₀ hc
  refine ⟨a, ha1, han, ?_⟩
  have hcomm : ∀ (T : Over (Spec (CommRingCat.of K))) (g : T ⟶ G.X),
      Commute ((scalarMap T).mapMatrix (aeval A₀ P))
        (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) := by
    intro T g
    have hxg : Commute (toBase T ≫ x) g := hy T (toBase T) g
    have hρ : Commute (ρ.pointMatrix T (toBase T ≫ x) : Matrix n n Γ(T.left, ⊤))
        (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) :=
      ((hxg.map (ρ.pointMatrix T)).map (Units.coeHom _))
    rw [pointMatrix_toBase] at hρ
    refine commute_map_aeval (scalarMap T).mapMatrix (A := A₀) (fun c' => ?_) hρ P
    have hsc : (scalarMap T).mapMatrix (algebraMap K (Matrix n n K) c') =
        Matrix.scalar n (scalarMap T c') := by
      rw [Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
      rfl
    rw [hsc]
    exact Matrix.scalar_commute (scalarMap T c') (fun r' => Commute.all _ r') _
  have hχ : d ≫ blockCharacter hπ hcomm = 1 :=
    congrArg Additive.toMul (hd.characterRestrict_eq_zero (Additive.ofMul (blockCharacter hπ hcomm)))
  have hpt : x ≫ (blockCharacter hπ hcomm).hom.hom = 1 := by
    rw [hxdef, Category.assoc, ← Grp.comp_hom_hom, hχ]
    simp only [Grp.Hom.hom_one, Mon.Hom.hom_one, MonObj.comp_one]
  rw [comp_blockCharacter] at hpt
  have hval := congrArg (fun u => (Gm.pointsEquiv (Spec (CommRingCat.of K)) _ u).val) hpt
  simp only [blockDetPoints_val, map_one, Units.val_one] at hval
  rw [← hdet]
  have hmap : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.mapMatrix
      (blockMatrix ρ (aeval A₀ P) _ x) = A₀ * aeval A₀ P + (1 - aeval A₀ P) := by
    have hs : ∀ M : Matrix n n K, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.mapMatrix
        ((scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of K))))).mapMatrix M) = M := by
      intro M
      ext i j
      exact scalarMap_base (R := CommRingCat.of K) (M i j)
    rw [blockMatrix, map_add, map_mul, map_sub, map_one, hs, hA₀,
      MatrixRepresentation.rationalMatrix_apply]
    rfl
  rw [← hmap, ← RingHom.map_det, hval, map_one]

/-- Every eigenvalue `c` of a central rational point of an actual derived subgroup satisfies
`c ^ (card n)! = 1`. -/
theorem pow_factorial_eq_one_of_mem_roots {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (ρ : MatrixRepresentation G n) (y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ D.X)
    (hy : y ≫ d.hom.hom ∈ (center G).carrier _) {c : K}
    (hc : c ∈ (ρ.rationalMatrix (y ≫ d.hom.hom) : Matrix n n K).charpoly.roots) :
    c ^ (Fintype.card n).factorial = 1 := by
  obtain ⟨a, ha1, han, hca⟩ := exists_pow_eq_one_of_isRoot_charpoly hd ρ y hy
    (Polynomial.isRoot_of_mem_roots hc)
  obtain ⟨b, hb⟩ := Nat.dvd_factorial ha1 han
  rw [hb, pow_mul, hca, one_pow]

end Eigenvalues

end Langlands.GroupScheme.CentralIntersection
