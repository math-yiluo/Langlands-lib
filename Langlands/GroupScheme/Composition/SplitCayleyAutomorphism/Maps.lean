import Langlands.GroupScheme.Composition.SplitCayleyAutomorphism.Points
import Langlands.GroupScheme.MatrixRepresentation.VectorGroupPolynomial
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Reductive.GeneralLinearMaximal

/-! # Root-group and torus homomorphisms into the split Cayley automorphism group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitCayley

/-! ### Change of coefficients -/

section Naturality

variable {A B : Type u} [CommRing A] [CommRing B]

theorem map_rootFun (f : A →+* B) (α : Root) (r : A) (x : Fin 8 → A) :
    (fun i => f (rootFun α r x i)) = rootFun α (f r) (fun i => f (x i)) := by
  cases α <;> funext i <;> fin_cases i <;>
    simp only [rootFun, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, map_sub, map_add, map_mul, map_pow]

theorem rootMatrix_map (f : A →+* B) (α : Root) (r : A) :
    (rootMatrix α r).map f = rootMatrix α (f r) := by
  ext i j
  rw [Matrix.map_apply, rootMatrix, rootMatrix, LinearMap.toMatrix'_apply,
    LinearMap.toMatrix'_apply]
  change f (rootFun α r (Pi.single j 1) i) = rootFun α (f r) (Pi.single j 1) i
  rw [congrFun (map_rootFun f α r (Pi.single j 1)) i]
  congr 1
  funext k
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

theorem rootGL_map (f : A →+* B) (α : Root) (r : A) :
    Matrix.GeneralLinearGroup.map f (rootGL α r) = rootGL α (f r) := by
  ext : 1
  exact rootMatrix_map f α r

theorem torusGL_map (f : A →+* B) (s t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (torusGL s t) =
      torusGL (Units.map f.toMonoidHom s) (Units.map f.toMonoidHom t) := by
  ext : 1
  change (((torusGL s t : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A)).map f = _
  rw [torusGL_val, torusGL_val, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  fin_cases i <;> simp [torusEntries]

theorem torusGL_one : torusGL (1 : Aˣ) 1 = 1 := by
  ext : 1
  rw [Units.val_one, torusGL_val, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [torusEntries]

end Naturality

variable {K : Type u} [Field K]

/-! ### Root groups -/

section Root

/-- The root-group homomorphism `t ↦ x_α(t)` into the automorphism matrices. -/
def rootHom (α : Root) {A : Type u} [CommRing A] (φ : K →+* A) :
    Multiplicative (Fin 1 → A) →* (CayleyDatum.split K).automorphismSubgroup φ where
  toFun t := ⟨rootGL α (t.toAdd 0),
    (mem_automorphismSubgroup_split_iff φ _).mpr (isAutomorphism_rootGL α _)⟩
  map_one' := Subtype.ext (rootGL_zero α)
  map_mul' _ _ := Subtype.ext (rootGL_add α _ _)

@[simp] theorem coe_rootHom (α : Root) {A : Type u} [CommRing A] (φ : K →+* A)
    (t : Multiplicative (Fin 1 → A)) :
    ((rootHom α φ t : (CayleyDatum.split K).automorphismSubgroup φ) : GL (Fin 8) A) =
      rootGL α (t.toAdd 0) :=
  rfl

variable (K) in
/-- The root-group homomorphism as a natural transformation of group functors. -/
def rootTrans (α : Root) : VectorGroup.functor (CommRingCat.of K) 1 ⟶
    Corepresented.cutFunctor (CayleyDatum.split K).isCutOutBy_automorphismIdeal where
  app A := GrpCat.ofHom (rootHom α (algebraMap (CommRingCat.of K) A))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro t
    apply Subtype.ext
    exact (rootGL_map f.hom.toRingHom α (t.toAdd 0)).symm

variable (K) in
/-- The root-group homomorphism `𝔾ₐ → Aut` of group schemes. -/
def rootMap (α : Root) :
    VectorGroup.groupScheme (CommRingCat.of K) 1 ⟶ (CayleyDatum.split K).automorphismGroup :=
  Corepresented.groupSchemeMap (VectorGroup.corepresentableBy _ 1)
    (Corepresented.cutCorepresentableBy _) (rootTrans K α)

theorem pointsEquiv_rootMap (α : Root) (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of K) 1).X) :
    pointsEquiv K T (x ≫ (rootMap K α).hom.hom) =
      rootHom α (scalarMap T) (VectorGroup.coordinates _ 1 T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

theorem affinePointsEquiv_rootMap (α : Root) (S : CommAlgCat.{u} (CommRingCat.of K))
    (t : Fin 1 → S) :
    affinePointsEquiv K S (VectorGroup.affinePoint S t ≫ (rootMap K α).hom.hom) =
      rootHom α (algebraMap (CommRingCat.of K) S) (Multiplicative.ofAdd t) := by
  refine (Corepresented.groupSchemeMap_affinePoints _ _ _ _).trans ?_
  change rootHom α (algebraMap (CommRingCat.of K) S)
    (Corepresented.affinePointsEquiv _ _ S (VectorGroup.affinePoint S t)) = _
  rw [VectorGroup.affinePointsEquiv_affinePoint]

/-- On affine points, the root homomorphism followed by the inclusion into `GL₈` is
`t ↦ x_α(t)`. -/
theorem affinePointsEquiv_rootMap_inclusion (α : Root) (S : CommAlgCat.{u} (CommRingCat.of K))
    (t : Fin 1 → S) :
    GeneralLinear.affinePointsEquiv (Fin 8) _ S (VectorGroup.affinePoint S t ≫
        (rootMap K α ≫ (CayleyDatum.split K).automorphismInclusion).hom.hom) =
      rootGL α (t 0) := by
  rw [Grp.comp_hom_hom, ← Category.assoc, affinePointsEquiv_inclusion,
    affinePointsEquiv_rootMap]
  rfl

end Root

/-! ### The diagonal torus -/

section Torus

/-- The torus homomorphism `(s, t) ↦ diag(1, s, t, s⁻¹t⁻¹, s⁻¹, t⁻¹, st, 1)` into the
automorphism matrices. -/
def torusHom {A : Type u} [CommRing A] (φ : K →+* A) :
    (ULift.{u} (Fin 2) → Aˣ) →* (CayleyDatum.split K).automorphismSubgroup φ where
  toFun τ := ⟨torusGL (τ ⟨0⟩) (τ ⟨1⟩),
    (mem_automorphismSubgroup_split_iff φ _).mpr (isAutomorphism_torusGL _ _)⟩
  map_one' := Subtype.ext torusGL_one
  map_mul' _ _ := Subtype.ext (torusGL_mul _ _ _ _)

@[simp] theorem coe_torusHom {A : Type u} [CommRing A] (φ : K →+* A)
    (τ : ULift.{u} (Fin 2) → Aˣ) :
    ((torusHom φ τ : (CayleyDatum.split K).automorphismSubgroup φ) : GL (Fin 8) A) =
      torusGL (τ ⟨0⟩) (τ ⟨1⟩) :=
  rfl

variable (K) in
/-- Points of the rank-two split torus go to the corresponding torus automorphisms. -/
def torusPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).X) →*
      (T ⟶ (CayleyDatum.split K).automorphismGroup.X) :=
  (pointsEquiv K T).symm.toMonoidHom.comp
    ((torusHom (scalarMap T)).comp (splitTorus.pointsEquiv (ULift.{u} (Fin 2)) T).toMonoidHom)

theorem pointsEquiv_torusPoints {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).X) :
    pointsEquiv K T (torusPoints K T x) =
      torusHom (scalarMap T) (splitTorus.pointsEquiv (ULift.{u} (Fin 2)) T x) :=
  MulEquiv.apply_symm_apply _ _

theorem torusPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).X) :
    torusPoints K T' (a ≫ x) = a ≫ torusPoints K T x := by
  apply (pointsEquiv K T').injective
  apply Subtype.ext
  apply Units.ext
  rw [pointsEquiv_naturality, pointsEquiv_torusPoints, pointsEquiv_torusPoints,
    splitTorus.pointsEquiv_naturality, coe_torusHom, coe_torusHom]
  exact congrArg Units.val (torusGL_map a.left.appTop.hom _ _).symm

variable (K) in
/-- The rank-two split torus of the automorphism group scheme. -/
def torusMap :
    (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).toGrp ⟶
      (CayleyDatum.split K).automorphismGroup :=
  homOfPoints (torusPoints K) (fun {_ _} a x => torusPoints_naturality a x)

theorem pointsEquiv_torusMap {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).X) :
    pointsEquiv K T (x ≫ (torusMap K).hom.hom) =
      torusHom (scalarMap T) (splitTorus.pointsEquiv (ULift.{u} (Fin 2)) T x) := by
  rw [torusMap, comp_homOfPoints, pointsEquiv_torusPoints]

/-- The torus homomorphism is injective on points. -/
instance mono_torusMap : Mono (torusMap K).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} (Fin 2)) Z).injective
  have h1 := congrArg (fun x => ((pointsEquiv K Z x : GL (Fin 8) Γ(Z.left, ⊤)) :
    Matrix (Fin 8) (Fin 8) Γ(Z.left, ⊤))) hgh
  simp only [pointsEquiv_torusMap, coe_torusHom, torusGL_val] at h1
  funext c
  apply Units.ext
  have h11 := congrFun (congrFun h1 1) 1
  have h22 := congrFun (congrFun h1 2) 2
  simp only [Matrix.diagonal_apply_eq] at h11 h22
  obtain ⟨c⟩ := c
  fin_cases c
  · simpa [torusEntries] using h11
  · simpa [torusEntries] using h22

/-- On affine points, the torus homomorphism is the torus matrix of the coordinates. -/
theorem affinePointsEquiv_torusMap {A : Type u} [CommRing A] [Algebra (CommRingCat.of K) A]
    (t : Lie.AffinePoints
      (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} (Fin 2))).toGrp A) :
    GeneralLinear.affinePointsEquiv (Fin 8) _ (CommAlgCat.of (CommRingCat.of K) A)
        (t ≫ (torusMap K ≫ (CayleyDatum.split K).automorphismInclusion).hom.hom) =
      torusGL (GeneralLinear.torusCoords t ⟨0⟩) (GeneralLinear.torusCoords t ⟨1⟩) := by
  rw [GeneralLinear.affinePointsEquiv_eq_map_pointsEquiv, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, pointsEquiv_torusMap, coe_torusHom]
  erw [torusGL_map]
  congr 1 <;>
  · apply Units.ext
    exact DFunLike.congr_fun
      (Corepresented.affineSectionsIso_hom_ringHom (CommAlgCat.of (CommRingCat.of K) A)) _

end Torus

end SplitCayley

end Langlands.GroupScheme
