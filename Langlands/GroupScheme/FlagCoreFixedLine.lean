import Langlands.GroupScheme.FlagCoreOrbits
import Langlands.GroupScheme.ProjectiveQuotientEmbedding
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.SolvableProperFixedPointStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.PointLines
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry

/-! # Stable lines of solvable groups from fixed points on projective space -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.ProjectiveOrbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Action

variable {n : ℕ} {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}

/-- The action morphism of `H` on the ambient projective space through the matrix
representation `σ`: on the universal test point it is the matrix action of `σ`. -/
def matrixActionHom (σ : MatrixRepresentation H (Fin (n + 1))) :
    H.X ⊗ ambient n R ⟶ ambient n R :=
  Over.homMk (pointSection (snd H.X (ambient n R)) ≫
      matrixAction n (σ.pointMatrix (H.X ⊗ ambient n R) (fst H.X (ambient n R))) ≫
      RelativeProjectiveSpace.map n (H.X ⊗ ambient n R).hom) (by
    simp [ambient, pointSection])

/-- On every test, the action morphism is the matrix action on the section of the point. -/
theorem comp_matrixActionHom_left (σ : MatrixRepresentation H (Fin (n + 1)))
    {Z : Over (Spec R)} (h : Z ⟶ H.X) (x : Z ⟶ ambient n R) :
    (lift h x ≫ matrixActionHom σ).left =
      pointSection x ≫ matrixAction n (σ.pointMatrix Z h) ≫
        RelativeProjectiveSpace.map n Z.hom := by
  have key := pointSection_matrixAction_naturality σ (lift h x) (fst H.X (ambient n R))
    (snd H.X (ambient n R))
  rw [lift_fst, lift_snd] at key
  rw [← key]
  rfl

/-- A section over the test scheme that maps to the test point is its section. -/
theorem pointSection_eq_of_left {Z : Over (Spec R)} (y : Z ⟶ ambient n R)
    (s : Z.left ⟶ RelativeProjectiveSpace Z.left n)
    (hs : s ≫ RelativeProjectiveSpace.toBase Z.left n = 𝟙 _)
    (hy : y.left = s ≫ RelativeProjectiveSpace.map n Z.hom) : pointSection y = s := by
  apply section_ext_of_map n Z.hom
  · simp [pointSection, hs]
  · rw [pointSection_map, hy]

/-- The action of `H` on the ambient projective space through a matrix representation. -/
@[instance_reducible]
def matrixSchemeAction (σ : MatrixRepresentation H (Fin (n + 1))) :
    SchemeAction H (ambient n R) :=
  schemeActionOfPointLaws (matrixActionHom σ)
    (fun {Z} x => by
      apply Over.OverMorphism.ext
      rw [comp_matrixActionHom_left, map_one, matrixAction_one, Category.id_comp,
        pointSection_map])
    (fun {Z} h h' x => by
      apply Over.OverMorphism.ext
      rw [comp_matrixActionHom_left, comp_matrixActionHom_left, map_mul, matrixAction_mul,
        pointSection_eq_of_left (lift h' x ≫ matrixActionHom σ)
          (pointSection x ≫ matrixAction n (σ.pointMatrix Z h')) (by simp [pointSection])
          (comp_matrixActionHom_left σ h' x)]
      simp only [Category.assoc])

/-- The action of a test point is the matrix action on the section of the point. -/
theorem matrixSchemeAction_act_left (σ : MatrixRepresentation H (Fin (n + 1)))
    {Z : Over (Spec R)} (h : Z ⟶ H.X) (x : Z ⟶ ambient n R) :
    ((matrixSchemeAction σ).act h x).left =
      pointSection x ≫ matrixAction n (σ.pointMatrix Z h) ≫
        RelativeProjectiveSpace.map n Z.hom :=
  comp_matrixActionHom_left σ h x

/-- The identity of projective space is matrix equivariant for the matrix action. -/
theorem isMatrixEquivariant_matrixSchemeAction (σ : MatrixRepresentation H (Fin (n + 1))) :
    IsMatrixEquivariant (matrixSchemeAction σ) σ (𝟙 _) := by
  intro Z h x
  simp only [Category.comp_id]
  exact matrixSchemeAction_act_left σ h x

end Action

section Field

variable {k : Type u} [Field k] {n : ℕ}

/-- **Rational points of projective space are translates of a basis section.** Every
rational point `x` of the ambient projective space over a field is the coordinate section
`e_j` moved by an invertible matrix `P` with entries in `k`. -/
theorem exists_pointSection_eq_basisSection
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ambient n (CommRingCat.of k)) :
    ∃ (j : Fin (n + 1)) (P : GL (Fin (n + 1)) k),
      pointSection x = RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j ≫
        matrixAction n (Matrix.GeneralLinearGroup.map (fieldToGlobal k) P) := by
  set p : Spec (CommRingCat.of k) ⟶ ProjectiveSpace k n :=
    pointSection x ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k)))
    with hpdef
  have hp : p ≫ projectiveSpaceToSpec k n = 𝟙 _ := by
    simp [hpdef, pointSection]
  set c := ProjectiveSpace.pointCoordinates n p hp with hcdef
  set j := ProjectiveSpace.pointChartIndex n p hp with hjdef
  have hcj : c j = 1 := ProjectiveSpace.pointCoordinates_index n p hp
  have hdet : (updateCol (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j c).det ≠ 0 := by
    rw [FlagCore.det_updateCol_one, hcj]
    exact one_ne_zero
  set P : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hPdef
  have hPcol : (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single j 1 = c := by
    funext i
    rw [mulVec_single_one]
    change updateCol (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j c i j = c i
    rw [updateCol_self]
  refine ⟨j, P, ?_⟩
  set q : Spec (CommRingCat.of k) ⟶ ProjectiveSpace k n :=
    RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j ≫
      matrixAction n (Matrix.GeneralLinearGroup.map (fieldToGlobal k) P) ≫
        RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) with hqdef
  have hq : q ≫ projectiveSpaceToSpec k n = 𝟙 _ := by
    simp [hqdef]
  -- The point `q` has homogeneous coordinates `P e_j = c`.
  have hqc : ProjectiveSpace.HasCoordinates (q (IsLocalRing.closedPoint k)) c := by
    have hpt : q = CategoryStruct.comp (Y := ProjectiveSpace k n)
        (Proj.fromOfGlobalSections (projectiveSpaceGrading k n)
          ((fieldToGlobal k).comp (MvPolynomial.eval (Pi.single j 1)))
          (ProjectiveSpace.irrelevant_map_eval_eq_top _ (basisVector_ne_zero n j)))
        (ProjectiveSpace.linearAction k n (coordinateEquiv n P)) := by
      rw [hqdef, matrixAction_toPolynomial, ← Category.assoc,
        basisSection_toPolynomial_eq_fromOfGlobalSections]
      congr 3
      ext i l
      exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) _
    rw [hpt, Scheme.Hom.comp_apply]
    have h := (ProjectiveSpace.hasCoordinates_fromOfGlobalSections (fieldToGlobal k)
      (Pi.single j 1)
      (ProjectiveSpace.irrelevant_map_eval_eq_top _ (basisVector_ne_zero n j))).linearAction
      (coordinateEquiv n P)
    rwa [coordinateEquiv_apply, hPcol] at h
  have hpq : p = q := by
    rw [ProjectiveSpace.eq_iff_linear_incidence n p q hp hq]
    intro ℓ
    rw [ProjectiveSpace.pointCoordinates_linearForm_mem_iff n p hp ℓ,
      hqc 1 _ ((MvPolynomial.mem_homogeneousSubmodule 1 _).mp
        (ProjectiveSpace.linearFormPolynomialEquiv k n ℓ).2),
      ProjectiveSpace.eval_linearFormPolynomialEquiv]
  apply RelativeProjectiveSpace.hom_ext_toPolynomial (𝟙 (Spec (CommRingCat.of k)))
  · simp [pointSection]
  · exact hpq

/-- **A fixed rational point gives a stable line on all tests.** If the rational point
`x = P e_j` of projective space is fixed by the matrix action of `σ`, then on every test
scheme every point of `H` maps the image of `P e_j` to a unit multiple of it. -/
theorem stabilizedLine_of_isFixed {H : GroupScheme (Spec (CommRingCat.of k))}
    (σ : MatrixRepresentation H (Fin (n + 1)))
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ambient n (CommRingCat.of k)}
    (hx : (matrixSchemeAction σ).IsFixed x) {j : Fin (n + 1)} {P : GL (Fin (n + 1)) k}
    (hP : pointSection x =
      RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j ≫
        matrixAction n (Matrix.GeneralLinearGroup.map (fieldToGlobal k) P))
    (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) :
    ∃ a : Γ(T.left, ⊤)ˣ,
      (σ.pointMatrix T h : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
          (fun i => scalarMap T (((P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
            Pi.single j 1) i)) =
        (a : Γ(T.left, ⊤)) • fun i => scalarMap T (((P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
            Pi.single j 1) i) := by
  let b : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) := Over.homMk T.hom (by simp)
  set PT : GL (Fin (n + 1)) Γ(T.left, ⊤) := Matrix.GeneralLinearGroup.map T.hom.appTop.hom
    (Matrix.GeneralLinearGroup.map (fieldToGlobal k) P) with hPT
  -- The section of the pulled-back point is the translated basis section over `T`.
  have hsec : pointSection (b ≫ x) =
      RelativeProjectiveSpace.basisSection n T.left j ≫ matrixAction n PT := by
    apply section_ext_of_map n T.hom
    · simp [pointSection]
    · have hnat := pointSection_naturality b x
      change T.hom ≫ pointSection x = pointSection (b ≫ x) ≫ RelativeProjectiveSpace.map n T.hom
        at hnat
      rw [← hnat, hP, RelativeProjectiveSpace.basisSection_naturality_assoc, map_matrixAction]
      rfl
  -- Fixedness gives a fixed translated basis section.
  have hfix := congrArg Over.Hom.left (hx T b h)
  rw [matrixSchemeAction_act_left, ← pointSection_map (b ≫ x)] at hfix
  have hfix' : pointSection (b ≫ x) ≫ matrixAction n (σ.pointMatrix T h) =
      pointSection (b ≫ x) := by
    apply section_ext_of_map n T.hom
    · simp [pointSection]
    · simpa only [Category.assoc] using hfix
  rw [hsec, Category.assoc, ← matrixAction_mul] at hfix'
  obtain ⟨a, ha⟩ := (basisSection_matrixAction_eq_iff n T.left j _).mp
    ((translates_eq_iff n _ PT (σ.pointMatrix T h * PT)).mp hfix'.symm)
  have hcol : (PT : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      fun i => scalarMap T (((P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single j 1) i) := by
    funext i
    rw [mulVec_single_one, mulVec_single_one]
    rfl
  refine ⟨a, ?_⟩
  rw [← hcol]
  have h2 := congrArg ((PT : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ ·) ha
  simp only [Units.val_mul, ← mulVec_mulVec, mulVec_smul] at h2
  rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at h2
  exact h2

end Field

end Langlands.GroupScheme.ProjectiveOrbit

namespace Langlands.GroupScheme.FlagCore

open ProjectiveOrbit

variable {k : Type u} [Field k]

/-- **Lie–Kolchin on all tests.** Granting the fixed-point theorem for smooth connected
solvable groups on proper schemes, every matrix representation of such a group over an
algebraically closed field has a nonzero vector whose line is stable on all tests. -/
theorem exists_stabilizedLine (hfix : SolvableProperFixedPointStatement.{u}) [IsAlgClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hconn : ConnectedSpace H.X.left) (hsolv : IsSolvableGroupScheme H) {n : ℕ}
    (σ : MatrixRepresentation H (Fin (n + 1))) :
    ∃ w : Fin (n + 1) → k, w ≠ 0 ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
        ∃ a : Γ(T.left, ⊤)ˣ,
          (σ.pointMatrix T h : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
              (fun i => scalarMap T (w i)) =
            (a : Γ(T.left, ⊤)) • fun i => scalarMap T (w i) := by
  have hne : Nonempty (ambient n (CommRingCat.of k)).left :=
    ⟨(RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) 0)
      (IsLocalRing.closedPoint k)⟩
  obtain ⟨x, hx⟩ := hfix k H hconn hsolv (ambient n (CommRingCat.of k))
    (inferInstanceAs (IsProper (RelativeProjectiveSpace.toBase _ n))) hne (matrixSchemeAction σ)
  obtain ⟨j, P, hP⟩ := exists_pointSection_eq_basisSection x
  exact ⟨_, mulVec_ne_zero P (basisVector_ne_zero n j), stabilizedLine_of_isFixed σ hx hP⟩

/-- **A Borel-stable dual line.** Granting the fixed-point theorem, a Borel subgroup `b`
stabilizes the line of some nonzero vector of the dual of any matrix representation of
`G`, on all tests. -/
theorem exists_stabilizesLine_dual (hfix : SolvableProperFixedPointStatement.{u}) [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G} (hb : IsBorelSubgroup b) {n : ℕ}
    (ρ : MatrixRepresentation G (Fin (n + 1))) :
    ∃ w₀ : Fin (n + 1) → k, w₀ ≠ 0 ∧ StabilizesLine ρ.dual w₀ b := by
  have : Smooth B.X.hom := hb.smooth
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  obtain ⟨w, hw, hstab⟩ := exists_stabilizedLine hfix hb.connectedSpace hb.isSolvableGroupScheme
    (ρ.dual.restrict b)
  refine ⟨w, hw, fun T x hx => ?_⟩
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨a, ha⟩ := hstab T y
  rw [MatrixRepresentation.pointMatrix_restrict] at ha
  exact ⟨a, ha⟩

end Langlands.GroupScheme.FlagCore
