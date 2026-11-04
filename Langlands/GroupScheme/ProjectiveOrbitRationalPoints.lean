import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.ProjectiveOrbit
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.CoordinateLines
import Langlands.AlgebraicGeometry.ProjectiveSpace.RationalPointZeros
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure
import Langlands.GroupScheme.ProjectiveLineStabilizerQuotient
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Homogeneous coordinates of rational points of projective orbits -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.ProjectiveOrbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] (n : ℕ)

/-- The coefficient map from a field to the global functions on its spectrum. -/
abbrev fieldToGlobal (k : Type u) [Field k] : k →+* Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem toSpecΓ_fieldToGlobal :
    (Spec (CommRingCat.of k)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (fieldToGlobal k)) =
      𝟙 _ :=
  AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv _

/-- Over a field, the matrix action of global-function matrices is the projective linear
action of the corresponding matrix with entries in the field. -/
theorem matrixAction_toPolynomial (M : GL (Fin (n + 1)) Γ(Spec (CommRingCat.of k), ⊤)) :
    matrixAction n M ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) =
      RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) ≫
        ProjectiveSpace.linearAction k n (coordinateEquiv n
          (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom M)) := by
  have h : matrixAction n M = RelativeProjectiveSpace.linearAction (𝟙 _) (coordinateEquiv n
      (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom M)) := by
    unfold matrixAction RelativeProjectiveSpace.globalLinearAction
    symm
    apply RelativeProjectiveSpace.linearAction_coefficientMap (𝟙 _) _ (fieldToGlobal k)
      toSpecΓ_fieldToGlobal
    intro i j
    simp only [coordinateEquiv_apply, mulVec_single_one]
    change (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((M : Matrix _ _ _) i j)) =
      (M : Matrix _ _ _) i j
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) _
  rw [h, RelativeProjectiveSpace.linearAction_toPolynomial]

theorem basisVector_ne_zero (j : Fin (n + 1)) : (Pi.single j 1 : Fin (n + 1) → k) ≠ 0 := by
  intro h
  simpa using congrFun h j

/-- The coordinate basis section over a field is the rational point with homogeneous
coordinates the basis vector. -/
theorem basisSection_toPolynomial_eq_fromOfGlobalSections (j : Fin (n + 1)) :
    RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j ≫
        RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) =
      Proj.fromOfGlobalSections (projectiveSpaceGrading k n)
        ((fieldToGlobal k).comp (MvPolynomial.eval (Pi.single j 1)))
        (ProjectiveSpace.irrelevant_map_eval_eq_top _ (basisVector_ne_zero n j)) := by
  let : Algebra k Γ(Spec (CommRingCat.of k), ⊤) := (fieldToGlobal k).toAlgebra
  rw [← RelativeProjectiveSpace.toPolynomial_coefficientMap (𝟙 _) _ (fieldToGlobal k)
    toSpecΓ_fieldToGlobal, RelativeProjectiveSpace.basisSection_toPolynomial_assoc,
    ProjectiveSpace.CoordinateLines.basisPoint_coefficientMap n (fieldToGlobal k)
      (by rw [Algebra.algebraMap_self, RingHom.id_comp]; rfl)]
  unfold ProjectiveSpace.CoordinateLines.basisPoint
  have hf : ProjectiveSpace.CoordinateLines.basisEval (R := k) n (Spec (CommRingCat.of k)) j =
      (fieldToGlobal k).comp (MvPolynomial.eval (Pi.single j 1)) := by
    ext a
    · exact ProjectiveSpace.CoordinateLines.basisEval_eq_eval n _ j _
    · exact ProjectiveSpace.CoordinateLines.basisEval_eq_eval n _ j _
  congr 1

/-- Pulling a section back along the identity does nothing. -/
theorem pullbackPoint_id {S : Scheme.{u}} (p : S ⟶ RelativeProjectiveSpace S n)
    (hp : p ≫ RelativeProjectiveSpace.toBase S n = 𝟙 S) :
    pullbackPoint n p (𝟙 S) = p := by
  apply RelativeProjectiveSpace.hom_ext <;> simp [hp]

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational point of `ProjectiveSpace k n` obtained from a rational point `g` of `G`
through the orbit map of the coordinate line `e_j` has homogeneous coordinates
`ρ(g) e_j`. -/
theorem hasCoordinates_orbitMap (ρ : MatrixRepresentation G (Fin (n + 1))) (j : Fin (n + 1))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ProjectiveSpace.HasCoordinates
      (((g ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j)).left ≫
        RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))))
          (IsLocalRing.closedPoint k))
      ((ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single j 1) := by
  have hpt : (g ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j)).left ≫
      RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) =
        CategoryStruct.comp (Y := ProjectiveSpace k n)
          (Proj.fromOfGlobalSections (projectiveSpaceGrading k n)
            ((fieldToGlobal k).comp (MvPolynomial.eval (Pi.single j 1)))
            (ProjectiveSpace.irrelevant_map_eval_eq_top _ (basisVector_ne_zero n j)))
          (ProjectiveSpace.linearAction k n (coordinateEquiv n (ρ.rationalMatrix g))) := by
    rw [comp_orbitMap, orbitSection, Category.assoc, Category.assoc,
      RelativeProjectiveSpace.map_toPolynomial]
    change pullbackPoint n (RelativeProjectiveSpace.basisSection n _ j) (𝟙 _) ≫
      matrixAction n _ ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 _ ≫ 𝟙 _) = _
    rw [Category.comp_id, pullbackPoint_id n _ (RelativeProjectiveSpace.basisSection_toBase n _ j),
      matrixAction_toPolynomial, ← Category.assoc, basisSection_toPolynomial_eq_fromOfGlobalSections]
    rfl
  rw [hpt, Scheme.Hom.comp_apply]
  have h := (ProjectiveSpace.hasCoordinates_fromOfGlobalSections (fieldToGlobal k)
    (Pi.single j 1) (ProjectiveSpace.irrelevant_map_eval_eq_top _ (basisVector_ne_zero n j))).linearAction
    (coordinateEquiv n (ρ.rationalMatrix g))
  rw [coordinateEquiv_apply] at h
  convert h using 2

/-- The rational point with nonzero homogeneous coordinates `c` lies over the identity of the
base. -/
theorem fromOfGlobalSections_toSpec {c : Fin (n + 1) → k} (hc : c ≠ 0) :
    CategoryStruct.comp (Y := ProjectiveSpace k n)
      (Proj.fromOfGlobalSections (projectiveSpaceGrading k n)
        ((fieldToGlobal k).comp (MvPolynomial.eval c))
        (ProjectiveSpace.irrelevant_map_eval_eq_top _ hc))
      (projectiveSpaceToSpec k n) = 𝟙 _ := by
  unfold projectiveSpaceToSpec
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  convert toSpecΓ_fieldToGlobal (k := k) using 3
  congr 1
  ext r
  change fieldToGlobal k (MvPolynomial.eval c (MvPolynomial.C r)) = fieldToGlobal k r
  rw [MvPolynomial.eval_C]

/-- **Rational points in the closure of a projective orbit.** Let `q : G ⟶ Q` be a quotient
onto a proper scheme over an algebraically closed field whose fibers stabilize the
coordinate line `e_j` under `ρ`. If `c` is a nonzero vector at which every homogeneous
polynomial vanishing on the orbit vectors `ρ(g) e_j` of rational points `g` vanishes, then `c`
is a nonzero multiple of one orbit vector. -/
theorem exists_eq_smul_orbit_of_isProper [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (ρ : MatrixRepresentation G (Fin (n + 1))) (j : Fin (n + 1))
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X), g ≫ q = h ≫ q →
      ∃ a : Γ(T.left, ⊤)ˣ,
        (ρ.pointMatrix T (g⁻¹ * h) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
            Pi.single j 1 =
          (a : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) : Fin (n + 1) → Γ(T.left, ⊤)))
    (c : Fin (n + 1) → k) (hc0 : c ≠ 0)
    (hc : ∀ (f : MvPolynomial (Fin (n + 1)) k) (d : ℕ), f.IsHomogeneous d →
      (∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        MvPolynomial.eval ((ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
          Pi.single j 1) f = 0) →
      MvPolynomial.eval c f = 0) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (a : k), a ≠ 0 ∧
      c = a • ((ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single j 1) := by
  have hdesc : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X), a ≫ q = b ≫ q →
      a ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j) =
        b ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j) := by
    intro T a b hab
    rw [orbitMap_fibers, pullbackPoint_basisSection, basisSection_matrixAction_eq_iff]
    exact hq T a b hab
  set Φ := HomogeneousQuotientComparison.desc q
    (orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j)) hdesc with hΦdef
  have hΦ : q ≫ Φ = orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j) :=
    HomogeneousQuotientComparison.fac_desc _ _ _
  set F' : Q.left ⟶ ProjectiveSpace k n :=
    Φ.left ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) with hF'def
  have hF'spec : F' ≫ projectiveSpaceToSpec k n = Q.hom := by
    rw [hF'def, Category.assoc, RelativeProjectiveSpace.toPolynomial_toSpec, Category.comp_id]
    exact Over.w Φ
  have : IsProper (F' ≫ projectiveSpaceToSpec k n) := by
    rw [hF'spec]
    infer_instance
  have : IsProper F' := IsProper.of_comp F' (projectiveSpaceToSpec k n)
  have hZ : IsClosed (Set.range F') := F'.isClosedMap.isClosed_range
  have hpt : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (g ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n _ j)).left ≫
          RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k))) =
        g.left ≫ q.left ≫ F' := by
    intro g
    rw [← hΦ]
    rfl
  have horbit : ∀ s ∈ Set.range fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
      (ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single j 1,
      ∃ x ∈ Set.range F', ProjectiveSpace.HasCoordinates x s := by
    rintro _ ⟨g, rfl⟩
    refine ⟨F' (q.left (g.left (IsLocalRing.closedPoint k))), Set.mem_range_self _, ?_⟩
    have h := hasCoordinates_orbitMap n ρ j g
    rw [hpt g, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    exact h
  set pc : Spec (CommRingCat.of k) ⟶ ProjectiveSpace k n :=
    Proj.fromOfGlobalSections (projectiveSpaceGrading k n)
      ((fieldToGlobal k).comp (MvPolynomial.eval c))
      (ProjectiveSpace.irrelevant_map_eval_eq_top _ hc0) with hpcdef
  have hpc : ProjectiveSpace.HasCoordinates (pc (IsLocalRing.closedPoint k)) c :=
    ProjectiveSpace.hasCoordinates_fromOfGlobalSections (fieldToGlobal k) c _
  have hy : pc (IsLocalRing.closedPoint k) ∈ Set.range F' := by
    refine ProjectiveSpace.mem_of_isClosed hZ _ horbit ?_ hpc
    intro f d hf hvan
    exact hc f d hf fun g => hvan _ ⟨g, rfl⟩
  obtain ⟨z, hz⟩ := hy
  obtain ⟨w, hw⟩ := q.left.surjective z
  have hFspec : (q.left ≫ F') ≫ projectiveSpaceToSpec k n = G.X.hom := by
    rw [Category.assoc, hF'spec, Over.w q]
  have : LocallyOfFiniteType ((q.left ≫ F') ≫ projectiveSpaceToSpec k n) := by
    rw [hFspec]
    infer_instance
  have : LocallyOfFiniteType (q.left ≫ F') :=
    locallyOfFiniteType_of_comp (q.left ≫ F') (projectiveSpaceToSpec k n)
  obtain ⟨g₀, hg₀⟩ := exists_rationalPoint_lift_of_mem_range (q.left ≫ F') pc
    ⟨w, by rw [Scheme.Hom.comp_apply, hw, hz]⟩
  have hg₀S : g₀ ≫ G.X.hom = 𝟙 _ := by
    rw [← hFspec, ← Category.assoc, hg₀]
    exact fromOfGlobalSections_toSpec n hc0
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk g₀ hg₀S
  have h := hasCoordinates_orbitMap n ρ j g
  rw [hpt g] at h
  change ProjectiveSpace.HasCoordinates ((g₀ ≫ q.left ≫ F') (IsLocalRing.closedPoint k)) _ at h
  rw [hg₀] at h
  obtain ⟨a, ha, hac⟩ := h.exists_eq_smul hpc
  exact ⟨g, a, ha, hac⟩

end Langlands.GroupScheme.ProjectiveOrbit
