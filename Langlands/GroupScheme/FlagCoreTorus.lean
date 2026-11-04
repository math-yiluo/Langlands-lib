import Langlands.GroupScheme.FlagCoreLinear
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Absolute.RationalNormalizer
import Langlands.GroupScheme.HomConjugacy

/-! # Maximal tori on rational points: diagonalization and torus-fixed lines -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FlagCore

set_option backward.isDefEq.respectTransparency false

section BaseTest

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- The base test `Spec R` over itself, identified with the affine test of the algebra `R`. -/
def baseAffineTestIso : Over.mk (𝟙 (Spec R)) ≅ (algSpec R).obj (op (CommAlgCat.of R R)) :=
  Gm.affineTestIso _ _ (by
    change 𝟙 (Spec R) = Spec.map (𝟙 R)
    exact (Spec.map_id R).symm)

/-- The rational matrix of a point of the affine test of `R` is its affine matrix. -/
theorem rationalMatrix_baseAffineTestIso (ρ : MatrixRepresentation G n)
    (x : (algSpec R).obj (op (CommAlgCat.of R R)) ⟶ G.X) :
    ρ.rationalMatrix (baseAffineTestIso.hom ≫ x) = ρ.affineMatrix (CommAlgCat.of R R) x := by
  apply Units.ext
  ext i j
  change (Scheme.ΓSpecIso R).hom
      ((ρ.pointMatrix (Over.mk (𝟙 (Spec R))) (baseAffineTestIso.hom ≫ x)).val i j) = _
  rw [MatrixRepresentation.pointMatrix_naturality, MatrixRepresentation.pointMatrix_eq_affineMatrix,
    Corepresented.affineSectionsIso_inv_ringHom]
  change (Scheme.ΓSpecIso R).hom ((𝟙 (Spec R) : Spec R ⟶ Spec R).appTop
      ((Scheme.ΓSpecIso R).inv _)) = _
  rw [Scheme.Hom.id_appTop]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso R) _

end BaseTest

variable {k : Type u} [Field k]

/-- **A maximal torus acts diagonally on rational points.** Granting finite Galois splitting
of tori, for a maximal torus `t : T ⟶ G` over an algebraically closed field and a matrix
representation `ρ` of `G`, there are a finite index type `I`, a change of basis `P`, integral
weights `wt` and a parametrization `τ` of the rational points of the image of `t` by
`I → kˣ`, such that `ρ(τ s)` is `P` times the diagonal matrix of the characters `wt` at `s`
times `P⁻¹`. -/
theorem exists_torusDiagonal (hsplit : TorusFiniteGaloisSplittingStatement.{u}) [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {t : T.toGrp ⟶ G} (ht : IsMaximalTorus t) {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) :
    ∃ (I : Type u) (_ : Fintype I) (P : GL n k) (wt : n → I → ℤ)
      (τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)),
      (∀ s, (ρ.rationalMatrix (τ s) : Matrix n n k) =
        (P : Matrix n n k) * diagonal (fun i => (charValue wt s i : k)) *
          (↑P⁻¹ : Matrix n n k)) ∧
      Set.range τ =
        Set.range fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X => z ≫ t.hom.hom := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := IsTorus.isSplitTorus_of_finiteGaloisSplitting hsplit ht.1
  let : Fintype I := Fintype.ofFinite I
  let σ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n := ρ.restrict (e.inv ≫ t)
  obtain ⟨B, w, hw⟩ := GeneralLinear.CocharacterDiagonal.exists_diagonalizingMatrix I σ
  let τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) := fun s =>
    baseAffineTestIso.hom ≫ (splitTorus.algebraPointsEquiv I k).symm s ≫ (e.inv ≫ t).hom.hom
  refine ⟨I, this, B, w, τ, fun s => ?_, ?_⟩
  · have h1 : ρ.rationalMatrix (τ s) = GeneralLinear.CocharacterDiagonal.matrixAt I σ s := by
      rw [rationalMatrix_baseAffineTestIso, GeneralLinear.CocharacterDiagonal.matrixAt,
        MatrixRepresentation.affineMatrix_restrict]
    have hB : Matrix.GeneralLinearGroup.map (algebraMap k k) B = B := by
      apply Units.ext
      ext i j
      rfl
    have h2 := hw k s
    rw [hB, ← h1] at h2
    have h3 : ρ.rationalMatrix (τ s) = B * GeneralLinear.CocharacterDiagonal.diagonalMatrix
        (fun j => splitTorus.exponentValue I s (Multiplicative.ofAdd (w j))) * B⁻¹ := by
      rw [← h2]
      group
    rw [h3]
    rfl
  · ext g
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨baseAffineTestIso.hom ≫ (splitTorus.algebraPointsEquiv I k).symm s ≫ e.inv.hom.hom,
        ?_⟩
      simp only [τ, Grp.comp_hom_hom, Category.assoc]
    · rintro ⟨z, rfl⟩
      let y : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶
          (splitTorus (Spec (CommRingCat.of k)) I).X :=
        baseAffineTestIso.inv ≫ z ≫ e.hom.hom.hom
      refine ⟨splitTorus.algebraPointsEquiv I k y, ?_⟩
      have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ := by
        rw [← Grp.comp_hom_hom, e.hom_inv_id]
        rfl
      simp only [τ, MulEquiv.symm_apply_apply, y, Grp.comp_hom_hom, Category.assoc,
        reassoc_of% he, Iso.hom_inv_id_assoc]

section FixedLine

variable [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {m : Type} [Fintype m] [DecidableEq m]

omit [IsAlgClosed k] in
/-- At the base test, a unit multiple of the coordinate line `j` under a point matrix is the
same as a multiple of it under the rational matrix. -/
theorem exists_unit_pointMatrix_iff (ρ : MatrixRepresentation G m) (j : m)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (∃ c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)ˣ,
      (ρ.pointMatrix _ x : Matrix m m Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) *ᵥ
          Pi.single j 1 =
        (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) •
          (Pi.single j (1 : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
            m → Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))) ↔
      ∃ c : k, (ρ.rationalMatrix x : Matrix m m k) *ᵥ Pi.single j 1 = c • Pi.single j 1 := by
  set M := (ρ.pointMatrix _ x :
    Matrix m m Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) with hM
  have hrat : (ρ.rationalMatrix x : Matrix m m k) =
      M.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom := rfl
  have hsingle : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      ((Pi.single j (1 : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
        m → Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) i) =
        (Pi.single j (1 : k) : m → k) i := fun i => by
    by_cases hi : i = j
    · subst hi
      simp
    · simp [hi]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)), ?_⟩
    rw [hrat]
    funext i
    have hci := congrFun hc i
    simp only [mulVec_single_one, col_apply, map_apply, Pi.smul_apply, smul_eq_mul] at hci ⊢
    rw [hci, map_mul, hsingle]
  · rintro ⟨c, hc⟩
    have he : (Pi.single j (1 : k) : m → k) ≠ 0 := fun h =>
      one_ne_zero (α := k) (by simpa using congrFun h j)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact FlagCore.mulVec_ne_zero (ρ.rationalMatrix x) he hc
    refine ⟨(Units.mk0 c hc0).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom, ?_⟩
    funext i
    have hci := congrFun hc i
    rw [hrat] at hci
    simp only [mulVec_single_one, col_apply, map_apply, Pi.smul_apply, smul_eq_mul] at hci ⊢
    rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) (M i j), hci, map_mul,
      ← hsingle, Iso.hom_inv_id_apply]
    rfl

/-- **Torus-fixed lines are stable under `U`.** Let `B` be a Borel subgroup which is the
stabilizer of the coordinate line `j` of `ρ` on all tests, and let `U` lie in every Borel
subgroup through the maximal torus `t`. Let `τ` parametrize the rational points of `t`. If the
line of `ρ(g) e_j` is fixed by every `ρ(τ s)`, then it is stable under every rational point of
`U`. -/
theorem stable_of_isTorusFixed {B U : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G} (ht : IsMaximalTorus t)
    {b : B ⟶ G} (hb : IsBorelSubgroup b) {i : U ⟶ G}
    (hthrough : ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G),
      IsBorelSubgroup b' → SubgroupFunctor.range t ≤ SubgroupFunctor.range b' →
        SubgroupFunctor.range i ≤ SubgroupFunctor.range b')
    (ρ : MatrixRepresentation G m) (j : m)
    (hstab : ∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier Z ↔
        ∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x : Matrix m m Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) : m → Γ(Z.left, ⊤)))
    {I : Type*} [Fintype I] (τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hτ : Set.range τ =
      Set.range fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X => z ≫ t.hom.hom)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix (Pi.single j 1) g))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) :
    ∃ c : k, (ρ.rationalMatrix (x ≫ i.hom.hom) : Matrix m m k) *ᵥ
        orbitVec ρ.rationalMatrix (Pi.single j 1) g =
      c • orbitVec ρ.rationalMatrix (Pi.single j 1) g := by
  have hrat : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, y ∈ (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ↔
      ∃ c : k, (ρ.rationalMatrix y : Matrix m m k) *ᵥ Pi.single j 1 = c • Pi.single j 1 := fun y =>
    (hstab _ y).trans (exists_unit_pointMatrix_iff ρ j y)
  -- Conjugating by `g` moves the stabilizer of the line of `ρ(g) e` to `B`.
  have hto : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, (∃ c : k, (ρ.rationalMatrix y : Matrix m m k) *ᵥ orbitVec ρ.rationalMatrix (Pi.single j 1) g =
      c • orbitVec ρ.rationalMatrix (Pi.single j 1) g) → g⁻¹ * y * g ∈ (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rintro y ⟨c, hc⟩
    refine (hrat _).mpr ⟨c, ?_⟩
    unfold orbitVec at hc
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hc,
      mulVec_smul, mulVec_mulVec, map_inv, Units.inv_mul, one_mulVec]
  have hfrom : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, g⁻¹ * y * g ∈ (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
      ∃ c : k, (ρ.rationalMatrix y : Matrix m m k) *ᵥ orbitVec ρ.rationalMatrix (Pi.single j 1) g = c • orbitVec ρ.rationalMatrix (Pi.single j 1) g := by
    intro y hy
    obtain ⟨c, hc⟩ := (hrat _).mp hy
    refine ⟨c, ?_⟩
    have hyg : y * g = g * (g⁻¹ * y * g) := by group
    unfold orbitVec
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, hyg, map_mul, Units.val_mul,
      ← mulVec_mulVec, hc, mulVec_smul]
  -- The torus conjugated by `g⁻¹` lies in `B`, first on rational points, then on all tests.
  have hTs : Smooth T.toGrp.X.hom := IsTorus.smooth ht.1
  have : IsReduced T.toGrp.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k T.toGrp.X.left T.toGrp.X.hom
  have hle₀ : SubgroupFunctor.range (t ≫ (G.innerIso g⁻¹).hom) ≤ SubgroupFunctor.range b := by
    apply SubgroupFunctor.range_le_of_algClosed_points hb.isClosedSubgroup
    intro y hy
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    obtain ⟨s, hs⟩ : z ≫ t.hom.hom ∈ Set.range τ := by
      rw [hτ]
      exact ⟨z, rfl⟩
    have h := hto (τ s) (hg s)
    rw [hs] at h
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_inv,
      constantPoint_self, inv_inv]
    exact h
  have hle : SubgroupFunctor.range t ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom) := by
    intro V y hy
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp
      (hle₀ V (SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨w, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hw, innerIso_inv_hom, Category.assoc,
      ← Grp.comp_hom_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- Hence `U` lies in the Borel subgroup `g B g⁻¹`.
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp
    (hthrough B (b ≫ (G.innerIso g).hom) (hb.comp_iso _) hle _
      (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩))
  apply hfrom
  rw [← hw, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_self]
  refine SubgroupFunctor.mem_range.mpr ⟨w, ?_⟩
  group

end FixedLine

end Langlands.GroupScheme.FlagCore
