import Langlands.GroupScheme.MatrixRepresentation.FrobeniusPower
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterRepresentation
import Langlands.GroupScheme.StabilizerImageDichotomy

/-! # Frobenius kills finite-coordinate stability defects -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]

/-- The algebra-valued matrix of a base-field point is its rational matrix. -/
theorem affineMatrix_baseField (ρ : MatrixRepresentation G n)
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) k)) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ρ.rationalMatrix g = ρ.affineMatrix _ x := by
  let b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)) :=
    Over.homMk (𝟙 _) (by
      simp only [algSpec_obj_hom]
      change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
      simp)
  refine ⟨b ≫ x, ?_⟩
  have he := ρ.pointMatrix_naturality b x
  rw [pointMatrix_eq_affineMatrix] at he
  apply Units.ext
  ext r s
  have hs := congrArg (fun M : GL n Γ(Spec (CommRingCat.of k), ⊤) => M r s) he
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (ρ.pointMatrix _ (b ≫ x) r s) = _
  rw [hs]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((ρ.affineMatrix _ x : Matrix n n k) r s)) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id _


variable [IsAffineHom G.X.hom]

/-- The coordinate-algebra defect in the universal split-coordinate stability equation. -/
def affineCoordinateStabilityDefect (ρ : MatrixRepresentation G n)
    (B : Matrix n m k) (C : Matrix m n k) : Matrix n m (CharacterUnits.Coord G) :=
  ρ.universalCharacterMatrix * B.map (algebraMap k (CharacterUnits.Coord G)) -
    B.map (algebraMap k (CharacterUnits.Coord G)) *
      (C.map (algebraMap k (CharacterUnits.Coord G)) * ρ.universalCharacterMatrix *
        B.map (algebraMap k (CharacterUnits.Coord G)))

/-- Rational stability forces every universal stability-defect coefficient to be
nilpotent, without a reducedness premise on the ambient group. -/
theorem isNilpotent_affineCoordinateStabilityDefect [IsAlgClosed k]
    [LocallyOfFiniteType G.X.hom] (ρ : MatrixRepresentation G n)
    (B : Matrix n m k) (C : Matrix m n k)
    (h : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (ρ.rationalMatrix g : Matrix n n k) * B =
        B * (C * (ρ.rationalMatrix g : Matrix n n k) * B)) (r : n) (s : m) :
    IsNilpotent (ρ.affineCoordinateStabilityDefect B C r s) := by
  have : Algebra.FiniteType k (CharacterUnits.Coord G) := Lie.coordinateAlgebraFiniteType G
  apply StabilizerImageDichotomy.isNilpotent_of_forall_algHom (k := k)
  intro φ
  let x := (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫
    CharacterUnits.universalPoint G
  obtain ⟨g, hg⟩ := ρ.affineMatrix_baseField x
  have hM := congrArg Units.val
    (ρ.affineMatrix_naturality (CommAlgCat.ofHom φ) (CharacterUnits.universalPoint G))
  change (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) k) x : Matrix n n k) =
    ρ.universalCharacterMatrix.map φ at hM
  have hB : (B.map (algebraMap k (CharacterUnits.Coord G))).map φ = B := by
    ext a b
    exact φ.commutes _
  have hC : (C.map (algebraMap k (CharacterUnits.Coord G))).map φ = C := by
    ext a b
    exact φ.commutes _
  have he : (ρ.affineCoordinateStabilityDefect B C).map φ = 0 := by
    simp only [affineCoordinateStabilityDefect, Matrix.map_sub _ (map_sub _),
      Matrix.map_mul (f := φ), hB, hC, ← hM, ← hg]
    exact sub_eq_zero.mpr (h g)
  exact congrArg (fun M : Matrix n m k => M r s) he


/-- One characteristic-power twist turns rational coordinate stability into
stability on every test scheme in positive characteristic. -/
theorem exists_frobeniusPower_isStableCoordinates [IsAlgClosed k]
    [LocallyOfFiniteType G.X.hom] (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (ρ : MatrixRepresentation G n) (B : Matrix n m k) (C : Matrix m n k)
    (h : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (ρ.rationalMatrix g : Matrix n n k) * B =
        B * (C * (ρ.rationalMatrix g : Matrix n n k) * B)) :
    ∃ e : ℕ, (ρ.frobeniusPower p e).IsStableCoordinates
      (B.map (characteristicPowerMap k p k e))
      (C.map (characteristicPowerMap k p k e)) := by
  classical
  let A := CharacterUnits.Coord G
  let D := ρ.affineCoordinateStabilityDefect B C
  have hn : ∀ q : n × m, ∃ t : ℕ, D q.1 q.2 ^ t = 0 :=
    fun q => isNilpotent_affineCoordinateStabilityDefect ρ B C h q.1 q.2
  choose t ht using hn
  obtain ⟨e, he⟩ := Finite.exists_le t
  let F := characteristicPowerMap k p A e
  let f := characteristicPowerMap k p k e
  have hkill : D.map F = 0 := by
    ext r s
    exact pow_eq_zero_of_le ((he (r, s)).trans (Nat.lt_pow_self hp.one_lt).le) (ht (r, s))
  refine ⟨e, ?_⟩
  apply isStableCoordinates_of_affine_model (ρ.frobeniusPower p e) (Lie.coordinateIso G)
    (B.map f) (C.map f)
  rw [← CharacterUnits.universalPoint_eq, frobeniusPower_affineMatrix]
  have hB : (B.map f).map (algebraMap k A) =
      (B.map (algebraMap k A)).map F := by
    ext r s
    change algebraMap k A (B r s ^ p ^ e) = algebraMap k A (B r s) ^ p ^ e
    exact map_pow _ _ _
  have hC : (C.map f).map (algebraMap k A) =
      (C.map (algebraMap k A)).map F := by
    ext r s
    change algebraMap k A (C r s ^ p ^ e) = algebraMap k A (C r s) ^ p ^ e
    exact map_pow _ _ _
  change ρ.universalCharacterMatrix.map F * (B.map f).map (algebraMap k A) =
    (B.map f).map (algebraMap k A) *
      ((C.map f).map (algebraMap k A) * ρ.universalCharacterMatrix.map F *
        (B.map f).map (algebraMap k A))
  rw [hB, hC]
  apply sub_eq_zero.mp
  simpa only [D, affineCoordinateStabilityDefect, Matrix.map_sub _ (map_sub F),
    Matrix.map_mul (f := F)] using hkill

end Langlands.GroupScheme.MatrixRepresentation
