import Langlands.GroupScheme.FlagCoreTorus

/-! # Generic integral weights of a split torus representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitTorusGenericWeights

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- **A split torus acts diagonally on rational points.** For a split torus `T` over a field
and a matrix representation `ρ` of `T`, there are a finite index type `I`, a change of basis
`P`, integral weights `wt` and a surjective parametrization `τ` of the rational points of `T`
by `I → kˣ`, such that `ρ(τ s)` is `P` times the diagonal matrix of the characters `wt` at `s`
times `P⁻¹`. -/
theorem exists_splitTorusDiagonal {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation T.toGrp n) :
    ∃ (I : Type u) (_ : Fintype I) (P : GL n k) (wt : n → I → ℤ)
      (τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X)),
      (∀ s, (ρ.rationalMatrix (τ s) : Matrix n n k) =
        (P : Matrix n n k) * diagonal (fun i => (FlagCore.charValue wt s i : k)) *
          (↑P⁻¹ : Matrix n n k)) ∧
      Function.Surjective τ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let σ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n := ρ.restrict e.inv
  obtain ⟨B, w, hw⟩ := GeneralLinear.CocharacterDiagonal.exists_diagonalizingMatrix I σ
  let τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X) := fun s =>
    FlagCore.baseAffineTestIso.hom ≫ (splitTorus.algebraPointsEquiv I k).symm s ≫
      e.inv.hom.hom
  refine ⟨I, this, B, w, τ, fun s => ?_, fun g => ?_⟩
  · have h1 : ρ.rationalMatrix (τ s) = GeneralLinear.CocharacterDiagonal.matrixAt I σ s := by
      rw [FlagCore.rationalMatrix_baseAffineTestIso, GeneralLinear.CocharacterDiagonal.matrixAt,
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
  · let y : (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) k)) ⟶
        (splitTorus (Spec (CommRingCat.of k)) I).X :=
      FlagCore.baseAffineTestIso.inv ≫ g ≫ e.hom.hom.hom
    refine ⟨splitTorus.algebraPointsEquiv I k y, ?_⟩
    have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ := by
      rw [← Grp.comp_hom_hom, e.hom_inv_id]
      rfl
    simp only [τ, MulEquiv.symm_apply_apply, y, Category.assoc, Iso.hom_inv_id_assoc]
    exact (congrArg (fun f => g ≫ f) he).trans (Category.comp_id g)

/-- **Generic integral weights of a split torus representation.** For a split torus `T` over
a field and a matrix representation `ρ` of `T`, there are a change of basis `P` and integral
weights `m` such that

* for every `z : kˣ` some rational point `t` of `T` acts by `P diag(z ^ m i) P⁻¹`, and
* every rational point `t` of `T` acts by `P diag(χ) P⁻¹` for some `χ` that is constant on
  each level set of `m`.

The weights `m` are the pairings of the weights of `ρ` with a cocharacter that separates
them. -/
theorem exists_genericWeights {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation T.toGrp n) :
    ∃ (P : GL n k) (m : n → ℤ),
      (∀ z : kˣ, ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X,
        (ρ.rationalMatrix t : Matrix n n k) =
          (P : Matrix n n k) * diagonal (fun i => ((z ^ m i : kˣ) : k)) *
            (↑P⁻¹ : Matrix n n k)) ∧
      (∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X, ∃ χ : n → kˣ,
        (∀ i l, m i = m l → χ i = χ l) ∧
        (ρ.rationalMatrix t : Matrix n n k) =
          (P : Matrix n n k) * diagonal (fun i => (χ i : k)) * (↑P⁻¹ : Matrix n n k)) := by
  classical
  obtain ⟨I, _, P, wt, τ, hτ, hsurj⟩ := exists_splitTorusDiagonal hT ρ
  obtain ⟨ν, hν⟩ := FlagCore.exists_separating wt
  refine ⟨P, fun i => ∑ a, ν a * wt i a, fun z => ⟨τ fun a => z ^ ν a, ?_⟩, fun t => ?_⟩
  · rw [hτ]
    simp only [FlagCore.charValue_cochar wt (fun i => rfl) z]
  · obtain ⟨s, rfl⟩ := hsurj t
    exact ⟨FlagCore.charValue wt s, fun i l h => by
      unfold FlagCore.charValue
      rw [hν i l h], hτ s⟩

end Langlands.GroupScheme.SplitTorusGenericWeights
