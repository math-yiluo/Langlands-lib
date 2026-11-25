/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver

/-!
# Towers of projective lines

For a scheme `S`, the *tower of projective lines* `Scheme.projectiveLineTower S d` is the
iterated relative projective line `ℙ¹_{ℙ¹_{⋯_{S}}}` (`d` times), the fibre product
`ℙ¹_S ×_S ⋯ ×_S ℙ¹_S`, as a scheme over `S`. Each step `ℙ¹_B ⟶ B` is proper and smooth of
relative dimension one, so the tower is proper over `S`. Over a field `k`, the affine space
`𝔸ᵈ_k` is open in the `d`-th step, and hence every affine scheme of finite type over `k` admits
an immersion into a tower of projective lines
(`AlgebraicGeometry.Scheme.exists_isImmersion_projectiveLineTower`).

This is the geometry behind the proof of the trace formula for Frobenius correspondences: the only
compactification used is
`𝔸¹ ⊆ ℙ¹`, applied in each coordinate.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The *tower of projective lines* over `S`: `projectiveLineTower S 0 = S` and
`projectiveLineTower S (d + 1) = ℙ¹_{projectiveLineTower S d}`, as schemes over `S`. -/
noncomputable def projectiveLineTower (S : Scheme.{u}) : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | d + 1 => overProjectiveLine (projectiveLineTower S d)

variable (S : Scheme.{u})

@[simp]
lemma projectiveLineTower_zero : projectiveLineTower S 0 = Over.mk (𝟙 S) :=
  rfl

@[simp]
lemma projectiveLineTower_succ (d : ℕ) :
    projectiveLineTower S (d + 1) = overProjectiveLine (projectiveLineTower S d) :=
  rfl

/-- Every structure morphism of the tower of projective lines satisfies a property of morphisms
which holds for the identity and is preserved by precomposition with projections `ℙ¹_B ⟶ B`. -/
lemma projectiveLineTower_hom_induction (P : MorphismProperty Scheme.{u}) (h₀ : P (𝟙 S))
    (h : ∀ B : Over S, P B.hom → P ((overProjectiveLineProj B).left ≫ B.hom)) (d : ℕ) :
    P (projectiveLineTower S d).hom := by
  induction d with
  | zero => exact h₀
  | succ d ih => exact h _ ih

instance (d : ℕ) : LocallyOfFiniteType (projectiveLineTower S d).hom :=
  projectiveLineTower_hom_induction S @LocallyOfFiniteType inferInstance
    (fun B (_ : LocallyOfFiniteType B.hom) ↦ inferInstance) d

instance (d : ℕ) : QuasiCompact (projectiveLineTower S d).hom :=
  projectiveLineTower_hom_induction S @QuasiCompact inferInstance
    (fun B (_ : QuasiCompact B.hom) ↦ inferInstance) d

instance (d : ℕ) : IsSeparated (projectiveLineTower S d).hom :=
  projectiveLineTower_hom_induction S @IsSeparated inferInstance
    (fun B (_ : IsSeparated B.hom) ↦ inferInstance) d

instance (d : ℕ) : IsProper (projectiveLineTower S d).hom :=
  projectiveLineTower_hom_induction S @IsProper inferInstance
    (fun B (_ : IsProper B.hom) ↦ inferInstance) d

/-- **`𝔸ᴺ_k` is open in the tower of projective lines**: there is an open immersion of
`polyAffine k N` into `projectiveLineTower (Spec k) N` over `Spec k`, given in each step by the
affine chart `𝔸¹ ⟶ ℙ¹`. -/
lemma exists_isOpenImmersion_polyAffine_projectiveLineTower (k : Type u) [Field k] (N : ℕ) :
    ∃ ι : polyAffine k N ⟶ projectiveLineTower (Spec (.of k)) N, IsOpenImmersion ι.left := by
  induction N with
  | zero =>
    refine ⟨Over.homMk (polyAffine k 0).hom (Category.comp_id _), ?_⟩
    exact inferInstanceAs (IsOpenImmersion (polyAffine k 0).hom)
  | succ N ih =>
    obtain ⟨a, ha⟩ := ih
    let c : polyAffine k (N + 1) ⟶ overProjectiveLine (polyAffine k N) :=
      Over.homMk ((polyAffineSuccHom k N : (polyAffine k (N + 1)).left ⟶ _) ≫
        ProjectiveLine.affineChart (polyAffine k N).left) (by
        dsimp only [overProjectiveLine, Over.mk_hom]
        rw [Category.assoc, ProjectiveLine.affineChart_over_assoc]
        exact (AffineSpace.homOfVector_over_assoc _ _ _).trans (Over.w (polyAffineProj k N)))
    refine ⟨c ≫ overProjectiveLineMap a, ?_⟩
    have : IsOpenImmersion (overProjectiveLineMap a).left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (isPullback_overProjectiveLineMap a).flip ha
    have : IsOpenImmersion c.left := inferInstanceAs
      (IsOpenImmersion (polyAffineSuccHom k N ≫ ProjectiveLine.affineChart _))
    rw [Over.comp_left]
    infer_instance

/-- **Affine schemes embed into towers of projective lines**: an affine scheme of finite type
over a field `k` admits an immersion over `k` into some `projectiveLineTower (Spec k) d`, the
composite of a closed immersion into `𝔸ᵈ_k` and of the open immersion of `𝔸ᵈ_k` into
`ℙ¹_k ×_k ⋯ ×_k ℙ¹_k`. -/
theorem exists_isImmersion_projectiveLineTower {k : Type u} [Field k] {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ (d : ℕ) (ι : X ⟶ (projectiveLineTower (Spec (.of k)) d).left),
      IsImmersion ι ∧ ι ≫ (projectiveLineTower (Spec (.of k)) d).hom = f := by
  have : IsAffine (Over.mk f).left := inferInstanceAs (IsAffine X)
  have : LocallyOfFiniteType (Over.mk f).hom := inferInstanceAs (LocallyOfFiniteType f)
  obtain ⟨N, i, hi⟩ := exists_isClosedImmersion_polyAffine (Over.mk f)
  obtain ⟨o, ho⟩ := exists_isOpenImmersion_polyAffine_projectiveLineTower k N
  refine ⟨N, i.left ≫ o.left, inferInstance, ?_⟩
  rw [Category.assoc, Over.w o]
  exact Over.w i

end AlgebraicGeometry.Scheme
