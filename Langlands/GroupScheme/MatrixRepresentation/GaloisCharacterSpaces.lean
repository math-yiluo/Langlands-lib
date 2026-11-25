import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Rational.CharacterGaloisAction

/-! # Galois compatibility of actual character spaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation

section Points

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

omit [IsAffineHom G.X.hom] in
private theorem characterEval_affine (χ : rationalCharacters G)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) :
    (characterEval χ ((algSpec (CommRingCat.of k)).obj (op A)) x :
        Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) =
      (Corepresented.affineSectionsIso A).inv.hom
        (Gm.affineUnitsEquiv (CommRingCat.of k) A (x ≫ χ.toMul.hom.hom) : A) := by
  change _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom _)
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id _).symm

/-- A character vector satisfies its eigenvector equation on every test scheme. -/
theorem characterSpace_pointMatrix {ρ : MatrixRepresentation G n}
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (fun r => scalarMap T (v r)) =
      (characterEval χ T x : Γ(T.left, ⊤)) • (fun r => scalarMap T (v r)) := by
  let A := CharacterUnits.Coord G
  let j := Lie.coordinateIso G
  let e := Corepresented.affineSectionsAlgEquiv A
  let q : A →+* Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) := e.symm.toRingHom
  have hs (c : k) : scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) c =
      q (algebraMap k A c) :=
    UnipotentMatrixCriterion.scalarMap_affine (R := CommRingCat.of k) A c
  have h₀ : (ρ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) j.hom :
        Matrix n n Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) *ᵥ
        (fun r => scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v r)) =
      (characterEval χ ((algSpec (CommRingCat.of k)).obj (op A)) j.hom :
        Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) •
        (fun r => scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v r)) := by
    rw [pointMatrix_eq_affineMatrix, characterEval_affine]
    change ((ρ.affineMatrix A j.hom : Matrix n n A).map q *ᵥ
        (fun r => scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v r))) =
      (fun r => q (Gm.affineUnitsEquiv (CommRingCat.of k) A
        (j.hom ≫ χ.toMul.hom.hom) : A) *
          scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v r))
    simp only [hs]
    funext r
    have h := congrArg q (congrFun (characterSpace_affine hv A j.hom) r)
    simpa only [RingHom.map_mulVec, map_mul, Pi.smul_apply, smul_eq_mul,
      Function.comp_def] using h
  let a := x ≫ j.inv
  have hx : a ≫ j.hom = x := by simp [a]
  have hmat := ρ.pointMatrix_naturality a j.hom
  have hχ := characterEval_naturality χ a j.hom
  rw [hx] at hmat hχ
  rw [hmat, hχ]
  funext r
  have h := congrArg a.left.appTop.hom (congrFun h₀ r)
  rw [a.left.appTop.hom.map_mulVec] at h
  change (((ρ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) j.hom :
      Matrix n n Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)).map a.left.appTop.hom) *ᵥ
        (fun i => scalarMap T (v i))) r =
    a.left.appTop.hom (characterEval χ ((algSpec (CommRingCat.of k)).obj (op A)) j.hom :
      Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)) * scalarMap T (v r)
  have hscalar (c : k) : a.left.appTop.hom
      (scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) c) = scalarMap T c :=
    scalarMap_naturality a c
  simpa only [map_mul, Pi.smul_apply, smul_eq_mul,
    Function.comp_def, hscalar] using h

/-- Character-space membership is equivalent to the eigenvector equation on all tests. -/
theorem mem_characterSpace_iff_points (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (v : n → k) :
    v ∈ ρ.characterSpace χ ↔
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
            (fun r => scalarMap T (v r)) =
          (characterEval χ T x : Γ(T.left, ⊤)) •
            (fun r => scalarMap T (v r)) := by
  constructor
  · exact fun hv T x => characterSpace_pointMatrix hv T x
  · intro h
    let A := CharacterUnits.Coord G
    have hh := h ((algSpec (CommRingCat.of k)).obj (op A)) (CharacterUnits.universalPoint G)
    rw [pointMatrix_eq_affineMatrix, characterEval_affine] at hh
    let e := Corepresented.affineSectionsAlgEquiv A
    let q : A →+* Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) := e.symm.toRingHom
    have hs (c : k) : scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) c =
        q (algebraMap k A c) :=
      UnipotentMatrixCriterion.scalarMap_affine (R := CommRingCat.of k) A c
    change (ρ.universalCharacterMatrix.map q *ᵥ
        (fun r => scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v r))) =
      (fun r => q (CharacterUnits.unit χ : A) *
        scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) (v r)) at hh
    simp only [hs] at hh
    apply (mem_characterSpace_iff ρ χ v).mpr
    funext r
    have hq : Function.Injective q :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1
    apply hq
    have hmap := q.map_mulVec
      (ρ.universalCharacterMatrix) (fun i => algebraMap k A (v i)) r
    simpa only [map_mul, Pi.smul_apply, smul_eq_mul, Function.comp_def] using
      hmap.trans (congrFun hh r)

end Points

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix of a representation defined over the ground field is unchanged by descent
of the test point along a coefficient automorphism. -/
theorem pointMatrix_baseChange_descentPoint (ρ : MatrixRepresentation G n)
    (σ : K ≃ₐ[k] K) (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X) :
    (ρ.baseChange (algebraBaseMap k K)).pointMatrix
        ((Over.map (galoisBaseMap k K σ)).obj T)
        (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G T x) =
      (ρ.baseChange (algebraBaseMap k K)).pointMatrix T x := by
  rw [pointMatrix_baseChange, baseChangePointsEquiv_descentPoint, pointMatrix_naturality,
    pointMatrix_baseChange]
  have hi : (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) T).inv.left = 𝟙 T.left := rfl
  rw [hi, Scheme.Hom.id_appTop]
  rfl

/-- Twisting a test scheme by `Spec σ` composes its scalar map with `σ`. -/
theorem scalarMap_galoisBaseMap (σ : K ≃ₐ[k] K)
    (T : Over (Spec (CommRingCat.of K))) (a : K) :
    scalarMap ((Over.map (galoisBaseMap k K σ)).obj T) a = scalarMap T (σ a) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (T.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop).hom a =
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ T.hom.appTop).hom (σ a)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable [IsAffineHom G.X.hom]

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

/-- Coefficientwise conjugation takes every character vector to a vector of the
Galois-conjugate character, including all nonreduced affine tests. -/
theorem conjugate_mem_characterSpace_baseChange (ρ : MatrixRepresentation G n)
    (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {v : n → K} (hv : v ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace χ) :
    (fun i => σ (v i)) ∈ (ρ.baseChange (algebraBaseMap k K)).characterSpace
      (rationalCharacters.galoisRepresentation k K G σ χ) := by
  apply (mem_characterSpace_iff_points _ _ _).mpr
  intro T x
  have h := characterSpace_pointMatrix hv
    ((Over.map (galoisBaseMap k K σ)).obj T)
    (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G T x)
  rw [pointMatrix_baseChange_descentPoint] at h
  have hs (c : K) : scalarMap ((Over.map (galoisBaseMap k K σ)).obj T) c =
      scalarMap T (σ c) := scalarMap_galoisBaseMap σ T c
  simpa only [hs, rationalCharacters.characterEval_galoisRepresentation] using h

end Galois

end Langlands.GroupScheme.MatrixRepresentation
