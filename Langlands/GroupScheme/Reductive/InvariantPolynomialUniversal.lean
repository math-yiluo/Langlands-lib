import Langlands.GroupScheme.Reductive.ZeroWeightProjection
import Langlands.GroupScheme.Rational.ProductDetection
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Universal polynomial identities and epimorphic subgroup products -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

set_option backward.isDefEq.respectTransparency false

section PolynomialAlgebra

variable {A B : Type*} [CommRing A] [CommRing B]
  {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Scalar change commutes with linear substitution. -/
theorem map_linearPullback (f : A →+* B) (M : Matrix n n A) (F : MvPolynomial n A) :
    MvPolynomial.map f (linearPullback M F) =
      linearPullback (M.map f) (MvPolynomial.map f F) := by
  rw [linearPullback, MvPolynomial.map_eval₂, linearPullback]
  congr 1
  funext i
  simp [Matrix.map_apply]

omit [DecidableEq n] in
/-- Substitution reverses the order of matrix composition. -/
theorem linearPullback_mul (P Q : Matrix n n A) (F : MvPolynomial n A) :
    linearPullback (P * Q) F = linearPullback Q (linearPullback P F) := by
  change MvPolynomial.eval₂ MvPolynomial.C
      ((P * Q).map MvPolynomial.C *ᵥ MvPolynomial.X) F =
    MvPolynomial.eval₂ MvPolynomial.C (Q.map MvPolynomial.C *ᵥ MvPolynomial.X)
      (linearPullback P F)
  rw [eval₂_linearPullback, Matrix.mulVec_mulVec, Matrix.map_mul]

end PolynomialAlgebra

variable {R : CommRingCat.{u}} {G H Z D : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The transformed polynomial at a point, with coefficients in its global sections. -/
def actionPolynomial (ρ : MatrixRepresentation G n) {T : Over (Spec R)}
    (g : T ⟶ G.X) (F : MvPolynomial n R) : MvPolynomial n Γ(T.left, ⊤) :=
  linearPullback (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤))
    (MvPolynomial.map (scalarMap T) F)

/-- Evaluation of the transformed polynomial is evaluation after the matrix action. -/
theorem eval_actionPolynomial (ρ : MatrixRepresentation G n) {T : Over (Spec R)}
    (g : T ⟶ G.X) (F : MvPolynomial n R) (x : n → Γ(T.left, ⊤)) :
    MvPolynomial.eval x (ρ.actionPolynomial g F) =
      MvPolynomial.eval₂ (scalarMap T)
        ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F := by
  rw [actionPolynomial, ← MvPolynomial.eval₂_id, eval₂_linearPullback]
  change MvPolynomial.eval ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x)
    (MvPolynomial.map (scalarMap T) F) = _
  exact MvPolynomial.eval_map _ _ _

/-- The transformed polynomial is natural under every relative test map. -/
theorem actionPolynomial_naturality (ρ : MatrixRepresentation G n)
    {T U : Over (Spec R)} (a : U ⟶ T) (g : T ⟶ G.X) (F : MvPolynomial n R) :
    MvPolynomial.map a.left.appTop.hom (ρ.actionPolynomial g F) =
      ρ.actionPolynomial (a ≫ g) F := by
  rw [actionPolynomial, map_linearPullback, actionPolynomial, pointMatrix_naturality,
    MvPolynomial.map_map]
  have hs : a.left.appTop.hom.comp (scalarMap T) = scalarMap U := by
    ext c
    exact scalarMap_naturality a c
  rw [hs]
  rfl

/-- All-test polynomial invariance follows from the universal polynomial identity. -/
theorem isInvariantPolynomial_of_universal (ρ : MatrixRepresentation G n)
    (F : MvPolynomial n R)
    (hF : ρ.actionPolynomial (𝟙 G.X) F = MvPolynomial.map (scalarMap G.X) F) :
    ρ.IsInvariantPolynomial F := by
  intro T g x
  have h := congrArg (MvPolynomial.map g.left.appTop.hom) hF
  rw [actionPolynomial_naturality, Category.comp_id, MvPolynomial.map_map] at h
  have hs : g.left.appTop.hom.comp (scalarMap G.X) = scalarMap T := by
    ext c
    exact scalarMap_naturality g c
  rw [hs] at h
  have hx := congrArg (MvPolynomial.eval x) h
  simpa only [eval_actionPolynomial, MvPolynomial.eval_map] using hx

/-- All-test invariance gives the corresponding equation in every affine test algebra. -/
theorem IsInvariantPolynomial.affine {ρ : MatrixRepresentation G n}
    {F : MvPolynomial n R} (hF : ρ.IsInvariantPolynomial F)
    (A : CommAlgCat.{u} R) (g : (algSpec R).obj (op A) ⟶ G.X) (x : n → A) :
    MvPolynomial.eval₂ (algebraMap R A) ((ρ.affineMatrix A g : Matrix n n A) *ᵥ x) F =
      MvPolynomial.eval₂ (algebraMap R A) x F := by
  let e := Corepresented.affineSectionsAlgEquiv A
  apply e.symm.injective
  change e.symm.toRingHom (MvPolynomial.eval₂ (algebraMap R A)
      ((ρ.affineMatrix A g : Matrix n n A) *ᵥ x) F) =
    e.symm.toRingHom (MvPolynomial.eval₂ (algebraMap R A) x F)
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  have hs : e.symm.toRingHom.comp (algebraMap R A) =
      scalarMap ((algSpec R).obj (op A)) := by
    ext c
    exact (UnipotentMatrixCriterion.scalarMap_affine A c).symm
  rw [hs]
  have hv : e.symm.toRingHom ∘ ((ρ.affineMatrix A g : Matrix n n A) *ᵥ x) =
      (ρ.pointMatrix ((algSpec R).obj (op A)) g : Matrix n n Γ(((algSpec R).obj (op A)).left, ⊤)) *ᵥ
        (e.symm.toRingHom ∘ x) := by
    rw [pointMatrix_eq_affineMatrix]
    funext i
    exact e.symm.toRingHom.map_mulVec _ _ i
  rw [hv]
  exact hF _ g _

/-- Testing at the generic vector produces a polynomial identity over an affine algebra. -/
theorem IsInvariantPolynomial.affine_polynomial {ρ : MatrixRepresentation G n}
    {F : MvPolynomial n R} (hF : ρ.IsInvariantPolynomial F)
    (A : CommAlgCat.{u} R) (g : (algSpec R).obj (op A) ⟶ G.X) :
    MatrixRepresentation.linearPullback (ρ.affineMatrix A g : Matrix n n A)
        (MvPolynomial.map (algebraMap R A) F) =
      MvPolynomial.map (algebraMap R A) F := by
  let B := CommAlgCat.of R (MvPolynomial n A)
  let f : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom R A (MvPolynomial n A))
  have h := hF.affine B ((algSpec R).map f.op ≫ g) MvPolynomial.X
  rw [affineMatrix_naturality] at h
  have hs : algebraMap R B = (MvPolynomial.C : A →+* MvPolynomial n A).comp
      (algebraMap R A) := by
    apply RingHom.ext
    intro c
    exact IsScalarTower.algebraMap_apply R A (MvPolynomial n A) c
  rw [hs] at h
  rw [MatrixRepresentation.linearPullback, MvPolynomial.eval₂_map,
    MvPolynomial.map_eq_eval₂Hom_C_comp]
  exact h

/-- On an affine-source point, an invariant polynomial has the coefficient identity. -/
theorem IsInvariantPolynomial.actionPolynomial {ρ : MatrixRepresentation G n}
    {F : MvPolynomial n R} (hF : ρ.IsInvariantPolynomial F)
    {T : Over (Spec R)} [IsAffine T.left] (g : T ⟶ G.X) :
    ρ.actionPolynomial g F = MvPolynomial.map (scalarMap T) F := by
  obtain ⟨⟨A⟩, ⟨j⟩⟩ := (essImage_algSpec (G := T)).mpr inferInstance
  have h := hF.affine_polynomial A (j.hom ≫ g)
  let q : A →+* Γ(((algSpec R).obj (op A)).left, ⊤) :=
    (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have hs : q.comp (algebraMap R A) = scalarMap ((algSpec R).obj (op A)) := by
    ext c
    exact (UnipotentMatrixCriterion.scalarMap_affine A c).symm
  have h₀ := congrArg (MvPolynomial.map q) h
  rw [map_linearPullback, MvPolynomial.map_map, hs] at h₀
  have hm : (ρ.pointMatrix ((algSpec R).obj (op A)) (j.hom ≫ g) :
      Matrix n n Γ(((algSpec R).obj (op A)).left, ⊤)) =
      (ρ.affineMatrix A (j.hom ≫ g) : Matrix n n A).map q := by
    rw [pointMatrix_eq_affineMatrix]
    rfl
  have h₀' : ρ.actionPolynomial (j.hom ≫ g) F =
      MvPolynomial.map (scalarMap ((algSpec R).obj (op A))) F := by
    rw [MatrixRepresentation.actionPolynomial, hm]
    exact h₀
  have h₁ := congrArg (MvPolynomial.map j.inv.left.appTop.hom) h₀'
  rw [actionPolynomial_naturality, ← Category.assoc, j.inv_hom_id, Category.id_comp,
    MvPolynomial.map_map] at h₁
  have hs' : j.inv.left.appTop.hom.comp (scalarMap ((algSpec R).obj (op A))) =
      scalarMap T := by
    ext c
    exact scalarMap_naturality j.inv c
  rwa [hs'] at h₁

/-- An affine group has polynomial invariance exactly when its universal identity holds. -/
theorem isInvariantPolynomial_iff_universal (ρ : MatrixRepresentation G n)
    [IsAffine G.X.left] (F : MvPolynomial n R) :
    ρ.IsInvariantPolynomial F ↔
      ρ.actionPolynomial (𝟙 G.X) F = MvPolynomial.map (scalarMap G.X) F :=
  ⟨fun h => h.actionPolynomial _, ρ.isInvariantPolynomial_of_universal F⟩

/-- An epimorphic point detects the universal coefficient identity. -/
theorem isInvariantPolynomial_of_epi_polynomial (ρ : MatrixRepresentation G n)
    {T : Over (Spec R)} (g : T ⟶ G.X) [Epi g.left] (F : MvPolynomial n R)
    (hF : ρ.actionPolynomial g F = MvPolynomial.map (scalarMap T) F) :
    ρ.IsInvariantPolynomial F := by
  apply ρ.isInvariantPolynomial_of_universal F
  apply MvPolynomial.map_injective g.left.appTop.hom
    (Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi g.left)
  rw [actionPolynomial_naturality, Category.comp_id, MvPolynomial.map_map]
  have hs : g.left.appTop.hom.comp (scalarMap G.X) = scalarMap T := by
    ext c
    exact scalarMap_naturality g c
  rwa [hs]

/-- Restriction of the representation is postcomposition of the tested point. -/
@[simp] theorem actionPolynomial_restrict (ρ : MatrixRepresentation G n)
    (i : H ⟶ G) {T : Over (Spec R)} (g : T ⟶ H.X) (F : MvPolynomial n R) :
    (ρ.restrict i).actionPolynomial g F = ρ.actionPolynomial (g ≫ i.hom.hom) F := by
  rw [actionPolynomial, pointMatrix_restrict, actionPolynomial]

/-- For an affine acting group, the coefficient identity holds on every source scheme. -/
theorem IsInvariantPolynomial.actionPolynomial_of_isAffine
    {ρ : MatrixRepresentation G n} [IsAffine G.X.left]
    {F : MvPolynomial n R} (hF : ρ.IsInvariantPolynomial F)
    {T : Over (Spec R)} (g : T ⟶ G.X) :
    ρ.actionPolynomial g F = MvPolynomial.map (scalarMap T) F := by
  have h := congrArg (MvPolynomial.map g.left.appTop.hom)
    (hF.actionPolynomial (𝟙 G.X))
  rw [actionPolynomial_naturality, Category.comp_id, MvPolynomial.map_map] at h
  have hs : g.left.appTop.hom.comp (scalarMap G.X) = scalarMap T := by
    ext c
    exact scalarMap_naturality g c
  rwa [hs] at h

/-- Multiplying points composes their polynomial substitutions in reverse order. -/
theorem actionPolynomial_mul (ρ : MatrixRepresentation G n) {T : Over (Spec R)}
    (g h : T ⟶ G.X) (F : MvPolynomial n R) :
    ρ.actionPolynomial (g * h) F =
      linearPullback (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤))
        (ρ.actionPolynomial g F) := by
  rw [actionPolynomial, map_mul, Matrix.GeneralLinearGroup.coe_mul,
    linearPullback_mul, actionPolynomial]

/-- Invariance on two affine subgroup factors with epimorphic product detects invariance. -/
theorem isInvariantPolynomial_of_epi_subgroupProductMap
    (ρ : MatrixRepresentation G n) (i : Z ⟶ G) (d : D ⟶ G)
    [IsAffine Z.X.left] [IsAffine D.X.left] [Epi (subgroupProductMap i d)]
    (F : MvPolynomial n R)
    (hi : (ρ.restrict i).IsInvariantPolynomial F)
    (hd : (ρ.restrict d).IsInvariantPolynomial F) : ρ.IsInvariantPolynomial F := by
  have : Epi (subgroupProductMap i d).left :=
    (Over.forget (Spec R)).map_epi (subgroupProductMap i d)
  apply ρ.isInvariantPolynomial_of_epi_polynomial (subgroupProductMap i d) F
  have hi' := hi.actionPolynomial_of_isAffine (fst Z.X D.X)
  have hd' := hd.actionPolynomial_of_isAffine (snd Z.X D.X)
  rw [actionPolynomial_restrict] at hi' hd'
  rw [subgroupProductMap, actionPolynomial_mul, hi']
  exact hd'

/-- The product criterion in both directions. -/
theorem isInvariantPolynomial_iff_epi_subgroupProductMap
    (ρ : MatrixRepresentation G n) (i : Z ⟶ G) (d : D ⟶ G)
    [IsAffine Z.X.left] [IsAffine D.X.left] [Epi (subgroupProductMap i d)]
    (F : MvPolynomial n R) :
    ρ.IsInvariantPolynomial F ↔
      (ρ.restrict i).IsInvariantPolynomial F ∧ (ρ.restrict d).IsInvariantPolynomial F :=
  ⟨fun h => ⟨h.restrict i, h.restrict d⟩,
    fun h => ρ.isInvariantPolynomial_of_epi_subgroupProductMap i d F h.1 h.2⟩

namespace CentralZeroWeight

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (d : D ⟶ G)

/-- The zero-weight pullback is invariant under the full epimorphic central product. -/
theorem linearPullback_invariant_of_epi_product
    (hc : IsCentral j) [IsAffine G.X.left] [IsAffine D.X.left]
    [Epi (subgroupProductMap j d)]
    {F : MvPolynomial (Fin N) k} (hF : (ρ.restrict d).IsInvariantPolynomial F) :
    ρ.IsInvariantPolynomial (linearPullback (projection ρ I j) F) := by
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    isAffineHom_splitTorus _ I
  have : IsAffine (splitTorus (Spec (CommRingCat.of k)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of k)) I).X.hom
  exact ρ.isInvariantPolynomial_of_epi_subgroupProductMap j d _
    (linearPullback_torus_invariant ρ I j F)
    (linearPullback_restrict_invariant ρ I j hc d hF)

/-- The same pullback preserves a supplied homogeneous separator of a torus-fixed vector. -/
theorem linearPullback_separator_of_epi_product
    (hc : IsCentral j) [IsAffine G.X.left] [IsAffine D.X.left]
    [Epi (subgroupProductMap j d)]
    (v : Fin N → k) (hv : (ρ.restrict j).IsFixedVector v)
    {F : MvPolynomial (Fin N) k} {r : ℕ}
    (hhom : F.IsHomogeneous r) (hinv : (ρ.restrict d).IsInvariantPolynomial F)
    (hne : MvPolynomial.eval v F ≠ 0) :
    (linearPullback (projection ρ I j) F).IsHomogeneous r ∧
      ρ.IsInvariantPolynomial (linearPullback (projection ρ I j) F) ∧
      MvPolynomial.eval v (linearPullback (projection ρ I j) F) ≠ 0 := by
  refine ⟨linearPullback_isHomogeneous _ hhom,
    linearPullback_invariant_of_epi_product ρ I j d hc hinv, ?_⟩
  rwa [eval_linearPullback_of_fixed _ _ v (projection_fixed ρ I j v hv)]

end CentralZeroWeight

end Langlands.GroupScheme.MatrixRepresentation
