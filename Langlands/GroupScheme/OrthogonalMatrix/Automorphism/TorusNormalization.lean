import Langlands.GroupScheme.OrthogonalMatrix.Automorphism.Conjugation
import Langlands.GroupScheme.OrthogonalMatrix.Automorphism.SignedPermutation
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitMono

/-! # Normalizing an automorphism of `SO_{2l}` on the diagonal torus

Let `α` be an automorphism of the identity component `SO_{2l}` of the split orthogonal group
over a field `k`, with `l` having at least two elements. We find a conjugation `γ` by an
orthogonal matrix such that `α` followed by `γ` restricts to the identity on the diagonal torus.

1. **Torus conjugacy.** The diagonal torus and its image under `α` are maximal split tori, so they
   are conjugate under an inner automorphism by a rational point `p`
   (`smoothMaximalSplitTorusConjugacy`). An inner automorphism by a rational point is conjugation
   by its orthogonal matrix (`isSimilitudeConj_innerIso`).
2. **Weyl step.** The composite then maps the diagonal torus onto itself through an automorphism
   `e` of the torus, and `e` preserves the roots (`roots_image_of_transport`). In coordinates,
   `e` permutes the weights `±e_a` by a permutation `σ` of `l ⊕ l` commuting with `swap`
   (`exists_perm_map_weightCoord`).
3. **Permutation matrix.** The permutation matrix of `σ` is orthogonal, and conjugation by it
   acts on the diagonal torus as `e⁻¹`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (torusWeights torusWeights_eq_prod weightCoord weightCoord_inl)

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### Inner automorphisms by rational points -/

section Inner

variable {R : CommRingCat.{u}}

/-- The orthogonal matrix over `R` of a point over the base `Spec R`. -/
def rationalPoint (p : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme l R).X) : orthogonalGroup l R :=
  map l (Scheme.ΓSpecIso R).hom.hom (pointsEquiv l R (Over.mk (𝟙 (Spec R))) p)

/-- The constant family of a base point has the scalar extension of its matrix. -/
theorem pointsEquiv_constantPoint_rational (p : Over.mk (𝟙 (Spec R)) ⟶ (groupScheme l R).X)
    (T : Over (Spec R)) :
    pointsEquiv l R T ((groupScheme l R).constantPoint p T) =
      map l (scalarMap T) (rationalPoint p) := by
  rw [GroupScheme.constantPoint, pointsEquiv_naturality]
  refine OrthogonalMatrix.ext fun r s => ?_
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  change T.hom.appTop.hom
      ((pointsEquiv l R (Over.mk (𝟙 (Spec R))) p).1 r s) =
    T.hom.appTop.hom (e.symm (e ((pointsEquiv l R (Over.mk (𝟙 (Spec R))) p).1 r s)))
  rw [e.symm_apply_apply]

end Inner

section InnerField

variable {k : Type u} [Field k]

/-- **Inner automorphisms are conjugations.** The inner automorphism of `SO_{2l}` by a rational
point is conjugation by the orthogonal matrix of that point. -/
theorem isSimilitudeConj_innerIso
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (identityComponent (groupScheme l (CommRingCat.of k))).X) :
    IsSimilitudeConj ((identityComponent (groupScheme l (CommRingCat.of k))).innerIso p) := by
  set j := identityComponentι (groupScheme l (CommRingCat.of k)) with hj
  set g := rationalPoint (p ≫ j.hom.hom) with hg
  refine ⟨toGL g, 1, ?_, fun T x => ?_⟩
  · rw [Units.val_one, isSimilitude_one_iff, coe_toGL]
    exact g.2
  · have h1 : ((identityComponent (groupScheme l (CommRingCat.of k))).innerIso p).hom.hom.hom ≫
        j.hom.hom =
        j.hom.hom ≫ ((groupScheme l (CommRingCat.of k)).innerIso (p ≫ j.hom.hom)).hom.hom.hom :=
      congrArg (fun f => f.hom.hom) (innerIso_hom_comp j p)
    have key : pointsEquiv l _ T (x ≫
        ((identityComponent (groupScheme l (CommRingCat.of k))).innerIso p).hom.hom.hom ≫
          j.hom.hom) =
        map l (scalarMap T) g * pointsEquiv l _ T (x ≫ j.hom.hom) *
          map l (scalarMap T) g⁻¹ := by
      rw [h1, ← Category.assoc, comp_innerIso_hom, map_mul, map_mul, map_inv,
        pointsEquiv_constantPoint_rational, map_inv]
    rw [key]
    rfl

end InnerField

/-! ### Permutation matrices -/

section Permutation

variable {A : Type*} [CommRing A]

variable (A) in
/-- The permutation matrix of `σ`, with entry `1` at `(y, σ y)`, as an invertible matrix. -/
def permGL (σ : Equiv.Perm (l ⊕ l)) : GL (l ⊕ l) A where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem coe_permGL (σ : Equiv.Perm (l ⊕ l)) :
    (permGL A σ : Matrix (l ⊕ l) (l ⊕ l) A) = σ.toPEquiv.toMatrix := rfl

theorem coe_permGL_inv (σ : Equiv.Perm (l ⊕ l)) :
    (↑(permGL A σ)⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) = σ.symm.toPEquiv.toMatrix := rfl

omit [Fintype l] in
theorem map_toPEquiv_toMatrix {B : Type*} [CommRing B] (f : A →+* B) (σ : Equiv.Perm (l ⊕ l)) :
    (σ.toPEquiv.toMatrix : Matrix (l ⊕ l) (l ⊕ l) A).map f = σ.toPEquiv.toMatrix := by
  ext y z
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

/-- Conjugating a matrix by a permutation matrix permutes its rows and columns. -/
theorem permMatrix_conj (σ : Equiv.Perm (l ⊕ l)) (D : Matrix (l ⊕ l) (l ⊕ l) A) :
    σ.toPEquiv.toMatrix * D * σ.symm.toPEquiv.toMatrix = D.submatrix σ σ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

omit [Fintype l] in
theorem formMatrix_apply_self (y : l ⊕ l) : formMatrix l A y y = 0 := by
  rcases y with a | a <;> simp [formMatrix_apply]

/-- The permutation matrix of a permutation commuting with `swap` is orthogonal. -/
theorem isSimilitude_permGL (σ : Equiv.Perm (l ⊕ l)) (hσ : ∀ x, σ x.swap = (σ x).swap) :
    IsSimilitude (permGL A σ : Matrix (l ⊕ l) (l ⊕ l) A) ((1 : Aˣ) : A) := by
  rw [Units.val_one, isSimilitude_one_iff, mem_orthogonalGroup_iff, defect, coe_permGL,
    ← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, permMatrix_conj, isAlt_iff]
  have hQ : ∀ a b : l ⊕ l, formMatrix l A a b + formMatrix l A b a = polarMatrix l A a b :=
    fun a b => by rw [← formMatrix_add_transpose]; rfl
  refine ⟨?_, fun y => ?_⟩
  · ext y z
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Matrix.zero_apply]
    have hJ : polarMatrix l A (σ y) (σ z) = polarMatrix l A y z := by
      simp only [polarMatrix_apply, ← hσ, σ.injective.eq_iff]
    linear_combination hQ (σ y) (σ z) - hQ y z + hJ
  · simp only [Matrix.sub_apply, Matrix.submatrix_apply, formMatrix_apply_self, sub_self]

end Permutation

/-! ### The diagonal torus -/

section Torus

variable {k : Type u} [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

variable (l k) in
theorem isMaximalSplitTorus_identityTorus : IsMaximalSplitTorus (identityTorus l k) :=
  (isMaximalTorus_identityTorus l k).isMaximalSplitTorus
    (SymplecticMatrix.isSplitTorus_diagonalTorus l k)

/-- **Torus conjugacy.** After an inner automorphism by a rational point, an automorphism of
`SO_{2l}` maps the diagonal torus onto itself. -/
theorem exists_innerIso_comp_identityTorus
    (α : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k))) :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (identityComponent (groupScheme l (CommRingCat.of k))).X)
      (e : (𝔻).toGrp ≅ (𝔻).toGrp),
      identityTorus l k ≫
          (α ≪≫ (identityComponent (groupScheme l (CommRingCat.of k))).innerIso p).hom =
        e.hom ≫ identityTorus l k := by
  obtain ⟨p, e, h⟩ := smoothMaximalSplitTorusConjugacy k
    (identityComponent (groupScheme l (CommRingCat.of k))) 𝔻 𝔻
    (identityTorus l k ≫ α.hom) (identityTorus l k)
    ((isMaximalSplitTorus_identityTorus l k).comp_iso α) (isMaximalSplitTorus_identityTorus l k)
  exact ⟨p, e, by rw [Iso.trans_hom, ← Category.assoc, h]⟩

/-- **Weyl step.** If an automorphism `β` of `SO_{2l}` maps the diagonal torus onto itself
through an automorphism `e` of the torus, then the transport of characters along `e` permutes
the weights `w(x)` by a permutation of `l ⊕ l` commuting with `swap`. -/
theorem exists_perm_of_comp_identityTorus [Nontrivial l]
    (β : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k)))
    (e : (𝔻).toGrp ≅ (𝔻).toGrp) (h : identityTorus l k ≫ β.hom = e.hom ≫ identityTorus l k) :
    ∃ σ : Equiv.Perm (l ⊕ l), (∀ x, σ x.swap = (σ x).swap) ∧
      ∀ x, GeneralLinear.characterCoordEquiv l k
          (characterLattice.congr (CommGroupScheme.isoOfGroupIso e)
            ((GeneralLinear.characterCoordEquiv l k).symm (weightCoord l x))) =
        weightCoord l (σ x) := by
  set E := CommGroupScheme.isoOfGroupIso e with hE
  set C := GeneralLinear.characterCoordEquiv l k with hC
  have hroots := roots_image_of_transport E β h
  rw [roots_identityTorus] at hroots
  let M : (l → ℤ) ≃+ (l → ℤ) :=
    (C.symm.toAddEquiv.trans (characterLattice.congr E)).trans C.toAddEquiv
  refine exists_perm_map_weightCoord M.toAddMonoidHom M.injective ?_
  intro x y hxy
  have hχ : C.symm (weightCoord l x - weightCoord l y) ∈
      roots (diagonalTorus l (CommRingCat.of k)) :=
    (mem_roots_iff _).mpr ⟨x, y, hxy, C.apply_symm_apply _⟩
  have hχ' : characterLattice.congr E (C.symm (weightCoord l x - weightCoord l y)) ∈
      roots (diagonalTorus l (CommRingCat.of k)) := by
    rw [← hroots]
    exact Set.mem_image_of_mem _ hχ
  obtain ⟨x', y', hxy', hc⟩ := (mem_roots_iff _).mp hχ'
  exact ⟨x', y', hxy', hc⟩

omit [Fintype l] [DecidableEq l] in
theorem torusWeights_swap {A : Type*} [CommRing A] (τ : ULift.{u} l → Aˣ) (x : l ⊕ l) :
    torusWeights τ x.swap = (torusWeights τ x)⁻¹ := by
  rcases x with a | a
  · rfl
  · exact (inv_inv _).symm

theorem characterCoordEquiv_symm_weightCoord_inl (j : l) :
    (GeneralLinear.characterCoordEquiv l k).symm (weightCoord l (Sum.inl j)) =
      splitTorus.proj (Spec (CommRingCat.of k)) (ULift l) ⟨j⟩ := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  funext i
  rw [GeneralLinear.characterCoordEquiv_apply, splitTorus.characterLatticeEquiv_proj,
    weightCoord_inl]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (fun h => hij (congrArg ULift.down h))]

/-- On points, a torus automorphism whose character transport permutes the weights by `σ` acts
on the weights by `σ`. -/
theorem torusWeights_comp_inv (e : (𝔻).toGrp ≅ (𝔻).toGrp) (σ : Equiv.Perm (l ⊕ l))
    (hσswap : ∀ x, σ x.swap = (σ x).swap)
    (hσ : ∀ x, GeneralLinear.characterCoordEquiv l k
          (characterLattice.congr (CommGroupScheme.isoOfGroupIso e)
            ((GeneralLinear.characterCoordEquiv l k).symm (weightCoord l x))) =
        weightCoord l (σ x))
    {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ (splitTorus (Spec (CommRingCat.of k))
      (ULift.{u} l)).X) (y : l ⊕ l) :
    torusWeights (splitTorus.pointsEquiv (ULift.{u} l) T (t ≫ e.inv.hom.hom)) y =
      torusWeights (splitTorus.pointsEquiv (ULift.{u} l) T t) (σ y) := by
  have hinl : ∀ j : l, splitTorus.pointsEquiv (ULift.{u} l) T (t ≫ e.inv.hom.hom) ⟨j⟩ =
      torusWeights (splitTorus.pointsEquiv (ULift.{u} l) T t) (σ (Sum.inl j)) := by
    intro j
    rw [splitTorus.pointsEquiv_comp, torusWeights_eq_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    rw [← hσ, characterCoordEquiv_symm_weightCoord_inl]
    rfl
  rcases y with j | j
  · exact hinl j
  · change (splitTorus.pointsEquiv (ULift.{u} l) T (t ≫ e.inv.hom.hom) ⟨j⟩)⁻¹ = _
    rw [hinl j, ← torusWeights_swap, ← hσswap]
    rfl

/-- **Permutation step.** Conjugation by the permutation matrix of `σ` acts on the diagonal torus
as `e⁻¹`. -/
theorem identityTorus_comp_specialConjIso_permGL (e : (𝔻).toGrp ≅ (𝔻).toGrp)
    (σ : Equiv.Perm (l ⊕ l)) (hσswap : ∀ x, σ x.swap = (σ x).swap)
    (hσ : ∀ x, GeneralLinear.characterCoordEquiv l k
          (characterLattice.congr (CommGroupScheme.isoOfGroupIso e)
            ((GeneralLinear.characterCoordEquiv l k).symm (weightCoord l x))) =
        weightCoord l (σ x)) :
    identityTorus l k ≫ (specialConjIso (permGL k σ) 1 (isSimilitude_permGL σ hσswap)).hom =
      e.inv ≫ identityTorus l k := by
  apply (cancel_mono (identityComponentι (groupScheme l (CommRingCat.of k)))).mp
  rw [Category.assoc, specialConjIso_hom_identityComponentι, identityTorus_comp_assoc,
    Category.assoc, identityTorus_comp]
  apply hom_ext_points
  intro T x
  apply (pointsEquiv l (CommRingCat.of k) T).injective
  apply Subtype.ext
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    pointsEquiv_conjMap, pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus]
  simp only [coe_leviHom, SymplecticMatrix.levi_diagonalTorusUnits]
  rw [coe_permGL, coe_permGL_inv, map_toPEquiv_toMatrix, map_toPEquiv_toMatrix, permMatrix_conj,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext y
  rw [Function.comp_apply, torusWeights_comp_inv e σ hσswap hσ x y]

/-- **Normalization on the diagonal torus.** For `l` with at least two elements, every
automorphism `α` of `SO_{2l}` followed by a suitable conjugation `γ` by an orthogonal matrix
fixes the diagonal torus pointwise. -/
theorem exists_isSimilitudeConj_comp_fix_of_nontrivial [Nontrivial l]
    (α : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k))) :
    ∃ ρ : identityComponent (groupScheme l (CommRingCat.of k)) ≅
        identityComponent (groupScheme l (CommRingCat.of k)),
      IsSimilitudeConj ρ ∧ identityTorus l k ≫ (α ≪≫ ρ).hom = identityTorus l k := by
  obtain ⟨p, e, h⟩ := exists_innerIso_comp_identityTorus α
  obtain ⟨σ, hσswap, hσ⟩ := exists_perm_of_comp_identityTorus _ e h
  have h2 := identityTorus_comp_specialConjIso_permGL e σ hσswap hσ
  refine ⟨(identityComponent (groupScheme l (CommRingCat.of k))).innerIso p ≪≫
      specialConjIso (permGL k σ) 1 (isSimilitude_permGL σ hσswap),
    (isSimilitudeConj_innerIso p).trans (isSimilitudeConj_specialConjIso _ _ _), ?_⟩
  calc identityTorus l k ≫ (α ≪≫ ((identityComponent (groupScheme l (CommRingCat.of k))).innerIso p ≪≫
        specialConjIso (permGL k σ) 1 (isSimilitude_permGL σ hσswap))).hom
      = (identityTorus l k ≫
          (α ≪≫ (identityComponent (groupScheme l (CommRingCat.of k))).innerIso p).hom) ≫
          (specialConjIso (permGL k σ) 1 (isSimilitude_permGL σ hσswap)).hom := by
        simp only [Iso.trans_hom, Category.assoc]
    _ = e.hom ≫ e.inv ≫ identityTorus l k := by rw [h, Category.assoc, h2]
    _ = identityTorus l k := e.hom_inv_id_assoc _

end Torus

/-- **Normalization on the diagonal torus, numbered form.** For `n ≥ 2`, every automorphism `α`
of `SO_{2n}` followed by a suitable conjugation `γ` by an orthogonal matrix fixes the diagonal
torus pointwise. -/
theorem exists_isSimilitudeConj_comp_fix {k : Type u} [Field k] {n : ℕ} (hn : 2 ≤ n)
    (α : identityComponent (groupScheme (Fin n) (CommRingCat.of k)) ≅
      identityComponent (groupScheme (Fin n) (CommRingCat.of k))) :
    ∃ ρ : identityComponent (groupScheme (Fin n) (CommRingCat.of k)) ≅
        identityComponent (groupScheme (Fin n) (CommRingCat.of k)),
      IsSimilitudeConj ρ ∧ identityTorus (Fin n) k ≫ (α ≪≫ ρ).hom = identityTorus (Fin n) k := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact exists_isSimilitudeConj_comp_fix_of_nontrivial α

end Langlands.GroupScheme.OrthogonalMatrix
