import Langlands.GroupScheme.OrthogonalMatrix.Roots
import Langlands.GroupScheme.OrthogonalMatrix.Subgroups
import Langlands.GroupScheme.OrthogonalMatrix.SpecialOrthogonalAutomorphismStatement
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.MatrixRepresentationDifferentialConjugation

/-! # Conjugation by similitudes of the split quadratic form

A similitude `g` of the split quadratic form (an invertible matrix with `g Q gᵀ - c Q`
alternating for a unit `c`) normalizes the split orthogonal group `O_{2l}`: conjugation
`x ↦ g x g⁻¹` is an automorphism of the group scheme, and it restricts to an automorphism of
the identity component `SO_{2l}`. We record the predicate `IsSimilitudeConj` saying that an
automorphism of `SO_{2l}` is of this form, which is the body of
`SpecialOrthogonalAutomorphismStatement`, and show that it is stable under composition and
inversion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

section Matrices

variable {A : Type*} [CommRing A]

/-- A matrix `g` is a similitude of the split quadratic form with multiplier `c` when
`g Q gᵀ - c Q` is alternating. -/
def IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) A) (c : A) : Prop :=
  IsAlt (g * formMatrix l A * gᵀ - c • formMatrix l A)

theorem IsSimilitude.map {g : Matrix (l ⊕ l) (l ⊕ l) A} {c : A} (hg : IsSimilitude g c)
    {B : Type*} [CommRing B] (f : A →+* B) : IsSimilitude (g.map f) (f c) := by
  have h := IsAlt.map hg f
  unfold IsSimilitude
  convert h using 1
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    formMatrix_map]
  congr 1
  rw [← formMatrix_map (l := l) f]
  ext i j
  simp

/-- Orthogonal matrices are the similitudes with multiplier one. -/
theorem isSimilitude_one_iff (g : Matrix (l ⊕ l) (l ⊕ l) A) :
    IsSimilitude g 1 ↔ g ∈ orthogonalGroup l A := by
  rw [IsSimilitude, one_smul, mem_orthogonalGroup_iff, defect]

theorem isSimilitude_one : IsSimilitude (1 : Matrix (l ⊕ l) (l ⊕ l) A) 1 :=
  (isSimilitude_one_iff 1).mpr (orthogonalGroup l A).one_mem

/-- The product of similitudes is a similitude, with the product multiplier. -/
theorem IsSimilitude.mul {g h : Matrix (l ⊕ l) (l ⊕ l) A} {c d : A} (hg : IsSimilitude g c)
    (hh : IsSimilitude h d) : IsSimilitude (g * h) (c * d) := by
  unfold IsSimilitude at *
  have key : g * h * formMatrix l A * (g * h)ᵀ - (c * d) • formMatrix l A =
      g * (h * formMatrix l A * hᵀ - d • formMatrix l A) * gᵀ +
        d • (g * formMatrix l A * gᵀ - c • formMatrix l A) := by
    simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, smul_sub, smul_smul, mul_comm d c]
    abel
  rw [key]
  exact (hh.conj g).add (hg.smul d)

/-- The inverse of a similitude is a similitude, with the inverse multiplier. -/
theorem IsSimilitude.inv {g g' : Matrix (l ⊕ l) (l ⊕ l) A} {c c' : A} (hg : IsSimilitude g c)
    (hg'g : g' * g = 1) (hc : c' * c = 1) : IsSimilitude g' c' := by
  unfold IsSimilitude at *
  have hT : gᵀ * g'ᵀ = 1 := by rw [← Matrix.transpose_mul, hg'g, Matrix.transpose_one]
  have key : g' * formMatrix l A * g'ᵀ - c' • formMatrix l A =
      -(c' • (g' * (g * formMatrix l A * gᵀ - c • formMatrix l A) * g'ᵀ)) := by
    have e1 : g' * (g * formMatrix l A * gᵀ) * g'ᵀ = formMatrix l A := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg'g, Matrix.one_mul, Matrix.mul_assoc,
        hT, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, Matrix.mul_smul, Matrix.smul_mul, smul_sub,
      smul_smul, hc, one_smul]
    abel
  rw [key]
  exact ((hg.conj g').smul c').neg

/-- Conjugation by a similitude preserves orthogonal matrices. -/
theorem IsSimilitude.conj_mem {g g' : Matrix (l ⊕ l) (l ⊕ l) A} {c c' : A}
    (hg : IsSimilitude g c) (hg'g : g' * g = 1) (hc : c' * c = 1)
    {x : Matrix (l ⊕ l) (l ⊕ l) A} (hx : x ∈ orthogonalGroup l A) :
    g * x * g' ∈ orthogonalGroup l A := by
  rw [← isSimilitude_one_iff] at hx ⊢
  have h := (hg.mul hx).mul (hg.inv hg'g hc)
  rwa [mul_one, mul_comm, hc] at h

/-- The inverse of an invertible similitude is a similitude, with the inverse multiplier. -/
theorem IsSimilitude.units_inv {g : GL (l ⊕ l) A} {c : Aˣ}
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) A) (c : A)) :
    IsSimilitude (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) (↑c⁻¹ : A) :=
  hg.inv (Units.inv_mul g) (Units.inv_mul c)

end Matrices

section Scheme

variable (R : CommRingCat.{u})

/-- Conjugation `x ↦ g x g⁻¹` by an invertible similitude, on orthogonal matrices. -/
def conjHom {A : Type*} [CommRing A] (g : GL (l ⊕ l) A) (c : Aˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) A) (c : A)) :
    orthogonalGroup l A →* orthogonalGroup l A where
  toFun x := ⟨g * x * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A),
    hg.conj_mem (Units.inv_mul g) (Units.inv_mul c) x.2⟩
  map_one' := Subtype.ext (by
    change (g : Matrix (l ⊕ l) (l ⊕ l) A) * 1 * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) = 1
    rw [Matrix.mul_one, Units.mul_inv])
  map_mul' x y := Subtype.ext (by
    change (g : Matrix (l ⊕ l) (l ⊕ l) A) * ((x : Matrix (l ⊕ l) (l ⊕ l) A) * y) *
        (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) =
      ((g : Matrix (l ⊕ l) (l ⊕ l) A) * x * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A)) *
        ((g : Matrix (l ⊕ l) (l ⊕ l) A) * y * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A))
    have h : (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) * (g : Matrix (l ⊕ l) (l ⊕ l) A) = 1 :=
      Units.inv_mul g
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A), h, Matrix.one_mul])

@[simp] theorem coe_conjHom {A : Type*} [CommRing A] (g : GL (l ⊕ l) A) (c : Aˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) A) (c : A)) (x : orthogonalGroup l A) :
    ((conjHom g c hg x : orthogonalGroup l A) : Matrix (l ⊕ l) (l ⊕ l) A) =
      g * x * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A) :=
  rfl

theorem IsSimilitude.mapGL {g : GL (l ⊕ l) R} {c : Rˣ}
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) {A : Type*} [CommRing A]
    (f : R →+* A) :
    IsSimilitude ((Matrix.GeneralLinearGroup.map f g : GL (l ⊕ l) A) :
      Matrix (l ⊕ l) (l ⊕ l) A) ((Units.map (f : R →* A) c : Aˣ) : A) :=
  hg.map f

/-- Conjugation by a similitude over the base, as a natural transformation of the functor of
orthogonal matrices. -/
def conjTrans (g : GL (l ⊕ l) R) (c : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) : functor l R ⟶ functor l R where
  app A := GrpCat.ofHom (conjHom (Matrix.GeneralLinearGroup.map (algebraMap R A) g)
    (Units.map (algebraMap R A : R →* A) c) (hg.mapGL R (algebraMap R A)))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change ((g : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R B) *
        (show orthogonalGroup l A from x).val.map f.hom.toRingHom *
        (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R B)) =
      ((g : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R A) *
        (show orthogonalGroup l A from x).val *
        (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R A)).map f.hom.toRingHom
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 3 <;> ext r <;> simp

/-- Conjugation by a similitude, as an endomorphism of the split orthogonal group scheme. -/
def conjMap (g : GL (l ⊕ l) R) (c : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) :
    groupScheme l R ⟶ groupScheme l R :=
  Corepresented.groupSchemeMap (corepresentableBy l R) (corepresentableBy l R)
    (conjTrans R g c hg)

variable {R}

theorem pointsEquiv_conjMap (g : GL (l ⊕ l) R) (c : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) (T : Over (Spec R))
    (x : T ⟶ (groupScheme l R).X) :
    (pointsEquiv l R T (x ≫ (conjMap R g c hg).hom.hom) :
        Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) =
      (g : Matrix (l ⊕ l) (l ⊕ l) R).map (scalarMap T) *
        (pointsEquiv l R T x : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *
        (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R).map (scalarMap T) :=
  congrArg (fun y : orthogonalGroup l Γ(T.left, ⊤) => (y : Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)))
    (Corepresented.groupSchemeMap_points (corepresentableBy l R) (corepresentableBy l R)
      (conjTrans R g c hg) x)

theorem affinePointsEquiv_conjMap (g : GL (l ⊕ l) R) (c : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (Opposite.op S) ⟶ (groupScheme l R).X) :
    (affinePointsEquiv l R S (x ≫ (conjMap R g c hg).hom.hom) :
        Matrix (l ⊕ l) (l ⊕ l) S) =
      (g : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R S) *
        (affinePointsEquiv l R S x : Matrix (l ⊕ l) (l ⊕ l) S) *
        (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R S) :=
  congrArg (fun y : orthogonalGroup l S => (y : Matrix (l ⊕ l) (l ⊕ l) S))
    (Corepresented.groupSchemeMap_affinePoints (corepresentableBy l R) (corepresentableBy l R)
      (conjTrans R g c hg) x)

theorem map_units_inv_mul {A B : Type*} [CommRing A] [CommRing B] (g : GL (l ⊕ l) A)
    (f : A →+* B) :
    (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A).map f * (g : Matrix (l ⊕ l) (l ⊕ l) A).map f = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]

theorem map_mul_units_inv {A B : Type*} [CommRing A] [CommRing B] (g : GL (l ⊕ l) A)
    (f : A →+* B) :
    (g : Matrix (l ⊕ l) (l ⊕ l) A).map f * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) A).map f = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]

theorem conjMap_comp_conjMap (g h : GL (l ⊕ l) R) (c d : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R))
    (hh : IsSimilitude (h : Matrix (l ⊕ l) (l ⊕ l) R) (d : R)) :
    conjMap R g c hg ≫ conjMap R h d hh =
      conjMap R (h * g) (d * c) (by simpa using hh.mul hg) := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv l R T).injective
  apply Subtype.ext
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_conjMap, pointsEquiv_conjMap,
    pointsEquiv_conjMap]
  simp only [Units.val_mul, mul_inv_rev, Matrix.map_mul, Matrix.mul_assoc]

theorem conjMap_one :
    conjMap R (1 : GL (l ⊕ l) R) 1 (by simpa using isSimilitude_one) = 𝟙 _ := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv l R T).injective
  apply Subtype.ext
  rw [pointsEquiv_conjMap]
  simp

/-- Conjugation by a similitude, as an automorphism of the split orthogonal group scheme. -/
def conjIso (g : GL (l ⊕ l) R) (c : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) :
    groupScheme l R ≅ groupScheme l R where
  hom := conjMap R g c hg
  inv := conjMap R g⁻¹ c⁻¹ hg.units_inv
  hom_inv_id := by
    rw [conjMap_comp_conjMap]
    convert conjMap_one (l := l) (R := R) <;> simp
  inv_hom_id := by
    rw [conjMap_comp_conjMap]
    convert conjMap_one (l := l) (R := R) <;> simp

open GeneralLinear.DualNumber in
/-- The differential of conjugation by a similitude is conjugation of Lie matrices. -/
theorem lieMatrix_targetMapLinear_conjMap (g : GL (l ⊕ l) R) (c : Rˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) R) (c : R)) {A : Type u} [CommRing A]
    [Algebra R A] (X : Additive (lieKernel (groupScheme l R) A)) :
    lieMatrix (Lie.targetMapLinear (conjMap R g c hg) A X) =
      (g : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R A) * lieMatrix X *
        (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R A) := by
  have h1 := affinePointsEquiv_lieKernel (Lie.targetMapLinear (conjMap R g c hg) A X)
  have h2 : (Lie.targetMapLinear (conjMap R g c hg) A X).toMul.val =
      X.toMul.val ≫ (conjMap R g c hg).hom.hom := rfl
  rw [h2, affinePointsEquiv_conjMap, affinePointsEquiv_lieKernel] at h1
  have e : ∀ M : Matrix (l ⊕ l) (l ⊕ l) R, M.map (algebraMap R (DualNumber A)) =
      (M.map (algebraMap R A)).map (TrivSqZeroExt.inlHom A A) := fun M =>
    Matrix.ext fun i j => by simp [TrivSqZeroExt.algebraMap_eq_inl']
  have hu : (g : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R A) *
      (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) R).map (algebraMap R A) = 1 :=
    map_mul_units_inv g (algebraMap R A)
  rw [e, e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, constantMatrix_mul_epsilonMatrix,
    epsilonMatrix_mul_constantMatrix, ← Matrix.map_mul, hu,
    Matrix.map_one _ (map_zero _) (map_one _)] at h1
  have h3 := add_left_cancel h1
  ext i j
  have h4 := congrArg (fun M : Matrix (l ⊕ l) (l ⊕ l) (DualNumber A) => (M i j).snd) h3
  simpa using h4.symm

end Scheme

section Field

variable {k : Type u} [Field k]

/-- Conjugation by a similitude, restricted to the identity component `SO_{2l}`. -/
def specialConjIso (g : GL (l ⊕ l) k) (c : kˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) k) (c : k)) :
    identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k)) :=
  IdentityComponent.mapIso (conjIso (R := CommRingCat.of k) g c hg)

@[reassoc]
theorem specialConjIso_hom_identityComponentι (g : GL (l ⊕ l) k) (c : kˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) k) (c : k)) :
    (specialConjIso g c hg).hom ≫ identityComponentι (groupScheme l (CommRingCat.of k)) =
      identityComponentι (groupScheme l (CommRingCat.of k)) ≫
        conjMap (CommRingCat.of k) g c hg :=
  IdentityComponent.mapIso_hom_identityComponentι _

/-- An automorphism of `SO_{2l}` is *conjugation by a similitude* when there are an invertible
matrix `g` and a unit `c` with `g Q gᵀ - c Q` alternating such that the automorphism sends the
point with matrix `x` to the point with matrix `g x g⁻¹`, on every test scheme. -/
def IsSimilitudeConj
    (α : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k))) : Prop :=
  ∃ (g : GL (l ⊕ l) k) (c : kˣ), IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) k) (c : k) ∧
    ∀ (T : Over (Spec (CommRingCat.of k)))
      (x : T ⟶ (identityComponent (groupScheme l (CommRingCat.of k))).X),
      (pointsEquiv l (CommRingCat.of k) T
          (x ≫ α.hom.hom.hom ≫
            (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom) :
          Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) =
        (g : Matrix (l ⊕ l) (l ⊕ l) k).map (scalarMap T) *
          (pointsEquiv l (CommRingCat.of k) T
            (x ≫ (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom) :
            Matrix (l ⊕ l) (l ⊕ l) Γ(T.left, ⊤)) *
          (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) k).map (scalarMap T)

theorem isSimilitudeConj_specialConjIso (g : GL (l ⊕ l) k) (c : kˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) k) (c : k)) :
    IsSimilitudeConj (specialConjIso g c hg) := by
  refine ⟨g, c, hg, fun T x => ?_⟩
  have h : (specialConjIso g c hg).hom.hom.hom ≫
      (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom =
      (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom ≫
        (conjMap (CommRingCat.of k) g c hg).hom.hom :=
    congrArg (fun f => f.hom.hom) (specialConjIso_hom_identityComponentι g c hg)
  rw [h, ← Category.assoc, pointsEquiv_conjMap]

theorem isSimilitudeConj_refl :
    IsSimilitudeConj (Iso.refl (identityComponent (groupScheme l (CommRingCat.of k)))) := by
  refine ⟨1, 1, by simpa using (isSimilitude_one (l := l) (A := k)), fun T x => ?_⟩
  simp

theorem IsSimilitudeConj.trans
    {α β : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k))}
    (hα : IsSimilitudeConj α) (hβ : IsSimilitudeConj β) : IsSimilitudeConj (α ≪≫ β) := by
  obtain ⟨g, c, hg, h1⟩ := hα
  obtain ⟨g', c', hg', h2⟩ := hβ
  refine ⟨g' * g, c' * c, by simpa using hg'.mul hg, fun T x => ?_⟩
  have e : (α ≪≫ β).hom.hom.hom = α.hom.hom.hom ≫ β.hom.hom.hom := rfl
  rw [e, Category.assoc, ← Category.assoc x, h2 T (x ≫ α.hom.hom.hom), Category.assoc, h1 T x]
  simp only [Units.val_mul, mul_inv_rev, Matrix.map_mul, Matrix.mul_assoc]

theorem IsSimilitudeConj.symm
    {α : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k))}
    (hα : IsSimilitudeConj α) : IsSimilitudeConj α.symm := by
  obtain ⟨g, c, hg, h⟩ := hα
  refine ⟨g⁻¹, c⁻¹, hg.units_inv, fun T x => ?_⟩
  have e : α.inv.hom.hom ≫ α.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, α.inv_hom_id, Grp.id_hom_hom]
  have hx : (x ≫ α.inv.hom.hom) ≫ α.hom.hom.hom ≫
      (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom =
      x ≫ (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom := by
    rw [← Category.assoc (x ≫ α.inv.hom.hom), Category.assoc x, e, Category.comp_id]
  have h1 := h T (x ≫ α.inv.hom.hom)
  rw [hx] at h1
  have e2 : x ≫ α.symm.hom.hom.hom ≫
      (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom =
      (x ≫ α.inv.hom.hom) ≫ (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom :=
    (Category.assoc _ _ _).symm
  rw [e2, h1, inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [map_units_inv_mul, Matrix.one_mul, Matrix.mul_assoc, map_units_inv_mul, Matrix.mul_one]

theorem IsSimilitudeConj.of_trans
    {α β : identityComponent (groupScheme l (CommRingCat.of k)) ≅
      identityComponent (groupScheme l (CommRingCat.of k))}
    (h : IsSimilitudeConj (α ≪≫ β)) (hβ : IsSimilitudeConj β) : IsSimilitudeConj α := by
  have e : α = (α ≪≫ β) ≪≫ β.symm := by simp
  rw [e]
  exact h.trans hβ.symm

/-- The differential of conjugation by a similitude on `SO_{2l}` is conjugation of Lie
matrices. -/
theorem lieMatrix_targetMapLinear_specialConjIso (g : GL (l ⊕ l) k) (c : kˣ)
    (hg : IsSimilitude (g : Matrix (l ⊕ l) (l ⊕ l) k) (c : k))
    (X : Additive (lieKernel (identityComponent (groupScheme l (CommRingCat.of k))) k)) :
    lieMatrix (Lie.targetMapLinear (identityComponentι (groupScheme l (CommRingCat.of k))) k
        (Lie.targetMapLinear (specialConjIso g c hg).hom k X)) =
      (g : Matrix (l ⊕ l) (l ⊕ l) k) *
        lieMatrix (Lie.targetMapLinear (identityComponentι (groupScheme l (CommRingCat.of k))) k
          X) * (↑g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) k) := by
  have e : Lie.targetMapLinear (identityComponentι (groupScheme l (CommRingCat.of k))) k
      (Lie.targetMapLinear (specialConjIso g c hg).hom k X) =
      Lie.targetMapLinear (conjMap (CommRingCat.of k) g c hg) k
        (Lie.targetMapLinear (identityComponentι (groupScheme l (CommRingCat.of k))) k X) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (X.toMul.val ≫ (specialConjIso g c hg).hom.hom.hom) ≫
        (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom =
      (X.toMul.val ≫ (identityComponentι (groupScheme l (CommRingCat.of k))).hom.hom) ≫
        (conjMap (CommRingCat.of k) g c hg).hom.hom
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun f => X.toMul.val ≫ f.hom.hom)
      (specialConjIso_hom_identityComponentι g c hg)
  rw [e, lieMatrix_targetMapLinear_conjMap]
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]

end Field

end Langlands.GroupScheme.OrthogonalMatrix
