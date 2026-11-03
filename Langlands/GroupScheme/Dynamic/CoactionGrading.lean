import Langlands.GroupScheme.Dynamic.Representability

/-! # The conjugation coaction of a cocharacter is a grading

For a cocharacter `χ` of an affine group scheme `Spec B` given by a corepresented functor, the
coaction `c : B ⟶ B[T, T⁻¹]` of `𝔾_m` by conjugation through `χ` is a `ℤ`-grading of `B`:
it is compatible with the base ring, the sum of the coefficients of `c(b)` is `b`, and
`c(c(b)ₙ) = c(b)ₙ Tⁿ`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- The orbit map of an orbit map is the orbit map precomposed with multiplication in `𝔾_m`. -/
theorem orbit_orbit {T : Over S} (g : T ⟶ G.X) :
    orbit χ (orbit χ g) =
      lift (fst (T ⊗ (Gm S).X) (Gm S).X ≫ fst T (Gm S).X)
        (snd (T ⊗ (Gm S).X) (Gm S).X * (fst (T ⊗ (Gm S).X) (Gm S).X ≫ snd T (Gm S).X)) ≫
        orbit χ g := by
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc,
    MonObj.mul_comp, Category.assoc]
  group

/-- The orbit map at the unit point of `𝔾_m` is the point itself. -/
theorem lift_one_comp_orbit {T : Over S} (g : T ⟶ G.X) :
    lift (𝟙 T) (1 : T ⟶ (Gm S).X) ≫ orbit χ g = g := by
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc,
    MonObj.one_comp, Category.id_comp]
  group

end Dynamic

namespace AffineLine

section Laurent

variable (A : CommRingCat.{u})

/-- Evaluation at `1`, `A[X, X⁻¹] ⟶ A`. -/
abbrev laurentEvalOne : CommRingCat.of (LaurentPolynomial A) ⟶ A :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id A) 1)

theorem polynomialC_comp_polynomialToLaurent_comp_laurentEvalOne :
    (polynomialC A ≫ polynomialToLaurent A) ≫ laurentEvalOne A = 𝟙 A := by
  ext a
  simp [Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C]

/-- The monoid map `m ↦ Tᵐ · Sᵐ` from `Multiplicative ℤ` to `A[S, S⁻¹][T, T⁻¹]`. -/
def laurentMulPow :
    Multiplicative ℤ →* LaurentPolynomial (CommRingCat.of (LaurentPolynomial A)) where
  toFun m := LaurentPolynomial.T m.toAdd * LaurentPolynomial.C (LaurentPolynomial.T m.toAdd)
  map_one' := by simp [LaurentPolynomial.T_zero]
  map_mul' m m' := by
    simp only [toAdd_mul, LaurentPolynomial.T_add, map_mul]
    ring

/-- The ring map `A[U, U⁻¹] →+* A[S, S⁻¹][T, T⁻¹]` sending `a ∈ A` to itself and `U` to `S T`. -/
def laurentMulRingHom :
    LaurentPolynomial A →+* LaurentPolynomial (CommRingCat.of (LaurentPolynomial A)) :=
  AddMonoidAlgebra.liftNCRingHom (LaurentPolynomial.C.comp LaurentPolynomial.C) (laurentMulPow A)
    (fun _ _ => Commute.all _ _)

/-- The ring map `A[U, U⁻¹] ⟶ A[S, S⁻¹][T, T⁻¹]` sending `a ∈ A` to itself and `U` to `S T`. -/
abbrev laurentMul :
    CommRingCat.of (LaurentPolynomial A) ⟶
      CommRingCat.of (LaurentPolynomial (CommRingCat.of (LaurentPolynomial A))) :=
  CommRingCat.ofHom (laurentMulRingHom A)

theorem laurentMulRingHom_single (m : ℤ) (a : A) :
    laurentMulRingHom A (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single m (AddMonoidAlgebra.single m a) := by
  rw [laurentMulRingHom, AddMonoidAlgebra.liftNCRingHom_single]
  change LaurentPolynomial.C (LaurentPolynomial.C a) *
      (LaurentPolynomial.T m * LaurentPolynomial.C (LaurentPolynomial.T m)) = _
  rw [LaurentPolynomial.single_eq_C_mul_T a m,
    LaurentPolynomial.single_eq_C_mul_T (LaurentPolynomial.C a * LaurentPolynomial.T m) m,
    map_mul]
  ring

theorem laurentMulRingHom_C (a : A) :
    laurentMulRingHom A (LaurentPolynomial.C a) =
      LaurentPolynomial.C (LaurentPolynomial.C a) := by
  rw [← LaurentPolynomial.single_eq_C, laurentMulRingHom_single, LaurentPolynomial.single_eq_C,
    LaurentPolynomial.single_eq_C]

theorem laurentMulRingHom_T_one :
    laurentMulRingHom A (LaurentPolynomial.T 1) =
      LaurentPolynomial.T 1 * LaurentPolynomial.C (LaurentPolynomial.T 1) := by
  rw [show (LaurentPolynomial.T 1 : LaurentPolynomial A) = AddMonoidAlgebra.single 1 1 from rfl,
    laurentMulRingHom_single, LaurentPolynomial.single_eq_C_mul_T, mul_comm]

theorem coeff_laurentMulRingHom (q : LaurentPolynomial A) (n : ℤ) :
    (laurentMulRingHom A q).coeff n = AddMonoidAlgebra.single n (q.coeff n) := by
  classical
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.single_add]
  | single m a =>
    rw [laurentMulRingHom_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · simp

theorem eval₂_id_one (q : LaurentPolynomial A) :
    LaurentPolynomial.eval₂ (RingHom.id A) 1 q = q.coeff.sum fun _ a => a := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  | single m a =>
    rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index rfl,
      LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
    simp

end Laurent

section Points

variable {A : CommRingCat.{u}} (f : Spec A ⟶ S)

theorem specMap_laurentEvalOne_comp :
    Spec.map (laurentEvalOne A) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_comp, polynomialC_comp_polynomialToLaurent_comp_laurentEvalOne,
    Spec.map_id]

/-- The point `X = 1` of `Spec A[X, X⁻¹]` over `S`. -/
def laurentOne : Over.mk f ⟶ laurentScheme f :=
  Over.homMk (Spec.map (laurentEvalOne A)) (by
    change Spec.map (laurentEvalOne A) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) ≫ f = f
    rw [reassoc_of% (specMap_laurentEvalOne_comp (A := A))])

/-- The Laurent point at `X = 1` is the unit point of `𝔾_m`. -/
theorem laurentOne_comp_laurentPoint :
    laurentOne f ≫ laurentPoint f = lift (𝟙 _) (1 : Over.mk f ⟶ (Gm S).X) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, laurentPoint, lift_fst, lift_fst]
    apply Over.OverMorphism.ext
    exact specMap_laurentEvalOne_comp
  · rw [Category.assoc, laurentPoint, lift_snd, lift_snd]
    apply (Gm.pointsEquiv S _).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, map_one]
    apply Units.ext
    change (Spec.map (laurentEvalOne A)).appTop
      ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) = 1
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp [LaurentPolynomial.eval₂_T]

theorem polynomialC_comp_polynomialToLaurent_comp_laurentMul :
    polynomialC A ≫ polynomialToLaurent A ≫ laurentMul A =
      polynomialC A ≫ polynomialToLaurent A ≫ polynomialC (CommRingCat.of (LaurentPolynomial A)) ≫
        polynomialToLaurent (CommRingCat.of (LaurentPolynomial A)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change laurentMulRingHom A (Polynomial.toLaurent (Polynomial.C a)) =
    Polynomial.toLaurent (Polynomial.C (Polynomial.toLaurent (Polynomial.C a)))
  rw [Polynomial.toLaurent_C, Polynomial.toLaurent_C, laurentMulRingHom_C]

theorem specMap_laurentMul_comp :
    Spec.map (laurentMul A) ≫ Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) =
      Spec.map (polynomialToLaurent (CommRingCat.of (LaurentPolynomial A))) ≫
        Spec.map (polynomialC (CommRingCat.of (LaurentPolynomial A))) ≫
          Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) := by
  simp only [← Spec.map_comp]
  congr 1
  simp only [Category.assoc]
  exact polynomialC_comp_polynomialToLaurent_comp_laurentMul

/-- Multiplication `(s, t) ↦ s t` of the two Laurent coordinates, as a morphism
`Spec A[S, S⁻¹][T, T⁻¹] ⟶ Spec A[U, U⁻¹]` over `S`. -/
def laurentMulHom : laurentScheme (laurentScheme f).hom ⟶ laurentScheme f :=
  Over.homMk (Spec.map (laurentMul A)) (by
    change Spec.map (laurentMul A) ≫ Spec.map (polynomialToLaurent A) ≫
      Spec.map (polynomialC A) ≫ f = Spec.map (polynomialToLaurent _) ≫
        Spec.map (polynomialC _) ≫ Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫ f
    rw [reassoc_of% (specMap_laurentMul_comp (A := A))])

@[reassoc]
theorem laurentPoint_fst :
    laurentPoint f ≫ fst (Over.mk f) (Gm S).X = laurentInclusion f ≫ polynomialProj f :=
  lift_fst _ _

@[reassoc]
theorem laurentPoint_snd :
    laurentPoint f ≫ snd (Over.mk f) (Gm S).X = (Gm.pointsEquiv _ _).symm (laurentUnit f) :=
  lift_snd _ _

/-- On `Spec A[S, S⁻¹][T, T⁻¹]`, the iterated Laurent point followed by multiplication in `𝔾_m`
is the Laurent point at `S T`. -/
theorem laurentMulHom_comp_laurentPoint :
    laurentMulHom f ≫ laurentPoint f =
      laurentPoint (laurentScheme f).hom ≫ laurentPoint f ▷ (Gm S).X ≫
        lift (fst (Over.mk f ⊗ (Gm S).X) (Gm S).X ≫ fst (Over.mk f) (Gm S).X)
          (snd (Over.mk f ⊗ (Gm S).X) (Gm S).X *
            (fst (Over.mk f ⊗ (Gm S).X) (Gm S).X ≫ snd (Over.mk f) (Gm S).X)) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, laurentPoint_fst, Category.assoc, Category.assoc, lift_fst,
      whiskerRight_fst_assoc, laurentPoint_fst,
      show laurentPoint (laurentScheme f).hom ≫ fst (laurentScheme f) (Gm S).X ≫
          laurentInclusion f ≫ polynomialProj f =
        laurentInclusion (laurentScheme f).hom ≫ polynomialProj (laurentScheme f).hom ≫
          laurentInclusion f ≫ polynomialProj f from
          laurentPoint_fst_assoc (laurentScheme f).hom _]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, laurentMulHom, laurentInclusion, polynomialProj, Over.homMk_left]
    exact specMap_laurentMul_comp
  · rw [Category.assoc, laurentPoint_snd, Category.assoc, Category.assoc, lift_snd,
      MonObj.comp_mul, MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc, laurentPoint_snd,
      show laurentPoint (laurentScheme f).hom ≫ snd (laurentScheme f) (Gm S).X =
        (Gm.pointsEquiv _ _).symm (laurentUnit (laurentScheme f).hom) from
          laurentPoint_snd (laurentScheme f).hom,
      show laurentPoint (laurentScheme f).hom ≫ fst (laurentScheme f) (Gm S).X ≫
          (Gm.pointsEquiv S (laurentScheme f)).symm (laurentUnit f) =
        laurentInclusion (laurentScheme f).hom ≫ polynomialProj (laurentScheme f).hom ≫
          (Gm.pointsEquiv S (laurentScheme f)).symm (laurentUnit f) from
          laurentPoint_fst_assoc (laurentScheme f).hom _, ← Category.assoc]
    apply (Gm.pointsEquiv S _).injective
    rw [Gm.pointsEquiv_mul, Gm.pointsEquiv_naturality, Gm.pointsEquiv_naturality,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    erw [MulEquiv.apply_symm_apply]
    apply Units.ext
    change (Spec.map (laurentMul A)).appTop
        ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) =
      (Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1) *
        (Spec.map (polynomialToLaurent _) ≫ Spec.map (polynomialC _)).appTop
          ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1))
    rw [← Spec.map_comp, Corepresented.appTop_ΓSpecIso_inv_of_specMap_eq _ _ rfl,
      Corepresented.appTop_ΓSpecIso_inv_of_specMap_eq _ _ rfl, ← map_mul]
    congr 1
    change laurentMulRingHom A (LaurentPolynomial.T 1) =
      LaurentPolynomial.T 1 * Polynomial.toLaurent (Polynomial.C (LaurentPolynomial.T 1))
    rw [laurentMulRingHom_T_one, Polynomial.toLaurent_C]

end Points

end AffineLine

namespace Corepresented

open AffineLine

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B} (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)

/-- The coaction is compatible with the base ring. -/
theorem coaction_algebraMap (r : R) :
    coaction χ (algebraMap R B r) = LaurentPolynomial.C (algebraMap R B r) := by
  have h := algebraMap_comp_pointRing
    (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e))
  have hf : Spec.preimage (Spec.map (polynomialToLaurent (CommRingCat.of B)) ≫
      (polynomialScheme (structureMap e)).hom) =
      CommRingCat.ofHom (algebraMap R B) ≫ polynomialC _ ≫ polynomialToLaurent _ := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_comp]
    simp only [Category.assoc]
    rfl
  rw [hf] at h
  exact (congrArg (fun φ => φ.hom r) h).trans (Polynomial.toLaurent_C _)

/-- Evaluating the coaction at `T = 1` gives back the original function. -/
theorem coaction_comp_laurentEvalOne :
    coaction χ ≫ laurentEvalOne (CommRingCat.of B) = 𝟙 _ := by
  apply Spec.map_injective
  have h : laurentOne (structureMap e) ≫ laurentPoint (structureMap e) ≫
      Dynamic.orbit χ (universalPoint e) = universalPoint e := by
    rw [← Category.assoc, laurentOne_comp_laurentPoint, Dynamic.lift_one_comp_orbit]
  have h' := congrArg (fun y => y.left) h
  rw [Spec.map_comp, specMap_coaction, Spec.map_id]
  exact h'

/-- The sum of the coefficients of the coaction of `b` is `b`. -/
theorem sum_coeff_coaction (b : B) : ((coaction χ b).coeff.sum fun _ a => a) = b := by
  rw [← eval₂_id_one]
  exact congrArg (fun φ => φ b) (coaction_comp_laurentEvalOne χ)

/-- Coassociativity of the coaction: `(c ⊗ id) ∘ c = (id ⊗ Δ) ∘ c`. -/
theorem coaction_comp_laurentCoeffMap_coaction :
    coaction χ ≫ laurentCoeffMap (coaction χ) = coaction χ ≫ laurentMul (CommRingCat.of B) := by
  apply Spec.map_injective
  have h1 : Spec.map (coaction χ ≫ laurentCoeffMap (coaction χ)) =
      (laurentPoint (laurentScheme (structureMap e)).hom ≫ Dynamic.orbit χ
        (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e))).left :=
    (laurentPoint_comp_orbit_left χ
      (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e))).symm
  have h2 : laurentPoint (laurentScheme (structureMap e)).hom ≫
      Dynamic.orbit χ (laurentPoint (structureMap e) ≫ Dynamic.orbit χ (universalPoint e)) =
        laurentMulHom (structureMap e) ≫ laurentPoint (structureMap e) ≫
          Dynamic.orbit χ (universalPoint e) := by
    rw [← Dynamic.whiskerRight_orbit, Dynamic.orbit_orbit,
      reassoc_of% laurentMulHom_comp_laurentPoint]
  rw [h1, h2, Over.comp_left, ← specMap_coaction, Spec.map_comp]
  rfl

/-- The coefficients of the coaction are homogeneous: `c(c(b)ₙ) = c(b)ₙ Tⁿ`. -/
theorem coaction_coeff_coaction (b : B) (n : ℤ) :
    coaction χ ((coaction χ b).coeff n) =
      AddMonoidAlgebra.single n ((coaction χ b).coeff n) :=
  calc coaction χ ((coaction χ b).coeff n)
      = (laurentCoeffMap (coaction χ) (coaction χ b)).coeff n :=
        (coeff_laurentCoeffMap _ _ _).symm
    _ = ((coaction χ ≫ laurentCoeffMap (coaction χ)) b).coeff n := rfl
    _ = ((coaction χ ≫ laurentMul (CommRingCat.of B)) b).coeff n := by
        rw [coaction_comp_laurentCoeffMap_coaction]
    _ = (laurentMulRingHom (CommRingCat.of B) (coaction χ b)).coeff n := rfl
    _ = AddMonoidAlgebra.single n ((coaction χ b).coeff n) := coeff_laurentMulRingHom _ _ _

end Corepresented

end Langlands.GroupScheme
