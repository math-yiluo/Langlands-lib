import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # Orbit extensions over affine test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

namespace AffineLine

section Affine

variable {A : CommRingCat.{u}} (f : Spec A ⟶ S)

theorem specHomEquiv_polynomialPointInvLeft :
    Gm.specHomEquiv _ _ (polynomialPointInvLeft f) = polynomialSections f :=
  Equiv.apply_symm_apply _ _

/-- `polynomialPoint` is an isomorphism, with inverse `polynomialPointInv`. -/
theorem polynomialPoint_comp_polynomialPointInv :
    polynomialPoint f ≫ polynomialPointInv f = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply (Gm.specHomEquiv _ _).injective
  change Gm.specHomEquiv _ _ ((polynomialPoint f).left ≫ polynomialPointInvLeft f) =
    Gm.specHomEquiv _ _ (𝟙 _)
  rw [Gm.specHomEquiv_comp, specHomEquiv_polynomialPointInvLeft]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext'
  · have h : polynomialC A ≫ polynomialSections f ≫ (polynomialPoint f).left.appTop =
        polynomialC A ≫ Gm.specHomEquiv _ _ (𝟙 _) := by
      rw [← Category.assoc, polynomialC_comp_polynomialSections, ← Gm.specHomEquiv_comp,
        ← Over.comp_left, polynomialPoint, lift_fst, ← Gm.specHomEquiv_specMap,
        Category.id_comp]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  · rw [CommRingCat.hom_comp, RingHom.comp_apply, polynomialSections_X, ← homEquiv_comp,
      polynomialPoint, lift_snd, Equiv.apply_symm_apply]
    simp [Gm.specHomEquiv]

/-- The point `(Spec A[X, X⁻¹] → Spec A, X)` of `Spec A ×_S 𝔾_{m,S}`. -/
def laurentPoint : laurentScheme f ⟶ Over.mk f ⊗ (Gm S).X :=
  lift (laurentInclusion f ≫ polynomialProj f) ((Gm.pointsEquiv _ _).symm (laurentUnit f))

/-- On `Spec A[X, X⁻¹]`, the polynomial point is the Laurent point followed by the inclusion of
`Spec A ×_S 𝔾_{m,S}` in `Spec A ×_S 𝔸¹_S`. -/
theorem laurentInclusion_comp_polynomialPoint :
    laurentInclusion f ≫ polynomialPoint f = laurentPoint f ≫ Over.mk f ◁ unitInclusion S :=
  laurentInclusion_polynomialPoint f

/-- The ring homomorphism `A[X, X⁻¹] ⟶ Γ(Spec A ×_S 𝔾_{m,S})` sending `a` to its pullback along
the first projection and `X` to the coordinate unit. -/
def laurentSections :
    CommRingCat.of (LaurentPolynomial A) ⟶ Γ((Over.mk f ⊗ (Gm S).X).left, ⊤) :=
  CommRingCat.ofHom (LaurentPolynomial.eval₂
    (Gm.specHomEquiv _ A (fst (Over.mk f) (Gm S).X).left).hom
    (Gm.pointsEquiv S _ (snd (Over.mk f) (Gm S).X)))

/-- The underlying morphism of the inverse of `laurentPoint`. -/
def laurentPointInvLeft :
    (Over.mk f ⊗ (Gm S).X).left ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  (Gm.specHomEquiv _ _).symm (laurentSections f)

theorem laurentPointInvLeft_comp :
    laurentPointInvLeft f ≫ Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) =
      (fst (Over.mk f) (Gm S).X).left := by
  apply (Gm.specHomEquiv _ _).injective
  rw [← Category.assoc, Gm.specHomEquiv_specMap, Gm.specHomEquiv_specMap, laurentPointInvLeft,
    Equiv.apply_symm_apply]
  ext a
  simp [laurentSections, Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C]

/-- The inverse of `laurentPoint`. -/
def laurentPointInv : Over.mk f ⊗ (Gm S).X ⟶ laurentScheme f :=
  Over.homMk (laurentPointInvLeft f) (by
    rw [← Over.w (fst (Over.mk f) (Gm S).X), ← laurentPointInvLeft_comp]
    simp only [Category.assoc]
    rfl)

/-- `laurentPoint` is a split epimorphism, with section `laurentPointInv`. -/
theorem laurentPointInv_comp_laurentPoint : laurentPointInv f ≫ laurentPoint f = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, laurentPoint, lift_fst, Category.id_comp]
    exact Over.OverMorphism.ext (laurentPointInvLeft_comp f)
  · rw [Category.assoc, laurentPoint, lift_snd, Category.id_comp]
    apply (Gm.pointsEquiv S _).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    apply Units.ext
    change (laurentPointInvLeft f).appTop ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)) = _
    change Gm.specHomEquiv _ _ (laurentPointInvLeft f) (LaurentPolynomial.T 1) = _
    rw [laurentPointInvLeft, Equiv.apply_symm_apply]
    simp [laurentSections, LaurentPolynomial.eval₂_T]

/-- An extension along `Spec A ×_S 𝔾_{m,S} ⊆ Spec A ×_S 𝔸¹_S` gives an extension along
`Spec A[X, X⁻¹] ⊆ Spec A[X]`. -/
theorem laurentInclusion_comp_of_whiskerLeft {Y : Over S} {e : Over.mk f ⊗ scheme S ⟶ Y}
    {o : Over.mk f ⊗ (Gm S).X ⟶ Y} (h : Over.mk f ◁ unitInclusion S ≫ e = o) :
    laurentInclusion f ≫ polynomialPoint f ≫ e = laurentPoint f ≫ o := by
  rw [← h, ← Category.assoc, laurentInclusion_comp_polynomialPoint, Category.assoc]

/-- An extension along `Spec A[X, X⁻¹] ⊆ Spec A[X]` gives an extension along
`Spec A ×_S 𝔾_{m,S} ⊆ Spec A ×_S 𝔸¹_S`. -/
theorem whiskerLeft_comp_of_laurentInclusion {Y : Over S} {e : polynomialScheme f ⟶ Y}
    {o : Over.mk f ⊗ (Gm S).X ⟶ Y} (h : laurentInclusion f ≫ e = laurentPoint f ≫ o) :
    Over.mk f ◁ unitInclusion S ≫ polynomialPointInv f ≫ e = o := by
  have hs := laurentPointInv_comp_laurentPoint f
  calc Over.mk f ◁ unitInclusion S ≫ polynomialPointInv f ≫ e
      = laurentPointInv f ≫ laurentPoint f ≫ Over.mk f ◁ unitInclusion S ≫
          polynomialPointInv f ≫ e := by
        rw [reassoc_of% hs]
    _ = laurentPointInv f ≫ laurentInclusion f ≫ polynomialPoint f ≫ polynomialPointInv f ≫ e := by
        rw [reassoc_of% (laurentInclusion_comp_polynomialPoint f)]
    _ = laurentPointInv f ≫ laurentInclusion f ≫ e := by
        rw [reassoc_of% (polynomialPoint_comp_polynomialPointInv f)]
    _ = o := by rw [h, reassoc_of% hs]

variable (A) in
/-- Evaluation at zero `A[X] ⟶ A`. -/
abbrev polynomialEvalZero : CommRingCat.of (Polynomial A) ⟶ A :=
  CommRingCat.ofHom (Polynomial.evalRingHom 0)

variable (A) in
theorem polynomialC_comp_polynomialEvalZero : polynomialC A ≫ polynomialEvalZero A = 𝟙 A := by
  ext a
  simp

/-- The zero section `Spec A ⟶ Spec A[X]` over `S`, given by evaluation at `0`. -/
def polynomialZero : Over.mk f ⟶ polynomialScheme f :=
  Over.homMk (Spec.map (polynomialEvalZero A)) (by
    change Spec.map (polynomialEvalZero A) ≫ Spec.map (polynomialC A) ≫ f = f
    rw [← Category.assoc, ← Spec.map_comp, polynomialC_comp_polynomialEvalZero, Spec.map_id,
      Category.id_comp])

/-- The zero section of `Spec A[X]` is the zero section of `Spec A ×_S 𝔸¹_S`. -/
theorem polynomialZero_comp_polynomialPoint :
    polynomialZero f ≫ polynomialPoint f = lift (𝟙 _) (toUnit _ ≫ zeroSection S) := by
  rw [polynomialPoint, comp_lift]
  congr 1
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.id_left]
    change Spec.map (polynomialEvalZero A) ≫ Spec.map (polynomialC A) = 𝟙 _
    rw [← Spec.map_comp, polynomialC_comp_polynomialEvalZero, Spec.map_id]
  · apply hom_ext
    rw [homEquiv_comp, Equiv.apply_symm_apply, homEquiv_comp_zeroSection]
    change (Spec.map (polynomialEvalZero A)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).inv Polynomial.X) = 0
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-- The value at zero of `polynomialPointInv f ≫ e` is the value of `e` at `X = 0`. -/
theorem evalZero_polynomialPointInv {Y : Over S} (e : polynomialScheme f ⟶ Y) :
    Dynamic.evalZero (polynomialPointInv f ≫ e) = polynomialZero f ≫ e := by
  rw [Dynamic.evalZero, ← polynomialZero_comp_polynomialPoint, Category.assoc,
    ← Category.assoc (polynomialPoint f), polynomialPoint_comp_polynomialPointInv,
    Category.id_comp]

end Affine

section Naturality

variable {A A' : CommRingCat.{u}}

/-- The map `A'[X, X⁻¹] ⟶ A[X, X⁻¹]` induced by a ring homomorphism `A' ⟶ A` on coefficients. -/
abbrev laurentCoeffMap (ψ : A' ⟶ A) :
    CommRingCat.of (LaurentPolynomial A') ⟶ CommRingCat.of (LaurentPolynomial A) :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ ψ.hom)

theorem polynomialC_comp_polynomialToLaurent_comp_laurentCoeffMap (ψ : A' ⟶ A) :
    polynomialC A' ≫ polynomialToLaurent A' ≫ laurentCoeffMap ψ =
      ψ ≫ polynomialC A ≫ polynomialToLaurent A := by
  ext b
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Polynomial.toLaurent_C, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]

theorem laurentCoeffMap_T (ψ : A' ⟶ A) (m : ℤ) :
    laurentCoeffMap ψ (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  simp only [CommRingCat.hom_ofHom, LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single,
    map_one]

variable {f : Spec A ⟶ S} {g : Spec A' ⟶ S}

/-- The map `Spec A[X, X⁻¹] ⟶ Spec A'[X, X⁻¹]` induced by a morphism `Spec A ⟶ Spec A'` over
`S`, on coefficients. -/
def laurentMap (a : Over.mk f ⟶ Over.mk g) : laurentScheme f ⟶ laurentScheme g :=
  Over.homMk (Spec.map (laurentCoeffMap (Spec.preimage a.left))) (by
    change _ ≫ Spec.map (polynomialToLaurent A') ≫ Spec.map (polynomialC A') ≫ g =
      Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫ f
    have hw : Spec.map (Spec.preimage a.left) ≫ g = f := by
      rw [Spec.map_preimage]
      exact Over.w a
    have hf : Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫ f =
        Spec.map (polynomialToLaurent A) ≫ Spec.map (polynomialC A) ≫
          Spec.map (Spec.preimage a.left) ≫ g := by
      rw [hw]
    rw [hf]
    simp only [← Category.assoc, ← Spec.map_comp]
    rw [Category.assoc, polynomialC_comp_polynomialToLaurent_comp_laurentCoeffMap,
      Category.assoc])

/-- The Laurent point is natural in the coefficients. -/
theorem laurentPoint_comp_whiskerRight (a : Over.mk f ⟶ Over.mk g) :
    laurentPoint f ≫ a ▷ (Gm S).X = laurentMap a ≫ laurentPoint g := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, whiskerRight_fst, laurentPoint, lift_fst_assoc,
      laurentPoint, lift_fst]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, laurentInclusion, polynomialProj, laurentMap, Over.homMk_left]
    conv_lhs => rw [← Spec.map_preimage a.left]
    simp only [← Spec.map_comp, ← Category.assoc]
    simp only [Category.assoc, polynomialC_comp_polynomialToLaurent_comp_laurentCoeffMap]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, laurentPoint, lift_snd, laurentPoint,
      lift_snd]
    apply (Gm.pointsEquiv S _).injective
    rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply Units.ext
    change (Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1) =
      (Spec.map (laurentCoeffMap (Spec.preimage a.left))).appTop
        ((Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1))
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      laurentCoeffMap_T]

end Naturality

end AffineLine

end Langlands.GroupScheme
