/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

/-! # Scalar square for the prescribed finite-stage exchange
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

section GenericTransport

/-- A heterogeneous equality of comparisons `Q ⋙ S ≅ I ⋙ Q'`, over an equality of the
middle functors, gives their components up to the induced `eqToHom`. -/
theorem iso_app_of_heq_functor {A B C : Type*} [Category A] [Category B] [Category C]
    (Q : A ⥤ B) (Q' : A ⥤ C) {S S' : B ⥤ C} (hS : S = S')
    {c : Q ⋙ S ≅ Q'} {c' : Q ⋙ S' ≅ Q'} (h : HEq c c') (K : A) :
    c.hom.app K = eqToHom (by rw [hS]) ≫ c'.hom.app K := by
  subst hS
  rw [eq_of_heq h]
  simp

/-- Scalar transport of a localized integral morphism is the localization of its image. -/
theorem transport_map_localization_map {R : Type*} [CommRing R] (p : R) {C D : Type*}
    [Category C] [Preadditive C] [Linear R C] [Category D] [Preadditive D] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] {K L : C} (f : K ⟶ L) :
    (ScalarLocalization.transport R p F).map ((ScalarLocalization.localization R C p).map f) =
      (ScalarLocalization.localization R D p).map (F.map f) := by
  exact LinearMap.baseChange_tmul (F.mapLinearMap R) (1 : Localization.Away p) f

section LocalizationMerge
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {p : R} {C : Type*} [Category C] [Preadditive C] [Linear R C]

/-- Merge two localized arrows across an `eqToHom`. -/
theorem localization_map_eqToHom_map {a b c e : C} (u : a ⟶ b)
    (h : (ScalarLocalization.localization R C p).obj b =
      (ScalarLocalization.localization R C p).obj c) (v : c ⟶ e) :
    (ScalarLocalization.localization R C p).map u ≫ eqToHom h ≫
        (ScalarLocalization.localization R C p).map v =
      (ScalarLocalization.localization R C p).map
        (u ≫ eqToHom (congrArg ScalarLocalization.obj h) ≫ v) := by
  obtain rfl : b = c := congrArg ScalarLocalization.obj h
  simp

/-- Merge two localized arrows across an `eqToHom`, followed by a further arrow. -/
theorem localization_map_eqToHom_map_assoc {a b c e : C} {Z : ScalarLocalization R C p}
    (u : a ⟶ b) (h : (ScalarLocalization.localization R C p).obj b =
      (ScalarLocalization.localization R C p).obj c) (v : c ⟶ e)
    (w : (ScalarLocalization.localization R C p).obj e ⟶ Z) :
    (ScalarLocalization.localization R C p).map u ≫ eqToHom h ≫
        (ScalarLocalization.localization R C p).map v ≫ w =
      (ScalarLocalization.localization R C p).map
        (u ≫ eqToHom (congrArg ScalarLocalization.obj h) ≫ v) ≫ w := by
  rw [← localization_map_eqToHom_map, Category.assoc, Category.assoc]

/-- Absorb a leading `eqToHom` into a localized arrow. -/
theorem eqToHom_localization_map {a b e : C}
    (h : (ScalarLocalization.localization R C p).obj a =
      (ScalarLocalization.localization R C p).obj b) (v : b ⟶ e) :
    eqToHom h ≫ (ScalarLocalization.localization R C p).map v =
      (ScalarLocalization.localization R C p).map
        (eqToHom (congrArg ScalarLocalization.obj h) ≫ v) := by
  obtain rfl : a = b := congrArg ScalarLocalization.obj h
  simp

/-- Absorb a trailing `eqToHom` into a localized arrow. -/
theorem localization_map_comp_eqToHom {a b c : C} (u : a ⟶ b)
    (h : (ScalarLocalization.localization R C p).obj b =
      (ScalarLocalization.localization R C p).obj c) :
    (ScalarLocalization.localization R C p).map u ≫ eqToHom h =
      (ScalarLocalization.localization R C p).map
        (u ≫ eqToHom (congrArg ScalarLocalization.obj h)) := by
  obtain rfl : b = c := congrArg ScalarLocalization.obj h
  simp

end LocalizationMerge

/-- Solve `u₁ ≫ b ≫ u₃ = X` for the middle factor when the outer factors are invertible. -/
theorem eq_inv_comp_comp_inv {C : Type*} [Category C] {s t r v : C} (u₁ : s ≅ t)
    (b : t ⟶ r) (u₃ : r ≅ v) (X : s ⟶ v) (h : u₁.hom ≫ b ≫ u₃.hom = X) :
    b = u₁.inv ≫ X ≫ u₃.inv := by
  rw [← h]
  simp

/-- Solve `b ≫ u.hom = X` for `b`. -/
theorem eq_comp_inv_of_comp_hom {C : Type*} [Category C] {t r v : C} (b : t ⟶ r) (u : r ≅ v)
    (X : t ⟶ v) (h : b ≫ u.hom = X) : b = X ≫ u.inv := by
  rw [← h]
  simp

/-- Move two invertible end factors across an equation. -/
theorem comp_comp_hom_eq_hom_comp {C : Type*} [Category C] {a b c c' d e : C} (p : a ≅ b)
    (q : c ≅ d) (A : a ⟶ c') (B : c' ⟶ c) (R : b ⟶ e) (T : e ⟶ d)
    (h : p.inv ≫ A ≫ B = R ≫ T ≫ q.inv) : A ≫ B ≫ q.hom = p.hom ≫ R ≫ T := by
  rw [← cancel_epi p.inv, ← cancel_mono q.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact h

/-- A heterogeneous equality of morphisms over equalities of their endpoints. -/
theorem hom_eq_of_heq_objects {C : Type*} [Category C] {x x' y y' : C}
    (hx : x = x') (hy : y = y') {a : x ⟶ y} {b : x' ⟶ y'} (h : HEq a b) :
    a = eqToHom hx ≫ b ≫ eqToHom hy.symm := by
  subst hx hy
  simp [eq_of_heq h]

/-- Conclude a square conjugated by `eqToHom`s from a square with inverted end factors. -/
theorem eqToHom_square_of_inv_square {C : Type*} [Category C]
    {s t p₀ p₁ m₀ m₁ d₀ d₁ a₁ x₀ x₁ b₀ : C}
    (P : p₀ ⟶ p₁) (Pinv : p₁ ⟶ p₀) (M : m₀ ⟶ m₁) (M' : p₁ ⟶ d₀) (D : d₀ ⟶ d₁)
    (A : p₀ ⟶ a₁) (X : x₀ ⟶ x₁) (X' : a₁ ⟶ b₀) (B : b₀ ⟶ d₁) (Binv : d₁ ⟶ b₀)
    (h₀ : s = p₀) (h₁ : p₁ = m₀) (h₂ : m₁ = d₀) (h₃ : d₁ = t)
    (k₀ : s = p₀) (k₁ : a₁ = x₀) (k₂ : x₁ = b₀) (k₃ : d₁ = t)
    (hP : P ≫ Pinv = 𝟙 _) (hB : Binv ≫ B = 𝟙 _)
    (hM : M = eqToHom h₁.symm ≫ M' ≫ eqToHom h₂.symm)
    (hX : X = eqToHom k₁.symm ≫ X' ≫ eqToHom k₂.symm)
    (hE : M' ≫ D ≫ Binv = Pinv ≫ A ≫ X') :
    eqToHom h₀ ≫ (P ≫ eqToHom h₁ ≫ M ≫ eqToHom h₂ ≫ D) ≫ eqToHom h₃ =
      eqToHom k₀ ≫ (A ≫ eqToHom k₁ ≫ X ≫ eqToHom k₂ ≫ B) ≫ eqToHom k₃ := by
  subst h₀ h₁ h₂ k₁ k₂ h₃ hM hX
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  calc P ≫ M' ≫ D = P ≫ (M' ≫ D ≫ Binv) ≫ B := by simp [hB]
    _ = A ≫ X' ≫ B := by rw [hE]; simp [reassoc_of% hP]

/-- Move a component of a natural transformation along an equality of objects. -/
theorem natTrans_app_eq_eqToHom {C D : Type*} [Category C] [Category D] {G H : C ⥤ D}
    (τ : G ⟶ H) {x y : C} (e : x = y) :
    τ.app x = eqToHom (congrArg G.obj e) ≫ τ.app y ≫ eqToHom (congrArg H.obj e).symm := by
  subst e
  simp

/-- A functor `S` equal to `S'` with `L ⋙ S' = I ⋙ L'` maps `L.map x` to `L'.map (I.map x)`
up to `eqToHom`s. -/
theorem map_map_eq_of_comp_eq {A B C D : Type*} [Category A] [Category B] [Category C]
    [Category D] {L : A ⥤ B} {S S' : B ⥤ C} {I : A ⥤ D} {L' : D ⥤ C} (hS : S = S')
    (h : L ⋙ S' = I ⋙ L') {a b : A} (x : a ⟶ b) :
    S.map (L.map x) = eqToHom (by subst hS; exact Functor.congr_obj h a) ≫ L'.map (I.map x) ≫
      eqToHom (by subst hS; exact (Functor.congr_obj h b).symm) := by
  subst hS
  simpa using Functor.congr_hom h x

end GenericTransport

section ScalarTransport
variable (T : Scheme.{u}) [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
  {E F : Padic.FiniteCoefficientFields l Ω}

/-- Integral scalar extension of the stages is the embedding tensor of the small fields. -/
theorem pbcIntegralScalarExtension_eq_tensor (h : E ≤ F) :
    pbcIntegralScalarExtension l Ω T hdim hl h =
      pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T hdim hl :=
  pbcIntegralScalarExtension_eq l Ω T hdim hl h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] ULift.module in
/-- The rational embedding tensor is compatible with localization, objectwise literally. -/
theorem pbcStageLocalization_comp_rationalScalarExtension (h : E ≤ F) :
    pbcStageLocalization l Ω T E ⋙ pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl =
      pbcIntegralScalarExtension l Ω T hdim hl h ⋙ pbcStageLocalization l Ω T F := by
  rw [pbcIntegralScalarExtension_eq l Ω T hdim hl h]
  refine CategoryTheory.Functor.ext
    (F := pbcStageLocalization l Ω T E ⋙ pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl)
    (G := pbcEmbeddingIntegralTensor l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) T hdim hl ⋙
        pbcStageLocalization l Ω T F) (fun _ ↦ rfl) ?_
  intro K L f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change pbcRationalScalarHom l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
    (pbcFiniteFieldInclusion l Ω h) T hdim hl K L (1 ⊗ₜ[_] f) = _
  rw [pbcRationalScalarHom_tmul]
  simp only [map_one]
  rfl

/-- For distinct stages the chosen scalar extension is the rational embedding tensor. -/
theorem pbcScalarExtension_eq_rational (h : E ≤ F) (hEF : E ≠ F) :
    pbcScalarExtension l Ω T hdim hl h =
      pbcRationalScalarExtension l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T hdim hl := by
  have hs : pbcScalarExtension l Ω T hdim hl h =
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
    simp [pbcScalarExtension, hEF]
  rw [hs]
  exact (pbcRationalScalarExtension_exists l Ω T hdim hl h).unique
    (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec
    (pbcStageLocalization_comp_rationalScalarExtension l Ω T hdim hl h)

/-- For distinct stages the scalar/integral comparison is the identity-component
isomorphism given by the defining functor equality. -/
theorem pbcScalarIntegralComparison_ne (h : E ≤ F) (hEF : E ≠ F) :
    HEq (pbcScalarIntegralComparison l Ω T hdim hl h)
      (eqToIso (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec) :=
  (pbcScalarIntegralComparison_exists l Ω T hdim hl h).exists.choose_spec.2 hEF

/-- For distinct stages every component of the scalar/integral comparison is an `eqToHom`. -/
theorem pbcScalarIntegralComparison_hom_app_ne (h : E ≤ F) (hEF : E ≠ F)
    (K : pbcIntegralStage l Ω T E) :
    ∃ e, (pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K = eqToHom e := by
  have hs : pbcScalarExtension l Ω T hdim hl h =
      (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose := by
    simp [pbcScalarExtension, hEF]
  rw [iso_app_of_heq_functor _ _ hs (pbcScalarIntegralComparison_ne l Ω T hdim hl h hEF) K]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
  refine ⟨?_, trivial⟩
  rw [hs]
  exact Functor.congr_obj (pbcRationalScalarExtension_exists l Ω T hdim hl h).exists.choose_spec K


/-- For distinct stages every inverse component of the scalar/integral comparison is an
`eqToHom`. -/
theorem pbcScalarIntegralComparison_inv_app_ne (h : E ≤ F) (hEF : E ≠ F)
    (K : pbcIntegralStage l Ω T E) :
    ∃ e, (pbcScalarIntegralComparison l Ω T hdim hl h).inv.app K = eqToHom e := by
  obtain ⟨e, he⟩ := pbcScalarIntegralComparison_hom_app_ne l Ω T hdim hl h hEF K
  refine ⟨e.symm, ?_⟩
  rw [← cancel_epi ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K), Iso.hom_inv_id_app,
    he, eqToHom_trans, eqToHom_refl]
end ScalarTransport

section ScalarExchange
variable (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The ambient scalar exchange equation: scalar extension along `i` carries the completed
exchange at `E` to the completed exchange at `F`, through the scalar direct-image and
completed-pullback comparisons. -/
theorem pbcScalarCompletedExchange (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i Y').map
        ((pbcActualCompletedExchange (pbcIntegralDatum l E) sq).app K) ≫
      (pbcScalarDirectImageIso l E F i f').hom.app
        ((pbcActualCompletedPull g' (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPush f' (pbcIntegralDatum l F)).map
        ((pbcScalarCompletedPullIso l E F i g').inv.app K) =
    (pbcScalarCompletedPullIso l E F i g).inv.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualCompletedPull g (pbcIntegralDatum l F)).map
        ((pbcScalarDirectImageIso l E F i f).hom.app K) ≫
      (pbcActualCompletedExchange (pbcIntegralDatum l F) sq).app
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) := by
  sorry


/-- The scalar exchange equation conjugated by `eqToHom`s, with the middle exchange
components given up to `eqToHom`s; this is the shape of the `E ≠ F` exchange branch. -/
theorem pbcScalarCompletedExchange_eqToHom_square
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    {s t m₀ m₁ x₀ x₁ : PbcCompletedDerived Y' (pbcIntegralDatum l F)}
    (M : m₀ ⟶ m₁) (Xm : x₀ ⟶ x₁)
    (h₀ : s = _) (h₁ : _ = m₀) (h₂ : m₁ = _) (h₃ : _ = t)
    (k₀ : s = _) (k₁ : _ = x₀) (k₂ : x₁ = _) (k₃ : _ = t)
    (hM : M = eqToHom h₁.symm ≫ (pbcEmbeddingAmbientTensor l E F i Y').map
      ((pbcActualCompletedExchange (pbcIntegralDatum l E) sq).app K) ≫ eqToHom h₂.symm)
    (hX : Xm = eqToHom k₁.symm ≫ (pbcActualCompletedExchange (pbcIntegralDatum l F) sq).app
      ((pbcEmbeddingAmbientTensor l E F i X).obj K) ≫ eqToHom k₂.symm) :
    eqToHom h₀ ≫ ((pbcScalarCompletedPullIso l E F i g).hom.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K) ≫ eqToHom h₁ ≫ M ≫
        eqToHom h₂ ≫ (pbcScalarDirectImageIso l E F i f').hom.app
          ((pbcActualCompletedPull g' (pbcIntegralDatum l E)).obj K)) ≫ eqToHom h₃ =
      eqToHom k₀ ≫ ((pbcActualCompletedPull g (pbcIntegralDatum l F)).map
          ((pbcScalarDirectImageIso l E F i f).hom.app K) ≫ eqToHom k₁ ≫ Xm ≫
          eqToHom k₂ ≫ (pbcActualDerivedPush f' (pbcIntegralDatum l F)).map
            ((pbcScalarCompletedPullIso l E F i g').hom.app K)) ≫ eqToHom k₃ :=
  eqToHom_square_of_inv_square _ _ M _ _ _ Xm _ _ _ h₀ h₁ h₂ h₃ k₀ k₁ k₂ k₃
    (Iso.hom_inv_id_app _ _)
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact CategoryTheory.Functor.map_id _ _) hM hX
    (pbcScalarCompletedExchange l E F i sq K)

end ScalarExchange

omit [IsAlgClosure ℚ_[l] Ω] in
/-- The rational direct image of a localized integral arrow is the localized direct image. -/
theorem pbcDescentDirectImage_map_homMk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) {K L : pbcIntegralStage l Ω X E}
    (φ : K.obj ⟶ L.obj) :
    (pbcDescentDirectImage l Ω f presRf E).map
        ((pbcStageLocalization l Ω X E).map (ObjectProperty.homMk φ)) =
      (pbcStageLocalization l Ω Y E).map
        (ObjectProperty.homMk
          (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)
          (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj L)
          ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).map φ)) :=
  transport_map_localization_map _ _ _

omit [IsAlgClosure ℚ_[l] Ω] in
/-- The rational pullback of a localized integral arrow is the localized pullback. -/
theorem pbcDescentPullback_map_homMk {X Y : Scheme.{u}} (g : X ⟶ Y)
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) {K L : pbcIntegralStage l Ω Y E}
    (φ : K.obj ⟶ L.obj) :
    (pbcDescentPullback l Ω g presLg E).map
        ((pbcStageLocalization l Ω Y E).map (ObjectProperty.homMk φ)) =
      (pbcStageLocalization l Ω X E).map
        (ObjectProperty.homMk
          (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj K)
          (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj L)
          ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).map φ)) :=
  transport_map_localization_map _ _ _

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

/-- `pbcExchangeStageSquare` on integral objects, with the composite comparisons of
`StageSystem.Morphism.comp` expanded. -/
theorem pbcExchangeStageSquare_integral
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (Rf' : StageSystem.Morphism (pbcScalarSystem l Ω X' dX'.out iX'.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg' : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω X' dX'.out iX'.out))
    (hRf : ∀ E, Rf.Φ E = pbcDescentDirectImage l Ω f presRf E)
    (hRf' : ∀ E, Rf'.Φ E = pbcDescentDirectImage l Ω f' presRf' E)
    (hLg : ∀ E, Lg.Φ E = pbcDescentPullback l Ω g presLg E)
    (hLg' : ∀ E, Lg'.Φ E = pbcDescentPullback l Ω g' presLg' E)
    (bRf : PbcDirectImageBetaSpec l Ω f presRf Rf)
    (bRf' : PbcDirectImageBetaSpec l Ω f' presRf' Rf')
    (bLg : PbcPullbackBetaSpec l Ω g presLg Lg)
    (bLg' : PbcPullbackBetaSpec l Ω g' presLg' Lg')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (Rf.comp Lg).Φ E ⟶ (Lg'.comp Rf').Φ E)
    (hτ : ∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app
                  K.obj)))) :
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcIntegralStage l Ω X E),
      ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map
          ((τ E).app (ScalarLocalization.mk K)) ≫
          (Rf'.β h).hom.app ((Lg'.Φ E).obj (ScalarLocalization.mk K)) ≫
          (Rf'.Φ F).map ((Lg'.β h).hom.app (ScalarLocalization.mk K)) =
        (Lg.β h).hom.app ((Rf.Φ E).obj (ScalarLocalization.mk K)) ≫
          (Lg.Φ F).map ((Rf.β h).hom.app (ScalarLocalization.mk K)) ≫
          (τ F).app
            (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj (ScalarLocalization.mk K)) := by
  obtain ⟨ΦRf, βRf, cohRf⟩ := Rf
  obtain ⟨ΦRf', βRf', cohRf'⟩ := Rf'
  obtain ⟨ΦLg, βLg, cohLg⟩ := Lg
  obtain ⟨ΦLg', βLg', cohLg'⟩ := Lg'
  obtain rfl : ΦRf = _ := funext hRf
  obtain rfl : ΦRf' = _ := funext hRf'
  obtain rfl : ΦLg = _ := funext hLg
  obtain rfl : ΦLg' = _ := funext hLg'
  intro E F h K
  -- The four BetaSpec identities, transported to homogeneous equations.
  have bRf₀ := bRf h rfl rfl K
  have bRf'₀ := bRf' h rfl rfl ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K)
  have bLg₀ := bLg h rfl rfl ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)
  have bLg'₀ := bLg' h rfl rfl K
  simp only [eqToIso_refl, Iso.refl_symm, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_trans, Iso.trans_refl] at bRf₀ bRf'₀ bLg₀ bLg'₀
  -- The localized ambient comparisons characterizing the four chosen rational ones.
  have rRf := (pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f
    dX.out dY.out iX.out iY.out (presRf E) (presRf F)).exists.choose_spec ⟨K⟩
  have rRf' := (pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f'
    dX'.out dY'.out iX'.out iY'.out (presRf' E) (presRf' F)).exists.choose_spec
      ⟨(pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K⟩
  have rLg := (pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) g
    dY'.out dY.out iY'.out iY.out (presLg E) (presLg F)).exists.choose_spec
      ⟨(pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K⟩
  have rLg' := (pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) g'
    dX'.out dX.out iX'.out iX.out (presLg' E) (presLg' F)).exists.choose_spec ⟨K⟩
  -- Compose the heterogeneous specifications before transporting their endpoints.
  have eRf := hom_eq_of_heq_objects ?x₁ ?y₁ (bRf₀.trans rRf)
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  have eRf' := hom_eq_of_heq_objects ?x₂ ?y₂ (bRf'₀.trans rRf')
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  have eLg := hom_eq_of_heq_objects ?x₃ ?y₃ (bLg₀.trans rLg)
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]
  have eLg' := hom_eq_of_heq_objects ?x₄ ?y₄ (bLg'₀.trans rLg')
  rotate_left
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]; rfl
  · simp only [Functor.comp_obj]; rw [pbcIntegralScalarExtension_eq_tensor]
  have hτE₁ := eq_of_heq (hτ E K)
  have βLg_inv := eq_inv_comp_comp_inv
    ((pbcDescentPullback l Ω g presLg F).mapIso
      ((pbcScalarIntegralComparison l Ω Y dY.out iY.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)).symm) _
    ((pbcScalarIntegralComparison l Ω Y' dY'.out iY'.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
          (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))) _ eLg
  have βLg'_inv := eq_inv_comp_comp_inv
    ((pbcDescentPullback l Ω g' presLg' F).mapIso
      ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).app K).symm) _
    ((pbcScalarIntegralComparison l Ω X' dX'.out iX'.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K)) _ eLg'
  -- Reduce record projections without unfolding the concrete stage functors.
  dsimp only
  refine comp_comp_hom_eq_hom_comp (C := pbcStageCategory l Ω Y' F)
    ((βLg h).app ((pbcDescentDirectImage l Ω f presRf E).obj ⟨K⟩))
    ((pbcDescentDirectImage l Ω f' presRf' F).mapIso ((βLg' h).app ⟨K⟩)) _ _ _ _ ?_
  simp only [Iso.app_inv, Functor.mapIso_inv]
  have βRf_hom := eq_inv_comp_comp_inv
    ((pbcScalarIntegralComparison l Ω Y dY.out iY.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)).symm _
    ((pbcDescentDirectImage l Ω f presRf F).mapIso
      ((pbcScalarIntegralComparison l Ω X dX.out iX.out h).app K)) _ eRf
  have βRf'_hom := eq_inv_comp_comp_inv
    ((pbcScalarIntegralComparison l Ω Y' dY'.out iY'.out h).app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
          (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))).symm _
    ((pbcDescentDirectImage l Ω f' presRf' F).mapIso
      ((pbcScalarIntegralComparison l Ω X' dX'.out iX'.out h).app
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
          (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))) _ eRf'
  -- Focus the rewrites on their components to avoid unfolding the whole square.
  conv_lhs =>
    arg 1
    erw [βLg_inv]
  conv_lhs =>
    arg 2
    arg 2
    erw [βRf'_hom]
  simp only [βLg'_inv, βRf_hom]
  by_cases hEF : E = F
  · sorry
  simp only [Iso.app_hom, Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv]
  have h₁ := (pbcScalarIntegralComparison_hom_app_ne l Ω Y dY.out iY.out h hEF
    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K)).choose_spec
  have h₄ := (pbcScalarIntegralComparison_inv_app_ne l Ω X' dX'.out iX'.out h hEF
    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K)).choose_spec
  have h₅ := pbcScalarIntegralComparison_hom_app_ne l Ω X dX.out iX.out h hEF K
  let e₅ := h₅.choose
  have h₅ := h₅.choose_spec
  have h₆ := (pbcScalarIntegralComparison_inv_app_ne l Ω X dX.out iX.out h hEF K).choose_spec
  have h₇ := (pbcScalarIntegralComparison_inv_app_ne l Ω Y' dY'.out iY'.out h hEF
    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))).choose_spec
  have h₈ := (pbcScalarIntegralComparison_hom_app_ne l Ω Y' dY'.out iY'.out h hEF
    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))).choose_spec
  simp only [h₁, h₄, h₅, h₆, h₇, h₈]
  -- τ-naturality: move `τ F` to the localized integral scalar extension and use `hτ F`.
  have hτF₁ := eq_of_heq
    (hτ F ((pbcIntegralScalarExtension l Ω X dX.out iX.out h).obj K))
  conv_rhs =>
    arg 2
    arg 1
    erw [natTrans_app_eq_eqToHom (τ F) e₅, hτF₁]
  simp only [hτE₁]
  conv_lhs =>
    arg 2
    arg 1
    erw [map_map_eq_of_comp_eq (pbcScalarExtension_eq_rational l Ω Y' dY'.out iY'.out h hEF)
      (pbcStageLocalization_comp_rationalScalarExtension l Ω Y' dY'.out iY'.out h)]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  set_option backward.isDefEq.respectTransparency false in
  simp only [pbcDescentPullback_map_homMk, pbcDescentDirectImage_map_homMk]
  set_option backward.isDefEq.respectTransparency false in
  simp only [localization_map_eqToHom_map_assoc]
  set_option backward.isDefEq.respectTransparency false in
  simp only [eqToHom_localization_map, localization_map_comp_eqToHom]
  congr 1
  ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom]
  refine pbcScalarCompletedExchange_eqToHom_square (l := l) (E := pbcFiniteField l Ω E)
    (F := pbcFiniteField l Ω F) (i := pbcFiniteFieldInclusion l Ω h) (sq := sq) (K := K.obj)
    (hM := ?_) (hX := ?_) ..
  · sorry
  · sorry

/-- The prescribed localized actual exchange components satisfy the scalar
square for already given normalized stage families. Existence and naturality of
the stage transformations are supplied separately. -/
theorem pbcExchangeStageSquare
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g' f' f g)
    (presRf : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presRf' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X' E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (presLg' : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete X' (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out))
    (Rf' : StageSystem.Morphism (pbcScalarSystem l Ω X' dX'.out iX'.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω Y' dY'.out iY'.out))
    (Lg' : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω X' dX'.out iX'.out))
    (hRf : ∀ E, Rf.Φ E = pbcDescentDirectImage l Ω f presRf E)
    (hRf' : ∀ E, Rf'.Φ E = pbcDescentDirectImage l Ω f' presRf' E)
    (hLg : ∀ E, Lg.Φ E = pbcDescentPullback l Ω g presLg E)
    (hLg' : ∀ E, Lg'.Φ E = pbcDescentPullback l Ω g' presLg' E)
    (bRf : PbcDirectImageBetaSpec l Ω f presRf Rf)
    (bRf' : PbcDirectImageBetaSpec l Ω f' presRf' Rf')
    (bLg : PbcPullbackBetaSpec l Ω g presLg Lg)
    (bLg' : PbcPullbackBetaSpec l Ω g' presLg' Lg')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (Rf.comp Lg).Φ E ⟶ (Lg'.comp Rf').Φ E)
    (hτ : ∀ (E : Padic.FiniteCoefficientFields l Ω)
          (K : pbcIntegralStage l Ω X E),
          HEq ((τ E).app (ScalarLocalization.mk K))
            ((pbcStageLocalization l Ω Y' E).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (presLg E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (presRf E)).obj K))
                (Y := (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                  (pbcActualDerivedPush f' (pbcStageDatum.{u} l Ω E)) (presRf' E)).obj
                    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
                      (pbcActualCompletedPull g' (pbcStageDatum.{u} l Ω E)) (presLg' E)).obj K))
                ((pbcActualCompletedExchange (pbcStageDatum.{u} l Ω E) sq).app
                  K.obj)))) :
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcStageCategory l Ω X E),
      ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map ((τ E).app K) ≫
          ((Lg'.comp Rf').β h).hom.app K =
        ((Rf.comp Lg).β h).hom.app K ≫
          (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj K) := by
  intro E F h K
  obtain ⟨K⟩ := K
  simp only [StageSystem.Morphism.comp, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  exact pbcExchangeStageSquare_integral l Ω X Y X' Y' f f' g g' sq presRf presRf' presLg presLg'
    Rf Rf' Lg Lg' hRf hRf' hLg hLg' bRf bRf' bLg bLg' τ hτ h K

end AlgebraicGeometry.Scheme
