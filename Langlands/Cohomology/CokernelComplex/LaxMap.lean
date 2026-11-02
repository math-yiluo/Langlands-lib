import Langlands.Cohomology.CokernelComplex.Map

/-! # Contravariant comparison of cokernel complexes without right exactness -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.CokernelComplex.Lax

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u''

variable {A : Type u} [Category.{v} A]
  {B : Type u'} [Category.{v'} B]
  {T : A ⥤ A} {η : 𝟭 A ⟶ T} {T' : B ⥤ B} {η' : 𝟭 B ⟶ T'}
  {Φ : A ⥤ B}
  (e : Φ ⋙ T' ⟶ T ⋙ Φ)
  (he : ∀ M : A, η'.app (Φ.obj M) ≫ e.app M = Φ.map (η.app M))

/-- Lift a residual comparison to the next terms using the given transformation. -/
def termMapOf {R : A ⥤ A} {R' : B ⥤ B} (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) :
    Φ ⋙ (R' ⋙ T') ⟶ (R ⋙ T) ⋙ Φ :=
  Functor.whiskerRight ρ T' ≫ Functor.whiskerLeft R e

@[simp]
theorem termMapOf_app {R : A ⥤ A} {R' : B ⥤ B} (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) (M : A) :
    (termMapOf e ρ).app M = T'.map (ρ.app M) ≫ e.app (R.obj M) := rfl

include he in
/-- The induced term map commutes with the two coaugmentations. -/
theorem termMapOf_comm {R : A ⥤ A} {R' : B ⥤ B} (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) (M : A) :
    η'.app (R'.obj (Φ.obj M)) ≫ (termMapOf e ρ).app M =
      ρ.app M ≫ Φ.map (η.app (R.obj M)) := by
  rw [termMapOf_app, ← Category.assoc, ← η'.naturality, Category.assoc]
  change ρ.app M ≫ (η'.app (Φ.obj (R.obj M)) ≫ e.app (R.obj M)) = _
  rw [he]

include he in
/-- The same coaugmentation square in the functor category. -/
theorem termMapOf_comm_nat {R : A ⥤ A} {R' : B ⥤ B} (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) :
    Functor.whiskerLeft Φ (Functor.whiskerLeft R' η') ≫ termMapOf e ρ =
      ρ ≫ Functor.whiskerRight (Functor.whiskerLeft R η) Φ := by
  ext M
  exact termMapOf_comm e he ρ M

variable [Abelian A] [Abelian B] [Φ.PreservesZeroMorphisms]

/-- Descend through the source cokernel; only precomposition preserves cokernels. -/
def stepMap {R : A ⥤ A} {R' : B ⥤ B} (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) :
    Φ ⋙ cokernel (Functor.whiskerLeft R' η') ⟶
      cokernel (Functor.whiskerLeft R η) ⋙ Φ :=
  (PreservesCokernel.iso ((Functor.whiskeringLeft A B B).obj Φ)
      (Functor.whiskerLeft R' η')).hom ≫
    cokernel.desc _
      (termMapOf e ρ ≫ Functor.whiskerRight (cokernel.π (Functor.whiskerLeft R η)) Φ)
      (by
        ext M
        change η'.app (R'.obj (Φ.obj M)) ≫ ((termMapOf e ρ).app M ≫
          Φ.map ((cokernel.π (Functor.whiskerLeft R η)).app M)) = 0
        rw [← Category.assoc, termMapOf_comm e he, Category.assoc, ← Φ.map_comp]
        have h := NatTrans.congr_app (cokernel.condition (Functor.whiskerLeft R η)) M
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.app_zero] at h
        rw [h, Φ.map_zero, comp_zero])

/-- The descended map has exactly the prescribed composite with the quotient. -/
theorem stepMap_comm {R : A ⥤ A} {R' : B ⥤ B} (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) :
    Functor.whiskerLeft Φ (cokernel.π (Functor.whiskerLeft R' η')) ≫ stepMap e he ρ =
      termMapOf e ρ ≫ Functor.whiskerRight (cokernel.π (Functor.whiskerLeft R η)) Φ := by
  dsimp only [stepMap]
  rw [← Category.assoc]
  erw [PreservesCokernel.π_iso_hom ((Functor.whiskeringLeft A B B).obj Φ)
    (Functor.whiskerLeft R' η')]
  exact cokernel.π_desc _ _ _

/-- The comparison of all successive residual functors. -/
def residualMap : (n : ℕ) → Φ ⋙ residual T' η' n ⟶ residual T η n ⋙ Φ
  | 0 => 𝟙 Φ
  | n + 1 => stepMap e he (residualMap n)

/-- The natural comparison in every degree. -/
def termMap (n : ℕ) : Φ ⋙ term T' η' n ⟶ term T η n ⋙ Φ :=
  termMapOf e (residualMap e he n)

/-- Compatibility at the residual coaugmentation in any degree. -/
theorem inclusion_comm (n : ℕ) (M : A) :
    (inclusion T' η' n).app (Φ.obj M) ≫ (termMap e he n).app M =
      (residualMap e he n).app M ≫ Φ.map ((inclusion T η n).app M) :=
  termMapOf_comm e he (residualMap e he n) M

/-- Compatibility at the actual successive cokernel projection. -/
theorem quotient_comm (n : ℕ) (M : A) :
    (quotient T' η' n).app (Φ.obj M) ≫ (residualMap e he (n + 1)).app M =
      (termMap e he n).app M ≫ Φ.map ((quotient T η n).app M) :=
  NatTrans.congr_app (stepMap_comm e he (residualMap e he n)) M

/-- The comparison commutes with the genuine differentials. -/
theorem differential_comm (n : ℕ) (M : A) :
    (differential T' η' n).app (Φ.obj M) ≫ (termMap e he (n + 1)).app M =
      (termMap e he n).app M ≫ Φ.map ((differential T η n).app M) := by
  simp only [differential, NatTrans.comp_app, Φ.map_comp, Category.assoc]
  rw [inclusion_comm, ← Category.assoc, quotient_comm, Category.assoc]

/-- A genuine chain map, although `Φ` need not preserve cokernels. -/
def complexMap (M : A) :
    complex T' η' (Φ.obj M) ⟶
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex T η M) where
  f n := (termMap e he n).app M
  comm' i j hij := by
    rcases hij with (rfl : i + 1 = j)
    simp only [Functor.mapHomologicalComplex_obj_d, complex_d]
    exact (differential_comm e he i M).symm

@[simp]
theorem complexMap_f (M : A) (n : ℕ) :
    (complexMap e he M).f n = (termMap e he n).app M := rfl

/-- The constructed chain map is natural in the original object. -/
def functorMap :
    Φ ⋙ functor T' η' ⟶ functor T η ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℕ) where
  app M := complexMap e he M
  naturality M N a := by
    ext n
    exact (termMap e he n).naturality a

@[simp]
theorem termMap_zero (M : A) : (termMap e he 0).app M = e.app M := by
  change T'.map (𝟙 (Φ.obj M)) ≫ e.app M = e.app M
  rw [T'.map_id, Category.id_comp]

/-- The chain map agrees with the original coaugmentation square. -/
theorem augmentation_complexMap (M : A) :
    augmentation T' η' (Φ.obj M) ≫ (complexMap e he M).f 0 =
      Φ.map (augmentation T η M) := by
  rw [complexMap_f, termMap_zero]
  exact he M

/-- The identity comparison remains the identity at all successive cokernels. -/
theorem residualMap_id (T : A ⥤ A) (η : 𝟭 A ⟶ T) (n : ℕ) :
    residualMap (Φ := 𝟭 A) (η := η) (η' := η) (𝟙 T)
        (fun M => Category.comp_id (η.app M)) n = 𝟙 (residual T η n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : Epi (quotient T η n) := by dsimp [quotient]; infer_instance
    apply (cancel_epi (quotient T η n)).1
    have h := stepMap_comm (Φ := 𝟭 A) (η := η) (η' := η) (𝟙 T)
      (fun M => Category.comp_id (η.app M))
      (residualMap (Φ := 𝟭 A) (η := η) (η' := η) (𝟙 T)
        (fun M => Category.comp_id (η.app M)) n)
    change quotient T η n ≫ stepMap (Φ := 𝟭 A) (η := η) (η' := η) (𝟙 T)
      (fun M => Category.comp_id (η.app M))
      (residualMap (Φ := 𝟭 A) (η := η) (η' := η) (𝟙 T)
        (fun M => Category.comp_id (η.app M)) n) = _
    erw [h]
    rw [ih]
    ext M
    simp [termMapOf, quotient, inclusion]

/-- The identity comparison gives the identity chain map. -/
theorem complexMap_id (T : A ⥤ A) (η : 𝟭 A ⟶ T) (M : A) :
    complexMap (Φ := 𝟭 A) (η := η) (η' := η) (𝟙 T)
        (fun M => Category.comp_id (η.app M)) M = 𝟙 (complex T η M) := by
  ext n
  simp [complexMap, termMap, termMapOf, residualMap_id]

section Composition

variable {C : Type u''} [Category.{v''} C] [Abelian C]
  {T'' : C ⥤ C} {η'' : 𝟭 C ⟶ T''} {Ψ : B ⥤ C} [Ψ.PreservesZeroMorphisms]
  (e' : Ψ ⋙ T'' ⟶ T' ⋙ Ψ)
  (he' : ∀ M : B, η''.app (Ψ.obj M) ≫ e'.app M = Ψ.map (η'.app M))

/-- Compose the original degree-zero comparisons in their spatial order. -/
def compose : (Φ ⋙ Ψ) ⋙ T'' ⟶ T ⋙ (Φ ⋙ Ψ) :=
  Functor.whiskerLeft Φ e' ≫ Functor.whiskerRight e Ψ

include he he' in
omit [Abelian A] [Abelian B] [Abelian C] [Φ.PreservesZeroMorphisms]
  [Ψ.PreservesZeroMorphisms] in
/-- The composite comparison also respects coaugmentation. -/
theorem compose_comm (M : A) :
    η''.app ((Φ ⋙ Ψ).obj M) ≫ (compose e e').app M =
      (Φ ⋙ Ψ).map (η.app M) := by
  change η''.app (Ψ.obj (Φ.obj M)) ≫ (e'.app (Φ.obj M) ≫ Ψ.map (e.app M)) = _
  rw [← Category.assoc, he', ← Ψ.map_comp, he]
  rfl

omit [Abelian A] [Abelian B] [Abelian C] [Φ.PreservesZeroMorphisms]
  [Ψ.PreservesZeroMorphisms] in
/-- Lifting a composite residual map gives the composite term map. -/
theorem termMapOf_comp {R : A ⥤ A} {R' : B ⥤ B} {R'' : C ⥤ C}
    (ρ : Φ ⋙ R' ⟶ R ⋙ Φ) (ρ' : Ψ ⋙ R'' ⟶ R' ⋙ Ψ) :
    termMapOf (compose e e')
        (Functor.whiskerLeft Φ ρ' ≫ Functor.whiskerRight ρ Ψ) =
      Functor.whiskerLeft Φ (termMapOf e' ρ') ≫
        Functor.whiskerRight (termMapOf e ρ) Ψ := by
  ext M
  change T''.map (ρ'.app (Φ.obj M) ≫ Ψ.map (ρ.app M)) ≫
      (e'.app (Φ.obj (R.obj M)) ≫ Ψ.map (e.app (R.obj M))) =
    (T''.map (ρ'.app (Φ.obj M)) ≫ e'.app (R'.obj (Φ.obj M))) ≫
      Ψ.map (T'.map (ρ.app M) ≫ e.app (R.obj M))
  rw [T''.map_comp, Ψ.map_comp]
  simp only [Category.assoc]
  have h := e'.naturality (ρ.app M)
  change T''.map (Ψ.map (ρ.app M)) ≫ e'.app (Φ.obj (R.obj M)) =
    e'.app (R'.obj (Φ.obj M)) ≫ Ψ.map (T'.map (ρ.app M)) at h
  rw [← Category.assoc (T''.map (Ψ.map (ρ.app M))), h]
  simp only [Category.assoc]

/-- Successive residual maps respect composition, by cokernel uniqueness. -/
theorem residualMap_comp (n : ℕ) :
    residualMap (compose e e') (compose_comm e he e' he') n =
      Functor.whiskerLeft Φ (residualMap e' he' n) ≫
        Functor.whiskerRight (residualMap e he n) Ψ := by
  induction n with
  | zero =>
    ext M
    change 𝟙 (Ψ.obj (Φ.obj M)) = 𝟙 _ ≫ Ψ.map (𝟙 (Φ.obj M))
    rw [Ψ.map_id, Category.id_comp]
  | succ n ih =>
    have : Epi (quotient T'' η'' n) := by dsimp [quotient]; infer_instance
    have : Epi (Functor.whiskerLeft (Φ ⋙ Ψ) (quotient T'' η'' n)) := by
      change Epi (((Functor.whiskeringLeft A C C).obj (Φ ⋙ Ψ)).map (quotient T'' η'' n))
      infer_instance
    apply (cancel_epi (Functor.whiskerLeft (Φ ⋙ Ψ) (quotient T'' η'' n))).1
    ext M
    change (quotient T'' η'' n).app (Ψ.obj (Φ.obj M)) ≫
        (residualMap (compose e e') (compose_comm e he e' he') (n + 1)).app M =
      (quotient T'' η'' n).app (Ψ.obj (Φ.obj M)) ≫
        ((residualMap e' he' (n + 1)).app (Φ.obj M) ≫
          Ψ.map ((residualMap e he (n + 1)).app M))
    erw [quotient_comm (compose e e') (compose_comm e he e' he') n M]
    rw [← Category.assoc, quotient_comm e' he', Category.assoc,
      ← Ψ.map_comp, quotient_comm e he, Ψ.map_comp]
    change (termMapOf (compose e e')
        (residualMap (compose e e') (compose_comm e he e' he') n)).app M ≫
        Ψ.map (Φ.map ((quotient T η n).app M)) = _
    rw [ih, termMapOf_comp]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      termMap, Category.assoc]

/-- The degreewise comparison respects composition. -/
theorem termMap_comp (n : ℕ) :
    termMap (compose e e') (compose_comm e he e' he') n =
      Functor.whiskerLeft Φ (termMap e' he' n) ≫
        Functor.whiskerRight (termMap e he n) Ψ := by
  unfold termMap
  rw [residualMap_comp, termMapOf_comp]

/-- The actual chain maps respect composition in the same order. -/
theorem complexMap_comp (M : A) :
    complexMap (compose e e') (compose_comm e he e' he') M =
      complexMap e' he' (Φ.obj M) ≫
        (Ψ.mapHomologicalComplex (ComplexShape.up ℕ)).map (complexMap e he M) := by
  ext n
  exact NatTrans.congr_app (termMap_comp e he e' he' n) M

end Composition

end Langlands.Cohomology.CokernelComplex.Lax
