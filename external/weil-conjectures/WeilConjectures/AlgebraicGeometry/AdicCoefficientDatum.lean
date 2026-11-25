/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.AlgebraicGeometry.AdicLisseModule
public import WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatum
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# The completed coefficient ring and its strict derived reduction tower

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
def-weil-pbc-adic-coefficient-datum, order 1239; Stacks Tags 06XN, 06YS, 06YY.
(blueprint: def-weil-pbc-adic-coefficient-datum).

The index n : ℕ denotes the positive exponent n+1. Every quotient reduction retains
its own coefficient action; tower levels restrict that action along the limit projection.
No constant/completed coefficient comparison is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.AdicCoefficients

private theorem ringHasWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) RingCat.{u + 1} := inferInstance

private theorem commRingHasWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) CommRingCat.{u + 1} := inferInstance

open scoped ChangeOfRings MonoidalCategory TensorProduct

/-- The recorded pure tensor in scalar extension, using the existing normalized witness.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev tensorSection (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R))
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((completedAdicChange T φ).obj M).val.obj U :=
  completedAdicChangeTensor T φ M U s m

/-- The commutative-ring presentation of the recorded continuous-function coefficient
presheaf; its objects and restrictions are exactly `finiteCoefficientPresheaf`.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def functionPresheaf (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    T.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  { obj := fun U ↦ CommRingCat.of C(ConnectedComponents U.unop.left, Λ)
    map := fun f ↦ CommRingCat.ofHom ((ProEtale.finiteCoefficientPresheaf T Λ).map f).hom
    map_id := fun U ↦ by
      ext s c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      rfl
    map_comp := fun f g ↦ by
      ext s c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      rfl }

/-- The actual coefficient sheaf, sheafifying those continuous functions.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def coefficientRing (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj (functionPresheaf T Λ)

/-- Postcomposition with a map of finite discrete commutative rings.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def functionPresheafMap (T : Scheme.{u}) {Λ Λ' : Type (u + 1)}
    [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (φ : Λ →+* Λ') :
    functionPresheaf T Λ ⟶ functionPresheaf T Λ' :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  letI : TopologicalSpace Λ' := ⊥
  letI : DiscreteTopology Λ' := ⟨rfl⟩
  { app := fun U ↦ CommRingCat.ofHom
      { toFun := fun s ↦ (⟨φ, continuous_of_discreteTopology⟩ : C(Λ, Λ')).comp s
        map_one' := by ext c; exact φ.map_one
        map_mul' := fun s t ↦ by ext c; exact φ.map_mul _ _
        map_zero' := by ext c; exact φ.map_zero
        map_add' := fun s t ↦ by ext c; exact φ.map_add _ _ }
    naturality := fun _ _ f ↦ by ext s; rfl }

/-- The quotient homomorphism on coefficient sheaves is the sheafified postcomposition map.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def coefficientMap (T : Scheme.{u}) {Λ Λ' : Type (u + 1)}
    [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (φ : Λ →+* Λ') :
    coefficientRing T Λ ⟶ coefficientRing T Λ' :=
  (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (functionPresheafMap T φ)

/-- The strict inverse system of the actual finite quotient coefficient sheaves.
Source: blueprint coefficient convention, Tag 09BT
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
def ringSystem (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  letI := hf
  Functor.ofOpSequence (X := fun n ↦ coefficientRing T (A ⧸ I ^ (n + 1)))
    (fun n ↦ coefficientMap T (Ideal.Quotient.factorPowSucc I (n + 1)))

/-- Completed coefficients are the actual inverse limit of the function coefficient sheaves,
with compatible-family sections. Source: blueprint, Tag 09BT
(blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev completedRing (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :=
  limit (ringSystem T I hf)

/-- The constants-to-functions morphism on presheaves, with its constant value formula.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def constants (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ) ⟶ functionPresheaf T Λ :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  { app := fun U ↦ CommRingCat.ofHom
      { toFun := fun x ↦ ContinuousMap.const _ x
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    naturality := fun _ _ f ↦ by ext x; rfl }

/-- The canonical comparison from constant sheafification to function sheafification.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def constantComparison (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    adicLisseConstantRing T Λ ⟶ coefficientRing T Λ :=
  (presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (constants T Λ)

/-- The RingCat presentation is precisely the dependency's recorded finite coefficient sheaf.
Source: blueprint coefficient convention (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def finiteRingPresentation (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : Sheaf (ProEt.topology T) RingCat.{u + 1} :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  ProEtale.finiteCoefficientRingSheaf T Λ

/-- The recorded presheaf's map into its RingCat sheafification.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def finiteRingUnit (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    functionPresheaf T Λ ⋙ forget₂ CommRingCat RingCat ⟶ (finiteRingPresentation T Λ).obj :=
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  toSheafify (ProEt.topology T) (ProEtale.finiteCoefficientPresheaf T Λ)

/-- Forgetting the commutative presentation gives the recorded coefficient sheaf, with the
comparison uniquely fixed by the sheafification units.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: a ring-valued sheaf receiving the continuous-function presheaf receives a unique
map from its sheafification. Commutativity holds locally on generating sections, hence
globally, so forgetting commutativity preserves this reflection. Both reflection units
therefore factor through each other uniquely, giving inverse maps with the stated equation. -/
theorem finiteRingComparison_exists (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    ∃! f : (adicLisseForget T).obj (coefficientRing T Λ) ⟶ finiteRingPresentation T Λ,
      IsIso f ∧
        Functor.whiskerRight (toSheafify (ProEt.topology T) (functionPresheaf T Λ))
          (forget₂ CommRingCat RingCat) ≫ f.hom = finiteRingUnit T Λ := by
  let J := ProEt.topology T
  let : HasWeakSheafify J RingCat.{u + 1} :=
    AdicCoefficients.ringHasWeakSheafify T
  let : HasWeakSheafify J CommRingCat.{u + 1} :=
    AdicCoefficients.commRingHasWeakSheafify T
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let P := functionPresheaf T Λ
  let η := Functor.whiskerRight (toSheafify J P) F
  have hηi : Presheaf.IsLocallyInjective J η :=
    (Presheaf.isLocallyInjective_forget_iff J η).1
      (inferInstanceAs (Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J P) (CategoryTheory.forget CommRingCat.{u + 1}))))
  have hηs : Presheaf.IsLocallySurjective J η :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J η).2
      (inferInstanceAs (Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J P) (CategoryTheory.forget CommRingCat.{u + 1}))))
  let g : finiteRingPresentation T Λ ⟶ (adicLisseForget T).obj (coefficientRing T Λ) :=
    (sheafComposeNatTrans J F (sheafificationAdjunction J CommRingCat.{u + 1})
      (sheafificationAdjunction J RingCat.{u + 1})).app P
  have hg : toSheafify J (P ⋙ F) ≫ g.hom = η :=
    sheafComposeNatTrans_fac J F (sheafificationAdjunction J CommRingCat.{u + 1})
      (sheafificationAdjunction J RingCat.{u + 1}) P
  have : Presheaf.IsLocallyInjective J (toSheafify J (P ⋙ F) ≫ g.hom) :=
    hg.symm ▸ hηi
  have : Presheaf.IsLocallySurjective J (toSheafify J (P ⋙ F) ≫ g.hom) :=
    hg.symm ▸ hηs
  have : Sheaf.IsLocallyInjective g :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
      J (toSheafify J (P ⋙ F)) g.hom
  have : Sheaf.IsLocallySurjective g :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J (toSheafify J (P ⋙ F)) g.hom
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).1 ⟨inferInstance, inferInstance⟩
  have he : η ≫ (inv g).hom = finiteRingUnit T Λ := by
    rw [← hg, Category.assoc]
    change toSheafify J (P ⋙ F) ≫ (g ≫ inv g).hom = _
    rw [IsIso.hom_inv_id]
    exact Category.comp_id _
  refine ⟨inv g, ⟨inferInstance, he⟩, ?_⟩
  intro f hf
  apply (cancel_epi g).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (finiteRingPresentation T Λ).property
  change toSheafify J (P ⋙ F) ≫ (g.hom ≫ f.hom) =
    toSheafify J (P ⋙ F) ≫ (g.hom ≫ (inv g).hom)
  calc
    _ = η ≫ f.hom := (Category.assoc _ _ _).symm.trans
      (congrArg (fun k ↦ k ≫ f.hom) hg)
    _ = finiteRingUnit T Λ := hf.2
    _ = η ≫ (inv g).hom := he.symm
    _ = _ := (congrArg (fun k ↦ k ≫ (inv g).hom) hg).symm.trans
      (Category.assoc _ _ _)

/-- Canonical identification with the existing RingCat coefficient sheaf, retaining its unit.
Source: blueprint, Tag 09BT (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def finiteRingComparison (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    (adicLisseForget T).obj (coefficientRing T Λ) ≅ finiteRingPresentation T Λ :=
  letI := (finiteRingComparison_exists T Λ).choose_spec.1.1
  asIso (finiteRingComparison_exists T Λ).choose

end AlgebraicGeometry.Scheme.AdicCoefficients

namespace AlgebraicGeometry.Scheme

/-- The quotient map between arbitrary positive powers, not just consecutive powers.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionQuotientMap {A : Type (t + 1)} [CommRing A] (I : Ideal A)
    (b a : ℕ) (h : a ≤ b) : A ⧸ I ^ (b + 1) →+* A ⧸ I ^ (a + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The quotient coefficient sheaf, obtained from continuous component functions.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionCoefficient (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  (AdicCoefficients.ringSystem T d.ideal d.quotientFinite).obj (op n)

/-- The strict diagram of all positive quotient coefficient sheaves.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionCoefficientSystem (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  AdicCoefficients.ringSystem T d.ideal d.quotientFinite

/-- The actual inverse limit sheaf of commutative rings. Limits of sheaves are computed
on sections, so its sections are compatible families with pointwise operations.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionCoefficient (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : Sheaf (ProEt.topology T) CommRingCat.{t + 1} :=
  limit (reductionCoefficientSystem T d)

/-- The n-th coordinate of the limit of quotient coefficient sheaves.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def completedReductionProjection (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    completedReductionCoefficient T d ⟶ reductionCoefficient T d n :=
  limit.π (reductionCoefficientSystem T d) (op n)

/-- The ring underlying a commutative coefficient sheaf on the small pro-etale site.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionModuleRing (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

/-- Left module sheaves over a given coefficient ring; this is the recorded category.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionModules (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  ringedSiteModules.{t + 1} (reductionModuleRing T R)

/-- The standard localization for these module sheaves, keeping site sizes t+1 and t.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionModulesHasDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    HasDerivedCategory (reductionModules T R) := HasDerivedCategory.standard _

/-- D(Mod(R)) with its canonical cochain localization.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev reductionDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  DerivedCategory (reductionModules T R)

/-- Standard localization for modules over any coefficient ring sheaf B.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionRingModulesHasDerivedCategory (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) RingCat.{t + 1}) :
    HasDerivedCategory (ringedSiteModules.{t + 1} B) := HasDerivedCategory.standard _

/-- The existing scalar-extension specification, named without changing its predicate.
The extractor uses the type of the existence proof and ignores that proof.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def reductionChangeSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionModules T R ⥤ reductionModules T S) → Prop :=
  (fun {B : Type (t + 2)} {P : B → Prop} (_ : ∃ x, P x) ↦ P)
    (completedAdicChangeData T φ)

/-- Specialize the recorded derived-change-of-rings theorem with standard localizations.
Its ordinary functor is fixed on objects and maps, and its derived pair is universal.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
theorem reductionChangeExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ E, reductionChangeSpec T φ E := completedAdicChangeData T φ

/-- Ordinary scalar extension, fixed by sheafified sectionwise tensor on objects and maps.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionModules T R ⥤ reductionModules T S := completedAdicChange T φ

/-- The additive structure supplied by the canonical scalar-extension witness.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable instance reductionChangeAdditive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionChange T φ).Additive :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose

/-- The universal derived scalar-extension specification for a fixed functor.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def reductionDerivedSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (LF : reductionDerivedCategory T R ⥤ reductionDerivedCategory T S) : Prop :=
    ∃ (ε : DerivedCategory.Qh ⋙ LF ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (reductionModules T R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (reductionModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The universal derived scalar-extension pair, including its K-flat counit isomorphisms.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: specialize derivedChangeOfRingsIndependentCoefficients to the small pro-etale
site and the two specified coefficient sheaves. Select its ordinary tensor functor,
with the fixed object and map formulas, exactly as in reductionChange. Its additive
instance is reductionChangeAdditive. The final existence clause of that theorem
supplies the universal derived pair, shift compatibility and K-flat counit computation. -/
theorem reductionDerivedExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ LF, reductionDerivedSpec T φ LF :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived scalar extension is chosen with its universal comparison, hence is determined
up to unique compatible isomorphism, rather than by a mere existence of a functor.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    reductionDerivedCategory T R ⥤ reductionDerivedCategory T S :=
  completedAdicDerivedChange T φ

/-- The universal counit comparing the derived functor with ordinary tensor on homotopy.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionDerivedCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    DerivedCategory.Qh ⋙ reductionDerivedChange T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (reductionDerivedExistence T φ).choose_spec.choose

attribute [local instance] reductionModulesHasDerivedCategory

/-- The sheafified pure tensor, including the object's canonical equality transport.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionTensorSection (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((reductionChange T φ).obj M).val.obj U :=
  completedAdicChangeTensor T φ M U s x

/-- Restrict the coefficient action without changing the underlying abelian sheaf.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable def reductionRestrict (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
@[instance]
theorem reductionRestrict_preservesFiniteLimits (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteLimits (reductionRestrict T φ) := by
  let F := SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T R)
  have : PreservesFiniteLimits (reductionRestrict T φ ⋙ F) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T S)))
  exact preservesFiniteLimits_of_reflects_of_preserves (reductionRestrict T φ) F
@[instance]
theorem reductionRestrict_preservesFiniteColimits (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteColimits (reductionRestrict T φ) := by
  let F := SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T R)
  have : PreservesFiniteColimits (reductionRestrict T φ ⋙ F) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{t + 1} (reductionModuleRing T S)))
  exact preservesFiniteColimits_of_reflects_of_preserves (reductionRestrict T φ) F

/-- Scalar restriction is additive on the unchanged underlying abelian sheaf.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance reductionRestrict_additive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (reductionRestrict T φ).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).Additive

private theorem reductionChange_obj_eq (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : reductionModules T R) :
    (reductionChange T φ).obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M :=
  (reductionChangeExistence T φ).choose_spec.choose M

private theorem reductionChange_map_eq (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : reductionModules T R} (f : M ⟶ N) :
    (reductionChange T φ).map f = eqToHom (reductionChange_obj_eq T φ M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (reductionChange_obj_eq T φ N).symm :=
  (reductionChangeExistence T φ).choose_spec.choose_spec.choose f

attribute [local irreducible] reductionChange reductionDerivedChange

private theorem ordinaryAdjunction_exists (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    ∃ a : reductionChange X φ ⊣ reductionRestrict X φ,
      ∀ (M : reductionModules X R) (N : reductionModules X S)
        (f : (reductionChange X φ).obj M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        HEq ((a.homEquiv M N f).val.app U x)
          (f.val.app U (reductionTensorSection X φ M U 1 x)) := by
  let h := reductionChange_obj_eq X φ
  obtain ⟨_, _, ho⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (J := ProEt.topology X) φ
  obtain ⟨a, ha⟩ := ho (reductionChange X φ) h (reductionChange_map_eq X φ)
  refine ⟨a, ?_⟩
  intro M N f U x
  have hh := ha M N (eqToHom (h M).symm ≫ f) U x
  have hi : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hi] at hh
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  with_unfolding_all exact heq_of_eq hh

private def reductionUnit (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) :
    M ⟶ (reductionRestrict X φ).obj ((reductionChange X φ).obj M) := by
  have h := (ordinaryAdjunction_exists X φ).choose.unit.app M
  exact h

private theorem reductionUnit_apply (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (reductionUnit X φ M).val.app U x = reductionTensorSection X φ M U 1 x := by
  have hh := (ordinaryAdjunction_exists X φ).choose_spec M
    ((reductionChange X φ).obj M) (𝟙 _) U x
  let adj := (ordinaryAdjunction_exists X φ).choose
  have hi : adj.homEquiv M ((reductionChange X φ).obj M) (𝟙 _) = adj.unit.app M := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hv := congrArg (fun f : M ⟶ (reductionRestrict X φ).obj
    ((reductionChange X φ).obj M) ↦ f.val.app U x) hi
  exact hv.symm.trans (eq_of_heq hh)

universe uB vB wB uD vD wD

attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionCoefficient
attribute [local irreducible] reductionCoefficientSystem AdicCoefficients.ringSystem

end AlgebraicGeometry.Scheme

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
namespace AlgebraicGeometry.Scheme

attribute [local instance] reductionModulesHasDerivedCategory

attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionCoefficient
attribute [local irreducible] reductionCoefficientSystem AdicCoefficients.ringSystem

universe v w u' v' w'
open CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

/-- The quotient ring tower, indexed by the positive exponent n+1.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.ringTower {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :=
  Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (reductionQuotientMap d.ideal (n + 1) n (Nat.le_succ n)))

/-- The finite quotient ring sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.finiteRing {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) (n : ℕ) := reductionCoefficient T d n

/-- The actual completed coefficient ring sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.completedRing {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) := completedReductionCoefficient T d

/-- The specified coordinate of the completed coefficient sheaf.
Source: blueprint adic coefficient datum (blueprint: def-weil-pbc-adic-coefficient-datum). -/
noncomputable abbrev AdicCoefficientDatum.projection {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (T : Scheme.{t}) (n : ℕ) :=
  completedReductionProjection T d n

/-- Every finite quotient has exactly the finiteness certificate of the arithmetic datum.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance AdicCoefficientDatum.positiveQuotient_finite {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : Finite (A ⧸ d.ideal ^ (n + 1)) :=
  d.quotientFinite n

end AlgebraicGeometry.Scheme
