/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete

/-!
# Bounded constructible derived-complete objects

Source: blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The coefficient ring is the actual inverse limit. The three defining conditions
are properties; no origin, local model, or completion representative is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The actual completed-coefficient ambient category. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcCompletedDerived := DerivedCategory (pbcModules T (pbcAdicCompletion T d))

/-- Derived extension along the actual limit projection. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcCompletedReduction (n : ℕ) := pbcDerivedExtend (pbcAdicProjection T d n)

/-- Constants mapped to the continuous-function coefficient presentation.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionScalars (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (PbcQuotient d n)) ⟶
      ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n))).obj :=
  finiteCoefficientScalarMap T (PbcQuotient d n) ≫
    (AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).inv.hom

/-- The coefficient-presentation transport preserves local bijectivity of constants.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: finiteCoefficientScalarMap is locally bijective. The second factor is a ring
sheaf isomorphism, so composing it preserves local injectivity and local surjectivity. -/
theorem pbcFunctionScalars_locallyBijective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n) := by
  dsimp only [pbcFunctionScalars]
  constructor <;> infer_instance

/-- Local injectivity of the specified coefficient presentation. Source: blueprint
order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionScalars_injective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) :=
  (pbcFunctionScalars_locallyBijective T d n).1

/-- Local surjectivity of the specified coefficient presentation. Source: blueprint
order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionScalars_surjective (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n) :=
  (pbcFunctionScalars_locallyBijective T d n).2

/-- Associated modules for any locally bijective coefficient presentation.
Keeping the presentation abstract avoids expanding the quotient limit during
normalization. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedModule (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α] :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P) ⥤ ringedSiteModules.{u + 1} R :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt P ⋙
    PresheafOfModules.sheafification α

/-- The underlying additive sheafification of a fixed-coefficient module sheaf.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedAdditive (P : Type (u + 1)) [CommRing P] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} P) ⋙
    finiteCoefficientModulePresheaf T.ProEt P ⋙
    PresheafOfModules.toPresheaf ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of P)) ⋙
    presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}

/-- The source restriction comparison forgets to exactly the ordinary additive
sheafification. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedRestrictionSource (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α] (q : P →+* Q) :
    (Sheaf.restrictScalars (ProEt.topology T) q ⋙ pbcAssociatedModule T P R α) ⋙
        SheafOfModules.toSheaf R ≅ pbcAssociatedAdditive T Q :=
  Iso.refl _

/-- The target restriction comparison forgets to the same additive sheafification.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedRestrictionTarget (Q : Type (u + 1)) [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (β : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) β]
    [Presheaf.IsLocallySurjective (ProEt.topology T) β] (r : R ⟶ S) :
    (pbcAssociatedModule T Q S β ⋙ SheafOfModules.restrictScalars r) ⋙
        SheafOfModules.toSheaf R ≅ pbcAssociatedAdditive T Q :=
  Iso.refl _

/-- Identity on the underlying additive sheafification uniquely normalizes the
restriction comparison for compatible scalar presentations.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: the scalar-square equality identifies the two restricted actions locally on
coefficient generators and hence everywhere. Identity on the underlying additive
sheafification is therefore linear and natural. Its inverse is the same identity;
faithfulness of the additive forgetful functor gives uniqueness. -/
theorem pbcAssociatedRestriction_exists
    (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (β : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α]
    [Presheaf.IsLocallyInjective (ProEt.topology T) β]
    [Presheaf.IsLocallySurjective (ProEt.topology T) β]
    (q : P →+* Q) (r : R ⟶ S)
    (_h : α ≫ r.hom = (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom q) ≫ β) :
    ∃! e : Sheaf.restrictScalars (ProEt.topology T) q ⋙ pbcAssociatedModule T P R α ≅
        pbcAssociatedModule T Q S β ⋙ SheafOfModules.restrictScalars r,
      Functor.whiskerRight e.hom (SheafOfModules.toSheaf R) =
        (pbcAssociatedRestrictionSource T P Q R α q).hom ≫
          (pbcAssociatedRestrictionTarget T Q R S β r).inv := by
  let δ := (pbcAssociatedRestrictionSource T P Q R α q).hom ≫
    (pbcAssociatedRestrictionTarget T Q R S β r).inv
  have hMap (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q)) :
      ∃ f : (pbcAssociatedModule T P R α).obj
          ((Sheaf.restrictScalars (ProEt.topology T) q).obj N) ⟶
        (SheafOfModules.restrictScalars r).obj ((pbcAssociatedModule T Q S β).obj N),
        (SheafOfModules.toSheaf R).map f = δ.app N := by
    let M₀ := (finiteCoefficientModulePresheaf T.ProEt Q).obj N.obj
    let M₁ := (finiteCoefficientModulePresheaf T.ProEt P).obj
      ((Sheaf.restrictScalars (ProEt.topology T) q).obj N).obj
    let φ := toSheafify (ProEt.topology T) M₀.presheaf
    let G := (SheafOfModules.restrictScalars r).obj
      ((pbcAssociatedModule T Q S β).obj N)
    let v : M₁ ⟶ (PresheafOfModules.restrictScalars α).obj G.val :=
      PresheafOfModules.homMk φ (fun X a m ↦ by
        change φ.app X (q a • (show M₀.obj X from m)) =
          (r.hom.app X (α.app X a)) •
            (show ((PresheafOfModules.sheafification β).obj M₀).val.obj X from φ.app X m)
        have hscalar : r.hom.app X (α.app X a) = β.app X (q a) :=
          ConcreteCategory.congr_hom (congr_app _h X) a
        rw [hscalar]
        exact ((PresheafOfModules.toSheafify β φ).app X).hom.map_smul (q a) m)
    let f := (PresheafOfModules.sheafificationHomEquiv α (P := M₁) (F := G)).symm v
    refine ⟨f, ?_⟩
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology T) _ _
      ((SheafOfModules.toSheaf R).obj G).property
    change φ ≫ (PresheafOfModules.toPresheaf R.obj).map f.val = φ ≫ 𝟙 _
    rw [Category.comp_id]
    have hf := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def α f
    rw [Equiv.apply_symm_apply] at hf
    exact hf.symm
  choose f hf using hMap
  let η : Sheaf.restrictScalars (ProEt.topology T) q ⋙ pbcAssociatedModule T P R α ⟶
      pbcAssociatedModule T Q S β ⋙ SheafOfModules.restrictScalars r :=
    { app := f
      naturality := by
        intro N N' g
        apply (SheafOfModules.toSheaf R).map_injective
        rw [Functor.map_comp, Functor.map_comp, hf, hf]
        exact δ.naturality g }
  have hη (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Q)) : IsIso (η.app N) := by
    have : IsIso ((SheafOfModules.toSheaf R).map (η.app N)) := by
      change IsIso ((SheafOfModules.toSheaf R).map (f N))
      rw [hf]
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  have : IsIso η := NatIso.isIso_of_isIso_app η
  refine ⟨asIso η, ?_, ?_⟩
  · apply NatTrans.ext
    funext N
    exact hf N
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (SheafOfModules.toSheaf R).map_injective
    have hn := congr_app he N
    exact hn.trans (hf N).symm

/-- Canonical associated-module-sheaf realization, with the coefficient presentation
changed along the recorded isomorphism. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcFunctionRealization (n : ℕ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (PbcQuotient d n)) ⥤
      pbcModules T ((pbcAdicRings T d).obj (op n)) :=
  pbcAssociatedModule T (PbcQuotient d n)
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
    (pbcFunctionScalars T d n)

/-- Realization is the canonical exact additive equivalence, including for zero rings.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: finiteRingComparison is fixed by the coefficient sheafification units.
Its composite with the constants map is locally bijective. Associated module
sheafification therefore has invertible unit and counit on module sheaves.
They identify the underlying sheaves and scalar actions. The equivalence is additive
sectionwise and hence preserves finite limits and colimits. -/
theorem pbcFunctionRealization_exact (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence ∧
      (pbcFunctionRealization T d n).Additive ∧
      PreservesFiniteLimits (pbcFunctionRealization T d n) ∧
      PreservesFiniteColimits (pbcFunctionRealization T d n) := by
  have : (pbcFunctionRealization T d n).IsEquivalence :=
    coefficientRealization_isEquivalence (ProEt.topology T) (PbcQuotient d n)
      ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
      (pbcFunctionScalars T d n)
  exact ⟨this, Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The canonical realization equivalence. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_equivalence (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence :=
  (pbcFunctionRealization_exact T d n).1

/-- Exact realization, additive part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_additive (n : ℕ) :
    (pbcFunctionRealization T d n).Additive :=
  (pbcFunctionRealization_exact T d n).2.1

/-- Exact realization, left exact part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_limits (n : ℕ) :
    PreservesFiniteLimits (pbcFunctionRealization T d n) :=
  (pbcFunctionRealization_exact T d n).2.2.1

/-- Exact realization, right exact part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_colimits (n : ℕ) :
    PreservesFiniteColimits (pbcFunctionRealization T d n) :=
  (pbcFunctionRealization_exact T d n).2.2.2

/-- Realization on derived categories. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcDerivedFunctionRealization (n : ℕ) :=
  (pbcFunctionRealization T d n).mapDerivedCategory

/-- The exact coefficient-presentation equivalence descends to an equivalence.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: apply the ordinary inverse equivalence termwise to cochain complexes.
Exactness preserves quasi-isomorphisms on both sides. Localize both functors and
the unit and counit, which remain isomorphisms and satisfy the triangle identities. -/
@[instance] theorem pbcDerivedFunctionRealization_equivalence (n : ℕ) :
    (pbcDerivedFunctionRealization T d n).IsEquivalence := by
  infer_instance

private theorem functionScalars_eq (n : ℕ) :
    pbcFunctionScalars T d n =
      Functor.whiskerRight
        (AdicCoefficients.constants T (PbcQuotient d n) ≫
          toSheafify (ProEt.topology T)
            (AdicCoefficients.functionPresheaf T (PbcQuotient d n)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e := AdicCoefficients.finiteRingComparison T (PbcQuotient d n)
  have he :
      Functor.whiskerRight (toSheafify (ProEt.topology T)
        (AdicCoefficients.functionPresheaf T (PbcQuotient d n)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫ e.hom.hom =
      AdicCoefficients.finiteRingUnit T (PbcQuotient d n) :=
    (AdicCoefficients.finiteRingComparison_exists T (PbcQuotient d n)).choose_spec.1.2
  apply (cancel_mono e.hom.hom).1
  have hi : e.inv.hom ≫ e.hom.hom = 𝟙 _ := congrArg
    (fun f : AdicCoefficients.finiteRingPresentation T (PbcQuotient d n) ⟶
      AdicCoefficients.finiteRingPresentation T (PbcQuotient d n) ↦ f.hom) e.inv_hom_id
  change (finiteCoefficientScalarMap T (PbcQuotient d n) ≫ e.inv.hom) ≫ e.hom.hom = _
  rw [Category.assoc, hi]
  erw [Category.comp_id]
  rw [Functor.whiskerRight_comp, Category.assoc, he]
  rfl

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The scalar-presentation square is the canonical quotient square.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: all four maps send a constant residue class to its lower residue class.
The finiteRingComparison maps are fixed by the sheafification units, so equality on
these generators proves equality of their sheafified maps. -/
theorem pbcFunctionScalars_comp (n : ℕ) :
    pbcFunctionScalars T d (n + 1) ≫
        ((adicLisseForget T).map
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).hom =
      (Functor.const T.ProEtᵒᵖ).map
        (RingCat.ofHom (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))) ≫
          pbcFunctionScalars T d n := by
  rw [functionScalars_eq, functionScalars_eq]
  let q := pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)
  have hmap : pbcAdicQuotient T d (n + 1) n (Nat.le_succ n) =
      AdicCoefficients.coefficientMap T q := by
    simp only [pbcAdicQuotient, pbcAdicRings, AdicCoefficients.ringSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    congr 1
  rw [hmap]
  change Functor.whiskerRight _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
      Functor.whiskerRight
        (((presheafToSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (AdicCoefficients.functionPresheafMap T q)).hom)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
    Functor.whiskerRight ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom q))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
    Functor.whiskerRight _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp]
  have hc : AdicCoefficients.constants T (PbcQuotient d (n + 1)) ≫
        AdicCoefficients.functionPresheafMap T q =
      (Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom q) ≫
        AdicCoefficients.constants T (PbcQuotient d n) := by
    ext U x
    rfl
  have hn := toSheafify_naturality (ProEt.topology T)
    (AdicCoefficients.functionPresheafMap T q)
  apply congrArg (fun f ↦ Functor.whiskerRight f
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  rw [Category.assoc, ← hn, ← Category.assoc, hc, Category.assoc]

/-- The normalized ordinary scalar-restriction comparison. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionRestriction (n : ℕ) :
    Sheaf.restrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)) ⋙
        pbcFunctionRealization T d (n + 1) ≅
      pbcFunctionRealization T d n ⋙
        pbcRestrict (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) :=
  (pbcAssociatedRestriction_exists T (PbcQuotient d (n + 1)) (PbcQuotient d n)
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op (n + 1))))
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
    (pbcFunctionScalars T d (n + 1)) (pbcFunctionScalars T d n)
    (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))
    ((adicLisseForget T).map (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)))
    (pbcFunctionScalars_comp T d n)).exists.choose

/-- Its exact derived descent. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcDerivedFunctionRestriction (n : ℕ) :
    Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)) ⋙
      pbcDerivedFunctionRealization T d (n + 1) ≅
    pbcDerivedFunctionRealization T d n ⋙
      pbcDerivedRestrict (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (pbcFunctionRestriction T d n) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The tensor comparison is the mate of the section-normalized restriction comparison.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionReductionMap (n : ℕ) :
    pbcDerivedFunctionRealization T d (n + 1) ⋙
        pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) ⟶
      pbcWitnessReduction T d n ⋙ pbcDerivedFunctionRealization T d n :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))))
    (pbcDerivedScalarAdjunction
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)))).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedFunctionRestriction T d n).hom))

/-- Mates across equivalences preserve invertibility, by conjugating the two
adjunctions with the inverse equivalences. -/
private theorem inverseMate_equivalences
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}
    (a : L ⊣ R) (b : L' ⊣ R') [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R H G R') [IsIso β] :
    IsIso ((mateEquiv a b).symm β) := by
  let eG := G.asEquivalence.toAdjunction
  let eH := H.asEquivalence.toAdjunction
  let α := (mateEquiv a b).symm β
  have hi : IsIso (mateEquiv eH eG β) := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have he := iterated_mateEquiv_conjugateEquiv a b eG eH α
  change (mateEquiv eH eG ((mateEquiv a b) ((mateEquiv a b).symm β))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  have : IsIso (conjugateEquiv (a.comp eH) (eG.comp b) α) := he ▸ hi
  exact conjugateEquiv_of_iso (a.comp eH) (eG.comp b) α

/-- The canonical tensor mate is invertible. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: use flat-term K-flat representatives. Realization is an exact coefficient
presentation equivalence and preserves K-flatness. The mate is ordinary balancing on
these representatives, because the restriction comparison is the identity on local
generators. Its inverse is the reverse balancing map. Localization proves the claim. -/
theorem pbcFunctionReductionMap_isIso (n : ℕ) : IsIso (pbcFunctionReductionMap T d n) := by
  exact inverseMate_equivalences _ _
    (TwoSquare.mk _ _ _ _ (pbcDerivedFunctionRestriction T d n).hom)

/-- Canonical coefficient-reduction comparison. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionReduction (n : ℕ) :
    pbcDerivedFunctionRealization T d (n + 1) ⋙
        pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) ≅
      pbcWitnessReduction T d n ⋙ pbcDerivedFunctionRealization T d n :=
  letI := pbcFunctionReductionMap_isIso T d n
  asIso (pbcFunctionReductionMap T d n)

/-- Intrinsic completeness transported along the normalized completed-ring comparison.
The generator tuple and complex representative are existential proof witnesses only.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcIsIntrinsicallyComplete (K : PbcCompletedDerived T d) : Prop :=
  ∃ (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (C : CochainComplex (adicDatumModules T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }) ℤ)
    (e : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison T d).inv).obj K),
    IsCompletedIntrinsicallyDerivedComplete T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } r f hf C e

/-- The canonical reduction tower has the recorded common local bounded models.
The equations identify its transitions, not merely its individual levels.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcHasUniformConstructibleReductions (K : PbcCompletedDerived T d) : Prop :=
  ∃ (M : AdicTower T d)
    (e : ∀ n : ℕ, M.level n ≅ (pbcCompletedReduction T d n).obj K),
    IsUniformlyBoundedConstructibleAdicTower d M ∧
    ∀ (b a : ℕ) (hab : a ≤ b),
      adicTowerSemilinearTransition T d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (e a).hom =
        (e b).hom ≫ pbcReductionTransition (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) K

/-- Existence of compatible bounded-below étale origins, with precisely the canonical
normalization. Adjacent equations give all quotient cocycles, including identities,
by the iterated-composite convention of PbcWitnessedTower.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcHasCompatibleEtaleOrigins (K : PbcCompletedDerived T d) : Prop :=
  ∃ (P : PbcWitnessedTower T d)
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (P.K n) ≅
      (pbcCompletedReduction T d n).obj K),
    ∀ n : ℕ,
      (pbcDerivedFunctionRealization T d n).map (P.theta n).hom ≫ (e n).hom =
        (pbcFunctionReduction T d n).inv.app (P.K (n + 1)) ≫
          (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).map
            (e (n + 1)).hom ≫
          (pbcReductionNormalization (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K).hom

/-- The three conditions defining the integral constructible category.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcIsBoundedConstructibleComplete (K : PbcCompletedDerived T d) : Prop :=
  PbcIsIntrinsicallyComplete T d K ∧ PbcHasUniformConstructibleReductions T d K ∧
    PbcHasCompatibleEtaleOrigins T d K

/-- The full subcategory; the defining witnesses are not part of its objects' data.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcBoundedConstructibleComplete :=
  ObjectProperty.FullSubcategory (PbcIsBoundedConstructibleComplete T d)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The integral full subcategory for the finite-extension coefficients and the base
hypotheses in the source. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcIntegralCategory (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :=
  PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)

end AlgebraicGeometry.Scheme
