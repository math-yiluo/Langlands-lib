/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement

/-!
# Transport of the intrinsic completion

The Koszul fiber is reused through the canonical comparison between
its completed quotient-ring presentation and the continuous-functions presentation.
Both rings are inverse limits of the finite quotient sheaves. Neither is identified
with the constant sheaf associated to A. The transport preserves the prescribed
fiber differential, positive-power transitions and the completion unit (u,0).

## References

* Stacks Tags 099M and 091Z
* Stacks Tag 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The same arithmetic datum in the completion interface. -/
def intrinsicPresentationDatum {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ProEtaleAdicCoefficientDatum A where
  toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
  quotientFinite := d.quotientFinite

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Exact restriction to the completed-ring presentation. -/
abbrev intrinsicPresentationModules : pbcModules T (pbcAdicCompletion T d) ⥤
    adicDatumModules T (intrinsicPresentationDatum d) :=
  pbcRestrict (pbcCompletedComparison T d).hom

/-- Exact restriction back through the inverse of the canonical ring comparison. -/
abbrev intrinsicPresentationModulesBack : adicDatumModules T (intrinsicPresentationDatum d) ⥤
    pbcModules T (pbcAdicCompletion T d) :=
  pbcRestrict (pbcCompletedComparison T d).inv

set_option backward.isDefEq.respectTransparency false in
/-- The round trip is uniquely fixed by identity on underlying sections. -/
theorem intrinsicPresentationRoundTrip_exists :
    ∃! e : 𝟭 (pbcModules T (pbcAdicCompletion T d)) ≅
        intrinsicPresentationModules T d ⋙ intrinsicPresentationModulesBack T d,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (pbcAdicCompletion T d)
  let φ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (pbcCompletedComparison T d).inv
  let ψ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (pbcCompletedComparison T d).hom
  have hU (U : T.ProEtᵒᵖ) : (ψ.hom.app U).hom.comp (φ.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg (fun k ↦ (k.hom.app U).hom) (pbcCompletedComparison T d).inv_hom_id
  let eM (M : pbcModules T (pbcAdicCompletion T d)) :
      (intrinsicPresentationModulesBack T d).obj
        ((intrinsicPresentationModules T d).obj M) ≅ M :=
    (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (φ.hom.app U).hom (ψ.hom.app U).hom
          (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
            (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  let e : 𝟭 (pbcModules T (pbcAdicCompletion T d)) ≅
      intrinsicPresentationModules T d ⋙ intrinsicPresentationModulesBack T d :=
    NatIso.ofComponents (fun M ↦ (eM M).symm) (fun f ↦ by ext U x; rfl)
  refine ⟨e, fun M U x ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext M U x
  exact he' M U x

/-- The actual identity-on-sections coefficient round trip. -/
def intrinsicPresentationRoundTrip : 𝟭 (pbcModules T (pbcAdicCompletion T d)) ≅
    intrinsicPresentationModules T d ⋙ intrinsicPresentationModulesBack T d :=
  (intrinsicPresentationRoundTrip_exists T d).exists.choose

/-- Apply the coefficient comparison to a representative, term by term. -/
abbrev intrinsicPresentationComplex :=
  (intrinsicPresentationModules T d).mapHomologicalComplex (.up ℤ)

/-- Return the explicit Koszul fiber to the specified coefficient ring. -/
def intrinsicCompletionComplex (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :=
  ((intrinsicPresentationModulesBack T d).mapHomologicalComplex (.up ℤ)).obj
    (completedKoszulFiber T (intrinsicPresentationDatum d) r a
      ((intrinsicPresentationComplex T d).obj C))

/-- The transported (u,0) completion map in each degree. -/
def intrinsicCompletionUnitComponent (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (q : ℤ) :
    C.X q ⟶ (intrinsicCompletionComplex T d r a C).X q :=
  (intrinsicPresentationRoundTrip T d).hom.app (C.X q) ≫
    (intrinsicPresentationModulesBack T d).map
      ((completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a
        ((intrinsicPresentationComplex T d).obj C)).f q)

set_option backward.isDefEq.respectTransparency false in
/-- The transported completion unit commutes with differentials. -/
theorem intrinsicCompletionUnitComponent_comm (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (q k : ℤ) :
    intrinsicCompletionUnitComponent T d r a C q ≫
        (intrinsicCompletionComplex T d r a C).d q k =
      C.d q k ≫ intrinsicCompletionUnitComponent T d r a C k := by
  let B := intrinsicPresentationModulesBack T d
  let η := intrinsicPresentationRoundTrip T d
  let u := completedKoszulUnitComplex T (intrinsicPresentationDatum d) r a
    ((intrinsicPresentationComplex T d).obj C)
  change (η.hom.app (C.X q) ≫ B.map (u.f q)) ≫ B.map
    ((completedKoszulFiber T (intrinsicPresentationDatum d) r a
      ((intrinsicPresentationComplex T d).obj C)).d q k) =
    C.d q k ≫ η.hom.app (C.X k) ≫ B.map (u.f k)
  rw [Category.assoc, ← B.map_comp, u.comm, B.map_comp]
  have hη := η.hom.naturality (C.d q k)
  dsimp only [Functor.id_map, Functor.comp_map] at hη
  change (η.hom.app (C.X q) ≫ B.map
    ((intrinsicPresentationModules T d).map (C.d q k))) ≫ B.map (u.f k) = _
  rw [← hη, Category.assoc]

/-- The completion chain map, transported with its fixed section normalization. -/
def intrinsicCompletionComplexUnit (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    C ⟶ intrinsicCompletionComplex T d r a C where
  f q := intrinsicCompletionUnitComponent T d r a C q
  comm' q k _ := intrinsicCompletionUnitComponent_comm T d r a C q k

/-- Intrinsic completion uses the explicit Koszul fiber on any representative.
Exact mutually inverse coefficient restrictions preserve its product, differential,
transitions and unit. No representative or unrelated fiber is chosen. -/
def intrinsicCompletion (r : ℕ) (a : Fin r → A)
    (_ha : Ideal.span (Set.range a) = d.ideal)
    (_K : reductionDerivedCategory T (completedReductionCoefficient T d))
    (C : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (_e : DerivedCategory.Q.obj C ≅ _K) :
    reductionDerivedCategory T (completedReductionCoefficient T d) :=
  DerivedCategory.Q.obj (intrinsicCompletionComplex T d r a C)

/-- The transported (u,0) completion unit, with the supplied realization. -/
def intrinsicCompletionUnit (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : reductionDerivedCategory T (completedReductionCoefficient T d))
    (C : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K) : K ⟶ intrinsicCompletion T d r a ha K C e :=
  e.inv ≫ DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)

/-- Derived I-completeness is invertibility of the same transported completion unit. -/
def IsDerivedCompleteIntrinsic (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : reductionDerivedCategory T (completedReductionCoefficient T d))
    (C : CochainComplex (reductionModules T (completedReductionCoefficient T d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K) : Prop :=
  IsIso (intrinsicCompletionUnit T d r a ha K C e)

end AlgebraicGeometry.Scheme
