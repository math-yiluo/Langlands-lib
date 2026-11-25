/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport

/-!
# The canonical open-square exchange in tensor-pullback coordinates

The original exchange uses the transported fixed-scalar inverse image. The Frobenius
comparison uses tensor inverse image over the same intrinsic constant ring. The bridge
below is uniquely fixed by the sectionwise units, and is descended termwise.

## References

* Stacks Tags 03S6, 03D3 and 00YV
* Stacks Tags 03S6 and 04J0
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem openSquare_coefficientMap (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
        proEtaleCoefficientDirectImageMap f A := by
  exact ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
    (proEtaleCoefficientDirectImageMap f A)

private def openSquare_directImageModel (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPushforward A f ≅ proEtaleConstantModuleDirectImage f A :=
  SheafOfModules.pushforwardCongr (by rw [openSquare_coefficientMap A f])

/-- The unique identification of the two pullbacks used in the open-square construction.
Its sectionwise equation preserves their specified units and fixes the scalar action. -/
theorem openSquarePullbackModel_existsUnique (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : proEtaleConstantRingPullback A f ≅ sfIntrinsicPullback A f,
      ∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
        (s : M.val.obj (Opposite.op V)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) s) =
          ((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (Opposite.op V) s := by
  let d := openSquare_directImageModel A f
  let adj₁ := (proEtaleConstantRingAdjunction A f).ofNatIsoRight d
  let adj₂ := sfIntrinsicConstantModuleAdjunction f A
  let e : proEtaleConstantRingPullback A f ≅ sfIntrinsicPullback A f :=
    adj₁.leftAdjointUniq adj₂
  refine ⟨e, ?_, ?_⟩
  · intro M V s
    have h := adj₁.unit_leftAdjointUniq_hom_app adj₂ M
    have hv := congrArg (fun z ↦ z.val.app (Opposite.op V) s) h
    change (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
      (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) s) =
        ((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (Opposite.op V) s
      at hv
    exact hv
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (adj₁.homEquiv M _).injective
    rw [adj₁.homEquiv_leftAdjointUniq_hom_app adj₂]
    rw [Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext s
    change (e'.hom.app M).val.app ((proEtaleBaseChange f).op.obj V)
      (((proEtaleConstantRingAdjunction A f).unit.app M).val.app V s) =
        ((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app V s
    exact he' M V.unop s

/-- The unique unit-preserving ordinary change of pullback coordinates. -/
def openSquarePullbackModel (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ≅ sfIntrinsicPullback A f :=
  (openSquarePullbackModel_existsUnique A f).exists.choose

/-- Exact termwise descent of the unit-preserving coordinate identification. -/
def openSquareDerivedPullbackModel (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingDerivedPullback A f ≅ sfIntrinsicDerivedPullback A f :=
  Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A f)

/-- The same canonical exchange in tensor-pullback coordinates. The middle comparison is
the existing exchange, whose inverse is the specified open-adjunction mate and whose
restriction, identity and pasting laws are recorded in SfOpenSquareExchangeData.
The two outer factors are the unique unit-preserving changes of coordinates; consequently
these normalizations transport with the exchange, including its identity on the open. -/
def constantOpenSquareExchange (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    @sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn) _ _ j _ ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) g ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) gU ⋙
        @sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn) _ _ j' _ := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exact Functor.isoWhiskerLeft (sfIntrinsicDerivedOpen _ j)
      (openSquareDerivedPullbackModel _ g) ≪≫
    (Classical.choice (proEtale_openSquareExchange l E n hn)).exchange gU j' j g sq ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel _ gU).symm
      (sfIntrinsicDerivedOpen _ j')

end AlgebraicGeometry.Scheme
