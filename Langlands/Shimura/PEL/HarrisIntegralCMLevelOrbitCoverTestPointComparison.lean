import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverPointComparison

/-! # Point comparison in the original Harris orbit-cover test equivalence -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open scoped FintypeCatDiscrete

private theorem pathPushforward_testEvaluation
    {X Z : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    (f : X ⟶ Z) (t : Spec (.of Ω) ⟶ X) (u : Spec (.of Ω') ⟶ X)
    (ht : ∀ Y : Cover X, Finite (Fiber t Y))
    (hu : ∀ Y : Cover X, Finite (Fiber u Y))
    (htf : ∀ Y : Cover Z, Finite (Fiber (t ≫ f) Y))
    (huf : ∀ Y : Cover Z, Finite (Fiber (u ≫ f) Y))
    (path : fiberFunctor t ht ≅ fiberFunctor u hu)
    (Y : Cover Z) (k : Over.mk f ⟶ Y.obj) :
    (pathPushforward f htf huf path).hom.app Y
        (Over.homMk (t ≫ k.left) (by change (t ≫ k.left) ≫ Y.obj.hom = t ≫ f; rw [Category.assoc, Over.w k]; rfl)) =
      Over.homMk (u ≫ k.left) (by change (u ≫ k.left) ≫ Y.obj.hom = u ≫ f; rw [Category.assoc, Over.w k]; rfl) := by
  let I : Cover X := cover (𝟙 X)
  let y : Fiber t I := Over.homMk t (by simp [I, cover])
  have hy : (path.hom.app I y).left = u := by
    simpa [I, cover] using Over.w (path.hom.app I y)
  apply Over.OverMorphism.ext
  rw [pathPushforward_apply_left_of_comp f htf huf path
    (Over.homMk (t ≫ k.left) (by change (t ≫ k.left) ≫ Y.obj.hom = t ≫ f; rw [Category.assoc, Over.w k]; rfl)) y k.left
    (by change k.left ≫ Y.obj.hom = (𝟙 X) ≫ f; simp) (by rfl)]
  rw [hy]
  rfl

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)
    (T : Over S) [QuasiSeparatedSpace T.left]
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)


local notation "H" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "FrameAt" T₀:max a₀:max s₀:max => harrisIntegralCMWeilFrame
  D C P B W lam T₀ a₀ compatibility h s₀
local notation "rightAt" T₀:max a₀:max s₀:max =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability
    (W.pullback P (T₀).hom).hasDual (W.pullback P (T₀).hom).geometry
    (W.pullback P (T₀).hom).inverseBundle (W.pullback P (T₀).hom).evaluation
    compatibility (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀
local notation "RawAt" T₀:max a₀:max s₀:max U₀:max =>
  @RightOrbit H _ (FrameAt T₀ a₀ s₀) (rightAt T₀ a₀ s₀) U₀
variable (htor : TorsionFiniteEtaleStatement.{0})

local notation "framePathAt" T₀:max a₀:max hu₀:max =>
  Tate.weilAdelicFrameTransport P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport
    (W.pullback P (T₀).hom).hasDual (W.pullback P (T₀).hom).geometry
    (W.pullback P (T₀).hom).inverseBundle (W.pullback P (T₀).hom).evaluation
    (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) htor hu₀

local notation "monAt" T₀:max a₀:max s₀:max hs₀:max hu₀:max =>
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (W.pullback P (T₀).hom).hasDual
    (W.pullback P (T₀).hom).geometry (W.pullback P (T₀).hom).inverseBundle
    (W.pullback P (T₀).hom).evaluation
    (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀ hs₀ htor hu₀
local notation "commAt" T₀:max a₀:max s₀:max hs₀:max hu₀:max =>
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (W.pullback P (T₀).hom).hasDual
    (W.pullback P (T₀).hom).geometry (W.pullback P (T₀).hom).inverseBundle
    (W.pullback P (T₀).hom).evaluation
    (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀ hs₀ htor hu₀
section Restriction

variable {T' : Over S} [QuasiSeparatedSpace T'.left] (f : T' ⟶ T)
    {Ω Ω' : Type} [Field Ω] [Field Ω']
    (t : Spec (.of Ω) ⟶ T'.left) (u : Spec (.of Ω') ⟶ T'.left)
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (hupt : ∀ Y : Cover T'.left, Finite (Fiber u Y))
    (htf : ∀ Y : Cover T.left, Finite (Fiber (t ≫ f.left) Y))
    (huf : ∀ Y : Cover T.left, Finite (Fiber (u ≫ f.left) Y))
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "aD" => (relativeEndRestrict B f).comp a
local notation "levelDAt" t₀:max ht₀:max =>
  harrisIntegralCMFullActionLevelTower
    D C P B W lam T' aD compatibility h t₀ ht₀ htor huD
local notation "pointD" => harrisIntegralCMFullActionLevelPointIso
  D C P B W lam T' aD compatibility h htor huD
local notation "evalAt" t₀:max ht₀:max hs₀:max =>
  harrisIntegralCMRestrictionRawClass
    D C P B W lam f a compatibility h t₀ ht₀ htor huD
    (t₀ ≫ f.left) rfl hs₀
local notation "rawPathT" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor htf huf huT
local notation "GammaT" => FundamentalGroup (t ≫ f.left) htf
local notation "GammaU" => FundamentalGroup (u ≫ f.left) huf
local notation "levelSubgroup" V₀:max => ((hodgeLevelFunctor D C).obj V₀).subgroup
local notation "selectedAt" t₀:max ht₀:max hs₀:max V₀:max q₀:max =>
  {l : (levelDAt t₀ ht₀).obj V₀ //
    (evalAt t₀ ht₀ hs₀) V₀ l ∈
      MulAction.orbit (FundamentalGroup (t₀ ≫ f.left) hs₀) q₀}

local notation "selectedPoint" => harrisIntegralCMTestLevelOrbitPointEquiv
  D C P B W lam T a compatibility h htor f t u ht hupt htf huf huT huD
local notation "levelTAt" s₀:max hs₀:max => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h s₀ hs₀ htor huT
local notation "coverAt" s₀:max hs₀:max => harrisIntegralCMFiniteOrbitCover
  D C P B W lam T a compatibility h s₀ hs₀ htor huT
local notation "fiberAt" s₀:max hs₀:max => harrisIntegralCMFiniteOrbitCoverFiberEquiv
  D C P B W lam T a compatibility h s₀ hs₀ htor huT
local notation "pushed" path₀:max => pathPushforward f.left htf huf path₀
local notation "targetNonempty" path₀:max => harrisIntegralCMFullActionLevelPointNonempty
  D C P B W lam T a compatibility h htor htf huf huT (pushed path₀)
local notation "coverPath" path₀:max => harrisIntegralCMFiniteOrbitCoverPointIso
  D C P B W lam T a compatibility h htor htf huf huT (pushed path₀)
local notation "testAt" t₀:max ht₀:max hs₀:max => harrisIntegralCMFiniteOrbitCoverTestLevelEquiv
  D C P B W lam T a compatibility h (t₀ ≫ f.left) hs₀ htor huT f t₀ rfl ht₀ huD

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left]
    [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left]
    [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Postcomposition with the actual cover point isomorphism identifies the
original sets of test morphisms. -/
def harrisIntegralCMFiniteOrbitCoverTestPointEquiv
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (U V : HarrisLevel D)
    (hRef : Nonempty ((levelTAt (t ≫ f.left) htf).obj U)) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ q : RawAt T a (t ≫ f.left) (levelSubgroup V),
      (Over.mk f.left ⟶ ((coverAt (t ≫ f.left) htf) U V hRef q).obj) ≃
        (Over.mk f.left ⟶ ((coverAt (u ≫ f.left) huf) U V
          ((targetNonempty path) U hRef)
          (rawPathT (pushed path) (levelSubgroup V) q)).obj) := by
  letI := rightAt T a (t ≫ f.left)
  letI := rightAt T a (u ≫ f.left)
  letI := monAt T a (t ≫ f.left) htf huT
  letI := monAt T a (u ≫ f.left) huf huT
  letI := commAt T a (t ≫ f.left) htf huT
  letI := commAt T a (u ≫ f.left) huf huT
  intro q
  exact (Iso.refl (Over.mk f.left)).homCongr
    ((inclusion T.left).mapIso ((coverPath path) U V hRef q))

omit [IsCMField F] [IsScalarTower ℚ F A] [QuasiSeparatedSpace T'.left]
  hμfinD hμetD [ConnectedSpace T'.left] [IsLocallyNoetherian T'.left] in
/-- The comparison of test morphisms is the original postcomposition map. -/
theorem harrisIntegralCMFiniteOrbitCoverTestPointEquiv_apply
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (U V : HarrisLevel D)
    (hRef : Nonempty ((levelTAt (t ≫ f.left) htf).obj U)) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (k : Over.mk f.left ⟶ ((coverAt (t ≫ f.left) htf) U V hRef q).obj),
      harrisIntegralCMFiniteOrbitCoverTestPointEquiv
        D C P B W lam T a compatibility h htor f t u ht hupt htf huf huT path U V hRef q k =
      k ≫ ((coverPath path) U V hRef q).hom.hom := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q k
  simp [harrisIntegralCMFiniteOrbitCoverTestPointEquiv, Iso.homCongr_apply]

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The original test correspondence intertwines actual cover point comparison
with original selected direct-level point transport. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointMap
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (U V : HarrisLevel D)
    (hRef : Nonempty ((levelTAt (t ≫ f.left) htf).obj U)) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (k : Over.mk f.left ⟶ ((coverAt (t ≫ f.left) htf) U V hRef q).obj),
      selectedPoint path V q ((testAt t ht htf) U V hRef q k) =
        (testAt u hupt huf) U V ((targetNonempty path) U hRef)
          (rawPathT (pushed path) (levelSubgroup V) q)
          (k ≫ ((coverPath path) U V hRef q).hom.hom) := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q k
  apply Subtype.ext
  apply harrisIntegralCMRestrictionRawClass_injective
    D C P B W lam f a compatibility h u hupt htor huD (u ≫ f.left) rfl huf V
  rw [harrisIntegralCMTestLevelOrbitPointEquiv_evaluation,
    harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val,
    harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_val]
  let x : Fiber (t ≫ f.left) ((coverAt (t ≫ f.left) htf) U V hRef q) :=
    Over.homMk (t ≫ k.left) (by rw [Category.assoc, Over.w k]; rfl)
  have heval := pathPushforward_testEvaluation f.left t u ht hupt htf huf path
    (((coverAt (u ≫ f.left) huf) U V ((targetNonempty path) U hRef)
      (rawPathT (pushed path) (levelSubgroup V) q)))
    (k ≫ ((coverPath path) U V hRef q).hom.hom)
  have hx : x ≫ ((coverPath path) U V hRef q).hom.hom =
      Over.homMk (t ≫ (k ≫ ((coverPath path) U V hRef q).hom.hom).left)
        (by rw [Category.assoc, Over.w (k ≫ ((coverPath path) U V hRef q).hom.hom)]; rfl) := by
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _
  rw [← hx] at heval
  rw [← heval]
  exact (harrisIntegralCMFiniteOrbitCoverPointIso_raw D C P B W lam T a
    compatibility h htor htf huf huT (pushed path) U V hRef q x).symm

/-- The original direct level obtained after postcomposing a test morphism with
the actual cover point isomorphism is independent of the chosen test path. -/
theorem harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointMap_val_path_independent
    (path path' : fiberFunctor t ht ≅ fiberFunctor u hupt) (U V : HarrisLevel D)
    (hRef : Nonempty ((levelTAt (t ≫ f.left) htf).obj U)) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (k : Over.mk f.left ⟶ ((coverAt (t ≫ f.left) htf) U V hRef q).obj),
      ((testAt u hupt huf) U V ((targetNonempty path) U hRef)
          (rawPathT (pushed path) (levelSubgroup V) q)
          (k ≫ ((coverPath path) U V hRef q).hom.hom)).val =
        ((testAt u hupt huf) U V ((targetNonempty path') U hRef)
          (rawPathT (pushed path') (levelSubgroup V) q)
          (k ≫ ((coverPath path') U V hRef q).hom.hom)).val := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q k
  have hp := congrArg Subtype.val
    (harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointMap
      D C P B W lam T a compatibility h htor f t u ht hupt htf huf huT huD
      path U V hRef q k)
  have hp' := congrArg Subtype.val
    (harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointMap
      D C P B W lam T a compatibility h htor f t u ht hupt htf huf huT huD
      path' U V hRef q k)
  rw [← hp, ← hp']
  exact harrisIntegralCMTestLevelOrbitPointEquiv_val_path_independent
    D C P B W lam T a compatibility h htor f t u ht hupt htf huf huT huD
    path path' V q ((testAt t ht htf) U V hRef q k)

end Restriction
end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
