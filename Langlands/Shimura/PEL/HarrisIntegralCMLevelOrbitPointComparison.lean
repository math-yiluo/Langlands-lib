import Langlands.Shimura.PEL.HarrisIntegralCMRestrictionPointComparison
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverTestNaturality

/-! # Point comparison of selected original Harris level orbits -/

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
section RawOrbits

variable {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ T.left} {r : Spec (.of Ω') ⟶ T.left}
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (hr : ∀ Y : Cover T.left, Finite (Fiber r Y))
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "rawPath" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor hs hr hu
local notation "GammaS" => FundamentalGroup s hs
local notation "GammaR" => FundamentalGroup r hr

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual raw point transport commutes with every right level transporter. -/
theorem harrisIntegralCMWeilRawPointEquiv_translate
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) {U V : Subgroup H}
    (g : H) (hg : ∀ v ∈ U, g⁻¹ * v * g ∈ V) :
    letI := rightAt T a s
    letI := rightAt T a r
    ∀ q : RawAt T a s U,
      rawPath path V (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (rawPath path U q) := by
  let := rightAt T a s
  let := rightAt T a r
  intro q
  induction q using Quotient.inductionOn with
  | h eta =>
    apply congrArg (RightOrbit.mk V)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original raw path transport intertwines actual base monodromy. -/
theorem harrisIntegralCMWeilRawPointEquiv_monodromy
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U : Subgroup H) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ (g : GammaS) (q : RawAt T a s U),
      rawPath path U (g • q) = pathConjugation path g • rawPath path U q := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro g q
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (Tate.weilAdelicFrameTransport_monodromy P.preservation P.composition
        P.unitCoherence P.associativity P.comparison P.symmetry P.stability
        compatibility rationalWeilGeometricTransport
        (W.pullback P T.hom).hasDual (W.pullback P T.hom).geometry
        (W.pullback P T.hom).inverseBundle (W.pullback P T.hom).evaluation
        (W.pullbackMap P T.hom (W.pullback P T.hom) lam) h
        (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange T.hom).obj B) a)
        A (D.harrisHodgePELForm C) htor hu path g eta)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Membership in the selected actual base orbit is preserved and reflected. -/
theorem harrisIntegralCMWeilRawPointEquiv_mem_orbit_iff
    (path : fiberFunctor s hs ≅ fiberFunctor r hr) (U : Subgroup H) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a s hs hu
    letI := monAt T a r hr hu
    letI := commAt T a s hs hu
    letI := commAt T a r hr hu
    ∀ q z : RawAt T a s U,
      rawPath path U z ∈ MulAction.orbit GammaR (rawPath path U q) ↔
        z ∈ MulAction.orbit GammaS q := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a s hs hu
  let := monAt T a r hr hu
  let := commAt T a s hs hu
  let := commAt T a r hr hu
  intro q z
  rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨g, rfl⟩ := (pathConjugation path).surjective g
    refine ⟨g, (rawPath path U).injective ?_⟩
    rw [harrisIntegralCMWeilRawPointEquiv_monodromy]
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨pathConjugation path g, ?_⟩
    rw [← harrisIntegralCMWeilRawPointEquiv_monodromy, hg]

end RawOrbits

section ChangePath

variable {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ T.left} {r : Spec (.of Ω') ⟶ T.left}
    (hs : ∀ Y : Cover T.left, Finite (Fiber s Y))
    (hr : ∀ Y : Cover T.left, Finite (Fiber r Y))
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "rawPath" => harrisIntegralCMWeilRawPointEquiv
  D C P B W lam T a compatibility h htor hs hr hu
local notation "GammaR" => FundamentalGroup r hr

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Changing the actual path changes a raw class by the actual target loop. -/
theorem harrisIntegralCMWeilRawPointEquiv_change_path
    (path path' : fiberFunctor s hs ≅ fiberFunctor r hr) (U : Subgroup H) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a r hr hu
    letI := commAt T a r hr hu
    ∀ q : RawAt T a s U,
      rawPath path' U q =
        (show GammaR from path.symm ≪≫ path') • rawPath path U q := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a r hr hu
  let := commAt T a r hr hu
  intro q
  induction q using Quotient.inductionOn with
  | h eta =>
    apply congrArg (RightOrbit.mk U)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact Tate.rationalTransport_change_path htor
      ((AbelianScheme.baseChange T.hom).obj B) (fun _ => True) hu path path' (eta.1 x)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The selected target monodromy orbit is independent of the supplied path. -/
theorem harrisIntegralCMWeilRawPointEquiv_orbit_path_independent
    (path path' : fiberFunctor s hs ≅ fiberFunctor r hr) (U : Subgroup H) :
    letI := rightAt T a s
    letI := rightAt T a r
    letI := monAt T a r hr hu
    letI := commAt T a r hr hu
    ∀ q : RawAt T a s U,
      MulAction.orbit GammaR (rawPath path' U q) =
        MulAction.orbit GammaR (rawPath path U q) := by
  let := rightAt T a s
  let := rightAt T a r
  let := monAt T a r hr hu
  let := commAt T a r hr hu
  intro q
  rw [harrisIntegralCMWeilRawPointEquiv_change_path]
  exact MulAction.orbit_smul _ _

end ChangePath

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

/-- Restrict the original fixed-level point isomorphism to the original test
levels selected by their actual base monodromy orbit. -/
def harrisIntegralCMTestLevelOrbitPointEquiv
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (V : HarrisLevel D) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ q : RawAt T a (t ≫ f.left) (levelSubgroup V),
      selectedAt t ht htf V q ≃
        selectedAt u hupt huf V
          (rawPathT (pathPushforward f.left htf huf path) (levelSubgroup V) q) := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q
  refine ((pointD path).app V).toEquiv.subtypeEquiv ?_
  intro l
  change _ ↔ (evalAt u hupt huf) V ((pointD path).hom.app V l) ∈ _
  rw [harrisIntegralCMRestrictionRawClass_pointMap]
  exact (harrisIntegralCMWeilRawPointEquiv_mem_orbit_iff D C P B W lam T a
    compatibility h htor htf huf huT (pathPushforward f.left htf huf path)
    (levelSubgroup V) q ((evalAt t ht htf) V l)).symm

local notation "selectedPoint" => harrisIntegralCMTestLevelOrbitPointEquiv
  D C P B W lam T a compatibility h htor f t u ht hupt htf huf huT huD
local notation "selectedMapAt" t₀:max ht₀:max hs₀:max =>
  harrisIntegralCMTestLevelOrbitMap
    D C P B W lam T a compatibility h (t₀ ≫ f.left) hs₀ htor huT
    f t₀ rfl ht₀ huD
local notation "levelArrow" => (hodgeLevelFunctor D C).map
local notation "transport" j₀:max =>
  RightOrbit.translate (G := H) (levelArrow j₀).element (levelArrow j₀).respects

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The selected comparison has the unchanged original fixed-level value. -/
theorem harrisIntegralCMTestLevelOrbitPointEquiv_val
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (V : HarrisLevel D) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (l : selectedAt t ht htf V q),
      (selectedPoint path V q l).val = (pointD path).hom.app V l.val := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q l
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The inverse selected comparison has the original inverse fixed-level value. -/
theorem harrisIntegralCMTestLevelOrbitPointEquiv_symm_val
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (V : HarrisLevel D) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (l : selectedAt u hupt huf V
        (rawPathT (pathPushforward f.left htf huf path) (levelSubgroup V) q)),
      ((selectedPoint path V q).symm l).val = (pointD path).inv.app V l.val := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q l
  rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Original raw evaluation of the selected comparison is actual base path
transport of the original raw evaluation. -/
theorem harrisIntegralCMTestLevelOrbitPointEquiv_evaluation
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt) (V : HarrisLevel D) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (l : selectedAt t ht htf V q),
      (evalAt u hupt huf) V (selectedPoint path V q l).val =
        rawPathT (pathPushforward f.left htf huf path) (levelSubgroup V)
          ((evalAt t ht htf) V l.val) := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q l
  exact harrisIntegralCMRestrictionRawClass_pointMap D C P B W lam T a
    compatibility h htor f t u ht hupt htf huf huT huD path V l.val

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The selected comparison commutes with the independently defined original
level-orbit transitions at both points. The transported orbit equation is proved
by actual raw path/translation compatibility. -/
theorem harrisIntegralCMTestLevelOrbitPointEquiv_natural
    (path : fiberFunctor t ht ≅ fiberFunctor u hupt)
    {V Z : HarrisLevel D} (j : V ⟶ Z) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (r : RawAt T a (t ≫ f.left) (levelSubgroup Z))
      (hqr : (transport j) q = r) (l : selectedAt t ht htf V q),
      selectedPoint path Z r ((selectedMapAt t ht htf) j q r hqr l) =
        (selectedMapAt u hupt huf) j
          (rawPathT (pathPushforward f.left htf huf path) (levelSubgroup V) q)
          (rawPathT (pathPushforward f.left htf huf path) (levelSubgroup Z) r)
          (by
            rw [← harrisIntegralCMWeilRawPointEquiv_translate]
            exact congrArg
              (rawPathT (pathPushforward f.left htf huf path) (levelSubgroup Z)) hqr)
          (selectedPoint path V q l) := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q r hqr l
  apply Subtype.ext
  rw [harrisIntegralCMTestLevelOrbitPointEquiv_val,
    harrisIntegralCMTestLevelOrbitMap_val,
    harrisIntegralCMTestLevelOrbitMap_val,
    harrisIntegralCMTestLevelOrbitPointEquiv_val]
  exact ConcreteCategory.congr_hom ((pointD path).hom.naturality j) l.val

/-- Changing the path preserves the underlying original selected test level. -/
theorem harrisIntegralCMTestLevelOrbitPointEquiv_val_path_independent
    (path path' : fiberFunctor t ht ≅ fiberFunctor u hupt) (V : HarrisLevel D) :
    letI := rightAt T a (t ≫ f.left)
    letI := rightAt T a (u ≫ f.left)
    letI := monAt T a (t ≫ f.left) htf huT
    letI := monAt T a (u ≫ f.left) huf huT
    letI := commAt T a (t ≫ f.left) htf huT
    letI := commAt T a (u ≫ f.left) huf huT
    ∀ (q : RawAt T a (t ≫ f.left) (levelSubgroup V))
      (l : selectedAt t ht htf V q),
      (selectedPoint path V q l).val = (selectedPoint path' V q l).val := by
  let := rightAt T a (t ≫ f.left)
  let := rightAt T a (u ≫ f.left)
  let := monAt T a (t ≫ f.left) htf huT
  let := monAt T a (u ≫ f.left) huf huT
  let := commAt T a (t ≫ f.left) htf huT
  let := commAt T a (u ≫ f.left) huf huT
  intro q l
  rw [harrisIntegralCMTestLevelOrbitPointEquiv_val,
    harrisIntegralCMTestLevelOrbitPointEquiv_val,
    harrisIntegralCMFullActionLevelPointIso_path_independent
      D C P B W lam T' aD compatibility h htor huD path path']

end Restriction
end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
