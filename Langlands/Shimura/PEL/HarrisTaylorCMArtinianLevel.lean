import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-! # Pointed Harris levels over local Artinian thickenings -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped PreGaloisCategory FintypeCatDiscrete

noncomputable section

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AlgebraicGeometry.FiniteEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cover_notInitial_of_nonempty {S : Scheme.{u}} (Y : Cover S)
    [Nonempty Y.obj.left] (h : IsInitial Y) : False := by
  have hEmpty := isInitial_iff_isEmpty.mp ⟨h.isInitialObj (coverToScheme S) _⟩
  exact hEmpty.false (Classical.choice ‹Nonempty Y.obj.left›)

private def cover_initial_of_empty {S : Scheme.{u}} (Y : Cover S)
    [IsEmpty Y.obj.left] : IsInitial Y := by
  let i : (⊥_ (Cover S)) ⟶ Y := initial.to Y
  have : IsEmpty ((coverToScheme S).obj Y) := ‹IsEmpty Y.obj.left›
  have : IsIso ((coverToScheme S).map i) :=
    AlgebraicGeometry.isIso_of_isEmpty _
  have : IsIso i := isIso_of_reflects_iso i (coverToScheme S)
  exact initialIsInitial.ofIso (asIso i)

private theorem cover_connectedSpace {S : Scheme.{u}} (Y : Cover S)
    [PreGaloisCategory.IsConnected Y] : ConnectedSpace Y.obj.left := by
  have hNonempty : Nonempty Y.obj.left := by
    by_contra h
    have : IsEmpty Y.obj.left := not_nonempty_iff.mp h
    exact PreGaloisCategory.IsConnected.notInitial (cover_initial_of_empty Y)
  refine connectedSpace_iff_clopen.mpr ⟨hNonempty, ?_⟩
  intro s hs
  by_cases he : s = ∅
  · exact Or.inl he
  let V : Y.obj.left.Opens := ⟨s, hs.2⟩
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hs.1)
  let Z : Cover S := cover (V.ι ≫ Y.obj.hom)
  let i : Z ⟶ Y := ObjectProperty.homMk (Over.homMk V.ι)
  have : Mono i := (coverToScheme S).mono_of_mono_map (f := i)
    (inferInstanceAs (Mono V.ι))
  have : Nonempty Z.obj.left := (Set.nonempty_iff_ne_empty.mpr he).to_subtype
  have : IsIso i := PreGaloisCategory.IsConnected.noTrivialComponent Z i
    (cover_notInitial_of_nonempty Z)
  have : IsIso V.ι := inferInstanceAs (IsIso ((coverToScheme S).map i))
  have hV := range_eq_univ V.ι
  rw [Scheme.Opens.range_ι] at hV
  exact Or.inr hV

private theorem cover_isConnected_of_connectedSpace {S : Scheme.{u}} (Y : Cover S)
    [ConnectedSpace Y.obj.left] : PreGaloisCategory.IsConnected Y where
  notInitial := cover_notInitial_of_nonempty Y
  noTrivialComponent Z i _ h := by
    have hNonempty : Nonempty Z.obj.left := by
      by_contra hEmpty
      have : IsEmpty Z.obj.left := not_nonempty_iff.mp hEmpty
      exact h (cover_initial_of_empty Z)
    have hfe : finiteEtale i.hom.left :=
      finiteEtale.of_postcomp (W' := finiteEtale) i.hom.left Y.obj.hom Y.property (by
        rw [Over.w]
        exact Z.property)
    have : IsFinite i.hom.left := hfe.1
    have : Etale i.hom.left := hfe.2
    have : Mono i.hom := preserves_mono_of_preservesLimit (inclusion S) i
    have : Mono i.hom.left := inferInstance
    have : IsClosedImmersion i.hom.left :=
      (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩
    have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
    have hr := (connectedSpace_iff_clopen.mp ‹ConnectedSpace Y.obj.left›).2
      (Set.range i.hom.left)
      ⟨i.hom.left.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range i.hom.left⟩
    have hsurj : Surjective i.hom.left := ⟨Set.range_eq_univ.mp
      (hr.resolve_left (Set.range_nonempty i.hom.left).ne_empty)⟩
    exact (isIso_iff_of_reflects_iso i (coverToScheme S)).mp
      ((isIso_iff_isOpenImmersion_and_surjective i.hom.left).mpr ⟨inferInstance, hsurj⟩)

private theorem fundamentalGroupMap_surjective_of_surjective_closedImmersion
    {S T : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
    [IsLocallyNoetherian S] [IsLocallyNoetherian T] (b : T ⟶ S)
    [IsClosedImmersion b] [Surjective b]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : ∀ Y : Cover T, Finite (Fiber t Y))
    (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y)) :
    Function.Surjective (fundamentalGroupMap b t (t ≫ b) rfl ht hs) := by
  obtain ⟨hGS, hFS⟩ := geometricGaloisFiberFunctor (t ≫ b) hs
  obtain ⟨hGT, hFT⟩ := geometricGaloisFiberFunctor t ht
  let F := fiberFunctor (t ≫ b) hs
  let G := FundamentalGroup t ht
  let α := fundamentalGroupMap b t (t ≫ b) rfl ht hs
  let (Y : Cover S) : MulAction G (F.obj Y) := MulAction.compHom (F.obj Y) α
  let : PreGaloisCategory.IsNaturalSMul F G := {
    naturality g _ _ f x := (smul_naturality (t ≫ b) hs f (α g) x).symm
  }
  let (Y : Cover S) : ContinuousSMul G (F.obj Y) :=
    MulAction.continuousSMul_compHom (continuous_fundamentalGroupMap b t (t ≫ b) rfl ht hs)
  have htrans (Y : Cover S) [PreGaloisCategory.IsGalois Y] :
      MulAction.IsPretransitive G (F.obj Y) := by
    let : ConnectedSpace Y.obj.left := cover_connectedSpace Y
    let p := pullback.fst Y.obj.hom b
    let e := p.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective p.surjective
    let : ConnectedSpace ((pullbackFunctor b).obj Y).obj.left :=
      e.connectedSpace_iff.mpr inferInstance
    let : PreGaloisCategory.IsConnected ((pullbackFunctor b).obj Y) :=
      cover_isConnected_of_connectedSpace _
    have hOrbit := PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected
      (fiberFunctor t ht) ((pullbackFunctor b).obj Y)
    let eY := pullbackFiberEquiv b t (t ≫ b) rfl Y
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := hOrbit.exists_smul_eq (eY x) (eY y)
    refine ⟨g, eY.injective ?_⟩
    exact (pullbackFiberEquiv_smul b t (t ≫ b) rfl ht hs g Y x).trans hg
  have hα : PreGaloisCategory.toAut F G = α := by
    ext g : 1
    exact fundamentalGroup_ext (fun _ _ => rfl)
  change Function.Surjective α
  rw [← hα]
  exact PreGaloisCategory.toAut_surjective_of_isPretransitive F G htrans

private theorem artinianSpecConnected (B : Type u)
    [CommRing B] [IsLocalRing B] [IsArtinianRing B] : ConnectedSpace (Spec (.of B)) := by
  change ConnectedSpace (PrimeSpectrum B)
  have hsub : (Set.univ : Set (PrimeSpectrum B)).Subsingleton :=
    Set.subsingleton_univ_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mpr ⟨Set.univ_nonempty, hsub.isPreconnected⟩

/-- Surjectivity of actual pointed monodromy for local Artinian surjections. -/
def SpecArtinianMonodromySurjectivityStatement : Prop :=
  ∀ {B' B : Type u} [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] (φ : B' →+* B), Function.Surjective φ →
    ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of B))
      (ht : ∀ Y : Cover (Spec (.of B)), Finite (Fiber t Y))
      (hs : ∀ Y : Cover (Spec (.of B')), Finite (Fiber (t ≫ Spec.map (CommRingCat.ofHom φ)) Y)),
      Function.Surjective
        (fundamentalGroupMap (Spec.map (CommRingCat.ofHom φ)) t _ rfl ht hs)

/-- A local Artinian surjection induces a surjection on actual pointed monodromy groups. -/
theorem specArtinianMonodromySurjectivity :
    SpecArtinianMonodromySurjectivityStatement.{u} := by
  intro B' B _ _ _ _ _ _ φ hφ Ω _ _ t ht hs
  let b := Spec.map (CommRingCat.ofHom φ)
  let : IsClosedImmersion b := IsClosedImmersion.spec_of_surjective _ hφ
  have : Nonempty (Spec (.of B)) := inferInstanceAs (Nonempty (PrimeSpectrum B))
  have : Subsingleton (Spec (.of B')) := inferInstanceAs (Subsingleton (PrimeSpectrum B'))
  have : Surjective b := inferInstance
  have : ConnectedSpace (Spec (.of B)) := artinianSpecConnected B
  have : ConnectedSpace (Spec (.of B')) := artinianSpecConnected B'
  exact fundamentalGroupMap_surjective_of_surjective_closedImmersion b t ht hs

private theorem invariantOrbit_pullback_surjective {G X Y Γ Δ : Type*}
    [Group G] [Group Γ] [Group Δ] [MulAction Gᵐᵒᵖ X] [MulAction Gᵐᵒᵖ Y]
    [MulAction Γ X] [MulAction Δ Y]
    [SMulCommClass Γ Gᵐᵒᵖ X] [SMulCommClass Δ Gᵐᵒᵖ Y]
    (U : Subgroup G) (α : Γ →* Δ) (hα : Function.Surjective α) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g)
    (hΓ : ∀ γ x, e (γ • x) = α γ • e x) :
    Function.Surjective (InvariantOrbit.pullback U α e he hΓ) := by
  intro q
  refine ⟨⟨RightOrbit.map U e he q.1, ?_⟩, ?_⟩
  · intro δ
    obtain ⟨γ, rfl⟩ := hα δ
    rw [← RightOrbit.map_smul U α e he hΓ, q.2 γ]
  · apply Subtype.ext
    exact (RightOrbit.equiv U e he).symm_apply_apply q.1

section HarrisLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.GroupScheme
open scoped CategoryTheory.MonObj TensorProduct
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {S T : Scheme.{0}} (b : T ⟶ S)
  [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (W : PositivePullbackDualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b X)

local notation "ψ" => D.harrisHodgePELForm C
local notation "lamBC" => canonicalDualValuedBaseChange b X.actionObj.abelianScheme
  preservation composition unitCoherence associativity comparison symmetry stability universality
  X.hasDual X.geometry X.inversePoincare X.evaluation
  W.hasDual W.geometry W.inversePoincare W.evaluation X.polarization
set_option quotPrecheck false in
local notation "iBC" => (rationalBaseChangeEnd b X.actionObj.abelianScheme).comp X.actionObj.action
local notation "geo" => rationalWeilGeometricTransport

set_option maxHeartbeats 800000 in
/-- The actual Harris tower pulls back surjectively at every level when pointed
monodromy maps surjectively. -/
theorem framedPositiveActionTowerBaseChange_surjective
    (hα : Function.Surjective (fundamentalGroupMap b t (t ≫ b) rfl ht hs))
    (frameExists :
      letI := auxiliaryStarRing D C
      letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Nonempty (Tate.AdelicFrame X.actionObj.abelianScheme h X.actionObj.action
        ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) (t ≫ b)))
    (U : HarrisLevel D) :
    letI := auxiliaryStarRing D C
    Function.Surjective ((framedPositiveActionTowerBaseChange D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT X
      W.hasDual W.geometry W.inversePoincare W.evaluation W.dualEndAdditivity frameExists).app U) := by
  let := auxiliaryStarRing D C
  let := Tate.weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability X.hasDual X.geometry X.inversePoincare X.evaluation
    compatibility X.polarization h X.actionObj.action A ψ (t ≫ b)
  let := Tate.weilAdelicFrameRightAction preservation composition unitCoherence associativity
    comparison symmetry stability W.hasDual W.geometry W.inversePoincare W.evaluation
    compatibility lamBC h iBC A ψ t
  let := Tate.weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geo X.hasDual X.geometry X.inversePoincare
    X.evaluation X.polarization h X.actionObj.action A ψ (t ≫ b) hs htor huS
  let := Tate.weilAdelicFrameMonodromyAction preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geo W.hasDual W.geometry W.inversePoincare
    W.evaluation lamBC h iBC A ψ t ht htor huT
  let := Tate.weilAdelicFrameActionsComm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geo X.hasDual X.geometry X.inversePoincare
    X.evaluation X.polarization h X.actionObj.action A ψ (t ≫ b) hs htor huS
  let := Tate.weilAdelicFrameActionsComm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geo W.hasDual W.geometry W.inversePoincare
    W.evaluation lamBC h iBC A ψ t ht htor huT
  change Function.Surjective (Tate.weilAdelicLevelBaseChange b X.actionObj.abelianScheme
    preservation composition unitCoherence associativity comparison symmetry stability universality
    X.hasDual X.geometry X.inversePoincare X.evaluation
    W.hasDual W.geometry W.inversePoincare W.evaluation compatibility X.polarization h
    X.actionObj.action A ψ t ht hs htor huS huT ((hodgeLevelFunctor D C).obj U).toSubgroup)
  unfold Tate.weilAdelicLevelBaseChange
  exact invariantOrbit_pullback_surjective _ _ hα _ _ _

end HarrisLevel

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
