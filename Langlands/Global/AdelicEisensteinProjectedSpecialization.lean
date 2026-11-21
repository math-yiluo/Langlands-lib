import Langlands.Global.AdelicEisensteinContinuationAnchors
import Langlands.Global.AdelicEisensteinWordCovariance
import Langlands.Global.EisensteinCompactSpecialization

/-! # Compact-projected specializations of the continued adelic series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Set NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1650000

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.Meromorphic UniformGrowthFrechetSpace
open AdelicGroupPoints GeneralLinearGroupPoints InfiniteAdelicGroupPoints
open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  {V : Type*} [AddCommGroup V] [Module ℂ V]

local notation "GL[" F "," n "]" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance projectedGeneralLinearIsAffine : IsAffine (GL[F, r + 1]).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin (r + 1)) (CommRingCat.of F)

local notation "Adeles" => AdelicGroupPoints F GL[F, r + 1]
local notation "Operators" => FreeOperatorAlgebra F (r + 1)
local notation "Stable" => StableAutomorphicFunctions F (r + 1)

local instance adelicProjectionRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance adelicProjectionContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance adelicProjectionSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) :=
  Submodule.addCommGroup _
local instance adelicProjectionStableAddCommGroup : AddCommGroup Stable := Submodule.addCommGroup _
local instance adelicProjectionStableComplexModule : Module ℂ Stable := Submodule.module _

local notation "Enveloping" => ArchimedeanGL.EnvelopingAlgebra F (r + 1)
local notation "realGenerator" => fun X => ArchimedeanGL.envelopingGenerator F (r + 1)
  (ArchimedeanGL.complexify F (r + 1) X)

variable (π : Module.End ℂ V) [FiniteDimensional ℂ π.range]

local notation "I" => Fin (Module.finrank ℂ π.range)
local notation "Coordinates" => (Fin (Module.finrank ℂ π.range) → ℂ)

/-- The series of a realized section detects every vector in the given section subspace. -/
def EisensteinSeriesInjectiveOn
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, r + 1]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ)) (S : Submodule ℂ V) : Prop :=
  Function.Injective (fun v : S => hK.eisensteinSeries (j v.val) lam)

private theorem continuedLinearCombination_injective_of_series
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ GL[F, r + 1]}
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K) (lam : ComplexCharacterParameter F P)
    {E : Type*} {t : E} (j : V →ₗ[ℂ] (Adeles → ℂ))
    (f : I → E → Adeles → ℂ)
    (hf : ∀ i, f i t = hK.eisensteinSeries (j (compactProjectionSeed π i)) lam)
    (hMajor : ∀ i, j (compactProjectionSeed π i) ∈ hK.compactMajorantSections lam)
    (hInj : EisensteinSeriesInjectiveOn F r hK lam j π.range) :
    Function.Injective (continuedLinearCombination f t) := by
  let b := Module.finBasis ℂ π.range
  let v (i : I) : hK.compactMajorantSections lam := ⟨j (compactProjectionSeed π i), hMajor i⟩
  have he (c : Coordinates) :
      continuedLinearCombination f t c = hK.eisensteinSeries (j (b.equivFun.symm c).val) lam := by
    let s := ∑ i, c i • v i
    have hsum : s.val = j (b.equivFun.symm c).val := by
      have hb := congrArg (j.comp π.range.subtype) (b.sum_repr (b.equivFun.symm c))
      simpa only [s, map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply,
        ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Submodule.coe_sum,
        Submodule.coe_smul, v, compactProjectionSeed, b] using hb
    rw [← hsum]
    change _ = hK.eisensteinSeriesLinear lam s
    simp only [continuedLinearCombination_apply, hf, s, map_sum, map_smul]
    rfl
  intro x y hxy
  exact b.equivFun.symm.injective (hInj ((he x).symm.trans (hxy.trans (he y))))

variable {N d : ℕ} (rho : GroupScheme.MatrixRepresentation GL[F, r + 1] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, r + 1]).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, r + 1] hsmooth)
  (hN : 0 < N) (hrho : GroupScheme.IsClosedSubgroup rho)
  (hG : GroupScheme.IsConnectedReductive GL[F, r + 1])

local notation "Growth[" R "," L "]" =>
  UniformGrowthFrechetSpace F GL[F, r + 1] rho hsmooth hcalc hN hrho R L
local notation "value[" R "," L "]" =>
  UniformGrowthFrechetSpace.toFun F GL[F, r + 1] rho hsmooth hcalc hN hrho R L

include hN hrho hG in
/-- The adelic continuation and convergence anchor construction realizes a
compact-projected simple specialization with its full operator action. -/
theorem exists_freeOperatorQuotient_of_adelic_projected_specialization
    {P M U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ GL[F, r + 1]} {l : M ⟶ P} {a : A.toGrp ⟶ M} {iU : U ⟶ P}
    [IsClosedImmersion p.hom.hom.left] (root : ParabolicRootPresentation p l a)
    [Mono root.data.i.hom.hom.left] [Fintype (relativeWeylGroup root.data.i)]
    [Mono (CommGroupScheme.groupHom root.data.f).hom.hom.left]
    (hA : GroupScheme.IsSplitTorus A.toGrp) (hT : GroupScheme.IsSplitTorus root.data.T.toGrp)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (hmax : IsMaximalCompactSubgroup F GL[F, r + 1] K)
    (hKstandard : K.comap (ofInfinite F GL[F, r + 1]).toMonoidHom =
      generalLinearStandardInfiniteCompact F (r + 1))
    (hKinf : ∀ k : standardInfiniteCompact F (r + 1),
      ofInfinite F GL[F, r + 1] ((infiniteHomeomorph F (r + 1)).symm k.val) ∈ K)
    {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ))
    (hAut : ∀ v, IsAutomorphicFunctionOn F GL[F, r + 1] hsmooth hcalc
      (parabolicQuotientSubgroup F p iU l) (generalLinearStandardInfiniteCompact F (r + 1)) rho (j v))
    (hH : hK.HasSmoothHeightPairings hsmooth)
    (hSmooth : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F GL[F, r + 1] hsmooth
      ∀ v : V, ∀ b : FiniteAdelicGroupPoints F GL[F, r + 1],
        ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => j v (pair F GL[F, r + 1] a b)))
    (R : (Fin m → ℂ) → Representation ℂ (FiniteAdelicGL F (r + 1)) V)
    (C : Representation ℂ (standardInfiniteCompact F (r + 1)) V)
    (D : (Fin m → ℂ) → Enveloping →ₐ[ℂ] Module.End ℂ V)
    (hRhol : ∀ g v, (fun t => R t g v) ∈ finiteHolomorphicSections (Fin m → ℂ) V)
    (hDhol : ∀ X v, (fun t => D t (realGenerator X) v) ∈ finiteHolomorphicSections (Fin m → ℂ) V)
    (hR : ∀ t g v, j (R t g v) = hK.parameterRightAction (e t)
      (ofFinite F GL[F, r + 1] ((finiteHomeomorph F (r + 1)).symm g)) (j v))
    (hC : ∀ k v, j (C k v) = fun x : Adeles =>
      j v (x * ofInfinite F GL[F, r + 1] ((infiniteHomeomorph F (r + 1)).symm k.val)))
    (hD : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F GL[F, r + 1] hsmooth
      ∀ t X v, j (D t (realGenerator X) v) = hK.parameterDirectionalSection hsmooth (e t)
        ((infiniteRealLieAlgebraEquiv F (r + 1) hsmooth).symm X) (j v))
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : ∀ᶠ t in eisensteinConvergenceAnchorFilter root hA hT e,
      EisensteinSeriesInjectiveOn F r hK (e t) j π.range)
    (hProjection : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S →
      ∃ b : Operators, ∀ t v, v ∈ S → sectionOperatorAction R C D t b v = π v)
    (z : Fin m → ℂ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (aW : Operators →ₐ[ℂ] Module.End ℂ W) (ha : Representation.IsIrreducible aW.toMonoidHom) :
    letI := moduleOfAlgebraAction (sectionOperatorAction R C D z)
    letI := moduleOfAlgebraAction aW
    letI := moduleOfAlgebraAction (stableFreeOperatorAction F (r + 1))
    ∀ (S : Submodule Operators V) (q : S →ₗ[Operators] W), Function.Surjective q →
      ∀ y : W, y ≠ 0 →
        (∀ x : S, q x = y → ∃ x' : S, x'.val = π x.val ∧ q x' = y) →
        ∃ U : Submodule Operators Stable, ∃ u : U →ₗ[Operators] W, Function.Surjective u := by
  classical
  let ℱ := eisensteinConvergenceAnchorFilter root hA hT e
  let T := sectionOperatorAction R C D
  choose f hf hGood hLocal using fun v : V =>
    exists_continuedSection_on_convergenceAnchorFilter root hA hT e hK rho hN hrho hsmooth hcalc
      hcont hG hU hmax (j v) (hKstandard.symm ▸ hAut v)
  let seed := compactProjectionSeed π
  let fs (i : I) := f (seed i)
  have hLocalAut (i : I) (x : Fin m → ℂ) : ∃ B : TopologicalSpace.Opens (Fin m → ℂ), x ∈ B ∧
      ∃ (s : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, r + 1])),
        IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, r + 1])) ∧
        ∃ (g : B → Growth[s, L]) (Z : Set B), IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) g Z ∧
          ∀ t ∈ Z, value[s, L] (g t) = fs i t.val ∧
            IsAutomorphicFunctionOn F GL[F, r + 1] hsmooth hcalc (rationalSubgroup F GL[F, r + 1])
              (generalLinearStandardInfiniteCompact F (r + 1)) rho (fs i t.val) := by
    simpa only [hKstandard] using hLocal (seed i) x
  have hNum := continuedLinearCombination_hasLocalHolomorphicNumerators F GL[F, r + 1]
    rho hsmooth hcalc hN hrho fs (fun i x => by
      obtain ⟨B, hB, s, L, hL, g, Z, hZ, hval⟩ := hLocalAut i x
      exact ⟨B, hB, s, L, hL, g, Z, hZ, fun t ht => (hval t ht).1⟩)
  have hMajor (v : V) : ∀ᶠ t in ℱ, j v ∈ hK.compactMajorantSections (e t) :=
    (hGood v).mono fun t ht => ((mem_smoothConvergenceSections F GL[F, r + 1] hK (e t) (j v)).mp ht).1
  have hRegInj : ∃ t₀, t₀ ∈ regularParameterSet univ (continuedLinearCombination fs) ∧
      Function.Injective (continuedLinearCombination fs t₀) := by
    have hEvent : ∀ᶠ t in ℱ, Function.Injective (continuedLinearCombination fs t) := by
      filter_upwards [hinj, eventually_all.mpr (fun i : I => hf (seed i)),
        eventually_all.mpr (fun i : I => hMajor (seed i))] with t ht hAgree hBounds
      exact continuedLinearCombination_injective_of_series F r π hK (e t) j fs hAgree hBounds ht
    obtain ⟨B, hB, hBne, hInj⟩ := exists_open_of_eventually_eisensteinConvergenceAnchorFilter
      root hA hT e hG hEvent
    have hdense : Dense (regularParameterSet univ (continuedLinearCombination fs)) :=
      fun t => subset_closure_regularParameterSet hNum (mem_univ t)
    obtain ⟨t, ht, htr⟩ := hdense.inter_open_nonempty B hB hBne
    exact ⟨t, htr, hInj t ht⟩
  have hGenerator := sectionOperatorAction_generator_mem R C D hRhol hDhol
  have hHol (w : I →₀ Operators) :
      (fun t => operatorLinearCombination (T t) seed w) ∈ finiteHolomorphicSections (Fin m → ℂ) V := by
    simpa only [operatorLinearCombination_apply] using
      FiniteHolomorphicSections.freeAlgebra_finsuppSum_mem T hGenerator seed w
  have hWord (b : Operators) (v : V) :=
    eventually_scalarAutomorphicOperator_eisensteinSeries_word F (r + 1) hK hsmooth ℱ e j hGood
      hH hSmooth R C D hRhol hDhol hR hC hKinf hD b (fun _ => v) (FiniteHolomorphicSections.const_mem v)
  refine exists_freeOperatorQuotient_of_compact_projected_seeds π F r rho hsmooth hcalc hN hrho hG
    T z hHol hProjection fs hLocalAut hRegInj ?_ aW ha
  intro w c hc
  exact exists_open_of_eventually_eisensteinConvergenceAnchorFilter root hA hT e hG
    (eventually_scalarSeedOperatorCombination_eq F (r + 1) hK ℱ e j T hMajor
      (FiniteHolomorphicSections.freeAlgebra_apply_mem T hGenerator) hWord seed fs (fun i => hf (seed i)) w c hc)

include hN hrho hG in
/-- For an automorphic section model with the deformed adelic actions, the
continuation theorem and convergence-region injectivity supply the seed
continuations, their operator anchor identities and a regular injective member.
A compact-projected simple quotient is then realized in automorphic forms. -/
theorem exists_automorphic_subquotient_of_adelic_projected_specialization
    {P M U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ GL[F, r + 1]} {l : M ⟶ P} {a : A.toGrp ⟶ M} {iU : U ⟶ P}
    [IsClosedImmersion p.hom.hom.left] (root : ParabolicRootPresentation p l a)
    [Mono root.data.i.hom.hom.left] [Fintype (relativeWeylGroup root.data.i)]
    [Mono (CommGroupScheme.groupHom root.data.f).hom.hom.left]
    (hA : GroupScheme.IsSplitTorus A.toGrp) (hT : GroupScheme.IsSplitTorus root.data.T.toGrp)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup Adeles} (hK : IsIwasawaCompact p K)
    (hmax : IsMaximalCompactSubgroup F GL[F, r + 1] K)
    (hKstandard : K.comap (ofInfinite F GL[F, r + 1]).toMonoidHom =
      generalLinearStandardInfiniteCompact F (r + 1))
    (hKinf : ∀ k : standardInfiniteCompact F (r + 1),
      ofInfinite F GL[F, r + 1] ((infiniteHomeomorph F (r + 1)).symm k.val) ∈ K)
    {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    (j : V →ₗ[ℂ] (Adeles → ℂ))
    (hAut : ∀ v, IsAutomorphicFunctionOn F GL[F, r + 1] hsmooth hcalc
      (parabolicQuotientSubgroup F p iU l) (generalLinearStandardInfiniteCompact F (r + 1)) rho (j v))
    (hH : hK.HasSmoothHeightPairings hsmooth)
    (hSmooth : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F GL[F, r + 1] hsmooth
      ∀ v : V, ∀ b : FiniteAdelicGroupPoints F GL[F, r + 1],
        ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => j v (pair F GL[F, r + 1] a b)))
    (R : (Fin m → ℂ) → Representation ℂ (FiniteAdelicGL F (r + 1)) V)
    (C : Representation ℂ (standardInfiniteCompact F (r + 1)) V)
    (D : (Fin m → ℂ) → Enveloping →ₐ[ℂ] Module.End ℂ V)
    (hRhol : ∀ g v, (fun t => R t g v) ∈ finiteHolomorphicSections (Fin m → ℂ) V)
    (hDhol : ∀ X v, (fun t => D t (realGenerator X) v) ∈ finiteHolomorphicSections (Fin m → ℂ) V)
    (hR : ∀ t g v, j (R t g v) = hK.parameterRightAction (e t)
      (ofFinite F GL[F, r + 1] ((finiteHomeomorph F (r + 1)).symm g)) (j v))
    (hC : ∀ k v, j (C k v) = fun x : Adeles =>
      j v (x * ofInfinite F GL[F, r + 1] ((infiniteHomeomorph F (r + 1)).symm k.val)))
    (hD : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F GL[F, r + 1] hsmooth
      ∀ t X v, j (D t (realGenerator X) v) = hK.parameterDirectionalSection hsmooth (e t)
        ((infiniteRealLieAlgebraEquiv F (r + 1) hsmooth).symm X) (j v))
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : ∀ᶠ t in eisensteinConvergenceAnchorFilter root hA hT e,
      EisensteinSeriesInjectiveOn F r hK (e t) j π.range)
    (hProjection : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S →
      ∃ b : Operators, ∀ t v, v ∈ S → sectionOperatorAction R C D t b v = π v)
    (z : Fin m → ℂ) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (aW : Operators →ₐ[ℂ] Module.End ℂ W) (ha : Representation.IsIrreducible aW.toMonoidHom)
    (fin : Representation ℂ (FiniteAdelicGL F (r + 1)) W)
    (hfin : ∀ g, aW (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) = fin g) :
    letI := moduleOfAlgebraAction (sectionOperatorAction R C D z)
    letI := moduleOfAlgebraAction aW
    ∀ (S : Submodule Operators V) (q : S →ₗ[Operators] W), Function.Surjective q →
      ∀ y : W, y ≠ 0 →
        (∀ x : S, q x = y → ∃ x' : S, x'.val = π x.val ∧ q x' = y) →
        ∃ Q : IrreducibleOperatorSubquotient F r,
          Nonempty (Q.subquotient.finiteRepresentation.Equiv fin) := by
  let := moduleOfAlgebraAction (sectionOperatorAction R C D z)
  let := moduleOfAlgebraAction aW
  intro S q hq y hy hπ
  obtain ⟨U, u, hu⟩ := exists_freeOperatorQuotient_of_adelic_projected_specialization F r π
    rho hsmooth hcalc hN hrho hG root hA hT hU hK hmax hKstandard hKinf e j hAut hH hSmooth
    R C D hRhol hDhol hR hC hD hcont hinj hProjection z aW ha S q hq y hy hπ
  exact exists_irreducibleOperatorSubquotient_of_freeModule F r aW ha fin hfin U u hu

end Langlands.Global.EisensteinJet
