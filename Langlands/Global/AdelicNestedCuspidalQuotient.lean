import Langlands.Global.AdelicParabolicConvolution
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite-dimensional spaces detected by nested cuspidal tests -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G fam.i fam.ν

/-- The moderate functions on the parabolic quotient, represented inside the continuous
functions on the adelic group. -/
def continuousParabolicModerateSubmodule (J : Idx) : Submodule ℂ C(A, ℂ) :=
  (fam.parabolicModerateSubmodule rho hN J).comap (ContinuousMap.coeFnLinearMap ℂ)

theorem mem_continuousParabolicModerateSubmodule_iff (J : Idx) (f : C(A, ℂ)) :
    f ∈ fam.continuousParabolicModerateSubmodule rho hN J ↔
      fam.IsModerateContinuousOnParabolic rho J f := by
  change ((f : A → ℂ) ∈ fam.parabolicModerateSubmodule rho hN J) ↔ _
  constructor
  · intro hf
    exact ⟨IsParabolicGeneratorInvariant.isLeftInvariantUnder fam hf.1, f.continuous,
      (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).2 hf.2.2⟩
  · intro hf
    refine ⟨⟨fun v x => hf.1 _ (Subgroup.mem_sup_left v.property) x, ?_⟩, f.continuous,
      (hasModerateGrowthFunction_iff_hasHeightGrowth hN _).1 hf.2.2⟩
    intro m x
    exact hf.1 _ (Subgroup.mem_sup_right ⟨m, rfl⟩) x

variable (J : StandardIndex F G fam.i fam.ν)

private theorem hasIntegrableConstantTerm_of_mem_moderate (Q : {Q : Idx // Q ≤ J})
    (f : fam.continuousParabolicModerateSubmodule rho hN J) :
    fam.HasIntegrableConstantTerm Q.val (f : C(A, ℂ)) := by
  intro x
  exact fam.integrable_constantTermIntegrand_of_le J Q.val Q.property
    (f : C(A, ℂ)).continuous
    ((fam.mem_continuousParabolicModerateSubmodule_iff rho hN J f).1 f.property).1 x

/-- The normalized constant term along a smaller standard parabolic is linear on the
moderate continuous functions of the inducing quotient. -/
def nestedConstantTermOnModerate (Q : {Q : Idx // Q ≤ J}) :
    fam.continuousParabolicModerateSubmodule rho hN J →ₗ[ℂ] (A → ℂ) where
  toFun f := fam.constantTerm Q.val (f : C(A, ℂ))
  map_add' f g := fam.constantTerm_add_of_hasIntegrableConstantTerm
    (fam.hasIntegrableConstantTerm_of_mem_moderate rho hN J Q f)
    (fam.hasIntegrableConstantTerm_of_mem_moderate rho hN J Q g)
  map_smul' c f := fam.constantTerm_const_smul Q.val c (f : C(A, ℂ))

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))

/-- The nested constant terms modulo the absolutely convergent cusp-test annihilators. -/
def nestedCuspidalQuotientMap :
    fam.continuousParabolicModerateSubmodule rho hN J →ₗ[ℂ]
      (∀ Q : {Q : Idx // Q ≤ J}, (A → ℂ) ⧸ fam.cuspidalAnnihilator Kinf rho Q.val) :=
  LinearMap.pi fun Q =>
    (fam.cuspidalAnnihilator Kinf rho Q.val).mkQ.comp
      (fam.nestedConstantTermOnModerate rho hN J Q)

/-- The parabolic vanishing criterion makes the map to the nested cuspidal quotients
injective. -/
theorem nestedCuspidalQuotientMap_injective_of_vanishing
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (Ktests : Subgroup A) (hmax : IsMaximalCompactSubgroup F G Ktests)
    (hIwasawa : ∀ Q : Idx, IsIwasawaCompact (fam.p Q) Ktests)
    (hrho : IsClosedSubgroup rho) :
    Function.Injective
      (fam.nestedCuspidalQuotientMap rho hN J (Ktests.comap (ofInfinite F G).toMonoidHom)) := by
  let T := fam.nestedCuspidalQuotientMap rho hN J (Ktests.comap (ofInfinite F G).toMonoidHom)
  have hzero (f : fam.continuousParabolicModerateSubmodule rho hN J) (hf : T f = 0) : f = 0 := by
    have hmoderate := (fam.mem_continuousParabolicModerateSubmodule_iff rho hN J f).1 f.property
    have hz : ((f : C(A, ℂ)) : A → ℂ) = 0 :=
      hvan F G fam Ktests hmax hIwasawa rho hN hrho J f hmoderate (fun Q hQP => by
        have heq := congrFun hf (⟨Q, hQP⟩ : {Q : Idx // Q ≤ J})
        exact (Submodule.Quotient.mk_eq_zero _).1 heq)
    apply Subtype.ext
    ext x
    exact congrFun hz x
  change Function.Injective T
  intro f g hfg
  exact sub_eq_zero.mp (hzero (f - g) ((map_sub T f g).trans (sub_eq_zero.mpr hfg)))

variable (V : ∀ Q : {Q : StandardIndex F G fam.i fam.ν // Q ≤ J},
  Submodule ℂ ((AdelicGroupPoints F G → ℂ) ⧸ fam.cuspidalAnnihilator Kinf rho Q.val))

/-- Impose a prescribed subspace constraint on each nested constant term modulo its
cuspidal annihilator, within the moderate continuous functions of the parabolic quotient. -/
def cuspidalConstraintSpace : Submodule ℂ C(A, ℂ) :=
  ((Submodule.pi Set.univ V).comap (fam.nestedCuspidalQuotientMap rho hN J Kinf)).map
    (fam.continuousParabolicModerateSubmodule rho hN J).subtype

theorem mem_cuspidalConstraintSpace_iff (f : C(A, ℂ)) :
    f ∈ fam.cuspidalConstraintSpace rho hN J Kinf V ↔
      fam.IsModerateContinuousOnParabolic rho J f ∧
        ∀ Q : {Q : Idx // Q ≤ J},
          (fam.cuspidalAnnihilator Kinf rho Q.val).mkQ (fam.constantTerm Q.val f) ∈ V Q := by
  constructor
  · rintro ⟨⟨f, hf⟩, hV, rfl⟩
    exact ⟨(fam.mem_continuousParabolicModerateSubmodule_iff rho hN J f).1 hf,
      fun Q => hV Q (Set.mem_univ Q)⟩
  · rintro ⟨hf, hV⟩
    exact ⟨⟨f, (fam.mem_continuousParabolicModerateSubmodule_iff rho hN J f).2 hf⟩,
      fun Q _ => hV Q, rfl⟩

/-- Finite-dimensional nested constraints cut out a finite-dimensional space when
the nested cuspidal tests detect every moderate continuous function. -/
theorem finiteDimensional_cuspidalConstraintSpace
    (hinj : Function.Injective (fam.nestedCuspidalQuotientMap rho hN J Kinf))
    (hV : ∀ Q : {Q : Idx // Q ≤ J}, FiniteDimensional ℂ (V Q)) :
    FiniteDimensional ℂ (fam.cuspidalConstraintSpace rho hN J Kinf V) := by
  let : Finite Idx :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).finite_subsets.to_subtype
  let : Finite {Q : Idx // Q ≤ J} :=
    Finite.of_injective (fun Q : {Q : Idx // Q ≤ J} => Q.val) Subtype.val_injective
  let : ∀ Q : {Q : Idx // Q ≤ J}, Module.Finite ℂ (V Q) := hV
  let : Module.Finite ℂ (∀ Q : {Q : Idx // Q ≤ J}, V Q) := Module.Finite.pi
  let : IsNoetherian ℂ (∀ Q : {Q : Idx // Q ≤ J}, V Q) :=
    isNoetherian_of_isNoetherianRing_of_finite ℂ (∀ Q : {Q : Idx // Q ≤ J}, V Q)
  let C := fam.nestedCuspidalQuotientMap rho hN J Kinf
  let W : Submodule ℂ (fam.continuousParabolicModerateSubmodule rho hN J) :=
    (Submodule.pi Set.univ V).comap C
  let L : W →ₗ[ℂ] (∀ Q : {Q : Idx // Q ≤ J}, V Q) :=
    LinearMap.pi fun Q => (((LinearMap.proj Q).comp C).comp W.subtype).codRestrict
      (V Q) (fun f => f.property Q (Set.mem_univ Q))
  have hL : Function.Injective L := by
    intro f g heq
    apply Subtype.ext (hinj (funext fun Q => ?_))
    exact congrArg Subtype.val (congrFun heq Q)
  let : Module.Finite ℂ W := Module.Finite.of_injective L hL
  exact Module.Finite.map W (fam.continuousParabolicModerateSubmodule rho hN J).subtype

/-- To preserve the continuous function space cut out by the cuspidal constraints, it
suffices that the transported convolution formula preserves each constrained class. -/
theorem twistedConvolutionEnd_mem_cuspidalConstraintSpace
    [IsClosedImmersion (fam.p J).hom.hom.left]
    {Kout : Subgroup A} (hK : IsIwasawaCompact (fam.p J) Kout)
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F (fam.P J))
    {f : C(A, ℂ)} (hf : f ∈ fam.cuspidalConstraintSpace rho hN J Kinf V)
    (hV : ∀ Q : {Q : Idx // Q ≤ J},
      (fam.cuspidalAnnihilator Kinf rho Q.val).mkQ (fam.constantTerm Q.val f) ∈ V Q →
      (fam.cuspidalAnnihilator Kinf rho Q.val).mkQ
        (hK.parameterTwist
          (rightConvolution F G h (hK.parameterTwist (fam.constantTerm Q.val f) lam)) (-lam)) ∈ V Q) :
    hK.twistedConvolutionEnd hsmooth hh lam f ∈ fam.cuspidalConstraintSpace rho hN J Kinf V := by
  obtain ⟨hf, hfV⟩ := (fam.mem_cuspidalConstraintSpace_iff rho hN J Kinf V f).1 hf
  obtain ⟨hres, hct⟩ := parabolicTwistedConvolution F G fam J Kout hK rho hN hsmooth h hh lam f hf
  refine (fam.mem_cuspidalConstraintSpace_iff rho hN J Kinf V _).2 ⟨hres, fun Q => ?_⟩
  rw [hct Q.val Q.property]
  exact hV Q (hfV Q)

end Langlands.Global.StandardParabolicFamily
