import Langlands.Representation.Families.RenardFamilyInductionBaseChangeProof
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Plancherel.UnramifiedUniversalTwist
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Category.Twist
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.GroupScheme.Reductive.Basic

/-!
# Fibers of the induced universal unramified family

Let `P = MN` be a represented rational parabolic of `G`, `(σ, W)` a smooth representation of
`M(F)`, `B` the published algebra of regular functions on the unramified characters of a
family of norms `ν` on `M(F)`, and `ρ_B` the universal unramified family `B ⊗ W`. For an
unramified character `ψ`, and `ℂ` regarded as a `B`-algebra through evaluation at `ψ`, the
specialization `ℂ ⊗_B i_P^G(ρ_B)` of the induced family is isomorphic to the published
complex induction `i_P^G(σ ⊗ ψ)` (`leviInductionFunctor`). Hence it is irreducible as soon as
`i_P^G(σ ⊗ ψ)` is (`isIrreducible_supercuspidalFamilyFiber`, through the general
`isIrreducible_baseChange_leviInduced`).

The isomorphism is the composite of three representation equivalences:

* base change commutes with induction (`exists_leviInducedBaseChangeRepEquiv`, repackaging
  the published `exists_leviInducedBaseChangeEquiv`, VI.8.2);
* the fiber of `ρ_B` at `ψ` is the twist `σ ⊗ ψ` (`universalFiberEquiv`, VI.8.1 Example),
  transported through the induction (`leviInducedEquiv`);
* the family induction at `B = ℂ` is the published complex induction, because the radical is
  unimodular (`leviInducedComplexEquiv`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Renard.AlgebraicFamily

universe u v uA uB uC uE uG uH uI uV uW

namespace SupercuspidalFiber

/-- Irreducibility transports along an equivariant linear equivalence. -/
theorem isIrreducible_of_equiv {H : Type uH} [Group H] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {σ : Representation ℂ H W} (e : ρ.Equiv σ)
    (hi : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at hi ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.bijective).mp hi

end SupercuspidalFiber

section Fiber

variable {A : Type uA} [CommRing A] [Algebra ℂ A] [Algebra A ℂ] [IsScalarTower ℂ A ℂ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The fiber `ℂ ⊗[A] (A ⊗[ℂ] V)` of the extended module `A ⊗[ℂ] V` along an `A`-algebra
structure on `ℂ`, identified with `V` by cancelling the base change. -/
def universalFiberCancel : ℂ ⊗[A] (A ⊗[ℂ] V) ≃ₗ[ℂ] V :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange ℂ A ℂ ℂ V).trans (TensorProduct.lid ℂ V)

theorem universalFiberCancel_tmul (c : ℂ) (b : A) (v : V) :
    universalFiberCancel (c ⊗ₜ[A] (b ⊗ₜ[ℂ] v)) = (algebraMap A ℂ b * c) • v := by
  change (b • c) • v = _
  rw [Algebra.smul_def]

/-- The fiber identification intertwines a base-changed action with an action on `V` as soon
as it does so on pure tensors `c ⊗ (b ⊗ v)`. -/
theorem universalFiberCancel_baseChange {H : Type uH} [Group H]
    (ρ : Representation A H (A ⊗[ℂ] V)) (σ : Representation ℂ H V) (g : H)
    (h : ∀ (c : ℂ) (b : A) (v : V),
      universalFiberCancel (c ⊗ₜ[A] ρ g (b ⊗ₜ[ℂ] v)) =
        σ g (universalFiberCancel (c ⊗ₜ[A] (b ⊗ₜ[ℂ] v))))
    (x : ℂ ⊗[A] (A ⊗[ℂ] V)) :
    universalFiberCancel (baseChange ℂ ρ g x) = σ g (universalFiberCancel x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | tmul b v => rw [baseChange_tmul, h]
    | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hz, map_add, map_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Fiber

section Universal

variable {H : Type uG} [Group H] [TopologicalSpace H] {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local instance fiberTensorAddCommGroup :
    AddCommGroup (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] V) :=
  TensorProduct.addCommGroup

local instance fiberTensorModule :
    Module (Plancherel.unramifiedRegularFunctions ν)
      (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] V) :=
  TensorProduct.leftModule

/-- An algebra structure of `ℂ` over `B` given by evaluation at an unramified character makes
`ℂ → B → ℂ` a scalar tower. -/
theorem isScalarTower_of_evaluation (ψ : Plancherel.unramifiedCharacters ν)
    [Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ]
    (hψ : ∀ b : Plancherel.unramifiedRegularFunctions ν,
      algebraMap (Plancherel.unramifiedRegularFunctions ν) ℂ b = b.val ψ) :
    IsScalarTower ℂ (Plancherel.unramifiedRegularFunctions ν) ℂ :=
  ⟨fun c b z => by
    rw [Algebra.smul_def (c • b) z, Algebra.smul_def b z, hψ, hψ, smul_eq_mul,
      Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]⟩

/-- The fiber identification intertwines the base change of the universal unramified family
of `π` with the twist `π ⊗ ψ`, when `ℂ` is a `B`-algebra through evaluation at `ψ`. -/
theorem universalFiberCancel_universal (ψ : Plancherel.unramifiedCharacters ν)
    [Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ]
    [IsScalarTower ℂ (Plancherel.unramifiedRegularFunctions ν) ℂ]
    (hψ : ∀ b : Plancherel.unramifiedRegularFunctions ν,
      algebraMap (Plancherel.unramifiedRegularFunctions ν) ℂ b = b.val ψ)
    (π : Representation ℂ H V) (g : H)
    (x : ℂ ⊗[Plancherel.unramifiedRegularFunctions ν]
      (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] V)) :
    universalFiberCancel
        (baseChange ℂ (Plancherel.universalUnramifiedRepresentation ν π) g x) =
      Langlands.twist ψ.val.toMonoidHom π g (universalFiberCancel x) := by
  refine universalFiberCancel_baseChange (Plancherel.universalUnramifiedRepresentation ν π)
    (Langlands.twist ψ.val.toMonoidHom π) g (fun c b v => ?_) x
  rw [Plancherel.universalUnramifiedRepresentation_tmul, universalFiberCancel_tmul,
    universalFiberCancel_tmul, hψ, hψ]
  change ((Plancherel.unramifiedEvaluationRegular ν g * b).val ψ * c) • π g v =
    ((ψ.val g : ℂˣ) : ℂ) • π g ((b.val ψ * c) • v)
  rw [map_smul, smul_smul]
  congr 1
  change ((ψ.val g : ℂ) * b.val ψ) * c = (ψ.val g : ℂ) * (b.val ψ * c)
  ring

/-- VI.8.1 Example for an arbitrary algebra structure of `ℂ` over `B` given by evaluation at
`ψ`: the specialization of the universal unramified family `ρ_B` of `π` at `ψ` is the twist
`π ⊗ ψ`, by `c ⊗ (b ⊗ v) ↦ c b(ψ) v`. -/
def universalFiberEquiv (ψ : Plancherel.unramifiedCharacters ν)
    [Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ]
    (hψ : ∀ b : Plancherel.unramifiedRegularFunctions ν,
      algebraMap (Plancherel.unramifiedRegularFunctions ν) ℂ b = b.val ψ)
    (π : Representation ℂ H V) :
    Representation.Equiv
      (baseChange ℂ (Plancherel.universalUnramifiedRepresentation ν π))
      (Langlands.twist ψ.val.toMonoidHom π) :=
  haveI := isScalarTower_of_evaluation ν ψ hψ
  Representation.Equiv.mk universalFiberCancel fun g =>
    LinearMap.ext (universalFiberCancel_universal ν ψ hψ π g)

end Universal

section Parabolic

/-- Restriction along a group homomorphism transports equivalences of representations. -/
def representationEquivComp {R : Type uB} [CommRing R] {H : Type uH} [Group H]
    {K : Type uG} [Group K] {V : Type uV} {W : Type uW} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {σ₁ : Representation R K V} {σ₂ : Representation R K W}
    (e : σ₁.Equiv σ₂) (f : H →* K) : Representation.Equiv (σ₁.comp f) (σ₂.comp f) :=
  Representation.Equiv.mk e.toLinearEquiv fun q => e.isIntertwining' (f q)

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- An equivalence of Levi families gives an equivalence of the inducing representations of
the parabolic. -/
def inducingRepresentationEquiv (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} {W : Type uW} [AddCommGroup V] [Module B V]
    [AddCommGroup W] [Module B W] {σ₁ : Representation B M V} {σ₂ : Representation B M W}
    (e : σ₁.Equiv σ₂) :
    (inducingRepresentation h hU σ₁).Equiv (inducingRepresentation h hU σ₂) :=
  representationEquivComp
    (Langlands.twistEquiv (inductionCharacter B U M hU h.levi_le_normalizer).toMonoidHom e)
    h.projection

end Parabolic

section Represented

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fiberAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction of families transports equivalences of Levi families. -/
def leviInducedEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    {B : Type uB} [CommRing B] [Algebra ℂ B] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module B V] [AddCommGroup W] [Module B W]
    {σ₁ : Representation B (rationalPoints M) V} {σ₂ : Representation B (rationalPoints M) W}
    (e : σ₁.Equiv σ₂) :
    (leviInducedRepresentation p l r hp hr hl hmul σ₁).Equiv
      (leviInducedRepresentation p l r hp hr hl hmul σ₂) :=
  letI := leviPointTopology l hl
  Induction.smoothInducedEquiv _ (inducingRepresentationEquiv _ _
    (representationEquivComp e (leviPointsEquiv p l hp hl).symm.toMonoidHom))

/-- The base change of the induced family is the induction of the base change, as an
equivalence of representations (VI.8.2). -/
theorem exists_leviInducedBaseChangeRepEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    (C : Type uC) [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C]
    {E : Type uE} [AddCommGroup E] [Module B E] (σ : Representation B (rationalPoints M) E)
    (hσ : letI := leviPointTopology l hl; IsSmooth σ) :
    Nonempty ((baseChange C (leviInducedRepresentation p l r hp hr hl hmul σ)).Equiv
      (leviInducedRepresentation p l r hp hr hl hmul (baseChange C σ))) := by
  obtain ⟨e, he, -⟩ := exists_leviInducedBaseChangeEquiv p l r hp hl hr hmul C σ hσ
  exact ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => he g x⟩

end Represented

section Complex

/-- Constant characters with values in `ℂ` itself are the characters themselves. -/
theorem constantCharacter_complex {H : Type uH} [Group H] (χ : H →* ℂˣ) :
    constantCharacter ℂ χ = χ :=
  MonoidHom.ext fun _ => Units.ext rfl

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fiberComplexAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- At `B = ℂ`, the normalized induction of families is the published complex induction
`leviInductionFunctor`: the two inducing representations agree, the radical being
unimodular. -/
def leviInducedComplexEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    (leviInducedRepresentation (B := ℂ) p l r hp hr hl hmul A.representation).Equiv
      ((leviInductionFunctor p l r hp hr hl hmul).obj A).representation :=
  letI := leviPointTopology l hl
  Induction.smoothInducedEquiv _ (Representation.Equiv.mk (LinearEquiv.refl ℂ A)
    fun q => by
      rw [inducingRepresentation_eq_twist_of_isUnimodularModulus _ _
        (isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1),
        constantCharacter_complex]
      rfl)

/-- The specialization `ℂ ⊗_B i_P^G(ρ)` of an induced smooth family is irreducible when the
specialization `ℂ ⊗_B ρ` is equivalent to a smooth complex representation `A` of `M(F)` whose
complex induction `i_P^G(A)` is irreducible. -/
theorem isIrreducible_baseChange_leviInduced (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    {B : Type uB} [CommRing B] [Algebra ℂ B] [Algebra B ℂ] [IsScalarTower ℂ B ℂ]
    {E : Type uE} [AddCommGroup E] [Module B E] (ρ : Representation B (rationalPoints M) E)
    (hρ : letI := leviPointTopology l hl; IsSmooth ρ)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (e : letI := leviPointTopology l hl; (baseChange ℂ ρ).Equiv A.representation)
    (hirr : letI := leviPointTopology l hl
      ((leviInductionFunctor p l r hp hr hl hmul).obj A).IsIrreducible) :
    (baseChange ℂ (leviInducedRepresentation p l r hp hr hl hmul ρ)).IsIrreducible := by
  obtain ⟨E₁⟩ := exists_leviInducedBaseChangeRepEquiv p l r hp hl hr hmul ℂ ρ hρ
  exact SupercuspidalFiber.isIrreducible_of_equiv
    (E₁.trans ((leviInducedEquiv p l r hp hl hr hmul e).trans
      (leviInducedComplexEquiv p l r hp hl hr hmul A))).symm hirr

end Complex

section Main

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fiberMainAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option synthInstance.maxHeartbeats 400000 in
/-- Fiber irreducibility for the induced universal unramified family (the input of VI.8.6
Example): for a smooth representation `σ` of `M(F)`, an unramified character `ψ` and the
evaluation `χ : B → ℂ` at `ψ`, the specialization `ℂ ⊗_{B,χ} i_P^G(ρ_B)` is irreducible as
soon as the complex induction `i_P^G(σ ⊗ ψ)` is. The binders follow
`SupercuspidalFamilyEndomorphismStatement`; the conclusion is the fiber premise of
`EndomorphismScalarStatement` at `χ`. -/
theorem isIrreducible_supercuspidalFamilyFiber (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (W : Type v) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (rationalPoints M) W)
      (hσ : IsSmooth σ),
      let ν := fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul
      letI : AddCommGroup (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) :=
        TensorProduct.addCommGroup
      letI : Module (Plancherel.unramifiedRegularFunctions ν)
          (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) := TensorProduct.leftModule
      let ρB := Plancherel.universalUnramifiedRepresentation ν σ
      ∀ (ψ : Plancherel.unramifiedCharacters ν)
        (χ : Plancherel.unramifiedRegularFunctions ν →ₐ[ℂ] ℂ),
        (∀ b, χ b = b.val ψ) →
        ((leviInductionFunctor p l r hp hr hl hmul).obj
            ((SmoothRep.of σ hσ).twist ψ.val.toMonoidHom
              (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))).IsIrreducible →
        letI : Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ := χ.toRingHom.toAlgebra
        Representation.IsIrreducible
          ((Module.End.baseChangeHom (Plancherel.unramifiedRegularFunctions ν) ℂ
              (LeviInduced p l r hp hr hl hmul ρB)).toMonoidHom.comp
            (leviInducedRepresentation p l r hp hr hl hmul ρB)) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro W _ _ σ hσ ν ρB ψ χ hχ hirr
  let : AddCommGroup (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) :=
    TensorProduct.addCommGroup
  let : Module (Plancherel.unramifiedRegularFunctions ν)
      (Plancherel.unramifiedRegularFunctions ν ⊗[ℂ] W) := TensorProduct.leftModule
  have hν : ∀ i, Continuous (ν i) := by
    have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    exact fun i => (Plancherel.rationalNormContinuousCharacter M i).continuous
  have hρB : IsSmooth ρB :=
    Plancherel.isSmooth_universalUnramifiedRepresentation_of_continuous ν hν σ hσ
  have := compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp
  let : Algebra (Plancherel.unramifiedRegularFunctions ν) ℂ := χ.toRingHom.toAlgebra
  have hψ : ∀ b : Plancherel.unramifiedRegularFunctions ν,
      algebraMap (Plancherel.unramifiedRegularFunctions ν) ℂ b = b.val ψ := hχ
  have : IsScalarTower ℂ (Plancherel.unramifiedRegularFunctions ν) ℂ :=
    IsScalarTower.of_algebraMap_eq fun c => (χ.commutes c).symm
  exact isIrreducible_baseChange_leviInduced p l r hp hl hr hmul ρB hρB
    ((SmoothRep.of σ hσ).twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ))
    (universalFiberEquiv ν ψ hψ σ) hirr

end Main

end Langlands.Renard.AlgebraicFamily
