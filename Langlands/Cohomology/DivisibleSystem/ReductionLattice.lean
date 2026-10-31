import Langlands.Cohomology.DivisibleSystem.ReductionAdic
import Langlands.Shimura.Coefficients.HarrisLattice

/-!
# Harris's stable coefficient lattices as `ℓ`-divisible systems

Harris's inverse system `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` of reductions of a stable lattice `𝓛` is modelled by
the published `reductionTower ℓ` and, when multiplication by `ℓ` is a monomorphism, by the
`ℓ`-divisible system `reductionSystem ℓ`. This file compares these with the published torsion
systems `Langlands.Shimura.Coefficients.torsionSystem` of actions on modules, and applies them to
the published stable lattices of Harris's coefficient representations.

* For an action `M` of a group on an `R`-module, `reductionTowerActionIso ℓ M` identifies the
  tower `{M / ℓ ^ m M}` in `Action (ModuleCat R) G` with `torsionSystem (ℓ) M`; at each level it
  sends the class of `x` to the class of `x` (`reductionπ_reductionActionIso_hom`).
* `mono_powSMul_action_iff`: multiplication by `ℓ` on an action is a monomorphism exactly when
  multiplication by `ℓ` on the underlying module is injective; `mono_powSMul_latticeAction`
  proves this for a stable submodule of a module over a ring in which `ℓ` is a unit.
* `reductionTowerActionToRepIso ℓ M` transports the tower along `Rep.ActionToRep`, which is
  additive (`actionToRep_additive`).
* `harrisReductionSystem ℓ ρ p U` is the `ℓ`-divisible system `{𝓛 / ℓ ^ m 𝓛}` of Harris's
  stable lattice `𝓛 = harrisLattice ρ p U` in `(L ⊗ ℚ_p) ⊗_L W`, for a nonzero natural number
  `ℓ`; `harrisReductionSystemTowerIso` identifies its tower with `torsionSystem (ℓ)` of the
  lattice.
* `stableLatticeReductionSystem ℓ Λ` is the same construction for a stable lattice `Λ` at one
  place `l` of `L`, and `stableLatticeReductionSystemTowerIso` identifies its tower with
  `Λ.system (ℓ)`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe w v u

namespace DivisibleSystem

section Action

variable (ℓ : ℕ) {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- The underlying module of `M / ℓ ^ m M` is the quotient `M / (ℓ) ^ m M`. -/
def reductionActionVIso (M : Action (ModuleCat.{w} R) G) (m : ℕ) :
    ((reductionTower ℓ M).obj (op m)).V ≅
      (Shimura.Coefficients.torsionAction (Ideal.span {(ℓ : R)}) M m).V :=
  reductionCompIso ℓ (Action.forget (ModuleCat.{w} R) G) M m ≪≫
    reductionAdicIso ℓ ((Action.forget (ModuleCat.{w} R) G).obj M) m

@[reassoc]
lemma reductionπ_hom_reductionActionVIso_hom (M : Action (ModuleCat.{w} R) G) (m : ℕ) :
    (reductionπ ℓ M m).hom ≫ (reductionActionVIso ℓ M m).hom =
      (Coefficients.AdicSystem.quotientMap (Ideal.span {(ℓ : R)}) m).app M.V :=
  (map_reductionπ_reductionCompIso_hom_assoc ℓ (Action.forget (ModuleCat.{w} R) G) M m _).trans
    (reductionπ_reductionAdicIso_hom ℓ ((Action.forget (ModuleCat.{w} R) G).obj M) m)

instance (M : Action (ModuleCat.{w} R) G) (m : ℕ) : Epi (reductionπ ℓ M m).hom :=
  Functor.map_epi (Action.forget (ModuleCat.{w} R) G) (reductionπ ℓ M m)

/-- For an action `M` of a group on an `R`-module, the reduction `M / ℓ ^ m M` is the published
torsion action `M / (ℓ) ^ m M`. -/
def reductionActionIso (M : Action (ModuleCat.{w} R) G) (m : ℕ) :
    (reductionTower ℓ M).obj (op m) ≅
      Shimura.Coefficients.torsionAction (Ideal.span {(ℓ : R)}) M m :=
  Action.mkIso (reductionActionVIso ℓ M m) (fun g => by
    rw [← cancel_epi (reductionπ ℓ M m).hom, ← Category.assoc, ← (reductionπ ℓ M m).comm g,
      Category.assoc, reductionπ_hom_reductionActionVIso_hom,
      reductionπ_hom_reductionActionVIso_hom_assoc]
    exact (Coefficients.AdicSystem.quotientMap (Ideal.span {(ℓ : R)}) m).naturality (M.ρ g))

@[reassoc (attr := simp)]
lemma reductionπ_reductionActionIso_hom (M : Action (ModuleCat.{w} R) G) (m : ℕ) :
    reductionπ ℓ M m ≫ (reductionActionIso ℓ M m).hom =
      Shimura.Coefficients.torsionQuotientMap (Ideal.span {(ℓ : R)}) M m := by
  apply Action.Hom.ext
  exact reductionπ_hom_reductionActionVIso_hom ℓ M m

/-- For an action `M` of a group on an `R`-module, the tower `{M / ℓ ^ m M}` is the published
torsion system `Shimura.Coefficients.torsionSystem (ℓ) M`. -/
def reductionTowerActionIso (M : Action (ModuleCat.{w} R) G) :
    reductionTower ℓ M ≅ Shimura.Coefficients.torsionSystem (Ideal.span {(ℓ : R)}) M :=
  NatIso.ofComponents (fun m => reductionActionIso ℓ M m.unop) (by
    intro n m f
    induction m using Opposite.rec with | op m =>
    induction n using Opposite.rec with | op n =>
    rw [← cancel_epi (reductionπ ℓ M n), reductionπ_map_assoc, reductionπ_reductionActionIso_hom,
      reductionπ_reductionActionIso_hom_assoc]
    apply Action.Hom.ext
    exact (congrArg (fun e => e.app M.V) (Coefficients.AdicSystem.quotientMap_transition
      (Ideal.span {(ℓ : R)}) (leOfHom f.unop))).symm)

@[simp]
lemma reductionTowerActionIso_hom_app (M : Action (ModuleCat.{w} R) G) (m : ℕ) :
    (reductionTowerActionIso ℓ M).hom.app (op m) = (reductionActionIso ℓ M m).hom :=
  rfl

/-- In a category of actions on `R`-modules, multiplication by `ℓ` is a monomorphism exactly
when multiplication by the scalar `ℓ` on the underlying module is injective. -/
lemma mono_powSMul_action_iff (M : Action (ModuleCat.{w} R) G) :
    Mono (powSMul ℓ 1 M) ↔ Function.Injective (fun x : M.V => (ℓ : R) • x) := by
  rw [← Functor.mono_map_iff_mono (Action.forget (ModuleCat.{w} R) G),
    map_powSMul, ModuleCat.mono_iff_injective]
  have h : ⇑(powSMul ℓ 1 ((Action.forget (ModuleCat.{w} R) G).obj M)).hom =
      fun x : M.V => (ℓ : R) • x :=
    funext fun x => by rw [powSMul_moduleCat_hom_apply, pow_one]
  rw [h]

/-- On the action of a group on a stable submodule `Λ` of a `K`-module, multiplication by `ℓ`
is a monomorphism when `ℓ` is a unit of `K`. -/
lemma mono_powSMul_latticeAction {K : Type*} [CommRing K] [Algebra R K] {V : Type w}
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (ρ : G →* (V ≃ₗ[K] V))
    (Λ : Submodule R V) (hΛ : Shimura.Coefficients.IsStable ρ Λ) (hℓ : IsUnit (ℓ : K)) :
    Mono (powSMul ℓ 1 (Shimura.Coefficients.latticeAction ρ Λ hΛ)) := by
  rw [mono_powSMul_action_iff]
  intro (x : Λ) (y : Λ) h
  change ((ℓ : R) • x : Λ) = (ℓ : R) • y at h
  have h' := congrArg Subtype.val h
  rw [Submodule.coe_smul, Submodule.coe_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
    ← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h'
  exact Subtype.ext ((hℓ.smul_left_cancel).mp h')

end Action

section Rep

variable (ℓ : ℕ) {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- The functor from actions on `R`-modules to representations is additive. -/
instance actionToRep_additive : (Rep.ActionToRep.{w} R G).Additive where
  map_add {_ _} _ _ := by
    ext1
    exact Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

/-- If multiplication by `ℓ` on an action `M` is a monomorphism, so is multiplication by `ℓ` on
the corresponding representation. -/
instance mono_powSMul_actionToRep (M : Action (ModuleCat.{w} R) G) [Mono (powSMul ℓ 1 M)] :
    Mono (powSMul ℓ 1 ((Rep.ActionToRep R G).obj M)) := by
  rw [← map_powSMul]
  infer_instance

/-- The representation attached to `M / ℓ ^ m M` is the reduction of the representation attached
to `M`. -/
def reductionTowerActionToRepIso (M : Action (ModuleCat.{w} R) G) :
    reductionTower ℓ M ⋙ Rep.ActionToRep R G ≅ reductionTower ℓ ((Rep.ActionToRep R G).obj M) :=
  reductionTowerCompIso ℓ (Rep.ActionToRep R G) M

end Rep

section Unit

/-- A nonzero natural number is a unit in every `ℚ`-algebra. -/
lemma isUnit_natCast_of_ratAlgebra (ℓ : ℕ) [NeZero ℓ] (K : Type*) [Ring K] [Algebra ℚ K] :
    IsUnit (ℓ : K) := by
  rw [← map_natCast (algebraMap ℚ K)]
  exact ((Nat.cast_ne_zero (R := ℚ)).mpr (NeZero.ne ℓ)).isUnit.map _

end Unit

section Harris

open Langlands.Global Langlands.Shimura Langlands.Shimura.Coefficients

variable (ℓ : ℕ) [NeZero ℓ]
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ)

section Whole

variable [Module.Finite L W] (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- On Harris's stable lattice in `(L ⊗ ℚ_p) ⊗_L W`, multiplication by a nonzero natural number
`ℓ` is a monomorphism. -/
instance mono_powSMul_harrisLatticeAction : Mono (powSMul ℓ 1 (harrisLatticeAction ρ p U)) :=
  mono_powSMul_latticeAction ℓ ((ρ.harrisAdelic p).comp U.subgroup.subtype)
    (harrisLattice ρ p U) (harrisLattice_stable ρ p U)
    (isUnit_natCast_of_ratAlgebra ℓ (L ⊗[ℚ] FiniteCompletion ℚ p))

/-- The `ℓ`-divisible system `{𝓛 / ℓ ^ m 𝓛}` of reductions of Harris's stable lattice `𝓛` in
`(L ⊗ ℚ_p) ⊗_L W`, as representations of the level `U`. -/
def harrisReductionSystem :
    DivisibleSystem (Action (ModuleCat.{u} (HarrisCoefficientIntegers L p)) U.subgroup) ℓ :=
  reductionSystem ℓ (harrisLatticeAction ρ p U)

/-- The tower of `harrisReductionSystem` is the published torsion system of Harris's lattice
for the ideal `(ℓ)`. -/
def harrisReductionSystemTowerIso :
    (harrisReductionSystem ℓ ρ p U).tower ≅
      torsionSystem (Ideal.span {(ℓ : HarrisCoefficientIntegers L p)})
        (harrisLatticeAction ρ p U) :=
  reductionTowerActionIso ℓ (harrisLatticeAction ρ p U)

end Whole

section Place

variable {ρ p} {l : FinitePlace L} [l.asIdeal.LiesOver p.asIdeal]
variable {U : Subgroup σ.FiniteAdelicPoints}

/-- A nonzero natural number is a unit in the completion `L_l`. -/
lemma isUnit_natCast_finiteCompletion : IsUnit (ℓ : FiniteCompletion L l) := by
  rw [← map_natCast (algebraMap L (FiniteCompletion L l))]
  exact ((Nat.cast_ne_zero (R := L)).mpr (NeZero.ne ℓ)).isUnit.map _

/-- On a stable lattice `Λ` in `L_l ⊗_L W`, multiplication by a nonzero natural number `ℓ` is a
monomorphism. -/
instance mono_powSMul_stableCoefficientLattice_action (Λ : StableCoefficientLattice ρ p l U) :
    Mono (powSMul ℓ 1 Λ.action) :=
  mono_powSMul_latticeAction ℓ ((ρ.placeAction p l).comp U.subtype) Λ.carrier Λ.stable
    (isUnit_natCast_finiteCompletion ℓ)

/-- The `ℓ`-divisible system `{Λ / ℓ ^ m Λ}` of reductions of a stable lattice `Λ` in
`L_l ⊗_L W`. -/
def stableLatticeReductionSystem (Λ : StableCoefficientLattice ρ p l U) :
    DivisibleSystem (Action (ModuleCat.{u} (CoefficientIntegers l)) U) ℓ :=
  reductionSystem ℓ Λ.action

/-- The tower of `stableLatticeReductionSystem ℓ Λ` is the published system of `Λ` for the ideal
`(ℓ)`. -/
def stableLatticeReductionSystemTowerIso (Λ : StableCoefficientLattice ρ p l U) :
    (stableLatticeReductionSystem ℓ Λ).tower ≅
      Λ.system (Ideal.span {(ℓ : CoefficientIntegers l)}) :=
  reductionTowerActionIso ℓ Λ.action

end Place

end Harris

end DivisibleSystem

end Langlands.Cohomology
