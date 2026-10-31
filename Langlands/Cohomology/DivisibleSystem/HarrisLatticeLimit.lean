import Langlands.Cohomology.DivisibleSystem.HarrisLatticeHom
import Langlands.Cohomology.DivisibleSystem.ReductionLimit
import Langlands.ClassField.Global.LocalUnitPowers
import Langlands.Shimura.Coefficients.HarrisReduction

/-!
# Harris's lattice as the inverse limit of its reductions

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §4, p.311: "let
`𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of `𝒪`-modules, and the
inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ`"; proof of
Proposition 4.10, p.312: the integral statement (4.10.4) with coefficients `𝓛`.

The published `ReductionLimit` shows, for representations in `Rep R G`, that `L` is the inverse
limit of `L / ℓ ^ m L` exactly when `L` is `ℓ`-adically complete, and that then
`Hom_R(A, L)` is the inverse limit of `Hom_R(A, L / ℓ ^ m L)`; the completeness of Harris's ring
`𝒪` was left as a hypothesis. This module proves it for the published model
`∏_{l | p} 𝒪_l` and applies the limit results to Harris's lattice `𝓛`:

* `isAdicComplete_of_le_of_pow_le`: completeness for an ideal `J` gives completeness for an
  ideal `I ≤ J` with `J ^ k ≤ I`;
* `smodEq_pi_span_singleton_iff`, `isAdicComplete_pi_span_singleton`,
  `isAdicComplete_pi_span_singleton_self`: a product of modules over a product of rings,
  complete for the principal ideals `(a i)`, is complete for `(a)`;
* `natCast_mem_maximalIdeal_coefficientIntegers`, `isAdicComplete_coefficientIntegers`: if the
  place `p` of `ℚ` divides `ℓ ≠ 0` and `l` lies above `p`, `𝒪_l` is `ℓ`-adically complete;
* `mapReductionConeIso`, `isLimitReductionConeMap`, `isLimitReductionConeOfMap`: the cone of
  projections `L ⟶ L / ℓ ^ m L` under an additive functor preserving cokernels;
* `nonempty_isLimit_reductionCone_action_iff`, `isLimitReductionConeAction`,
  `reductionLimitIsoAction`, `reductionSystemLimitIsoAction`: the limit criterion for actions
  of a group on modules, through the equivalence `Rep.ActionToRep`;
* `isAdicComplete_harrisCoefficientIntegers`, `isAdicComplete_harrisLattice`,
  `harrisReductionSystemLimitIso`, `harrisLatticeTrivialReductionSystemLimitIso`,
  `harrisPermutationIhomSystemLimitIso`: for `p` dividing `ℓ ≠ 0`, `∏_{l | p} 𝒪_l` and `𝓛` are
  `ℓ`-adically complete, `𝓛` is the inverse limit of `{𝓛 / ℓ ^ m 𝓛}` as a representation of the
  level `U`, and `Hom(M[X], 𝓛)` is the inverse limit of Harris's system
  `m ↦ Hom(M[X], 𝓛 / ℓ ^ m 𝓛)`;
* `isAdicComplete_stableCoefficientLattice`, `stableLatticeReductionSystemLimitIso`: the same
  for a stable lattice at one place `l` above `p`.

The statements and proofs are ours.
-/

noncomputable section

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open scoped NumberField

namespace Langlands.Cohomology.DivisibleSystem

section Adic

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- If `I ≤ J` and `J ^ k ≤ I`, a `J`-adically complete module is `I`-adically complete. -/
theorem isAdicComplete_of_le_of_pow_le {I J : Ideal R} (hIJ : I ≤ J) {k : ℕ} (hk : J ^ k ≤ I)
    (h : IsAdicComplete J M) : IsAdicComplete I M where
  haus' x hx := h.haus' x fun n =>
    (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))
  prec' f hf := by
    obtain ⟨L, hL⟩ := h.prec' f fun {m n} hmn =>
      (hf hmn).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ m))
    refine ⟨L, fun n => ?_⟩
    have hle : J ^ ((k + 1) * n) ≤ I ^ n :=
      calc J ^ ((k + 1) * n) ≤ J ^ (k * n) :=
            Ideal.pow_le_pow_right (Nat.mul_le_mul_right n k.le_succ)
        _ = (J ^ k) ^ n := pow_mul J k n
        _ ≤ I ^ n := Ideal.pow_right_mono hk n
    have hn : n ≤ (k + 1) * n := Nat.le_mul_of_pos_left n k.succ_pos
    exact (hf hn).trans ((hL ((k + 1) * n)).mono (Submodule.smul_mono_left hle))

end Adic

section Pi

open Langlands.Shimura.Coefficients

variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] (V : ι → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module (R i) (V i)] (a : (i : ι) → R i)

/-- Over a product of rings, congruence modulo `a ^ n` is congruence modulo `a i ^ n` in every
component. -/
lemma smodEq_pi_span_singleton_iff (n : ℕ) (x y : (i : ι) → V i) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule ((i : ι) → R i) ((i : ι) → V i))] ↔
      ∀ i, x i ≡ y i [SMOD ((Ideal.span {a i}) ^ n • ⊤ : Submodule (R i) (V i))] := by
  simp only [SModEq.sub_mem, mem_principalPower_smul_top]
  constructor
  · rintro ⟨z, hz⟩ i
    exact ⟨z i, congrFun hz i⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

/-- A product of modules `V i` over rings `R i`, each complete for the `a i`-adic topology, is
complete for the `a`-adic topology over `∏ i, R i`. -/
theorem isAdicComplete_pi_span_singleton
    (h : ∀ i, IsAdicComplete (Ideal.span {a i}) (V i)) :
    IsAdicComplete (Ideal.span {a}) ((i : ι) → V i) where
  haus' x hx := funext fun i => (h i).haus' (x i) fun n =>
    (smodEq_pi_span_singleton_iff R V a n x 0).1 (hx n) i
  prec' f hf := by
    choose L hL using fun i => (h i).prec' (fun n => f n i) fun {m n} hmn =>
      (smodEq_pi_span_singleton_iff R V a m (f m) (f n)).1 (hf hmn) i
    exact ⟨L, fun n => (smodEq_pi_span_singleton_iff R V a n (f n) L).2 fun i => hL i n⟩

/-- A product of rings `R i`, each complete for the `a i`-adic topology, is complete for the
`a`-adic topology. -/
theorem isAdicComplete_pi_span_singleton_self
    (h : ∀ i, IsAdicComplete (Ideal.span {a i}) (R i)) :
    IsAdicComplete (Ideal.span {a}) ((i : ι) → R i) :=
  isAdicComplete_pi_span_singleton R R a h

end Pi

section Local

open Langlands.Global Langlands.Shimura.Coefficients IsDedekindDomain

variable (ℓ : ℕ) {L : Type u} [Field L] [NumberField L] {p : FinitePlace ℚ}

/-- If the place `p` of `ℚ` divides `ℓ` and `l` lies above `p`, then `ℓ` lies in the maximal
ideal of `𝒪_l`. -/
lemma natCast_mem_maximalIdeal_coefficientIntegers (hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal] :
    (ℓ : CoefficientIntegers l) ∈ maximalIdeal (CoefficientIntegers l) := by
  have h₁ : (ℓ : 𝓞 L) ∈ l.asIdeal := by
    have := (Ideal.mem_of_liesOver l.asIdeal p.asIdeal (ℓ : 𝓞 ℚ)).1 hℓ
    rwa [map_natCast] at this
  rw [← IsLocalRing.residue_eq_zero_iff,
    ← map_natCast (algebraMap (𝓞 L) (CoefficientIntegers l)) ℓ,
    ← Langlands.Global.CompletionResidue.adicResidueEquiv_mk,
    Ideal.Quotient.eq_zero_iff_mem.2 h₁, map_zero]

/-- If the place `p` of `ℚ` divides `ℓ ≠ 0` and `l` lies above `p`, then `𝒪_l` is complete for
the `ℓ`-adic topology. -/
theorem isAdicComplete_coefficientIntegers [NeZero ℓ] (hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (l : FinitePlace L) [l.asIdeal.LiesOver p.asIdeal] :
    IsAdicComplete (Ideal.span {(ℓ : CoefficientIntegers l)}) (CoefficientIntegers l) := by
  let : CharZero (FiniteCompletion L l) := Algebra.charZero_of_charZero L (FiniteCompletion L l)
  have hne : (ℓ : CoefficientIntegers l) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (CoefficientIntegers l)
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  refine isAdicComplete_of_le_of_pow_le (J := maximalIdeal (CoefficientIntegers l)) ?_ (k := k)
    ?_ (Langlands.ClassField.Global.isAdicComplete_adicCompletionIntegers l)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_maximalIdeal_coefficientIntegers ℓ hℓ l
  · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.span_singleton_eq_span_singleton.2 hk.symm]

end Local

section Transport

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (ℓ : ℕ) (F : C ⥤ D) [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F]

/-- The image under `F` of the cone of projections `L ⟶ L / ℓ ^ m L`, composed with
`reductionTowerCompIso`, is the cone of projections of `F L`. -/
def mapReductionConeIso (L : C) :
    (Cone.postcompose (reductionTowerCompIso ℓ F L).hom).obj (F.mapCone (reductionCone ℓ L)) ≅
      reductionCone ℓ (F.obj L) :=
  Cone.ext (Iso.refl _) fun m => by
    induction m using Opposite.rec with | op m =>
    exact (map_reductionπ_reductionCompIso_hom ℓ F L m).trans (Category.id_comp _).symm

variable {ℓ F}

/-- If `F` preserves limits of shape `ℕᵒᵖ` and `L` is the inverse limit of `L / ℓ ^ m L`, then
`F L` is the inverse limit of `F L / ℓ ^ m F L`. -/
def isLimitReductionConeMap [PreservesLimitsOfShape ℕᵒᵖ F] {L : C}
    (h : IsLimit (reductionCone ℓ L)) : IsLimit (reductionCone ℓ (F.obj L)) :=
  ((IsLimit.postcomposeHomEquiv (reductionTowerCompIso ℓ F L) _).symm
    (isLimitOfPreserves F h)).ofIsoLimit (mapReductionConeIso ℓ F L)

/-- If `F` reflects limits of shape `ℕᵒᵖ` and `F L` is the inverse limit of `F L / ℓ ^ m F L`,
then `L` is the inverse limit of `L / ℓ ^ m L`. -/
def isLimitReductionConeOfMap [ReflectsLimitsOfShape ℕᵒᵖ F] {L : C}
    (h : IsLimit (reductionCone ℓ (F.obj L))) : IsLimit (reductionCone ℓ L) :=
  isLimitOfReflects F ((IsLimit.postcomposeHomEquiv (reductionTowerCompIso ℓ F L) _)
    (h.ofIsoLimit (mapReductionConeIso ℓ F L).symm))

end Transport

section Action

variable (ℓ : ℕ) {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- An action `M` of `G` on an `R`-module is the inverse limit of `M / ℓ ^ m M` along the
projections exactly when the underlying module is `ℓ`-adically complete. -/
theorem nonempty_isLimit_reductionCone_action_iff (M : Action (ModuleCat.{w} R) G) :
    Nonempty (IsLimit (reductionCone ℓ M)) ↔ IsAdicComplete (Ideal.span {(ℓ : R)}) M.V := by
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨?_⟩⟩
  · exact (nonempty_isLimit_reductionCone_iff ℓ ((Rep.ActionToRep R G).obj M)).1
      ⟨isLimitReductionConeMap h⟩
  · exact isLimitReductionConeOfMap (F := Rep.ActionToRep R G) (isLimitReductionCone ℓ h)

variable {ℓ} {M : Action (ModuleCat.{w} R) G}

/-- If the module underlying an action `M` is `ℓ`-adically complete, the projections exhibit `M`
as the inverse limit of `M / ℓ ^ m M`. -/
def isLimitReductionConeAction (hM : IsAdicComplete (Ideal.span {(ℓ : R)}) M.V) :
    IsLimit (reductionCone ℓ M) :=
  isLimitReductionConeOfMap (F := Rep.ActionToRep R G) (isLimitReductionCone ℓ hM)

variable (ℓ)

/-- For an action `M` whose underlying module is `ℓ`-adically complete, the inverse limit of
`M / ℓ ^ m M` is isomorphic to `M`. -/
def reductionLimitIsoAction (hM : IsAdicComplete (Ideal.span {(ℓ : R)}) M.V) :
    limit (reductionTower ℓ M) ≅ M :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitReductionConeAction hM)

/-- `reductionLimitIsoAction` commutes with the projections. -/
@[reassoc (attr := simp)]
lemma reductionLimitIsoAction_hom_reductionπ (hM : IsAdicComplete (Ideal.span {(ℓ : R)}) M.V)
    (m : ℕ) :
    (reductionLimitIsoAction ℓ hM).hom ≫ reductionπ ℓ M m = limit.π (reductionTower ℓ M) (op m) :=
  (limit.isLimit _).conePointUniqueUpToIso_hom_comp (isLimitReductionConeAction hM) (op m)

/-- For an action `M` whose underlying module is `ℓ`-adically complete, the inverse limit of the
reduction system of `M` is isomorphic to `M`. -/
def reductionSystemLimitIsoAction [Mono (powSMul ℓ 1 M)]
    (hM : IsAdicComplete (Ideal.span {(ℓ : R)}) M.V) :
    inverseLimit (reductionSystem ℓ M) ≅ M :=
  reductionLimitIsoAction ℓ hM

end Action

section Harris

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Shimura
  Langlands.Shimura.Coefficients

variable (ℓ : ℕ) [NeZero ℓ] {p : FinitePlace ℚ}

/-- If the place `p` of `ℚ` divides `ℓ ≠ 0`, the product `∏_{l | p} 𝒪_l` is complete for the
`ℓ`-adic topology. -/
theorem isAdicComplete_harrisCoefficientIntegers (L : Type u) [Field L] [NumberField L]
    (hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal) :
    IsAdicComplete (Ideal.span {(ℓ : HarrisCoefficientIntegers L p)})
      (HarrisCoefficientIntegers L p) :=
  isAdicComplete_pi_span_singleton_self (fun l : FinitePlacesAbove L p => CoefficientIntegers l.1)
    (fun l => (ℓ : CoefficientIntegers l.1)) fun l =>
    have := l.2
    isAdicComplete_coefficientIntegers ℓ hℓ l.1

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)

section Whole

variable [Module.Finite L W] (U : CompactOpenLevel σ.FiniteAdelicPoints) (hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)

include hℓ in
/-- If the place `p` of `ℚ` divides `ℓ ≠ 0`, Harris's lattice `𝓛` is complete for the `ℓ`-adic
topology over `∏_{l | p} 𝒪_l`. -/
theorem isAdicComplete_harrisLattice :
    IsAdicComplete (Ideal.span {(ℓ : HarrisCoefficientIntegers L p)}) (harrisLattice ρ p U) :=
  have := isAdicComplete_harrisCoefficientIntegers ℓ L hℓ
  have : Module.Finite (HarrisCoefficientIntegers L p) (harrisLattice ρ p U) :=
    Module.Finite.of_basis (harrisLatticeBasis ρ p U)
  NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite.{u, u}
    (HarrisCoefficientIntegers L p) (harrisLattice ρ p U) _

/-- For `p` dividing `ℓ ≠ 0`, the inverse limit of the `ℓ`-divisible system `{𝓛 / ℓ ^ m 𝓛}` of
Harris's lattice `𝓛` is isomorphic to `𝓛`, as representations of the level `U`. -/
def harrisReductionSystemLimitIso :
    inverseLimit (harrisReductionSystem ℓ ρ p U) ≅ harrisLatticeAction ρ p U :=
  reductionSystemLimitIsoAction ℓ (isAdicComplete_harrisLattice ℓ ρ U hℓ)

variable (G : Type u) [Group G]

/-- For `p` dividing `ℓ ≠ 0`, the inverse limit of `{𝓛 / ℓ ^ m 𝓛}`, for Harris's lattice `𝓛` with
the trivial action of `G`, is isomorphic to `𝓛`. -/
def harrisLatticeTrivialReductionSystemLimitIso :
    inverseLimit (reductionSystem ℓ
        (Rep.trivial (HarrisCoefficientIntegers L p) G (harrisLattice ρ p U))) ≅
      Rep.trivial (HarrisCoefficientIntegers L p) G (harrisLattice ρ p U) :=
  reductionSystemLimitIso ℓ (isAdicComplete_harrisLattice ℓ ρ U hℓ)

variable (X : Type u) [MulAction G X] (M : Type u) [AddCommGroup M]
  [Module (HarrisCoefficientIntegers L p) M] [Module.Free (HarrisCoefficientIntegers L p) M]
  [Module.Finite (HarrisCoefficientIntegers L p) M]

/-- For `p` dividing `ℓ ≠ 0`, the inverse limit of Harris's system
`m ↦ Hom(M[X], 𝓛 / ℓ ^ m 𝓛)` is isomorphic to `Hom(M[X], 𝓛)`. -/
def harrisPermutationIhomSystemLimitIso :
    inverseLimit (harrisPermutationIhomSystem ℓ ρ p U G X M) ≅
      (Rep.ihom (Rep.of (Induction.permutation (HarrisCoefficientIntegers L p) G X M))).obj
        (Rep.trivial (HarrisCoefficientIntegers L p) G (harrisLattice ρ p U)) :=
  ihomReductionSystemLimitIso ℓ _ (isAdicComplete_harrisLattice ℓ ρ U hℓ)

end Whole

section Place

variable {ρ} {l : FinitePlace L} [l.asIdeal.LiesOver p.asIdeal]
variable {U : Subgroup σ.FiniteAdelicPoints}

/-- If the place `p` of `ℚ` divides `ℓ ≠ 0` and `l` lies above `p`, a stable lattice `Λ` in
`L_l ⊗_L W` is complete for the `ℓ`-adic topology. -/
theorem isAdicComplete_stableCoefficientLattice (hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (Λ : StableCoefficientLattice ρ p l U) :
    IsAdicComplete (Ideal.span {(ℓ : CoefficientIntegers l)}) Λ.carrier :=
  have := isAdicComplete_coefficientIntegers ℓ hℓ l
  NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite.{u, u}
    (CoefficientIntegers l) Λ.carrier _

/-- For `p` dividing `ℓ ≠ 0` and `l` above `p`, the inverse limit of the `ℓ`-divisible system
`{Λ / ℓ ^ m Λ}` of a stable lattice `Λ` in `L_l ⊗_L W` is isomorphic to `Λ`. -/
def stableLatticeReductionSystemLimitIso (hℓ : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (Λ : StableCoefficientLattice ρ p l U) :
    inverseLimit (stableLatticeReductionSystem ℓ Λ) ≅ Λ.action :=
  reductionSystemLimitIsoAction ℓ (isAdicComplete_stableCoefficientLattice ℓ hℓ Λ)

end Place

end Harris

end Langlands.Cohomology.DivisibleSystem
