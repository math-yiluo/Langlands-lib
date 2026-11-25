module

public import StacksFrontier.RingTheory.Depth.Nakayama
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant.BaseChangeSquare
import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.RingTheory.Flat.TowerLTensor

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Critère de platitude par fibres

Two cases of the fibrewise criterion for flatness.

*The nilpotent case.* Let `R → S` be a map of commutative rings, let `I ⊆ R` be a nilpotent ideal
and let `M` be an `S`-module, regarded as an `R`-module through `R → S`. If `M/IM` is flat over
`S/IS` and `M` is flat over `R`, then `M` is flat over `S`, and the localization `S_𝔮` is flat
over `R` at every prime `𝔮 ⊆ S` whose fibre `M ⊗_S κ(𝔮)` is nonzero.

Tensoring `0 → K → R → R/K → 0` with the `R`-flat module `M` shows that `K ⊗_R M → M` is
injective for every ideal `K ⊆ R`, and the comparison `K ⊗_R M → KS ⊗_S M` is surjective, so
`KS ⊗_S M → M` is injective as well, that is `Tor_1^S(S/KS, M) = 0`. Feeding this into the
square-zero local criterion along the filtration by the powers of `IS` gives, by induction on
`k`, flatness of `M/(IS)^k M` over `S/(IS)^k`, and at `k` one less than the nilpotency degree of
`I` the criterion applies to `(IS)^k` itself. At a prime `𝔮` with `M ⊗_S κ(𝔮) ≠ 0` the module
`S_𝔮 ⊗_S M` is faithfully flat over `S_𝔮` and flat over `R`, whence `S_𝔮` is flat over `R`.

*The Noetherian local case.* Let `R → S → S'` be local homomorphisms of Noetherian local rings,
let `𝔪 ⊆ R` be the maximal ideal of `R` and let `M` be a finite nonzero `S'`-module, regarded as
an `S`-module and an `R`-module through the two ring maps. If `M` is flat over `R` and `M/𝔪M` is
flat over `S/𝔪S`, then `S` is flat over `R` and `M` is flat over `S`.

Put `I = 𝔪S`. Both conclusions come from the variant local criterion, whose `Tor` hypothesis is
the injectivity of `J ⊗ N → N`. Contracting `M ⊗_S (S ⊗_R 𝔪)` along the multiplication
`S ⊗_R 𝔪 → S` is, across `TensorProduct.AlgebraTensorModule.cancelBaseChange`, the map
`M ⊗_R 𝔪 → M`, which is injective because `M` is flat over `R`. As `S ⊗_R 𝔪 → S` factors as
`S ⊗_R 𝔪 ↠ I ↪ S`, this is the `Tor` hypothesis for `I ⊆ S`, and `M` is flat over `S`.
Nakayama's lemma for the finite nonzero `S'`-module `M` then makes `M` faithfully flat over `S`,
so the kernel `K` of `S ⊗_R 𝔪 → S`, which satisfies `M ⊗_S K = 0`, vanishes; this is the `Tor`
hypothesis for `𝔪 ⊆ R` and the module `S`, and `S` is flat over `R`.

## Main results

* `Module.flat_and_flat_localization_of_flat_quotient_of_isNilpotent`: the nilpotent case.
* `Module.flat_and_flat_of_flat_quotient_maximalIdeal_of_flat`: the Noetherian local case.
* `Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat`: if an `S`-module is
  flat over `R` and faithfully flat over `S`, then `S` is flat over `R`.

## Implementation notes

In both cases `IM` is written as `IS • ⊤` inside `M` viewed as an `S`-module, so that the
quotient carries the `S/IS`-module structure the hypothesis is about; this is the same submodule
as `I • ⊤` computed over `R` (`restrictScalars_smul_top_map`), since `(IS) · M = I · M`.

In the nilpotent case `M` is an `S`-module with `IsScalarTower R S M`, rather than a module over
a third ring `S'` under `S`, which plays no part in the statement. The localization is left
abstract: `S_𝔮` is any `S`-algebra `Sq` with `IsLocalization.AtPrime Sq 𝔮` and
`IsScalarTower R S Sq`, the fibre is `Ideal.ResidueField 𝔮` and "nonzero" is `Nontrivial`. The
filtration is indexed by `Ideal.map (algebraMap R S) (I ^ n)` rather than by the powers of
`Ideal.map (algebraMap R S) I`, so that the ideals appearing in the types of the relative
injectivity statements are literally extensions of ideals of `R`.

In the Noetherian local case `S'` carries the finiteness hypothesis on `M`; no `Algebra R S'` is
assumed, the two scalar towers on `M` already pinning its `R`-action. The auxiliary module
`S ⊗_R 𝔪` is written with `S` on the left, as `TensorProduct R S 𝔪`, because that is the side
carrying the `S`-module structure (`TensorProduct.leftModule`), which the kernel of the
multiplication map needs for faithful flatness of `M` over `S` to apply to it.

## References

* [Stacks, Tag 06A5](https://stacks.math.columbia.edu/tag/06A5)
* [Stacks, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP)
* [Stacks, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
* [Stacks, Tag 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [Stacks, Tag 00HP](https://stacks.math.columbia.edu/tag/00HP)
* [Stacks, Tag 039V](https://stacks.math.columbia.edu/tag/039V)
* [Stacks, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

@[expose] public section

open TensorProduct

namespace Stacks.Flatness.NilpotentFibreCriterion

section Comparison

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

end Comparison

section Permanence

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Flat permanence**. If an `S`-module `M` is flat over `R` and faithfully flat over `S`,
then `S` is flat over `R`. -/
@[stacks 039V]
theorem flat_of_flat_of_faithfullyFlat
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R M] [Module.FaithfullyFlat S M] : Module.Flat R S :=
  have : Module.Flat R (M ⊗[S] S) :=
    Module.Flat.of_linearEquiv ((TensorProduct.rid S M).restrictScalars R)
  Module.Flat.of_tensorProduct_of_faithfullyFlat (A := R) (C := S) (D := M) (P := S)

end Permanence

end Stacks.Flatness.NilpotentFibreCriterion

open TensorProduct

@[expose] public section

end

namespace Stacks.Flatness.NoetherianFibreCriterion

open TensorProduct

universe u v w x

section SMulMap

variable (R : Type u) (N : Type v) [CommRing R] [AddCommGroup N] [Module R N]
  {P : Type w} [AddCommGroup P] [Module R P] {Q : Type x} [AddCommGroup Q] [Module R Q]

/-- Contraction of a tensor product along a linear form: the map `N ⊗[R] P → N`,
`n ⊗ p ↦ f p • n`, attached to `f : P →ₗ[R] R`. -/
noncomputable def smulMap (f : P →ₗ[R] R) : N ⊗[R] P →ₗ[R] N :=
  (TensorProduct.rid R N).toLinearMap ∘ₗ LinearMap.lTensor N f

/-- `smulMap R N f` is `TensorProduct.rid R N` after `LinearMap.lTensor N f`. -/
lemma coe_smulMap (f : P →ₗ[R] R) :
    (smulMap R N f : N ⊗[R] P → N) = TensorProduct.rid R N ∘ LinearMap.lTensor N f := rfl

/-- `smulMap R N f` sends `n ⊗ p` to `f p • n`. -/
lemma smulMap_tmul (f : P →ₗ[R] R) (n : N) (p : P) :
    smulMap R N f (n ⊗ₜ p) = f p • n := by simp [smulMap]

attribute [local simp] smulMap_tmul

/-- Contracting along `f ∘ₗ g` is contracting along `f` after tensoring `g` with `N`. -/
lemma smulMap_comp (f : P →ₗ[R] R) (g : Q →ₗ[R] P) :
    smulMap R N (f ∘ₗ g) = smulMap R N f ∘ₗ LinearMap.lTensor N g := by
  ext n q; simp

/-- Contracting `N ⊗[R] J` along the inclusion of an ideal is injective as soon as `N` is flat
over `R`: it is the base change of `J ↪ R` followed by an isomorphism. -/
lemma injective_smulMap_subtype [Module.Flat R N] (J : Ideal R) :
    Function.Injective (smulMap R N J.subtype) := by
  rw [coe_smulMap]
  exact (TensorProduct.rid R N).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype)

/-- If the contraction `N ⊗[R] J → N`, `n ⊗ x ↦ x • n`, along the inclusion of an ideal `J` is
injective, then so is `J ⊗[R] N → R ⊗[R] N`. -/
lemma injective_rTensor_subtype_of_injective_smulMap (J : Ideal R)
    (h : Function.Injective (smulMap R N J.subtype)) :
    Function.Injective (J.subtype.rTensor N) := by
  rw [coe_smulMap] at h
  exact (LinearMap.lTensor_inj_iff_rTensor_inj N J.subtype).mp h.of_comp

end SMulMap

section MulMap

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (J : Ideal R)

/-- The `S`-linear multiplication map `S ⊗[R] J → S`, `s ⊗ x ↦ algebraMap R S x * s`, attached to
an ideal `J` of `R`; its range is the ideal `J S` of `S`. -/
noncomputable def mulMap : S ⊗[R] J →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ J.subtype.baseChange S

/-- `mulMap R S J` sends `s ⊗ x` to `algebraMap R S x * s`. -/
lemma mulMap_tmul (s : S) (x : J) : mulMap R S J (s ⊗ₜ x) = algebraMap R S x * s := by
  simp [mulMap, Algebra.smul_def]

attribute [local simp] mulMap_tmul smulMap_tmul

/-- The range of `mulMap R S J` is the ideal `J S` of `S`. -/
lemma range_mulMap : LinearMap.range (mulMap R S J) = J.map (algebraMap R S) := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, rfl⟩
    induction z with
    | tmul s x => simpa using Ideal.mul_mem_right s _ (Ideal.mem_map_of_mem _ x.2)
    | add a b ha hb => simpa using add_mem ha hb
  · rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => ⟨(1 : S) ⊗ₜ ⟨x, hx⟩, by simp⟩

/-- `mulMap` with its target cut down to its range, the ideal `J S` of `S`. -/
noncomputable def mulMap' : S ⊗[R] J →ₗ[S] (J.map (algebraMap R S)) :=
  (mulMap R S J).codRestrict _ fun z => (range_mulMap R S J).le (LinearMap.mem_range_self _ z)

/-- `mulMap' R S J` followed by the inclusion of `J S` into `S` is `mulMap R S J`. -/
lemma subtype_comp_mulMap' :
    (J.map (algebraMap R S)).subtype ∘ₗ mulMap' R S J = mulMap R S J :=
  LinearMap.subtype_comp_codRestrict _ _ _

/-- `mulMap' R S J` is surjective onto the ideal `J S`. -/
lemma surjective_mulMap' : Function.Surjective (mulMap' R S J) := fun y => by
  obtain ⟨z, hz⟩ : (y : S) ∈ LinearMap.range (mulMap R S J) := (range_mulMap R S J).ge y.2
  exact ⟨z, Subtype.ext hz⟩

end MulMap

section Core

attribute [local simp] smulMap_tmul mulMap_tmul

variable (R : Type u) (S : Type v) (M : Type x) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (J : Ideal R)

/-- The two routes from `M ⊗[S] (S ⊗[R] J)` to `M` agree: both send `m ⊗ (s ⊗ x)` to
`(algebraMap R S x * s) • m`. -/
lemma smulMap_mulMap_apply (w : M ⊗[S] (S ⊗[R] J)) :
    smulMap S M (mulMap R S J) w =
      smulMap R M J.subtype (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J w) := by
  induction w with
  | tmul m z =>
      induction z with
      | tmul s x =>
          simp only [smulMap_tmul, mulMap_tmul, Submodule.coe_subtype,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
          rw [mul_smul, algebraMap_smul]
      | add z₁ z₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Contracting `M ⊗[S] (S ⊗[R] J)` along the multiplication `S ⊗[R] J → S` is injective when
`M` is flat over `R`. -/
lemma injective_smulMap_mulMap [Module.Flat R M] :
    Function.Injective (smulMap S M (mulMap R S J)) := by
  rw [show (smulMap S M (mulMap R S J) : M ⊗[S] (S ⊗[R] J) → M) =
      smulMap R M J.subtype ∘ TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J from
    funext (smulMap_mulMap_apply R S M J)]
  exact (injective_smulMap_subtype R M J).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M J).injective

/-- If `M` is flat over `R`, then `J S ⊗[S] M → S ⊗[S] M` is injective for the ideal `J S` of
`S`. -/
lemma injective_rTensor_subtype_map [Module.Flat R M] :
    Function.Injective ((J.map (algebraMap R S)).subtype.rTensor M) := by
  refine injective_rTensor_subtype_of_injective_smulMap S M _ ?_
  refine Function.Injective.of_comp_right (g := LinearMap.lTensor M (mulMap' R S J)) ?_
    (LinearMap.lTensor_surjective M (surjective_mulMap' R S J))
  rw [← LinearMap.coe_comp, ← smulMap_comp, subtype_comp_mulMap']
  exact injective_smulMap_mulMap R S M J

end Core

/-- A module that is flat over a local ring `S` and finite and nonzero over a local ring `S'`
above `S` is faithfully flat over `S`: Nakayama's lemma over `S'` gives `𝔪_{S'} M ≠ M`, and
`𝔪_S M` is contained in `𝔪_{S'} M`. -/
lemma faithfullyFlat_of_flat (S : Type v) (S' : Type w) (M : Type x)
    [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S'] [Algebra S S']
    [IsLocalHom (algebraMap S S')] [AddCommGroup M] [Module S M] [Module S' M]
    [IsScalarTower S S' M] [Module.Finite S' M] [Nontrivial M] [Module.Flat S M] :
    Module.FaithfullyFlat S M := by
  rw [Module.faithfullyFlat_iff]
  refine ⟨‹_›, fun {m} hm hm' => Module.maximalIdeal_smul_top_ne_top (R := S') M (top_le_iff.mp ?_)⟩
  rw [IsLocalRing.eq_maximalIdeal hm] at hm'
  refine le_trans (le_of_eq ?_)
    (Submodule.smul_mono_left (IsLocalRing.map_maximalIdeal_le (algebraMap S S')))
  refine ((Submodule.restrictScalars_eq_top_iff S S' _).mp ?_).symm
  rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top, hm']

end Stacks.Flatness.NoetherianFibreCriterion

universe u v w

@[expose] public section

end
