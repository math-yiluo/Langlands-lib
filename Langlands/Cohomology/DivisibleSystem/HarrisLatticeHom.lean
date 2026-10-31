import Langlands.Cohomology.DivisibleSystem.ReductionLattice
import Langlands.Cohomology.DivisibleSystem.IHomReduction
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-!
# Freeness of Harris's lattice and Harris's system `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §3, p.307: "Let `𝒪`
denote the ring of integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in `W(L)`";
proof of Proposition 4.10, p.312: "`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` [is a] free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-module".

The published `harrisLattice ρ p U` (Worker 57) models `𝓛` as a lattice over the product
`∏_{l | p} 𝒪_l` of the valuation rings of the completions of `L` at the places above `p`. Over a
product of rings, a lattice need not be free; this module shows that `𝓛` is:

* `piEquivFunOfBases`, `piBasisOfBases`: bases of modules `M i` over rings `R i` with a common
  index type `κ` give a basis of `∏ i, M i` over `∏ i, R i` indexed by `κ`
  (`piBasisOfBases_apply`);
* `finrank_stableCoefficientLattice`, `stableCoefficientLatticeBasis`: a stable lattice in
  `L_l ⊗_L W` has rank `dim_L W` over `𝒪_l`, hence a basis indexed by `Fin (dim_L W)`;
* `harrisLatticeBasis`, `harrisLattice_free`, `finrank_harrisLattice`: hence `𝓛` has a basis
  over `∏_{l | p} 𝒪_l` indexed by `Fin (dim_L W)`, and is free of rank `dim_L W`.

With `𝓛` given the trivial action of a group `G`, `harrisPermutationIhomSystem` is the published
`ℓ`-divisible system `m ↦ Hom(M[X], 𝓛 / ℓ ^ m 𝓛)` of IHomReduction for a permutation
representation `M[X]`, `reductionSystemHarrisPermutationIhomIso` identifies it with the
reduction system of `Hom(M[X], 𝓛)`, and for free actions on finite sets its levels are free over
`(∏_{l | p} 𝒪_l ⧸ (ℓ ^ m))[G]` (`freeOverPowQuotient_harrisPermutationIhomSystem_obj`,
`freeOverPowQuotient_harrisPermutationIhomSystem_subgroup_obj`): Harris's freeness statement
for the published lattice. The definitions and proofs are ours.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace Langlands.Cohomology.DivisibleSystem

section Products

variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)] {κ : Type*} [Finite κ]

/-- Bases of the factors `M i` over `R i` with a common finite index type `κ` give coordinates
of the product module `∏ i, M i` over the product ring `∏ i, R i`: the `k`-th coordinate of `x`
is the family of the `k`-th coordinates of the components `x i`. -/
def piEquivFunOfBases (b : ∀ i, Module.Basis κ (R i) (M i)) :
    ((i : ι) → M i) ≃ₗ[(i : ι) → R i] (κ → (i : ι) → R i) where
  toFun x k i := (b i).equivFun (x i) k
  invFun c i := (b i).equivFun.symm fun k => c k i
  left_inv x := funext fun i => (b i).equivFun.symm_apply_apply (x i)
  right_inv c := funext fun k => funext fun i => by simp
  map_add' x y := funext fun k => funext fun i => by simp
  map_smul' r x := funext fun k => funext fun i => by simp

/-- The basis of `∏ i, M i` over `∏ i, R i` indexed by `κ` assembled from bases of the factors
indexed by `κ`. -/
def piBasisOfBases (b : ∀ i, Module.Basis κ (R i) (M i)) :
    Module.Basis κ ((i : ι) → R i) ((i : ι) → M i) :=
  Module.Basis.ofEquivFun (piEquivFunOfBases R M b)

/-- The `k`-th vector of `piBasisOfBases R M b` has components the `k`-th vectors of the
bases `b i`. -/
lemma piBasisOfBases_apply (b : ∀ i, Module.Basis κ (R i) (M i)) (k : κ) (i : ι) :
    piBasisOfBases R M b k i = b i k := by
  classical
  rw [piBasisOfBases, Module.Basis.coe_ofEquivFun]
  conv_rhs => rw [← Module.Basis.ofEquivFun_equivFun (b i), Module.Basis.coe_ofEquivFun]
  change (b i).equivFun.symm
      (fun k' => (Pi.single (M := fun _ : κ => (j : ι) → R j) k 1 k') i) = _
  congr 1
  funext k'
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs <;> rfl

end Products

section Lattice

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Shimura
  Langlands.Shimura.Coefficients

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W]
variable {σ : AlgebraInvolution ℚ A} {ρ : (σ.baseChange L).AlgebraicRepresentation W}
variable {p : FinitePlace ℚ}

section Place

variable {l : FinitePlace L} [l.asIdeal.LiesOver p.asIdeal] {U : Subgroup σ.FiniteAdelicPoints}

/-- A stable lattice `Λ` in `L_l ⊗_L W` has rank `dim_L W` over `𝒪_l`. -/
lemma finrank_stableCoefficientLattice (Λ : StableCoefficientLattice ρ p l U) :
    Module.finrank (CoefficientIntegers l) Λ.carrier = Module.finrank L W :=
  (congrArg Cardinal.toNat (Submodule.IsLattice.rank' (FiniteCompletion L l) Λ.carrier)).trans
    Module.finrank_baseChange

/-- A basis of a stable lattice `Λ` in `L_l ⊗_L W` over `𝒪_l`, indexed by `Fin (dim_L W)`. -/
def stableCoefficientLatticeBasis (Λ : StableCoefficientLattice ρ p l U) :
    Module.Basis (Fin (Module.finrank L W)) (CoefficientIntegers l) Λ.carrier :=
  Module.finBasisOfFinrankEq _ _ (finrank_stableCoefficientLattice Λ)

end Place

variable (ρ p) [Module.Finite L W] (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- A basis of Harris's lattice `𝓛` in `(L ⊗ ℚ_p) ⊗_L W` over `∏_{l | p} 𝒪_l`, indexed by
`Fin (dim_L W)`: transported along the splitting of `𝓛` into the stable lattices at the places
`l` above `p` from the product of bases of these lattices. -/
def harrisLatticeBasis :
    Module.Basis (Fin (Module.finrank L W)) (HarrisCoefficientIntegers L p)
      (harrisLattice ρ p U) :=
  (piBasisOfBases (fun l : FinitePlacesAbove L p => CoefficientIntegers l.1)
    (fun l => (algebraicCompactCoefficientLattice ρ p l.1 U).carrier)
    (fun l => stableCoefficientLatticeBasis (algebraicCompactCoefficientLattice ρ p l.1 U))).map
    ((harrisLatticeEquiv ρ p U).trans (dependentProductSubmoduleEquiv _ _ _)).symm

/-- Harris's lattice `𝓛` is free over `∏_{l | p} 𝒪_l`. -/
instance harrisLattice_free :
    Module.Free (HarrisCoefficientIntegers L p) (harrisLattice ρ p U) :=
  Module.Free.of_basis (harrisLatticeBasis ρ p U)

/-- Harris's lattice `𝓛` has rank `dim_L W` over `∏_{l | p} 𝒪_l`. -/
lemma finrank_harrisLattice :
    Module.finrank (HarrisCoefficientIntegers L p) (harrisLattice ρ p U) = Module.finrank L W := by
  have : Nontrivial (HarrisCoefficientIntegers L p) :=
    Pi.nontrivial_at (Classical.arbitrary (FinitePlacesAbove L p))
  rw [Module.finrank_eq_card_basis (harrisLatticeBasis ρ p U), Fintype.card_fin]

end Lattice

section Hom

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Shimura
  Langlands.Shimura.Coefficients

variable (ℓ : ℕ) [NeZero ℓ]
variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints)

/-- On Harris's lattice `𝓛`, the scalar `ℓ` is a non-zero-divisor. -/
lemma isSMulRegular_harrisLattice :
    IsSMulRegular (harrisLattice ρ p U) (ℓ : HarrisCoefficientIntegers L p) :=
  (mono_powSMul_action_iff ℓ (harrisLatticeAction ρ p U)).1
    (mono_powSMul_harrisLatticeAction ℓ ρ p U)

variable (G : Type u) [Group G]

/-- On Harris's lattice `𝓛` with the trivial action of a group `G`, multiplication by `ℓ` is a
monomorphism. -/
instance mono_powSMul_harrisLatticeTrivial :
    Mono (powSMul ℓ 1 (Rep.trivial (HarrisCoefficientIntegers L p) G
      (harrisLattice ρ p U))) :=
  (mono_powSMul_one_iff_isSMulRegular ℓ _).2 (isSMulRegular_harrisLattice ℓ ρ p U)

variable (X : Type u) [MulAction G X] (M : Type u) [AddCommGroup M]
  [Module (HarrisCoefficientIntegers L p) M] [Module.Free (HarrisCoefficientIntegers L p) M]
  [Module.Finite (HarrisCoefficientIntegers L p) M]

/-- Harris's system `m ↦ Hom(𝒪[X]^M, 𝓛 / ℓ ^ m 𝓛)` for Harris's lattice `𝓛`, with the trivial
action of `G`, and the permutation representation `M[X]` of a `G`-set `X`. -/
def harrisPermutationIhomSystem :
    DivisibleSystem (Rep.{u} (HarrisCoefficientIntegers L p) G) ℓ :=
  ihomReductionSystem ℓ (Rep.of (Induction.permutation (HarrisCoefficientIntegers L p) G X M))
    (Rep.trivial (HarrisCoefficientIntegers L p) G (harrisLattice ρ p U))

/-- The reduction system of `Hom(M[X], 𝓛)` is isomorphic to `harrisPermutationIhomSystem`. -/
def reductionSystemHarrisPermutationIhomIso :
    reductionSystem ℓ ((Rep.ihom (Rep.of (Induction.permutation (HarrisCoefficientIntegers L p)
      G X M))).obj (Rep.trivial (HarrisCoefficientIntegers L p) G
        (harrisLattice ρ p U))) ≅ harrisPermutationIhomSystem ℓ ρ p U G X M :=
  reductionSystemIhomIso ℓ _ _

/-- Harris's freeness of `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` for Harris's lattice `𝓛`: if `G` acts
freely on a finite set `X`, every level of `harrisPermutationIhomSystem` is free over
`(∏_{l | p} 𝒪_l ⧸ (ℓ ^ m))[G]`. -/
theorem freeOverPowQuotient_harrisPermutationIhomSystem_obj [Finite X]
    (h : ∀ x : X, MulAction.stabilizer G x = ⊥) (m : ℕ) :
    FreeOverPowQuotient ℓ m ((harrisPermutationIhomSystem ℓ ρ p U G X M).obj m) :=
  freeOverPowQuotient_permutation_ihom_reduction h m

/-- The case of Harris's proof of Prop. 4.10: for a subgroup `S` of a finite group `Q`, acting
on `Q` by left multiplication, every level of `harrisPermutationIhomSystem` is free over
`(∏_{l | p} 𝒪_l ⧸ (ℓ ^ m))[S]`. -/
theorem freeOverPowQuotient_harrisPermutationIhomSystem_subgroup_obj (Q : Type u) [Group Q]
    [Finite Q] (S : Subgroup Q) (m : ℕ) :
    FreeOverPowQuotient ℓ m ((harrisPermutationIhomSystem ℓ ρ p U S Q M).obj m) :=
  freeOverPowQuotient_subgroup_permutation_ihom_reduction S m

end Hom

end Langlands.Cohomology.DivisibleSystem
