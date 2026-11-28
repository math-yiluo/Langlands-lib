import Langlands.AbelianScheme.AbelianInertiaPowerConjugacy
import Langlands.AbelianScheme.Tate.GeometricTorsionReduction
import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeProof
import Langlands.AlgebraicGeometry.FiniteEtale.FiniteSeparableFiberSplit
import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
import WeilConjectures.RingTheory.HenselianDVRExtension

/-! # Reducing Tate power conjugacy to trivial prime torsion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open CategoryTheory AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme

/-- Pointed base change gives a residue-linear identification of the finite torsion modules
intertwining the restriction of the pointed monodromy. -/
theorem Tate.exists_levelBaseChange_intertwiner {S S' : Scheme.{u}} (f : S' ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ S') (s : Spec (.of Ω) ⟶ S) (hts : t ≫ f = s)
    (A : AbelianScheme S) (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(S, ⊤))) (hu' : IsUnit (n : Γ(S', ⊤))) :
    ∃ e : Tate.Level ((baseChange f).obj A) (Over.mk t) n ≃ₗ[ZMod n]
        Tate.Level A (Over.mk s) n,
      ∀ (g : FundamentalGroup t (geometricFiberFinite t)) (x : Tate.Level _ (Over.mk t) n),
        e (Tate.levelMonodromy t (geometricFiberFinite t) torsionFiniteEtale
          ((baseChange f).obj A) n hn hu' g x) =
        Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale A n hn hu
          (fundamentalGroupMap f t s hts (geometricFiberFinite t) (geometricFiberFinite s) g) (e x) := by
  subst s
  exact ⟨GroupScheme.Tate.levelBaseChangeLinear A.toGrp f (Over.mk t) n,
    Tate.levelBaseChange_monodromy f t (geometricFiberFinite t) (geometricFiberFinite (t ≫ f))
      torsionFiniteEtale A n hn hu hu'⟩

/-- Over a strictly Henselian trait with trivial action on prime torsion, an inertia action
and its `q`-th power are conjugate at every prime-power torsion level for one integer `q > 1`. -/
def SplitAbelianInertiaPowerConjugacyStatement : Prop :=
  ∀ (W L : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L]
    (A : AbelianScheme (Spec (.of L))) (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : W) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of L))
      (hu : ∀ n : ℕ, IsUnit ((ℓ ^ n : ℕ) : Γ(Spec (.of L), ⊤))),
      (∀ (g : FundamentalGroup s (geometricFiberFinite s)) (x : Tate.Level A (Over.mk s) ℓ),
        Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale A ℓ
          (Fact.out : ℓ.Prime).pos (by simpa using hu 1) g x = x) →
      ∀ (g : FundamentalGroup s (geometricFiberFinite s)),
      ∃ q : ℕ, 1 < q ∧
        ∀ n : ℕ, ∃ e : Tate.PrimeAdic.Level A (Over.mk s) ℓ n ≃ₗ[ZMod (ℓ ^ n)]
            Tate.PrimeAdic.Level A (Over.mk s) ℓ n,
          e.conj (Tate.PrimeAdic.levelMonodromyZMod s (geometricFiberFinite s) A ℓ hu n g) =
            Tate.PrimeAdic.levelMonodromyZMod s (geometricFiberFinite s) A ℓ hu n (g ^ q)

open Tate.PrimeAdic

private theorem finiteModelPowerConjugacy
    (hSplit : SplitAbelianInertiaPowerConjugacyStatement.{u})
    (W L Ω : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L] [Field Ω] [IsAlgClosed Ω] [Algebra L Ω]
    (A : AbelianScheme (Spec (.of L))) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : W))
    (hu : ∀ n : ℕ, IsUnit ((ℓ ^ n : ℕ) : Γ(Spec (.of L), ⊤)))
    (g : FundamentalGroup (Spec.algebraMap L Ω) (geometricFiberFinite (Spec.algebraMap L Ω))) :
    ∃ a q : ℕ, 0 < a ∧ 1 < q ∧
      ∀ n : ℕ, ∃ e : Level A (Over.mk (Spec.algebraMap L Ω)) ℓ n ≃ₗ[ZMod (ℓ ^ n)]
          Level A (Over.mk (Spec.algebraMap L Ω)) ℓ n,
        e.conj (levelMonodromyZMod (Spec.algebraMap L Ω) (geometricFiberFinite _) A ℓ hu n (g ^ a)) =
          levelMonodromyZMod (Spec.algebraMap L Ω) (geometricFiberFinite _) A ℓ hu n (g ^ (a * q)) := by
  let s := Spec.algebraMap L Ω
  let hs := geometricFiberFinite s
  have hpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  let hu₁ : IsUnit (ℓ : Γ(Spec (.of L), ⊤)) := by simpa using hu 1
  let Y := Tate.torsionCover torsionFiniteEtale A ℓ hpos hu₁
  obtain ⟨E, hEfin, hEsep, hE⟩ := finiteSeparableFiberSplit L Ω Y
  let f := Spec.algebraMap L E
  let t := Spec.algebraMap E Ω
  let ht := geometricFiberFinite t
  let Z := fieldExtensionCover L E
  let x : Fiber s Z := ringTestMap L E.val
  have hts : t ≫ f = s := Over.w x
  let fStar := fundamentalGroupMap f t s hts ht hs
  let P := (baseChange f).obj A
  let huP (n : ℕ) : IsUnit ((ℓ ^ n : ℕ) : Γ(Spec (.of ↥E), ⊤)) :=
    Tate.isUnit_natCast_pullback f (ℓ ^ n) (hu n)
  let huP₁ : IsUnit (ℓ : Γ(Spec (.of ↥E), ⊤)) := by simpa using huP 1
  have hfix (k : FundamentalGroup t ht) (y : Tate.Level P (Over.mk t) ℓ) :
      Tate.levelMonodromy t ht torsionFiniteEtale P ℓ hpos huP₁ k y = y := by
    obtain ⟨e, he⟩ := Tate.exists_levelBaseChange_intertwiner f t s hts A ℓ hpos hu₁ huP₁
    apply e.injective
    rw [he]
    obtain ⟨z, hz⟩ := (Tate.kernelLevelEquiv A (Over.mk s) ℓ).surjective (e y)
    rw [← hz, Tate.levelMonodromy_kernel]
    exact congrArg (fun z' : Fiber s Y ↦ Tate.kernelLevelEquiv A (Over.mk s) ℓ (Additive.ofMul z'))
      (splitFiber_fundamentalGroupMap_smul L Ω Y E hE k z.toMul)
  let : Finite (Fiber s Z) := hs Z
  let a := Nat.card (Equiv.Perm (Fiber s Z))
  obtain ⟨k, hk⟩ := liftPowerToCover s hs Z x ht g
  change fStar k = g ^ a at hk
  let : Algebra W E := ((algebraMap L E).comp (algebraMap W L)).toAlgebra
  let : IsScalarTower W L E := IsScalarTower.of_algebraMap_eq' rfl
  let W₁ := integralClosure W E
  have : IsDiscreteValuationRing W₁ :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure W L E
  have : HenselianLocalRing W₁ := IsDiscreteValuationRing.henselianLocalRing_integralClosure W L E
  have : IsFractionRing W₁ E :=
    Stacks.DiscreteValuationRing.Ramification.isFractionRing_integralClosure W L E
  have : IsLocalHom (algebraMap W W₁) :=
    IsDiscreteValuationRing.isLocalHom_algebraMap_integralClosure W L E
  have := Algebra.IsAlgebraic.residueField_of_isIntegral (R := W) (S := W₁)
  have : IsSepClosed (ResidueField W₁) := Algebra.IsAlgebraic.isSepClosed (F := ResidueField W)
  have hℓ₁ : IsUnit (ℓ : W₁) := by simpa using hℓ.map (algebraMap W W₁)
  obtain ⟨q, hq, hconj⟩ := hSplit W₁ E P ℓ hℓ₁ Ω t huP hfix k
  refine ⟨a, q, Nat.card_pos, hq, fun n ↦ ?_⟩
  obtain ⟨d, hd⟩ := hconj n
  obtain ⟨e, he⟩ := Tate.exists_levelBaseChange_intertwiner f t s hts A (ℓ ^ n)
    (pow_pos hpos n) (hu n) (huP n)
  have he' (σ : FundamentalGroup t ht) :
      e.conj (levelMonodromyZMod t ht P ℓ huP n σ) = levelMonodromyZMod s hs A ℓ hu n (fStar σ) := by
    apply LinearMap.ext
    intro z
    rw [LinearEquiv.conj_apply_apply]
    exact (he σ (e.symm z)).trans (congrArg _ (e.apply_symm_apply z))
  have hqmap : fStar (k ^ q) = g ^ (a * q) := by rw [map_pow, hk, pow_mul]
  refine ⟨e.symm.trans (d.trans e), ?_⟩
  rw [← hk, ← hqmap, ← he', ← he', ← LinearEquiv.conj_trans, LinearEquiv.trans_apply,
    LinearEquiv.conj_symm_conj, ← LinearEquiv.conj_trans, LinearEquiv.trans_apply, hd]

/-- A finite separable field extension splits the prime torsion. Lifting a positive power
of the inertia element and comparing finite Tate modules reduces to that split case. -/
def SplitInertiaPowerConjugacyReductionStatement : Prop :=
  SplitAbelianInertiaPowerConjugacyStatement.{u} → AbelianInertiaTatePowerConjugacyStatement.{u}

/-- The finite-field extension comparison transports both powers through the same equivariant
residue-linear identification. -/
theorem splitInertiaPowerConjugacyReduction : SplitInertiaPowerConjugacyReductionStatement.{u} := by
  intro hSplit W L _ _ _ _ _ _ _ _ A ℓ _ hℓ Ω _ _ s hu
  let : Algebra L Ω := (Spec.preimage s).hom.toAlgebra
  have hs : Spec.algebraMap L Ω = s := Spec.map_preimage s
  rw [← hs]
  exact finiteModelPowerConjugacy hSplit W L Ω A ℓ hℓ hu

end Langlands.AbelianScheme
