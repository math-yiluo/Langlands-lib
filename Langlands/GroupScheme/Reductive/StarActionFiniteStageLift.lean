import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Lifting Galois pinning data from a finite stage to a larger field -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace StarActionFiniteStage

local instance liftBaseChangeAffine (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

section Lift

variable {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
  [Algebra L K] [Algebra.IsAlgebraic k L]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- Galois pinning data over an intermediate field `L` lift to Galois pinning data over `K`
with the same torus, through a base-preserving equivalence of root data that intertwines the
star actions of compatible automorphisms. -/
theorem exists_lift (d' : GaloisPinningData k L G)
    (hc : algebraBaseMap L K ≫ algebraBaseMap k L = algebraBaseMap k K) :
    ∃ (d : GaloisPinningData k K G)
      (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ d'.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      ∀ (σ : L ≃ₐ[k] L) (τ : K ≃ₐ[k] K),
        (∀ x, τ (algebraMap L K x) = algebraMap L K (σ x)) →
          RootPairing.Equiv.comp e (d'.starAction σ).val =
            RootPairing.Equiv.comp (d.starAction τ).val e := by
  -- Connected reductivity over `k`, `K` and, along `L → K`, of `G_L`.
  have hG : IsConnectedReductive G :=
    connectedReductiveAlgebraicExtensionReflection k L G d'.isConnectedReductive
  have hGK := connectedReductiveFieldExtensionStatement k K G hG
  have hGLK := connectedReductiveFieldExtensionStatement L K _ d'.isConnectedReductive
  have := hG.smooth
  -- The tower isomorphisms comparing `(·)_K` with `((·)_L)_K`.
  have hsq := towerIsoOf_square (algebraBaseMap k L) (algebraBaseMap L K) d'.torus
    (algebraBaseMap k K) hc d'.inclusion
  have heq := baseChange_map_eq_groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K)
    (algebraBaseMap k K) hc d'.inclusion
  -- Splitness and maximality of `(T_L)_K`, then of `T_K`.
  have hTLK := d'.isSplitTorus.baseChange (algebraBaseMap L K)
  have hsplitK : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj d'.torus).toGrp :=
    IsSplitTorus.of_iso
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc
        d'.torus.toGrp) hTLK
  have hiLK : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap L K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d'.torus))
      ((GroupScheme.baseChange (algebraBaseMap L K)).map
        ((GroupScheme.baseChange (algebraBaseMap k L)).map d'.inclusion)) :=
    (maximalTorusBaseChange L K ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d'.torus)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map d'.inclusion)
      d'.isSplitTorus.isTorus d'.isMaximalTorus.2.1).mp d'.isMaximalTorus
  have hiK : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d'.torus)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map d'.inclusion) :=
    IsMaximalTorus.of_eq_iso_comp_comp_iso
      (T := (CommGroupScheme.baseChange (algebraBaseMap L K)).obj
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d'.torus))
      (T' := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj d'.torus)
      hiLK
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc
        d'.torus.toGrp)
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc G).symm
      (by rw [heq]; simp)
  -- A reduced root datum of `(G_K, T_K)` and the comparison with the transport of `d'`.
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K _ hGK _ hsplitK _ hiK
  have hP'K := d'.isRootDatum.baseChange (K := K)
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj d'.torus) d'.isSplitTorus
    ((GroupScheme.baseChange (algebraBaseMap k L)).map d'.inclusion)
  let E₁ := latticeBaseChangeEquiv (algebraBaseMap L K) _ d'.isSplitTorus d'.rootDatum
  let E₂ := rootDatumEquivOfTorusCompatibleIso hGK hGLK hsplitK hTLK hiK hiLK
    (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc G)
    (towerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) d'.torus (algebraBaseMap k K) hc)
    hsq hP hP'K
  let e := RootPairing.Equiv.comp E₂ E₁
  have he : ∀ χ, e.weightMap χ = towerCharacterOf (algebraBaseMap k L) (algebraBaseMap L K)
      d'.torus (algebraBaseMap k K) hc χ := fun χ =>
    rootDatumEquivOfTorusCompatibleIso_weightMap hGK hGLK hsplitK hTLK hiK hiLK
      (groupTowerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) (algebraBaseMap k K) hc G)
      (towerIsoOf (algebraBaseMap k L) (algebraBaseMap L K) d'.torus (algebraBaseMap k K) hc)
      hsq hP hP'K (E₁.weightMap χ)
  -- The base over `K` pushed forward from the base of `d'`.
  let base : P.Base := d'.base.map e
  let d : GaloisPinningData k K G :=
    { torus := d'.torus
      inclusion := d'.inclusion
      isConnectedReductive := hGK
      isSplitTorus := hsplitK
      isMaximalTorus := hiK
      rootIndex := J
      finiteRootIndex := hJ
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := base
      pinning := RootPinning.ofSplitMaximalTorus hGK hsplitK _ hiK P hP base }
  have hb : ∀ a, a ∈ d'.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d.toSplitPinning.base.support := by
    classical
    intro a
    change a ∈ d'.base.support ↔ e.indexEquiv a ∈ (d'.base.map e).support
    rw [RootPairing.Base.support_map_eq, Finset.mem_image]
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨c, hc, hca⟩
      rwa [← e.indexEquiv.injective hca]
  refine ⟨d, e, hb, fun σ τ hστ => ?_⟩
  refine starAction_comp_of_weightMap d' d e hb σ τ (fun χ => ?_)
  exact (he _).trans ((towerCharacterOf_transport (algebraBaseMap k L) (algebraBaseMap L K)
    d'.torus (algebraBaseMap k K) hc (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    (galoisBaseMap k K τ) (galoisBaseMap_over k K τ)
    (algebraBaseMap_comp_galoisBaseMap σ τ hστ) χ).trans
    (congrArg (characterLattice.galoisRepresentation k K d'.torus τ) (he χ).symm))

end Lift

end StarActionFiniteStage

/-- **Lifting the star action from a finite stage to the separable closure.** Let `k` be a
field, `L/k` an algebraic extension with a `k`-embedding `ι : L → k_s`, and `G` an affine group
locally of finite type over `k` with Galois pinning data `d'` over `L`. Then `G` has Galois
pinning data `d` over `k_s` and a base-preserving equivalence `e` from the root datum of `d'` to
that of `d` with `e ∘ μ_{d'}(σ) = μ_d(τ) ∘ e` whenever `τ ∘ ι = ι ∘ σ`. This is the converse
of `StarActionFiniteStageStatement`. -/
def StarActionFiniteStageLiftStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d' : GaloisPinningData k L G)
    (ι : L →ₐ[k] SeparableClosure k),
    ∃ (d : GaloisPinningData k (SeparableClosure k) G)
      (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ d'.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      ∀ (σ : L ≃ₐ[k] L) (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
        (∀ x, τ (ι x) = ι (σ x)) →
          RootPairing.Equiv.comp e (d'.starAction σ).val =
            RootPairing.Equiv.comp (d.starAction τ).val e

/-- Proof of `StarActionFiniteStageLiftStatement`: make `k_s` an `L`-algebra through `ι` and
apply `StarActionFiniteStage.exists_lift`. -/
theorem starActionFiniteStageLift : StarActionFiniteStageLiftStatement.{u} := by
  intro k L _ _ _ _ G _ _ d' ι
  let : Algebra L (SeparableClosure k) := ι.toRingHom.toAlgebra
  have hc : algebraBaseMap L (SeparableClosure k) ≫ algebraBaseMap k L =
      algebraBaseMap k (SeparableClosure k) := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg Subtype.val (ι.commutes x)
  obtain ⟨d, e, hb, hstar⟩ := StarActionFiniteStage.exists_lift d' hc
  exact ⟨d, e, hb, fun σ τ hστ => hstar σ τ hστ⟩

namespace StarActionFiniteStage

section FiniteField

variable {k L : Type u} [Field k] [Fintype k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- Over a finite field `k`, Galois pinning data over an algebraic extension `L` lift to Galois
pinning data over `k_s` through a base-preserving equivalence of root data that intertwines the
star actions of the arithmetic Frobenius of `L` and of `k_s`. -/
theorem exists_frobenius_lift (d' : GaloisPinningData k L G) :
    ∃ (d : GaloisPinningData k (SeparableClosure k) G)
      (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ d'.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      RootPairing.Equiv.comp e
          (d'.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k L)).val =
        RootPairing.Equiv.comp
          (d.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k))).val e := by
  let ι : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  obtain ⟨d, e, hb, hstar⟩ := starActionFiniteStageLift k L G d' ι
  refine ⟨d, e, hb, hstar _ _ fun x => ?_⟩
  change ι x ^ Fintype.card k = ι (x ^ Fintype.card k)
  exact (map_pow ι x _).symm

/-- Over a finite field `k`: if `G` with Galois pinning data `d'` over an algebraic extension `L`
has Frobenius star action `θ` (transported by a base-preserving `f'`), then `G` has Galois
pinning data `d` over `k_s` whose Frobenius star action is `θ`, transported by a
base-preserving `f`. -/
theorem exists_frobenius_class_of_stage {G₀ : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₀.X.hom] (p : SplitPinning G₀) (θ : p.basedRootDatumAut)
    (d' : GaloisPinningData k L G)
    (f' : RootPairing.Equiv p.rootDatum d'.toSplitPinning.rootDatum)
    (hf' : ∀ a, a ∈ p.base.support ↔ f'.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (hθ : RootPairing.Equiv.comp f' θ.val =
      RootPairing.Equiv.comp (d'.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k L)).val
        f') :
    ∃ (d : GaloisPinningData k (SeparableClosure k) G)
      (f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ p.base.support ↔ f.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      RootPairing.Equiv.comp f θ.val =
        RootPairing.Equiv.comp
          (d.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k))).val f := by
  obtain ⟨d, e, hb, he⟩ := exists_frobenius_lift d'
  refine ⟨d, RootPairing.Equiv.comp e f', fun a => (hf' a).trans (hb _), ?_⟩
  rw [RootPairing.Equiv.comp_assoc, hθ, ← RootPairing.Equiv.comp_assoc, he,
    RootPairing.Equiv.comp_assoc]

end FiniteField

end StarActionFiniteStage

end Langlands.GroupScheme
