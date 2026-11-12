import Langlands.Representation.Smooth.RenardHeckeSeparatingQuotient
import Langlands.Representation.Smooth.RenardSigmaCompactSchurProof
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement
import Langlands.Representation.Category.RenardFinitenessProof
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Algebra.NondegenerateModuleSubobject
import Langlands.Topology.LocallyProfiniteProof

/-! # Small realizations and the Hecke-completeness reduction -/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.Smooth

open Hecke

/-- Finite families of actual Hecke functions admit a common two-sided local unit. -/
theorem hecke_isIdempotented
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    Langlands.Algebra.IsIdempotented (HeckeAlgebra μ) := by
  classical
  intro s
  obtain ⟨K, _, hK, hs⟩ := TestFunction.commonCompactOpenBiInvariance G
    (s.image (HeckeAlgebra.toTestFunction μ)) (⊤ : OpenSubgroup G)
  refine ⟨⟨HeckeAlgebra.normalizedIndicator μ K hK,
    HeckeAlgebra.normalizedIndicator_idempotent μ K hK⟩, ?_⟩
  intro a ha
  exact (HeckeAlgebra.mem_biInvariant_iff_sandwich μ K hK a).mp
    (hs _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩))

/-- Sigma-compactness suffices to realize an irreducible smooth representation
in any prescribed carrier universe. -/
theorem exists_irreducible_smoothRep_equiv_of_sigmaCompact
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] {w : SmoothRep.{0, u, u} ℂ G} (hw : w.IsIrreducible) :
    ∃ σ : SmoothRep.{0, u, v} ℂ G,
      σ.IsIrreducible ∧ Nonempty (w.representation.Equiv σ.representation) := by
  classical
  let := hw
  let : Nontrivial w := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) w.representation.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : w)
  let S : Set w := Set.range fun g => w.representation g x
  have hSc : S.Countable := sigmaCompact_countable_orbit w.representation (w.isSmooth x)
  have hSspan : Submodule.span ℂ S = ⊤ := span_range_orbit_eq_top hw hx
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ S
  have : Countable b := (hSc.mono hbS).to_subtype
  let basis : Module.Basis b ℂ w :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hSspan]))
  let e : w ≃ₗ[ℂ] (Shrink.{v} b →₀ ℂ) :=
    basis.repr.trans (Finsupp.domLCongr (equivShrink.{v} b))
  let φ := transportRepresentationEquiv w.representation e
  have hsmooth : IsSmooth (transportRepresentation w.representation e) :=
    isSmooth_of_surjective φ.toIntertwiningMap e.surjective w.isSmooth
  exact ⟨SmoothRep.of (transportRepresentation w.representation e) hsmooth,
    (isIrreducible_iff_of_equiv φ).mp hw, ⟨φ⟩⟩

/-- A chosen realization of an irreducible smooth representation in the requested universe.
The equivalence is supplied by the preceding countable-basis construction. -/
def sigmaCompactSmallRealization
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] {π : SmoothRep.{0, u, u} ℂ G} (hπ : π.IsIrreducible) :
    SmoothRep.{0, u, v} ℂ G :=
  (exists_irreducible_smoothRep_equiv_of_sigmaCompact.{u, v} hπ).choose

/-- The chosen small realization retains irreducibility and the actual group action up to equivalence. -/
theorem sigmaCompactSmallRealization_spec
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] {π : SmoothRep.{0, u, u} ℂ G} (hπ : π.IsIrreducible) :
    (sigmaCompactSmallRealization.{u, v} hπ).IsIrreducible ∧
      Nonempty (π.representation.Equiv
        (sigmaCompactSmallRealization.{u, v} hπ).representation) :=
  (exists_irreducible_smoothRep_equiv_of_sigmaCompact.{u, v} hπ).choose_spec

/-- From a separating original simple Hecke module, categorical equivalence
recovers a separating irreducible smooth representation. -/
theorem exists_irreducible_smoothRep_of_simple_heckeModule
    (hequiv : HeckeNondegenerateModuleEquivalenceStatement.{u, u})
    {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    {M : Type u} [AddCommGroup M] [Langlands.Algebra.NonUnitalModule (HeckeAlgebra μ) M]
    (hM : Langlands.Algebra.IsNondegenerate (HeckeAlgebra μ) M)
    (hs : Nontrivial M ∧ ∀ S : Langlands.Algebra.NonUnitalSubmodule (HeckeAlgebra μ) M,
      S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤)
    (a : HeckeAlgebra μ) (ha : ∃ m : M, a • m ≠ 0) :
    ∃ π : SmoothRep.{0, u, u} ℂ G, π.IsIrreducible ∧
      heckeAction μ π.representation π.isSmooth a ≠ 0 := by
  let F := heckeNondegenerateModuleFunctor.{u, u} μ
  let : F.IsEquivalence := hequiv G μ
  let X : Langlands.Algebra.NondegenerateModuleCat.{u, u} (HeckeAlgebra μ) :=
    ⟨Langlands.Algebra.NonUnitalModuleCat.of (HeckeAlgebra μ) M, hM⟩
  let π := F.objPreimage X
  let e : F.obj π ≅ X := F.objObjPreimageIso X
  let hA := hecke_isIdempotented μ
  let := Langlands.Algebra.NondegenerateModuleCat.abelian (HeckeAlgebra μ) hA
  let := Langlands.Algebra.nondegenerateInclusion_preservesHomology.{u, u} hA
  let : Simple ((Langlands.Algebra.nondegenerateInclusion (HeckeAlgebra μ)).obj X) :=
    (Langlands.Algebra.NonUnitalModuleCat.additiveSimple_iff_simple
      ((Langlands.Algebra.nondegenerateInclusion (HeckeAlgebra μ)).obj X)).mp hs
  let : Simple X := Functor.simple_of_simple_obj
    (Langlands.Algebra.nondegenerateInclusion (HeckeAlgebra μ)) X
  let : Simple (F.obj π) := Simple.of_iso e
  let : Simple π := Functor.simple_of_simple_obj F π
  have hi : π.IsIrreducible := by
    apply (Representation.irreducible_iff_isSimpleModule_asModule π.representation).2
    rw [isSimpleModule_iff]
    exact (OrderIso.isSimpleOrder_iff (SmoothRep.groupAlgebraSubobjectOrderIso π)).mp
      inferInstance
  refine ⟨π, hi, ?_⟩
  intro hzero
  obtain ⟨m, hm⟩ := ha
  let n : π := e.inv.hom.toAddMonoidHom m
  have hcancel : e.hom.hom.toAddMonoidHom n = m := by
    exact congrArg (fun f : X ⟶ X => f.hom.toAddMonoidHom m) e.inv_hom_id
  have hcomm := e.hom.hom.map_smul' a n
  change e.hom.hom.toAddMonoidHom (heckeAction μ π.representation π.isSmooth a n) =
    a • e.hom.hom.toAddMonoidHom n at hcomm
  rw [hzero, LinearMap.zero_apply, hcancel] at hcomm
  exact hm (hcomm.symm.trans e.hom.hom.toAddMonoidHom.map_zero)

/-- Renard III.1.11, reduced only to the independently owned III.1.4 equivalence. -/
theorem heckeCompleteness_of_equivalence
    (hequiv : HeckeNondegenerateModuleEquivalenceStatement.{u, u}) :
    HeckeCompletenessStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ T hT
  let : NonarchimedeanGroup G :=
    { is_nonarchimedean := fun U hU => by
        obtain ⟨K, _, hKU⟩ := (Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp
          Langlands.Topology.isLocallyProfinite_of_mathlib |>.2 U hU
        exact ⟨K, hKU⟩ }
  obtain ⟨K, _, hK, hKT⟩ := TestFunction.commonCompactOpenBiInvariance G
    {HeckeAlgebra.toTestFunction μ T} (⊤ : OpenSubgroup G)
  let t : HeckeAlgebra.Corner μ K hK :=
    ⟨T, hKT _ (Finset.mem_singleton_self _)⟩
  have ht : t ≠ 0 := fun h => hT (congrArg Subtype.val h)
  let h := heckeCornerAdjoint μ K hK t * t
  have hh : h ≠ 0 := heckeCornerAdjoint_mul_self_ne_zero μ K hK t ht
  have hself : heckeCornerAdjoint μ K hK h = h := by
    dsimp only [h]
    rw [heckeCornerAdjoint_mul, heckeCornerAdjoint_involutive]
  have hnil := heckeCorner_selfAdjoint_not_isNilpotent μ K hK h hself hh
  obtain ⟨I, hnd, hadd, hnonzero⟩ := exists_separating_nondegenerate_quotient μ K hK h hnil
  let ρ := separatingQuotientAction μ I
  let := Langlands.Algebra.NonUnitalModule.ofLinearEndHom ρ
  have hex : ∃ m : Unitization ℂ (HeckeAlgebra μ) ⧸ I, h.val • m ≠ 0 := by
    by_contra! hzero
    apply hnonzero
    exact LinearMap.ext hzero
  obtain ⟨π, hi, hsep⟩ :=
    exists_irreducible_smoothRep_of_simple_heckeModule hequiv μ hnd hadd h.val hex
  have hπT : heckeAction μ π.representation π.isSmooth T ≠ 0 := by
    intro hzero
    apply hsep
    change heckeAction μ π.representation π.isSmooth (heckeAdjoint μ T * T) = 0
    rw [map_mul, hzero, mul_zero]
  obtain ⟨σ, hσ, ⟨e⟩⟩ := exists_irreducible_smoothRep_equiv_of_sigmaCompact.{u, v} hi
  refine ⟨σ, hσ, ?_⟩
  intro hzero
  apply hπT
  ext x
  apply e.injective
  have hc : e (heckeAction μ π.representation π.isSmooth T x) =
      heckeAction μ σ.representation σ.isSmooth T (e x) :=
    integratedAction_intertwiner μ π.isSmooth σ.isSmooth e.toIntertwiningMap T x
  rw [hzero, LinearMap.zero_apply] at hc
  exact hc.trans e.toLinearEquiv.map_zero.symm

end Langlands.Renard.Smooth
