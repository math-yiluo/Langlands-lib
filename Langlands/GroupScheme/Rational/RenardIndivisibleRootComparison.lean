import Langlands.GroupScheme.Rational.IndivisibleRootPairing
import Langlands.GroupScheme.Rational.RelativeRootCoxeterConstruction
import Langlands.GroupScheme.Rational.RenardRadicalWeightComparison

/-! # Actual simple roots and indivisible positive indecomposables -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRootSystem

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

namespace RelativeRootCoxeter

variable {R : Type u}
    (P : RootPairing R ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i)))
    (hT : IsSplitTorus T.toGrp)
    (hroots : Subtype.val '' Set.range P.root = toRat '' relativeRoots i)

omit [Mono i.hom.hom.left] in
/-- Integral root multiples agree before and after rationalization. -/
theorem root_eq_nsmul_iff (a b : R) (n : ℕ) :
    P.root a = n • P.root b ↔
      (rootIndexEquiv P hT hroots a).val =
        n • (rootIndexEquiv P hT hroots b).val := by
  rw [← rootVector_rootIndexEquiv P hT hroots a,
    ← rootVector_rootIndexEquiv P hT hroots b]
  constructor
  · intro h
    apply hT.character_toRat_injective
    simpa only [rootVector, Submodule.coe_smul_of_tower, map_nsmul] using
      congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    change toRat _ = n • toRat _
    rw [h, map_nsmul]

omit [Mono i.hom.hom.left] in
/-- Indivisibility in the witness is exactly indivisibility among actual roots. -/
theorem mem_indivisibleIndices_iff (a : R) :
    a ∈ P.indivisibleIndices ↔
      (rootIndexEquiv P hT hroots a).val ∈ RelativeRoot.indivisibleRoots i := by
  let e := rootIndexEquiv P hT hroots
  constructor
  · intro ha
    refine ⟨(e a).property, ?_⟩
    intro β hβ n hn heq
    let b := e.symm ⟨β, hβ⟩
    have hb : (e b).val = β := congrArg Subtype.val (e.apply_symm_apply ⟨β, hβ⟩)
    apply ha b n (by omega)
    apply (root_eq_nsmul_iff P hT hroots a b n).mpr
    change (e a).val = n • (e b).val
    rw [hb, heq]
  · intro ha b n hn heq
    exact ha.2 (e b).val (e b).property n (by omega)
      ((root_eq_nsmul_iff P hT hroots a b n).mp heq).symm

end RelativeRootCoxeter

namespace RelativeRoot

/-- Comparison of indecomposables using the indivisible and the full positive roots. -/
def IndivisiblePositiveRootComparison (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) : Prop :=
  {α | α ∈ indivisiblePositiveRoots i ν ∧
    ¬ ∃ β ∈ indivisiblePositiveRoots i ν,
      ∃ γ ∈ indivisiblePositiveRoots i ν, α = β + γ} =
    simpleRelativeRoots i ν

end RelativeRoot

/-- The actual simple-root comparison follows from the structural root-system
witness; no reducedness or positive-rank hypothesis is used. -/
theorem HasRelativeRootSystem.indivisiblePositiveRootComparison
    (hR : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν) :
    RelativeRoot.IndivisiblePositiveRootComparison i ν := by
  classical
  obtain ⟨R, hRfin, P, _, hcrys, _, hroots, _, _⟩ := hR
  have := hRfin
  have := hcrys
  let e := RelativeRootCoxeter.rootIndexEquiv P hT hroots
  let f : relativeRootSpan i →+ ℚ := corootFunctional i ν
  let Q := P.indivisiblePairing
  have hf (r : R) : f (P.root r) ≠ 0 := by
    change corootFunctional i ν (P.root r) ≠ 0
    rw [RelativeRootCoxeter.functional_root P hT hroots]
    exact_mod_cast hν (e r).val (e r).property
  have hpos (r : R) :
      0 < f (P.root r) ↔ 0 < latticePairing T (e r).val ν := by
    change 0 < corootFunctional i ν (P.root r) ↔ _
    rw [RelativeRootCoxeter.functional_root P hT hroots, Int.cast_pos]
  have hind (r : R) :
      r ∈ P.indivisibleIndices ↔ (e r).val ∈ RelativeRoot.indivisibleRoots i :=
    RelativeRootCoxeter.mem_indivisibleIndices_iff P hT hroots r
  change {α | α ∈ RelativeRoot.indivisiblePositiveRoots i ν ∧
    ¬ ∃ β ∈ RelativeRoot.indivisiblePositiveRoots i ν,
      ∃ γ ∈ RelativeRoot.indivisiblePositiveRoots i ν, α = β + γ} = _
  ext α
  constructor
  · rintro ⟨ha, hndecomp⟩
    let r := e.symm ⟨α, ha.1.1⟩
    have her : (e r).val = α :=
      congrArg Subtype.val (e.apply_symm_apply ⟨α, ha.1.1⟩)
    have hr : r ∈ P.indivisibleIndices := (hind r).mpr (her ▸ ha.1)
    let r' : P.indivisibleIndices := ⟨r, hr⟩
    have hbase : r' ∈ IsAddIndecomposable.baseOf Q.root f := by
      refine ⟨?_, fun b hb c hc heq => ?_⟩
      · change 0 < f (P.root r)
        exact (hpos r).mpr (her ▸ ha.2)
      · exfalso
        apply hndecomp
        refine ⟨(e b.val).val, ⟨(hind b.val).mp b.property,
          (hpos b.val).mp hb⟩, (e c.val).val,
          ⟨(hind c.val).mp c.property, (hpos c.val).mp hc⟩, ?_⟩
        apply hT.character_toRat_injective
        rw [map_add, ← her]
        have hv := congrArg Subtype.val heq
        simpa only [Q, RootPairing.indivisiblePairing_root, r',
          ← RelativeRootCoxeter.rootVector_rootIndexEquiv P hT hroots,
          rootVector, Submodule.coe_add] using hv
    have hv : Q.root r' ∈ P.root '' IsAddIndecomposable.baseOf P.root f := by
      rw [← P.image_baseOf_indivisiblePairing f hf]
      exact ⟨r', hbase, rfl⟩
    obtain ⟨s, hs, hsr⟩ := hv
    have hsr' : s = r := P.root.injective hsr
    subst s
    have hs' := (RelativeRootCoxeter.mem_base_iff P hT hroots ν r).mp hs
    rwa [her] at hs'
  · intro ha
    let r := e.symm ⟨α, ha.1.1⟩
    have her : (e r).val = α :=
      congrArg Subtype.val (e.apply_symm_apply ⟨α, ha.1.1⟩)
    have hbase : r ∈ IsAddIndecomposable.baseOf P.root f :=
      (RelativeRootCoxeter.mem_base_iff P hT hroots ν r).mpr (her ▸ ha)
    have hr := P.mem_indivisibleIndices_of_mem_baseOf f hbase
    have har : α ∈ RelativeRoot.indivisibleRoots i := her ▸ (hind r).mp hr
    refine ⟨⟨har, ha.1.2⟩, ?_⟩
    rintro ⟨β, hβ, γ, hγ, heq⟩
    exact ha.2 ⟨β, ⟨hβ.1.1, hβ.2⟩, γ, ⟨hγ.1.1, hγ.2⟩, heq⟩

/-- The remaining structural premise for the Renard comparison assembly. -/
def RenardRootConventionFromRootSystemStatement : Prop :=
  RelativeRootSystemStatement.{u} → RenardRootConventionStatement.{u}

/-- The root-system statement supplies the only remaining premise in the
four-comparison assembly. -/
theorem renardRootConventionStatement_of_relativeRootSystem :
    RenardRootConventionFromRootSystemStatement.{u} := by
  intro hroot k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro hν
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  dsimp only
  rw [RelativeRoot.nonzero_actionWeightSupport_dynamicUnipotent hT i ν,
    RelativeRoot.indivisibleRoots_inter_positiveRelativeRoots i ν]
  refine ⟨rfl, rfl,
    RelativeRoot.indivisiblePositiveRoots_eq_reducedPositiveRelativeRoots i ν, ?_⟩
  exact (hroot k G hG T i hi).indivisiblePositiveRootComparison hT hν

end Langlands.GroupScheme
