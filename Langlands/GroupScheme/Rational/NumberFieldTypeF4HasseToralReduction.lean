import Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction
import Langlands.GroupScheme.Rational.NumberFieldQuadraticToralReductionStatement
import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesInjectivity
import Langlands.GroupScheme.SimplyConnected.TypeF4LongRootSubgroupStatement
import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionProof
import Langlands.GroupScheme.Rational.SteinbergAssembly
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan
import Langlands.GroupScheme.Reductive.FullRootSpanCenter
import Langlands.GroupScheme.Reductive.GeometricAdjoint
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.InnerFormStarActionProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceProof
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.Reductive.TitsPrescribedStabilizerField
import Langlands.GroupScheme.CocycleDescent
import Langlands.GroupScheme.CocycleFpqcBaseCover

/-! # The type `F₄` Hasse kernel from toral reductions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj


namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Cocycle

variable {S : Scheme.{u}} {G H K : GroupScheme S} {U : Over S}

private theorem eq_of_toFun_eq' {ξ ζ : Cocycle G U}
    (h : ∀ {Z : Over S} (x y : Z ⟶ U), ξ.toFun x y = ζ.toFun x y) : ξ = ζ := by
  cases ξ
  cases ζ
  congr
  funext Z x y
  exact h x y

private theorem map_map' (ξ : Cocycle G U) (f : G ⟶ H) (g : H ⟶ K) :
    (ξ.map f).map g = ξ.map (f ≫ g) := by
  apply eq_of_toFun_eq'
  intro Z x y
  change (ξ.toFun x y ≫ f.hom.hom) ≫ g.hom.hom = ξ.toFun x y ≫ (f ≫ g).hom.hom
  simp only [Grp.comp_hom_hom, Category.assoc]

private theorem isTrivial_of_cohomologous {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ)
    (hζ : ζ.IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := h
  apply IsTrivial.of_twist (f := f)
  obtain ⟨g, hg⟩ := hζ
  exact ⟨g, fun a b => (hf a b).symm.trans (hg a b)⟩

private theorem cohomologous_of_isTrivial' {c d : Cocycle G U} (hc : c.IsTrivial)
    (hd : d.IsTrivial) : c.Cohomologous d := by
  obtain ⟨f, hf⟩ := hc
  obtain ⟨g, hg⟩ := hd
  refine ⟨f * g⁻¹, fun x y => ?_⟩
  simp only [Cocycle.twist, MonObj.comp_mul, GrpObj.comp_inv, hf, hg]
  group

end Cocycle

open Cocycle

/-- The Hasse kernel for every simply connected absolutely almost-simple group of type
`D₄`: a fixed leaf gives the classical type `D` case, otherwise the group is
trialitarian. -/
theorem numberFieldTypeD4Hasse_of_quaternionic_trialitarian
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u})
    (htri : NumberFieldTrialitarianTypeDHasseStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (he : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  by_cases hleaf : ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a = a
  · obtain ⟨a, ha, hfix⟩ := hleaf
    exact numberFieldClassicalTypeDHasse_of_quaternionic hquat F G d 4
      (d.d4NumberingAt e a) le_rfl hsc habs (d.d4NumberingAt_cartan e he a ha)
      (fun τ b hb => d.star_fixes_nonfork_of_D4_fixed_leaf e he a ha hfix τ b hb) L ξ hξ
  · push Not at hleaf
    exact htri F G d e hsc habs he hleaf L ξ hξ

/-- A torus cocycle that is trivial at the real places has trivial image in a group of
type `F₄`: it lies in a simply connected subgroup of type `D₄`, where it is trivial at
every place. -/
theorem typeF4_torusCocycle_isTrivial
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u})
    (htri : NumberFieldTrialitarianTypeDHasseStatement.{u})
    (hlong : TypeF4LongRootSubgroupStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (he : ∀ a b, d.cartan a b = CartanMatrix.F₄ (e a) (e b))
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ν : Cocycle T.toGrp (GaloisCocycle.cover F L))
    (hνr : ∀ w : InfinitePlace F, w.IsReal →
      let b := algebraBaseMap F (Global.placeCompletion F (.inl w))
      let r := (Over.mapPullbackAdj b).counit.app (GaloisCocycle.cover F L)
      (ν.baseChange b _ r).IsTrivial) :
    (ν.map i).IsTrivial := by
  obtain ⟨H, j, f, -, hfj, hHsc, hHabs, hA, hL, dH, eH, hcartH⟩ :=
    hlong F G d e hsc habs he T i hi
  let ζ : Cocycle H (GaloisCocycle.cover F L) := Cocycle.coboundary 1
  have hζ : ζ.IsTrivial := ⟨1, fun a b => rfl⟩
  have hloc : (ν.map f).LocallyCohomologous ζ := by
    refine simplyConnectedRealToAllPlacesComparison F H hHsc L (ν.map f) ζ ?_
    intro w hw
    dsimp only
    refine cohomologous_of_isTrivial' ?_ (hζ.baseChange _ _ _)
    obtain ⟨g, hg⟩ := (hνr w hw).map ((GroupScheme.baseChange _).map f)
    exact ⟨g, fun a c => (baseChange_map_toFun _ _ _ _ _ a c).trans (hg a c)⟩
  have hlt : (ν.map f).LocallyTrivial := by
    intro v
    exact isTrivial_of_cohomologous (hloc v) (hζ.baseChange _ _ _)
  have := (numberFieldTypeD4Hasse_of_quaternionic_trialitarian hquat htri F H dH eH hHsc
    hHabs hcartH L (ν.map f) hlt).map j
  rwa [map_map', hfj] at this

/-- A simply connected group whose Tits index has a Cartan matrix of type `F₄` has trivial
full centre: the Cartan determinant is one, so the roots span the character lattice of the
split torus over the separable closure. -/
theorem typeF4_center_eq_bot {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (he : ∀ a b, d.cartan a b = CartanMatrix.F₄ (e a) (e b)) :
    center G = ⊥ := by
  have hc := d.natCard_centerCharacter_eq_cartanDet hsc e CartanMatrix.F₄ he
  rw [CartanMatrix.F₄_det] at hc
  have hq : Nat.card (characterLattice d.pinning.toSplitPinning.torus ⧸
      d.pinning.rootDatum.rootSpan ℤ) = 1 :=
    (Nat.card_congr d.centerCharacterQuotientEquiv.toEquiv).trans hc
  have : Finite (characterLattice d.pinning.toSplitPinning.torus ⧸
      d.pinning.rootDatum.rootSpan ℤ) := Nat.finite_of_card_ne_zero (by rw [hq]; decide)
  have hsub : Subsingleton (characterLattice d.pinning.toSplitPinning.torus ⧸
      d.pinning.rootDatum.rootSpan ℤ) :=
    Finite.card_le_one_iff_subsingleton.mp hq.le
  have hspan : d.pinning.rootDatum.rootSpan ℤ = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hsub
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (SeparableClosure k)
  rw [← center_eq_bot_baseChange_iff G (algebraBaseMap k (SeparableClosure k))]
  exact center_eq_bot_of_full_rootSpan d.pinning.isConnectedReductive d.pinning.isSplitTorus
    _ d.pinning.isMaximalTorus d.pinning.rootDatum d.pinning.isRootDatum hspan

/-- Over a number field without real places, every finite-Galois cocycle of a quasi-split
group of type `F₄` is trivial: Steinberg's torus reduction puts it in a torus, which lies in
a maximal torus, and the torus lemma applies with no condition at real places. -/
theorem typeF4_quasiSplit_totallyComplex_isTrivial
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u})
    (htri : NumberFieldTrialitarianTypeDHasseStatement.{u})
    (hlong : TypeF4LongRootSubgroupStatement.{u})
    (F : Type u) [Field F] [NumberField F] (hF : ∀ w : InfinitePlace F, ¬ w.IsReal)
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (he : ∀ a b, d.cartan a b = CartanMatrix.F₄ (e a) (e b)) (hqs : IsQuasiSplit G)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))))) :
    ξ.IsTrivial := by
  obtain ⟨R⟩ := quasiSplitCocycleTorusReduction F G hsc.isSemisimple hqs L ξ
  let : IsClosedImmersion R.inclusion.hom.hom.left := R.isClosedSubgroup
  let : Mono R.inclusion.hom.hom := Over.mono_of_mono_left _
  let : QuasiCompact R.refinement.left := R.quasiCompact_refinement
  let : Flat R.refinement.left := R.flat_refinement
  let : Surjective R.refinement.left := R.surjective_refinement
  let T : CommGroupScheme (Spec (CommRingCat.of F)) :=
    { R.torus with comm := R.isTorus.isCommMonObj }
  obtain ⟨M, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G (T := T) R.inclusion R.isTorus
      R.isClosedSubgroup
  have h₁ : ((R.torusCocycle.map f).map j).IsTrivial :=
    typeF4_torusCocycle_isTrivial hquat htri hlong F G d e hsc habs he M j hj R.carrier
      (R.torusCocycle.map f) (fun w hw => (hF w hw).elim)
  rw [map_map', hf] at h₁
  have h₂ : R.torusCocycle.map R.inclusion = (ξ.refine R.refinement).twist R.cochain := by
    apply eq_of_toFun_eq'
    intro Z x y
    exact Cocycle.lift_toFun _ _ _ x y
  rw [h₂] at h₁
  exact (ξ.isTrivial_refine_iff R.refinement).mp h₁.of_twist

/-- An adjoint quotient of a group with trivial full centre is an isomorphism. -/
theorem IsAdjointQuotient.isIso_of_center_eq_bot {k : Type u} [Field k]
    {H A : GroupScheme (Spec (CommRingCat.of k))} {q : H ⟶ A} (hq : IsAdjointQuotient q)
    (hc : center H = ⊥) : IsIso q := by
  have hk : KillsCenter (𝟙 H) := by
    intro T x hx
    rw [hc, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    rw [hx]
    rfl
  obtain ⟨g, hg, -⟩ := hq.groupUniversal H (𝟙 H) hk
  obtain ⟨g', -, hg'⟩ := hq.groupUniversal A q hq.killsCenter
  have h₁ : g ≫ q = 𝟙 A := by
    have ha := hg' (g ≫ q) (by
      change q ≫ g ≫ q = q
      rw [← Category.assoc, hg, Category.id_comp])
    have hb := hg' (𝟙 A) (Category.comp_id q)
    exact ha.trans hb.symm
  exact ⟨g, hg, h₁⟩

/-- A local isomorphism with a discrepancy cocycle has inner discrepancy. -/
theorem LocalGroupIso.hasInnerDiscrepancy_of_hasDiscrepancy {S : Scheme.{u}}
    {G H A : GroupScheme S} {U : Over S} (e : LocalGroupIso G H U) (a : AutomorphicAction A G)
    (ξ : Cocycle A U) (h : e.HasDiscrepancy a ξ) : e.HasInnerDiscrepancy a := by
  intro T b c
  refine ⟨ξ.toFun b c, fun t g => ?_⟩
  rw [← ξ.naturality]
  exact h (t ≫ b) (t ≫ c) g

/-- Over a number field without real places, every finite-Galois cocycle of a group of
type `F₄` is trivial. The quasi-split inner form is again of type `F₄` with trivial centre,
so its adjoint discrepancy is a cocycle of a quasi-split group of type `F₄`, hence trivial;
the group is then quasi-split itself. -/
theorem typeF4_totallyComplex_isTrivial
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u})
    (htri : NumberFieldTrialitarianTypeDHasseStatement.{u})
    (hlong : TypeF4LongRootSubgroupStatement.{u})
    (F : Type u) [Field F] [NumberField F] (hF : ∀ w : InfinitePlace F, ¬ w.IsReal)
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (he : ∀ a b, d.cartan a b = CartanMatrix.F₄ (e a) (e b))
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))))) :
    ξ.IsTrivial := by
  obtain ⟨Q⟩ := quasiSplitInnerFormExistence F G hsc.isSemisimple.isConnectedReductive
  let H := Q.model
  let M := Q.carrier
  let eM : (GroupScheme.baseChange (algebraBaseMap F M)).obj H ≅
      (GroupScheme.baseChange (algebraBaseMap F M)).obj G := Q.localIso.toBaseChangeIso
  have hHsc : IsSimplyConnected H :=
    (isSimplyConnected_fieldExtension_iff (K := M) H).mp
      ((isSimplyConnected_iff_of_iso eM).mpr
        ((isSimplyConnected_fieldExtension_iff (K := M) G).mpr hsc))
  have hHabs : IsAbsolutelyAlmostSimple H :=
    IsAbsolutelyAlmostSimple.of_fieldExtension (K := M)
      ((habs.baseChange_of_algebraicExtension (K := M)).of_iso eM)
  let hR := hHsc.isSemisimple.isConnectedReductive
  let : IsAffineHom H.X.hom := hR.isAffineHom
  let : Smooth H.X.hom := hR.smooth
  obtain ⟨dH⟩ := titsIndexExistence F H hHsc.isSemisimple
  obtain ⟨f, hfbase, -⟩ := (innerFormStarAction F H G Q.adjoint Q.quotient Q.isAdjointQuotient
    dH.pinning d.pinning).mp ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
      Q.localIso, Q.localIso.hasInnerDiscrepancy_of_hasDiscrepancy _ _ Q.hasDiscrepancy⟩
  let v : dH.Vertex ≃ d.Vertex := f.indexEquiv.subtypeEquiv hfbase
  have hcartH : ∀ a b, dH.cartan a b = CartanMatrix.F₄ ((v.trans e) a) ((v.trans e) b) := by
    intro a b
    rw [Equiv.trans_apply, Equiv.trans_apply, ← he]
    exact (f.toHom.pairing (i := a.val) (j := b.val)).symm
  have hcH : center H = ⊥ := typeF4_center_eq_bot dH (v.trans e) hHsc hcartH
  have hiso : IsIso Q.quotient := Q.isAdjointQuotient.isIso_of_center_eq_bot hcH
  have hc' : (Q.cocycle.map (inv Q.quotient)).IsTrivial :=
    typeF4_quasiSplit_totallyComplex_isTrivial hquat htri hlong F hF H dH (v.trans e) hHsc
      hHabs hcartH Q.isQuasiSplit M (Q.cocycle.map (inv Q.quotient))
  have hc : Q.cocycle.IsTrivial := by
    have := hc'.map Q.quotient
    rwa [map_map', IsIso.inv_hom_id, show Q.cocycle.map (𝟙 Q.adjoint) = Q.cocycle from
      eq_of_toFun_eq' (fun x y => Category.comp_id _)] at this
  exact typeF4_quasiSplit_totallyComplex_isTrivial hquat htri hlong F hF G d e hsc habs he
    (Q.isQuasiSplit_of_isTrivial hc) L ξ

/-! ### A totally complex quadratic extension -/

set_option backward.isDefEq.respectTransparency true in
/-- A number field with a real place has no square root of `-1`. -/
private theorem not_sq_eq_neg_one_of_isReal {K : Type u} [Field K] [NumberField K]
    {w : InfinitePlace K} (hw : w.IsReal) (x : K) : x ^ 2 ≠ -1 := by
  intro hx
  have h := congrArg (InfinitePlace.embedding_of_isReal hw) hx
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw x)]

set_option backward.isDefEq.respectTransparency true in
/-- Adjoining a square root of `-1` inside the separable closure gives a quadratic,
totally complex extension of a number field with a real place. -/
theorem exists_totallyComplex_quadratic (F : Type u) [Field F] [NumberField F]
    {w₀ : InfinitePlace F} (hw₀ : w₀.IsReal) :
    ∃ E : IntermediateField F (SeparableClosure F), FiniteDimensional F E ∧
      Module.finrank F E = 2 ∧
      ∀ (_ : NumberField E) (w : InfinitePlace E), ¬ w.IsReal := by
  classical
  let Ω := SeparableClosure F
  obtain ⟨r₀, hr₀⟩ := IsSepClosed.exists_root (k := Ω) (Polynomial.X ^ 2 - Polynomial.C (-1))
    (by rw [Polynomial.degree_X_pow_sub_C two_pos]; decide)
    (Polynomial.separable_X_pow_sub_C (-1) (by norm_num) (by norm_num))
  have hr₀2 : r₀ ^ 2 = -1 := by
    have h : r₀ ^ 2 + 1 = 0 := by simpa [Polynomial.IsRoot] using hr₀
    linear_combination h
  let p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (-1)
  have hpm : p.Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hpdeg : p.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  have hpirr : Irreducible p := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hpdeg]; decide
    · intro x hx
      apply not_sq_eq_neg_one_of_isReal hw₀ x
      have h : x ^ 2 + 1 = 0 := by simpa [p, Polynomial.IsRoot] using hx
      linear_combination h
  have hroot : Polynomial.aeval r₀ p = 0 := by
    simp [p, hr₀2]
    ring
  have hint : IsIntegral F r₀ := ⟨p, hpm, by rwa [Polynomial.aeval_def] at hroot⟩
  have hmin : minpoly F r₀ = p := (minpoly.eq_of_irreducible_of_monic hpirr hroot hpm).symm
  refine ⟨IntermediateField.adjoin F {r₀}, IntermediateField.adjoin.finiteDimensional hint, ?_, ?_⟩
  · rw [IntermediateField.adjoin.finrank hint, hmin, hpdeg]
  · intro _ w hw
    let y : IntermediateField.adjoin F {r₀} := ⟨r₀, IntermediateField.mem_adjoin_simple_self F r₀⟩
    apply not_sq_eq_neg_one_of_isReal hw y
    apply Subtype.ext
    simp [y, hr₀2]

/-! ### Assembly -/

/-- The type `F₄` Hasse kernel over number fields follows from the quaternionic spin kernel,
the trialitarian type `D₄` kernel, the long-root subgroup statement for type `F₄` and the
quadratic toral reduction over number fields. -/
def NumberFieldTypeF4HasseToralReductionStatement : Prop :=
  NumberFieldQuaternionicSpinHasseStatement.{u} →
    NumberFieldTrialitarianTypeDHasseStatement.{u} →
    TypeF4LongRootSubgroupStatement.{u} →
    NumberFieldQuadraticToralReductionStatement.{u} →
    NumberFieldTypeF4HasseStatement.{u}

private theorem eq_refine_of_toFun {S : Scheme.{u}} {G : GroupScheme S} {U V : Over S}
    (ζ : Cocycle G V) (ν : Cocycle G U) (p : V ⟶ U)
    (h : ∀ {Z : Over S} (a b : Z ⟶ V), ν.toFun (a ≫ p) (b ≫ p) = ζ.toFun a b) :
    ν.refine p = ζ :=
  Cocycle.eq_of_toFun_eq' (fun a b => h a b)

set_option maxHeartbeats 1600000 in
/-- The type `F₄` Hasse kernel follows from the quaternionic spin and trialitarian `D₄`
kernels, the long-root subgroup statement and the quadratic toral reduction. Over a field
with a real place, adjoin a square root of `-1`: over this totally complex quadratic
extension the cocycle becomes trivial, so it comes from the quadratic cover, where it is
cohomologous to a torus cocycle trivial at the real places; the torus lemma finishes. -/
theorem numberFieldTypeF4Hasse_of_longRoot_quadratic
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u})
    (htri : NumberFieldTrialitarianTypeDHasseStatement.{u})
    (hlong : TypeF4LongRootSubgroupStatement.{u})
    (hquad : NumberFieldQuadraticToralReductionStatement.{u}) :
    NumberFieldTypeF4HasseStatement.{u} := by
  intro F _ _ G _ _ d e hsc habs he L _ _ _ _ ξ hξ
  by_cases hF : ∀ w : InfinitePlace F, ¬ w.IsReal
  · exact typeF4_totallyComplex_isTrivial hquat htri hlong F hF G d e hsc habs he L ξ
  push Not at hF
  obtain ⟨w₀, hw₀⟩ := hF
  obtain ⟨E, hEfin, hE2, hEc⟩ := exists_totallyComplex_quadratic F hw₀
  let : NumberField E := NumberField.of_module_finite F E
  have : Algebra.IsQuadraticExtension F E := ⟨hE2⟩
  have : IsGalois F E := inferInstance
  -- A finite Galois extension of `E` receiving `L`.
  let pb := Field.powerBasisOfFiniteOfSeparable F L
  let f : Polynomial E := (minpoly F pb.gen).map (algebraMap F E)
  let M := Polynomial.SplittingField f
  have hfsep : f.Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)
  have : IsGalois E M := IsGalois.of_separable_splitting_field hfsep
  have : FiniteDimensional F M := Module.Finite.trans E M
  obtain ⟨y, hy⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_map]
    exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral pb.gen)).ne')
  have hy' : Polynomial.aeval y (minpoly F pb.gen) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, IsScalarTower.algebraMap_eq F E M,
      ← Polynomial.map_map]
    exact hy
  let j : L →ₐ[F] M := pb.lift y hy'
  -- The covers.
  let UM : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M)))
  let UE : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))
  let UL : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L)))
  let ξL : Cocycle G UL := ξ
  have hξL : ξL.LocallyTrivial := hξ
  let s : UM ⟶ UL :=
    Over.homMk (Spec.map (CommRingCat.ofHom j.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact j.commutes x)
  let p : UM ⟶ UE :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E M))) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  obtain ⟨hMs, hMf, hMq⟩ := fieldExtension_fpqc F M
  have : QuasiCompact UM.hom := hMq
  have : Flat UM.hom := hMf
  have : Surjective UM.hom := hMs
  obtain ⟨hEMs, hEMf, hEMq⟩ := fieldExtension_fpqc E M
  have : QuasiCompact p.left := hEMq
  have : Flat p.left := hEMf
  have : Surjective p.left := hEMs
  let : Algebra L M := j.toRingHom.toAlgebra
  obtain ⟨hLMs, hLMf, hLMq⟩ := fieldExtension_fpqc L M
  have : QuasiCompact s.left := hLMq
  have : Flat s.left := hLMf
  have : Surjective s.left := hLMs
  let ξM : Cocycle G UM := ξL.refine s
  -- Base change to the totally complex field `E`.
  let b := algebraBaseMap F E
  let V : Over (Spec (CommRingCat.of E)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap E M)))
  let r : (Over.map b).obj V ⟶ UM := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])
  let r' : UM ⟶ (Over.map b).obj V := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (Spec.map _ ≫ Spec.map _) = Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])
  have hrr : r' ≫ r = 𝟙 UM := by
    apply Over.OverMorphism.ext
    simp [r, r']
  let GE := (GroupScheme.baseChange b).obj G
  have hscE : IsSimplyConnected GE := (isSimplyConnected_fieldExtension_iff (K := E) G).mpr hsc
  have habsE : IsAbsolutelyAlmostSimple GE := habs.baseChange_of_algebraicExtension (K := E)
  let : IsAffineHom GE.X.hom := hscE.isSemisimple.isConnectedReductive.isAffineHom
  let : Smooth GE.X.hom := hscE.isSemisimple.isConnectedReductive.smooth
  let C := d.prescribedStabilizerIndexComparison E
  have heE : ∀ a b, C.index.cartan a b =
      CartanMatrix.F₄ ((C.vertices.symm.trans e) a) ((C.vertices.symm.trans e) b) := by
    intro a b
    rw [Equiv.trans_apply, Equiv.trans_apply, ← he, ← C.cartan_eq, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have hζ : (ξM.baseChange b V r).IsTrivial :=
    typeF4_totallyComplex_isTrivial hquat htri hlong E (hEc inferInstance) GE C.index
      (C.vertices.symm.trans e) hscE habsE heE M (ξM.baseChange b V r)
  obtain ⟨f₀, hf₀⟩ := Cocycle.exists_of_baseChange_isTrivial b ξM V r hζ
  let c : UM ⟶ G.X := r' ≫ f₀
  let ζ' : Cocycle G UM := ξM.twist c
  have hfib : ∀ {Z : Over (Spec (CommRingCat.of F))} (a a' : Z ⟶ UM),
      a ≫ p = a' ≫ p → ζ'.toFun a a' = 1 := by
    intro Z a a' haa
    have h := hf₀ (a ≫ r') (a' ≫ r') (by
      have := congrArg CommaMorphism.left haa
      simpa [r', p, V] using this)
    rw [Category.assoc, Category.assoc, hrr, Category.comp_id, Category.comp_id] at h
    change (a ≫ c)⁻¹ * ξM.toFun a a' * (a' ≫ c) = 1
    rw [h]
    simp only [c, Category.assoc]
    group
  obtain ⟨ν, hν⟩ := Cocycle.exists_refine_eq_of_comp_eq ζ' p hfib
  have hνp : ν.refine p = ζ' := eq_refine_of_toFun ζ' ν p hν
  -- Triviality of `ν` at the real places.
  have hνreal : ∀ w : InfinitePlace F, w.IsReal →
      let bw := algebraBaseMap F (Global.placeCompletion F (.inl w))
      let rw := (Over.mapPullbackAdj bw).counit.app (GaloisCocycle.cover F E)
      (ν.baseChange bw _ rw).IsTrivial := by
    intro w hw
    dsimp only
    let bw := algebraBaseMap F (Global.placeCompletion F (.inl w))
    have hL : (ξL.baseChange bw _ ((Over.mapPullbackAdj bw).counit.app UL)).IsTrivial :=
      hξL (.inl w)
    have hM : (ξM.baseChange bw _ ((Over.mapPullbackAdj bw).counit.app UM)).IsTrivial := by
      obtain ⟨g, hg⟩ := hL.refine ((Over.pullback bw).map s)
      exact ⟨g, fun x y => (baseChange_pullback_refine_toFun ξL s bw x y).trans (hg x y)⟩
    have hζw : (ζ'.baseChange bw _ ((Over.mapPullbackAdj bw).counit.app UM)).IsTrivial :=
      isTrivial_of_cohomologous
        ((Cohomologous.baseChange ⟨c, fun _ _ => rfl⟩ bw _ _).symm) hM
    have hνw : ((ν.baseChange bw _ ((Over.mapPullbackAdj bw).counit.app UE)).refine
        ((Over.pullback bw).map p)).IsTrivial := by
      obtain ⟨g, hg⟩ := hζw
      refine ⟨g, fun x y => ?_⟩
      rw [← baseChange_pullback_refine_toFun ν p bw x y, hνp]
      exact hg x y
    have : QuasiCompact ((Over.pullback bw).obj UM).hom :=
      inferInstanceAs (QuasiCompact (CategoryTheory.Limits.pullback.snd UM.hom bw))
    have : Flat ((Over.pullback bw).obj UM).hom :=
      inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd UM.hom bw))
    have : Surjective ((Over.pullback bw).obj UM).hom :=
      inferInstanceAs (Surjective (CategoryTheory.Limits.pullback.snd UM.hom bw))
    let one : Cocycle ((GroupScheme.baseChange bw).obj G) ((Over.pullback bw).obj UE) :=
      Cocycle.coboundary 1
    have hone : one.IsTrivial := ⟨1, fun _ _ => rfl⟩
    have hcoh := Cohomologous.of_refine_fpqcCover ((Over.pullback bw).map p)
      (cohomologous_of_isTrivial' hνw (hone.refine _))
    exact isTrivial_of_cohomologous hcoh hone
  obtain ⟨T, i, θ, hi, hθ, hcoh⟩ :=
    hquad F G hsc.isSemisimple.isConnectedReductive E hE2 ν hνreal
  have hνt : ν.IsTrivial := isTrivial_of_cohomologous hcoh
    (typeF4_torusCocycle_isTrivial hquat htri hlong F G d e hsc habs he T i hi E θ hθ)
  have hζ't : ζ'.IsTrivial := hνp ▸ hνt.refine p
  exact (ξL.isTrivial_refine_iff s).mp hζ't.of_twist

/-- The implication `NumberFieldTypeF4HasseToralReductionStatement` holds. -/
theorem numberFieldTypeF4HasseToralReduction :
    NumberFieldTypeF4HasseToralReductionStatement.{u} :=
  fun hquat htri hlong hquad =>
    numberFieldTypeF4Hasse_of_longRoot_quadratic hquat htri hlong hquad

end Langlands.GroupScheme
