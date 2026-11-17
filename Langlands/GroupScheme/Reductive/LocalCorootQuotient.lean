import Langlands.GroupScheme.Reductive.CorootRankOneQuotient
import Langlands.GroupScheme.Reductive.SimpleWallRankOneRelation
import Langlands.GroupScheme.Reductive.CorootCellExtensionGeometry
import Langlands.GroupScheme.Reductive.NormalizedLocalRootFamily

/-! # Actual local coroot quotients from the negative-simple cell law -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}

/-- Two actual parametrizations of the same root have the same points,
  with a scalar coordinate on every relative scheme test. -/
theorem IsRootParametrization.exists_rootPoint_eq
    {m : I → ℤ} {v w : Ga R ⟶ G}
    (hv : IsRootParametrization i m v) (hw : IsRootParametrization i m w)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    ∃ d : Γ(Z.left, ⊤), rootPoint w Z d = rootPoint v Z c := by
  have h : rootPoint v Z c ∈ (SubgroupFunctor.range w).carrier Z := by
    rw [hw.represents.2, ← hv.represents.2]
    exact SubgroupFunctor.mem_range.mpr ⟨RingRootCell.gpt c, rfl⟩
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp h
  refine ⟨(VectorGroup.coordinates (CommRingCat.of R) 1 Z z).toAdd 0, ?_⟩
  exact (congrArg (fun z => z ≫ w.hom.hom) (RingRootCell.eq_gpt z)).symm.trans hz

variable [IsLocalRing R] [DecidableEq I] [IsAffineHom G.X.hom]
  (hG : IsReductive G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
  (u : J → (Ga R ⟶ G)) (hu : ∀ α, IsRootParametrization i (P.root α) (u α))
  {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})

include hG hi hmax hP hu in
/-- Every negative-simple translation relation between actual full-cell
  points has the same value under the coroot cell projection. -/
theorem corootCellProjection_eq_of_negativeSimple_relation
    {a : J} (ha : a ∈ b.support)
    (v : Ga R ⟶ G) (hv : IsRootParametrization i (P.root (P.reflectionPerm a a)) v)
    {Z : Over (Spec (CommRingCat.of R))} (x y : Z ⟶ cellObj R I m n)
    (c : Γ(Z.left, ⊤))
    (hxy : (x ≫ cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))) *
      rootPoint v Z c = y ≫ cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))) :
    x ≫ RelativeDerived.corootCellProjection R I P m n =
      y ≫ RelativeDerived.corootCellProjection R I P m n := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hp : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hn : ¬ b.IsPos (P.reflectionPerm a a) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) a).mp h hp
  let kn := neg.symm ⟨P.reflectionPerm a a, hn⟩
  let kp := pos.symm ⟨a, hp⟩
  have hkn : (neg kn : J) = P.reflectionPerm a a :=
    congrArg Subtype.val (neg.apply_symm_apply _)
  have hkp : (pos kp : J) = a := congrArg Subtype.val (pos.apply_symm_apply _)
  obtain ⟨d, hd⟩ := hv.exists_rootPoint_eq (hu (P.reflectionPerm a a)) Z c
  rw [← hd] at hxy
  have hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y :=
    hP.pairing (IsLocalRing.ResidueField R)
  have hr := cellRankOnePart_mul_negativeSimple_of_cell_relation
    b hpair ha neg pos kn kp hkn hkp hu x y d hxy
  have hm : IsRootParametrization i (-P.root a) (u (P.reflectionPerm a a)) := by
    simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] using
      hu (P.reflectionPerm a a)
  have ht := rankOneQuotientLaw_corootProjection hG i hi hmax hP a (hu a) hm
    Z (negCoord x kn) (negCoord y kn) (posCoord x kp) (posCoord y kp) d
      (torusCoord x) (torusCoord y) hr
  simpa only [RelativeDerived.comp_corootCellProjection] using ht

include hG hi hmax hP hu in
/-- The required negative-simple generator relation for any Weyl family,
  with trivial root maps in the quotient. -/
theorem negSimpleRelations_corootCellProjection
    (W : ∀ α, SimpleWord P b α)
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) :
    NegSimpleRelations P
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (RelativeDerived.corootCellProjection R I P m n) b u
      (fun _ : J => (0 : Ga R ⟶ (RelativeDerived.corootQuotient (CommRingCat.of R) P).toGrp)) := by
  intro A _ _ _ s x y a ha hxy
  have hW := isRootParametrization_weylFamily (fun a _ => hu a) hw W
  have h := corootCellProjection_eq_of_negativeSimple_relation hG hi hmax hP b
    (weylFamily P W u) hW neg pos ha (u (P.reflectionPerm a a))
    (hu (P.reflectionPerm a a)) x y (-1) hxy
  simpa only [rootPoint, trivialRootMap_hom, MonObj.comp_one, mul_one] using h

include hG hi hmax hP hu in
/-- The actual coroot cell projection is compatible on all tests, with
  all generator laws now discharged over the local base. -/
theorem cellCompatible_corootCellProjection
    (W : ∀ α, SimpleWord P b α)
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) :
    CellGluing.CellCompatible
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (RelativeDerived.corootCellProjection R I P m n) := by
  apply RelativeDerived.cellCompatible_corootCellProjection_of_negSimpleRelations
    hG hmax hP W u (fun a _ => hu a) hw neg pos
  exact negSimpleRelations_corootCellProjection hG hi hmax hP b u hu neg pos W hw

end Langlands.GroupScheme.LocalSplitCell


namespace Langlands.GroupScheme.RelativeDerived

open LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P)

include hG hi hmax hP in
/-- An actual smooth surjective quotient with exactly the required torus
  restriction exists over every commutative local base. -/
theorem exists_localCorootQuotient :
    ∃ q : G ⟶ (corootQuotient (CommRingCat.of R) P).toGrp,
      i ≫ q = corootProjection (CommRingCat.of R) P ∧
      Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  obtain ⟨u, hu, hw⟩ := exists_normalizedLocalRootFamily hG i hi hmax hP b
  let W : ∀ α, SimpleWord P b α := descWord P b
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  have hW := isRootParametrization_weylFamily (fun a _ => hu a) hw W
  let := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _ hW neg pos
  have hc := cellCompatible_corootCellProjection hG hi hmax hP b u hu neg pos W hw
  exact ⟨(smoothCorootCellExtension hG hc).val,
    (smoothCorootCellExtension hG hc).property⟩

/-- The actual local quotient, together with its exact torus restriction,
  smoothness and surjectivity. -/
def localCorootQuotient :
    {q : G ⟶ (corootQuotient (CommRingCat.of R) P).toGrp //
      i ≫ q = corootProjection (CommRingCat.of R) P ∧
      Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left} :=
  ⟨(exists_localCorootQuotient hG i hi hmax hP).choose,
    (exists_localCorootQuotient hG i hi hmax hP).choose_spec⟩

end Langlands.GroupScheme.RelativeDerived
