import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial

/-! # Actual torus-equivariant vector coordinates without higher roots -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Convert vectors of global functions on `Spec k` to vectors over `k`. -/
def rootVectorRationalCoeffEquiv (n : ℕ) :
    Multiplicative (Fin n → Γ(Spec (CommRingCat.of k), ⊤)) ≃*
      Multiplicative (Fin n → k) where
  toFun x := Multiplicative.ofAdd fun j =>
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom (x.toAdd j)
  invFun x := Multiplicative.ofAdd fun j =>
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv (x.toAdd j)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext j
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext j
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply _
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext j
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.map_add _ _

/-- Positive finite vector coordinates on the actual rational root subgroup,
with the prescribed split torus acting through its actual root character. -/
structure WeightedRootVectorCoordinates (i : S.toGrp ⟶ G) (a : characterLattice S) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  equiv : Multiplicative (Fin dimension → k) ≃* rootGroupPoints i a
  conjugation : ∀ (s : rationalPoints S.toGrp) (x : Fin dimension → k),
    rationalPoints.map i s * (equiv (Multiplicative.ofAdd x) : rationalPoints G) *
        (rationalPoints.map i s)⁻¹ =
      (equiv (Multiplicative.ofAdd
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : k)
          • x)) : rationalPoints G)

/-- The actual cyclic quotient with trivial next term supplies equivariant
vector coordinates. No root-coordinate premise is assumed. -/
theorem nonempty_weightedRootVectorCoordinates_of_noHigherRoots
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hhigh : RelativeRoot.HasNoHigherRoots i a) :
    Nonempty (WeightedRootVectorCoordinates i a) := by
  obtain ⟨H, j, hj, _⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hS i a ha.1
  let b := AutomorphicAction.conjugation i
  have hfirst : RelativeRoot.weightFiltration b a 1 = RelativeRoot.subgroup i a :=
    RelativeRoot.cyclicRootFunctorComparison k G inferInstance inferInstance S hS i a ha.1
  have htwo : RelativeRoot.weightFiltration b a 2 = ⊥ :=
    RelativeRoot.weightFiltration_two_eq_bot_of_noHigherRoots inferInstance hS i ha.1 hhigh
  have hrep : (RelativeRoot.weightFiltration b a 1).IsRepresentedBy j := hfirst.symm ▸ hj
  obtain ⟨V, q, c, d, hq, hc, hdj, hqd⟩ :=
    (RelativeRoot.cyclicWeightFiltration k G inferInstance inferInstance S hS b a ha.1 1
      (by decide)).2 H j hrep
  let : Mono j.hom.hom := hj.1
  have hq0 : RelativeRoot.IsFppfQuotient ⊥ q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
      SubgroupFunctor.comap_bot_of_mono] using hq
  let Q : H ≅ V := hq0.isoOfBot
  let T : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let p : rationalPoints H ≃* rationalPoints V :=
    ((yonedaGrp.mapIso Q).app (op T)).groupIsoToMulEquiv
  obtain ⟨n, ec, hec⟩ := hc.1
  have hweight : RelativeRoot.IsWeightVectorCoordinates c a ec := by
    simpa only [one_smul] using hec
  let R : rationalPoints H ≃* Multiplicative (Fin n → k) :=
    (p.trans (ec T)).trans (rootVectorRationalCoeffEquiv n)
  have hR (s : rationalPoints S.toGrp) (h : rationalPoints H) :
      R (d.act s h) = Multiplicative.ofAdd
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : k)
          • (R h).toAdd) := by
    apply Multiplicative.toAdd.injective
    funext l
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((ec T (d.act s h ≫ q.hom.hom)).toAdd l) = _
    rw [← hqd T s h, hweight.2]
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.map_mul _ _
  let E : Multiplicative (Fin n → k) ≃* rootGroupPoints i a :=
    R.symm.trans (hj.pointsEquiv T)
  have hE (s : rationalPoints S.toGrp) (x : Fin n → k) :
      rationalPoints.map i s * (E (Multiplicative.ofAdd x) : rationalPoints G) *
          (rationalPoints.map i s)⁻¹ =
        (E (Multiplicative.ofAdd
          ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : k)
            • x)) : rationalPoints G) := by
    let h := R.symm (Multiplicative.ofAdd x)
    have hd : d.act s h = R.symm (Multiplicative.ofAdd
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : k)
          • x)) := by
      apply R.injective
      rw [hR, R.apply_symm_apply]
      simp only [R.apply_symm_apply, toAdd_ofAdd]
    have hi := hdj T s h
    rw [hd] at hi
    change (s ≫ i.hom.hom) * (h ≫ j.hom.hom) * (s ≫ i.hom.hom)⁻¹ =
      R.symm (Multiplicative.ofAdd
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : k)
          • x)) ≫ j.hom.hom
    simpa only [b, AutomorphicAction.conjugation_act] using hi.symm
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    obtain ⟨g, hg, hg1⟩ := RelativeRoot.exists_rootPoint_of_noHigherRoots hS i ha hhigh
    have he : E.symm ⟨g, hg⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext l
      exact Fin.elim0 (hn0 ▸ l)
    have he' := congrArg E he
    apply hg1
    exact congrArg Subtype.val (by simpa only [E.apply_symm_apply, map_one] using he')
  exact ⟨⟨n, hn, E, hE⟩⟩

/-- A choice of actual positive finite equivariant coordinates for a root with
no higher positive integral multiple. -/
def weightedRootVectorCoordinatesOfNoHigherRoots
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hhigh : RelativeRoot.HasNoHigherRoots i a) :
    WeightedRootVectorCoordinates i a :=
  Classical.choice (nonempty_weightedRootVectorCoordinates_of_noHigherRoots hS i ha hhigh)

end Langlands.Geometry.Building
