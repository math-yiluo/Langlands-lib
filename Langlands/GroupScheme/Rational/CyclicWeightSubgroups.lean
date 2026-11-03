import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.Rational.TorusWeightTangent
import Langlands.GroupScheme.Rational.TorusWeightClosed
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Cyclic weight subgroups of affine groups with split-torus actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

open Corepresented

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B) (ψ : groupScheme F e ≅ G)
  {I : Type u} [Fintype I] [DecidableEq I]
  (φ : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I) (b : AutomorphicAction S.toGrp G)

/-- The torus action on algebra points of the corepresented model, transported from `b`. -/
abbrev modelAction : TorusAction F I :=
  TorusAction.ofAutomorphicAction e (b.transport φ.inv ψ)

/-- The weight subgroup functor of `G` attached to a semigroup of exponent vectors. -/
abbrev weightSubgroupFunctor (P : AddSubsemigroup (I → ℤ)) : SubgroupFunctor G :=
  (cutSubgroupFunctor (isCutOutBy_weightIdeal e (modelAction e ψ φ b) P)).comap ψ.inv

theorem mem_weightSubgroupFunctor (P : AddSubsemigroup (I → ℤ))
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) :
    g ∈ (weightSubgroupFunctor e ψ φ b P).carrier T ↔
      pointsEquiv F e T (g ≫ ψ.inv.hom.hom) ∈ weightSubgroup e (modelAction e ψ φ b) P _ :=
  Iff.rfl

/-- A weight subgroup functor is normalized by a larger one whose semigroup it absorbs. -/
theorem weightSubgroupFunctor_isNormalizedBy {P P' : AddSubsemigroup (I → ℤ)}
    (hP'P : (P' : Set (I → ℤ)) ⊆ P) (hPP' : ∀ m ∈ P, ∀ p ∈ P', m + p ∈ P') :
    (weightSubgroupFunctor e ψ φ b P').IsNormalizedBy (weightSubgroupFunctor e ψ φ b P) := by
  intro T g x hg hx
  rw [mem_weightSubgroupFunctor] at hg hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, map_mul, map_mul, map_inv]
  exact conj_mem_weightSubgroup e _ hP'P hPP' hg hx

/-- Weight subgroup functors are stable under the action. -/
theorem isStable_weightSubgroupFunctor (P : AddSubsemigroup (I → ℤ)) :
    b.IsStable (weightSubgroupFunctor e ψ φ b P) :=
  AutomorphicAction.isStable_transport b φ ψ (isStable_weightSubgroup e (b.transport φ.inv ψ) P)

omit [DecidableEq I] in
/-- Stability under the action passes to the transported action on the model. -/
theorem isStable_transport_comap {F' : SubgroupFunctor G} (hF' : b.IsStable F') :
    (b.transport φ.inv ψ).IsStable (F'.comap ψ.hom) := by
  intro T s x hx
  rw [SubgroupFunctor.mem_comap] at hx ⊢
  rw [AutomorphicAction.transport_act, Category.assoc, iso_inv_hom_hom, Category.comp_id]
  exact hF' T _ _ hx

/-- The weight subgroup functor of a cyclic tail is smooth, connected and closed. -/
theorem isSmoothConnectedClosed_weightSubgroupFunctor [IsAffineHom G.X.hom]
    [IsAffineHom (groupScheme F e).X.hom]
    [Algebra.FormallySmooth k B] [Algebra.FiniteType k B] {a : I → ℤ} (ha : a ≠ 0) (r : ℕ) :
    IsSmoothConnectedClosed (weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail a r)) := by
  obtain ⟨n, d, x, -, -, -, hx⟩ := exists_aeval_bijective_cyclicTail e (modelAction e ψ φ b) ha r
  exact IsSmoothConnectedClosed.comap_iso (isSmoothConnectedClosed_cutSubgroupFunctor _ hx) ψ

omit [DecidableEq I] in
/-- The induced torus action preserves the affine points of a stable subgroup functor. -/
theorem modelAction_mem_affineSubgroups {F' : SubgroupFunctor G} (hF' : b.IsStable F')
    {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) {x : F.obj A}
    (hx : x ∈ affineSubgroups (F'.comap ψ.hom) A) :
    (modelAction e ψ φ b).act t x ∈ affineSubgroups (F'.comap ψ.hom) A := by
  change (affinePointsEquiv F e A).symm (affinePointsEquiv F e A
    ((b.transport φ.inv ψ).act (torusPt I A t) ((affinePointsEquiv F e A).symm x))) ∈
      (F'.comap ψ.hom).carrier _
  rw [MulEquiv.symm_apply_apply]
  exact isStable_transport_comap e ψ φ b hF' _ _ _ hx

/-- Maximality: a smooth connected closed stable subgroup functor whose tangent vectors
supported on single weights outside `P` are trivial lies in the weight subgroup functor of `P`,
if `0 ∉ P`. -/
theorem le_weightSubgroupFunctor [Algebra.FiniteType k B] {P : AddSubsemigroup (I → ℤ)}
    (h0 : (0 : I → ℤ) ∉ P) {F' : SubgroupFunctor G} (hF' : IsSmoothConnectedClosed F')
    (hb : b.IsStable F')
    (hrigid : ∀ {J : Ideal B} (hJ : IsCutOutBy e (affineSubgroups (F'.comap ψ.hom)) J)
      (hH : ∀ {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) {x : F.obj A},
        x ∈ affineSubgroups (F'.comap ψ.hom) A →
          (modelAction e ψ φ b).act t x ∈ affineSubgroups (F'.comap ψ.hom) A),
      ∀ χ ∉ P, ∀ X : (cutFunctor hJ).obj
          (CommAlgCat.of (CommRingCat.of k) (DualNumber (CommRingCat.of k))),
        (cutFunctor hJ).map
            (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))) X = 1 →
          (∀ g m, m ≠ χ → (coord (cutCorepresentableBy hJ) X
            (comp (cutCorepresentableBy hJ) ((modelAction e ψ φ b).restrict hJ hH) m g)).snd =
              0) → X = 1) :
    F' ≤ weightSubgroupFunctor e ψ φ b P := by
  obtain ⟨K, j, hj, hjc, -, hKc⟩ := hF'
  have hrep : (F'.comap ψ.hom).IsRepresentedBy (j ≫ ψ.inv) := hj.comp_iso ψ.symm
  have hcl : IsClosedImmersion (j ≫ ψ.inv).hom.hom.left := hjc.comp_iso ψ.symm
  obtain ⟨J, hJr, htriv⟩ := exists_ideal_range_of_connectedSpace (j ≫ ψ.inv)
  have hJ : IsCutOutBy e (affineSubgroups (F'.comap ψ.hom)) J := by
    rw [← hrep.2]
    exact isCutOutBy_range hJr
  have hH : ∀ {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) {x : F.obj A},
      x ∈ affineSubgroups (F'.comap ψ.hom) A →
        (modelAction e ψ φ b).act t x ∈ affineSubgroups (F'.comap ψ.hom) A :=
    fun t _ hx => modelAction_mem_affineSubgroups e ψ φ b hb t hx
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hle := fun {A : CommAlgCat.{u} (CommRingCat.of k)} {x : F.obj A}
      (hx : x ∈ affineSubgroups (F'.comap ψ.hom) A) =>
    le_weightSubgroup e (modelAction e ψ φ b) hJ hH htriv P h0 (hrigid hJ hH) hx
  rw [SubgroupFunctor.le_def]
  intro T g hg
  rw [mem_weightSubgroupFunctor]
  apply hle
  have hmem : g ≫ ψ.inv.hom.hom ∈ (SubgroupFunctor.range (j ≫ ψ.inv)).carrier T := by
    rw [hrep.2, SubgroupFunctor.mem_comap, Category.assoc, iso_inv_hom_hom, Category.comp_id]
    exact hg
  have h := (mem_range_iff_mem_affineSubgroups hJr _).1 hmem
  rwa [hrep.2] at h

omit [DecidableEq I] in
/-- The exponent vectors of the cyclic tail of `a` form the cyclic tail of the exponent vector
of `a`. -/
theorem mem_cyclicTail_characterExponents (a : characterLattice S) (r : ℕ)
    (χ : characterLattice S) :
    characterExponents φ χ ∈ Corepresented.cyclicTail (characterExponents φ a) r ↔
      χ ∈ cyclicTail a r := by
  constructor
  · rintro ⟨n, hn, hn0, h⟩
    refine ⟨n, hn, hn0, (characterExponents φ).injective ?_⟩
    rw [map_nsmul, h]
  · rintro ⟨n, hn, hn0, rfl⟩
    exact ⟨n, hn, hn0, (map_nsmul _ _ _).symm⟩

/-- The rigidity hypothesis of `le_weightSubgroupFunctor` for a subgroup functor `F'`. -/
def TangentRigid (P : AddSubsemigroup (I → ℤ)) (F' : SubgroupFunctor G) : Prop :=
  ∀ {J : Ideal B} (hJ : IsCutOutBy e (affineSubgroups (F'.comap ψ.hom)) J)
    (hH : ∀ {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) {x : F.obj A},
      x ∈ affineSubgroups (F'.comap ψ.hom) A →
        (modelAction e ψ φ b).act t x ∈ affineSubgroups (F'.comap ψ.hom) A),
    ∀ χ ∉ P, ∀ X : (cutFunctor hJ).obj
        (CommAlgCat.of (CommRingCat.of k) (DualNumber (CommRingCat.of k))),
      (cutFunctor hJ).map
          (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))) X = 1 →
        (∀ g m, m ≠ χ → (coord (cutCorepresentableBy hJ) X
          (comp (cutCorepresentableBy hJ) ((modelAction e ψ φ b).restrict hJ hH) m g)).snd =
            0) → X = 1

/-- The cyclic weight filtration is the weight subgroup functor of the cyclic tail of exponent
vectors, given the two Lie-algebra inputs: the weights of the latter lie in the tail, and every
generator of the filtration is tangentially rigid outside the tail. -/
theorem weightFiltration_eq_weightSubgroupFunctor [IsAffineHom G.X.hom]
    [IsAffineHom (groupScheme F e).X.hom] [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    {a : characterLattice S} (ha : characterExponents φ a ≠ 0) (r : ℕ)
    (hL1 : actionWeightSupport b
      (weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) r)) ⊆
        cyclicTail a r)
    (hL2 : ∀ F' : SubgroupFunctor G, IsSemigroupGenerator b (cyclicTail a r) F' →
      TangentRigid e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) r) F') :
    weightFiltration b a r =
      weightSubgroupFunctor e ψ φ b (Corepresented.cyclicTail (characterExponents φ a) r) := by
  apply le_antisymm
  · rw [SubgroupFunctor.le_def]
    intro T
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨F', hF', hg⟩
    exact (SubgroupFunctor.le_def.1 (le_weightSubgroupFunctor e ψ φ b
      (zero_notMem_cyclicTail ha r) hF'.1 hF'.2.1 (hL2 F' hF')) T) hg
  · exact generator_le_semigroupSubgroup b _ _
      ⟨isSmoothConnectedClosed_weightSubgroupFunctor e ψ φ b ha r,
        isStable_weightSubgroupFunctor e ψ φ b _, hL1⟩

end Langlands.GroupScheme.RelativeRoot
