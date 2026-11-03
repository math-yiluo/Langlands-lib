import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Rational.WeightSupportVanishing

/-! # Inversion on actual root groups with one positive weight -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section VectorCoordinates

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V : GroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {a : characterLattice S} {n : ℕ}
    {e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ V.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))}

/-- In weight-vector coordinates, a torus point of character value `-1`
acts by group inversion, in every characteristic and on every test scheme. -/
theorem IsWeightVectorCoordinates.act_eq_inv_of_weight_eq_neg_one
    (he : IsWeightVectorCoordinates b a e)
    {X : Over (Spec (CommRingCat.of k))} (s : X ⟶ S.X)
    (hs : (Gm.pointsEquiv _ X (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
      Γ(X.left, ⊤)) = -1) (v : X ⟶ V.X) :
    b.act s v = v⁻¹ := by
  apply (e X).injective
  apply Multiplicative.toAdd.injective
  rw [he.2 X s v, hs, map_inv]
  simp

end VectorCoordinates

section EquivariantQuotient

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H V : GroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    (j : H ⟶ G) (q : H ⟶ V)
    (c : AutomorphicAction S.toGrp V) (d : AutomorphicAction S.toGrp H)

/-- A vector quotient with trivial actual kernel transports inversion to the
ambient subgroup; no surjectivity on groups of points is used. -/
theorem conj_eq_inv_of_equivariantVectorQuotient
    (hq : IsFppfQuotient ⊥ q) (hc : HasUniqueWeightVectorStructure c a)
    (hj : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ S.X) (h : X ⟶ H.X),
      d.act s h ≫ j.hom.hom =
        (AutomorphicAction.conjugation i).act s (h ≫ j.hom.hom))
    (hqd : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ S.X) (h : X ⟶ H.X),
      c.act s (h ≫ q.hom.hom) = d.act s h ≫ q.hom.hom)
    {X : Over (Spec (CommRingCat.of k))} (s : X ⟶ S.X)
    (hs : (Gm.pointsEquiv _ X (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
      Γ(X.left, ⊤)) = -1)
    {g : X ⟶ G.X} (hg : g ∈ (SubgroupFunctor.range j).carrier X) :
    (s ≫ i.hom.hom) * g * (s ≫ i.hom.hom)⁻¹ = g⁻¹ := by
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨n, e, he⟩ := hc.1
  have : Mono q.hom.hom :=
    SubgroupFunctor.mono_of_range_kernel_eq_bot q hq.2.2.2
  have hd : d.act s h = h⁻¹ := by
    apply (cancel_mono q.hom.hom).mp
    rw [← hqd, GrpObj.inv_comp]
    exact he.act_eq_inv_of_weight_eq_neg_one s hs _
  have h := hj X s h
  rw [hd, GrpObj.inv_comp] at h
  simpa only [AutomorphicAction.conjugation_act] using h.symm

end EquivariantQuotient

section RootSubgroups

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A torus point acting by inversion on an actual root subgroup, on its
given scheme test. This does not assert existence of such a point. -/
def IsInversionPoint (i : S.toGrp ⟶ G) (a : characterLattice S)
    {X : Over (Spec (CommRingCat.of k))} (s : X ⟶ S.X) : Prop :=
  ∀ ⦃g : X ⟶ G.X⦄, g ∈ (subgroup i a).carrier X →
    (s ≫ i.hom.hom) * g * (s ≫ i.hom.hom)⁻¹ = g⁻¹

/-- If the actual positive cyclic filtration has only its first weight, the
source filtration and realization statements give inversion by every torus
point whose character value is `-1`, on every scheme test. -/
theorem subgroup_conj_eq_inv_of_noHigherPositiveRoots
    (hreal : SemigroupRealizationStatement.{u})
    (hcyclic : CyclicRootFunctorComparisonStatement.{u})
    (hfilter : CyclicWeightFiltrationStatement.{u})
    (hG : Smooth G.X.hom) (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 2 ≤ n → n • a ∉ relativeRoots i)
    {X : Over (Spec (CommRingCat.of k))} (s : X ⟶ S.X)
    (hs : (Gm.pointsEquiv _ X (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
      Γ(X.left, ⊤)) = -1)
    {g : X ⟶ G.X} (hg : g ∈ (subgroup i a).carrier X) :
    (s ≫ i.hom.hom) * g * (s ≫ i.hom.hom)⁻¹ = g⁻¹ := by
  let b := AutomorphicAction.conjugation i
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    hcyclic k G hG inferInstance S hS i a ha
  have htwo : weightFiltration b a 2 = ⊥ :=
    weightFiltration_eq_bot_of_noRelativeRoots hreal hG hS i ha 2
      (fun n hn _ => hhigh n hn)
  obtain ⟨H, j, hj, _⟩ := (hreal k G hG inferInstance S hS b (cyclicTail a 1)).1
  obtain ⟨V, q, c, d, hq, hc, hjd, hqd⟩ :=
    (hfilter k G hG inferInstance S hS b a ha 1 (by omega)).2 H j hj
  let : Mono j.hom.hom := hj.1
  have hq0 : IsFppfQuotient ⊥ q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
      SubgroupFunctor.comap_bot_of_mono] using hq
  have hc' : HasUniqueWeightVectorStructure c a := by
    simpa only [one_nsmul] using hc
  have hgj : g ∈ (SubgroupFunctor.range j).carrier X := by
    rw [hj.2]
    change g ∈ (weightFiltration b a 1).carrier X
    rw [hfirst]
    exact hg
  exact conj_eq_inv_of_equivariantVectorQuotient i a j q c d
    hq0 hc' hjd hqd s hs hgj

/-- The conditional cyclic-filtration criterion, packaged as the actual
inversion-point predicate. -/
theorem isInversionPoint_of_noHigherPositiveRoots
    (hreal : SemigroupRealizationStatement.{u})
    (hcyclic : CyclicRootFunctorComparisonStatement.{u})
    (hfilter : CyclicWeightFiltrationStatement.{u})
    (hG : Smooth G.X.hom) (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 2 ≤ n → n • a ∉ relativeRoots i)
    {X : Over (Spec (CommRingCat.of k))} (s : X ⟶ S.X)
    (hs : (Gm.pointsEquiv _ X (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
      Γ(X.left, ⊤)) = -1) :
    IsInversionPoint i a s := by
  intro g hg
  exact subgroup_conj_eq_inv_of_noHigherPositiveRoots
    hreal hcyclic hfilter hG hS i ha hhigh s hs hg

end RootSubgroups

end Langlands.GroupScheme.RelativeRoot
