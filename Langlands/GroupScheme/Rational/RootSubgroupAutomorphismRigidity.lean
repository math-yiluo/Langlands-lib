import Langlands.GroupScheme.Rational.VectorEndomorphismRigidity
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Rational.RootSubgroupFixedByEndomorphism
import Langlands.GroupScheme.Rational.RootSubgroupStability
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Scalar linearity and Lie rigidity for torus-equivariant root automorphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section WeightCoordinates

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ V.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))) (q : V ≅ V)

/-- Recoordinate a vector group by precomposing the coordinates with an actual automorphism. -/
def coordinatesPrecompIso (X : Over (Spec (CommRingCat.of k))) :
    (X ⟶ V.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)) :=
  (((yonedaGrp.mapIso q).app (op X)).groupIsoToMulEquiv).trans (e X)

@[simp]
theorem coordinatesPrecompIso_apply (X : Over (Spec (CommRingCat.of k))) (v : X ⟶ V.X) :
    coordinatesPrecompIso e q X v = e X (v ≫ q.hom.hom.hom) := rfl

variable {e q}

theorem IsNaturalVectorCoordinates.precompIso (he : IsNaturalVectorCoordinates e) :
    IsNaturalVectorCoordinates (coordinatesPrecompIso e q) := by
  intro X Y c v
  change (e Y ((c ≫ v) ≫ q.hom.hom.hom)).toAdd = _
  rw [Category.assoc]
  exact he X Y c (v ≫ q.hom.hom.hom)

/-- Equivariance preserves the weight of the recoordinatized vector group. -/
theorem IsWeightVectorCoordinates.precompIso
    {b : AutomorphicAction T.toGrp V} {a : characterLattice T}
    (he : IsWeightVectorCoordinates b a e)
    (hq : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ T.X) (v : X ⟶ V.X),
      b.act s v ≫ q.hom.hom.hom = b.act s (v ≫ q.hom.hom.hom)) :
    IsWeightVectorCoordinates b a (coordinatesPrecompIso e q) := by
  refine ⟨he.1.precompIso, ?_⟩
  intro X s v
  simp only [coordinatesPrecompIso_apply, hq]
  exact he.2 X s (v ≫ q.hom.hom.hom)

/-- Uniqueness of the weight scalar structure forces a torus-equivariant
vector-group automorphism to be scalar-linear on every test scheme. -/
theorem isCoordinateLinear_of_weightCoordinates
    {b : AutomorphicAction T.toGrp V} {a : characterLattice T}
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (he : IsWeightVectorCoordinates b a e)
    (hq : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ T.X) (v : X ⟶ V.X),
      b.act s v ≫ q.hom.hom.hom = b.act s (v ≫ q.hom.hom.hom)) :
    IsCoordinateLinear e q.hom := by
  let e' := coordinatesPrecompIso e q
  have he' : IsWeightVectorCoordinates b a e' := he.precompIso hq
  intro X c v
  change (e' X (coordinateSmul e X c v)).toAdd = c • (e' X v).toAdd
  rw [coordinateSmul_eq_of_isWeightVectorCoordinates hT ha he he']
  exact coordinateSmul_coord e' X c v

end WeightCoordinates

section RootRestriction

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G U : GroupScheme B}
    (i : T.toGrp ⟶ G) (a : characterLattice T)
    (j : U ⟶ G) (hj : (subgroup i a).IsRepresentedBy j)

/-- Restrict an actual torus-fixing endomorphism to any representative of its root functor. -/
def rootHomOfFixesTorus (f : G ⟶ G) (hi : i ≫ f = i) : U ⟶ U :=
  hj.factorHom (j ≫ f) (by
    intro X g hg
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    change (v ≫ j.hom.hom) ≫ f.hom.hom ∈ (subgroup i a).carrier X
    exact comp_mem_subgroup_of_fixes_torus i f hi a
      (hj.2 ▸ SubgroupFunctor.mem_range.mpr ⟨v, rfl⟩))

/-- The restricted map intertwines the ambient endomorphism and the original inclusion. -/
theorem rootHomOfFixesTorus_comp (f : G ⟶ G) (hi : i ≫ f = i) :
    rootHomOfFixesTorus i a j hj f hi ≫ j = j ≫ f :=
  hj.factorHom_comp _ _

/-- Fixing the torus is inherited by the inverse automorphism. -/
theorem fixes_torus_inv (σ : G ≅ G) (hi : i ≫ σ.hom = i) : i ≫ σ.inv = i := by
  calc
    i ≫ σ.inv = (i ≫ σ.hom) ≫ σ.inv := by rw [hi]
    _ = i := by rw [Category.assoc, σ.hom_inv_id, Category.comp_id]

/-- Restrict an actual torus-fixing automorphism to the represented root group. -/
def rootIsoOfFixesTorus (σ : G ≅ G) (hi : i ≫ σ.hom = i) : U ≅ U where
  hom := rootHomOfFixesTorus i a j hj σ.hom hi
  inv := rootHomOfFixesTorus i a j hj σ.inv (fixes_torus_inv i σ hi)
  hom_inv_id := by
    apply hj.hom_ext
    rw [Category.assoc, rootHomOfFixesTorus_comp, ← Category.assoc,
      rootHomOfFixesTorus_comp, Category.assoc, σ.hom_inv_id, Category.comp_id,
      Category.id_comp]
  inv_hom_id := by
    apply hj.hom_ext
    rw [Category.assoc, rootHomOfFixesTorus_comp, ← Category.assoc,
      rootHomOfFixesTorus_comp, Category.assoc, σ.inv_hom_id, Category.comp_id,
      Category.id_comp]

/-- The induced root automorphism is equivariant for the whole original torus action. -/
theorem rootIsoOfFixesTorus_equivariant (σ : G ≅ G) (hi : i ≫ σ.hom = i)
    (X : Over B) (s : X ⟶ T.X) (v : X ⟶ U.X) :
    (subgroupAction i a j hj).act s v ≫ (rootIsoOfFixesTorus i a j hj σ hi).hom.hom.hom =
      (subgroupAction i a j hj).act s (v ≫ (rootIsoOfFixesTorus i a j hj σ hi).hom.hom.hom) := by
  have : Mono j.hom.hom := hj.1
  have hcomp : (rootIsoOfFixesTorus i a j hj σ hi).hom ≫ j = j ≫ σ.hom :=
    rootHomOfFixesTorus_comp i a j hj σ.hom hi
  have htorus : (s ≫ i.hom.hom) ≫ σ.hom.hom.hom = s ≫ i.hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : T.toGrp ⟶ G => s ≫ f.hom.hom) hi
  apply (cancel_mono j.hom.hom).mp
  rw [Category.assoc, ← Grp.comp_hom_hom, hcomp, Grp.comp_hom_hom,
    ← Category.assoc, subgroupAction_act_comp, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, htorus, subgroupAction_act_comp]
  have hv := congrArg (fun r : U ⟶ G => v ≫ r.hom.hom) hcomp
  simp only [Grp.comp_hom_hom, ← Category.assoc] at hv
  rw [hv]

end RootRestriction

section FieldRigidity

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]
    (i : T.toGrp ⟶ G) (a : characterLattice T)
    (j : U ⟶ G) (hj : (subgroup i a).IsRepresentedBy j)

/-- Weight coordinates and fixedness of the differential on the actual root
tangent image imply fixedness of the entire root functor on every test. -/
theorem isFixedBy_of_weightCoordinates_of_targetMap_fixed
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (σ : G ≅ G) (hi : i ≫ σ.hom = i) {n : ℕ}
    {e : ∀ X : Over (Spec (CommRingCat.of k)),
      (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤))}
    (he : IsWeightVectorCoordinates (subgroupAction i a j hj) a e)
    (hLie : ∀ x, Lie.targetMapLinear σ.hom k (Lie.targetMapLinear j k x) =
      Lie.targetMapLinear j k x) :
    IsFixedBy i σ.hom a := by
  let q := rootIsoOfFixesTorus i a j hj σ hi
  have hcomp : q.hom ≫ j = j ≫ σ.hom := rootHomOfFixesTorus_comp i a j hj σ.hom hi
  have hlin : IsCoordinateLinear e q.hom :=
    isCoordinateLinear_of_weightCoordinates hT ha he
      (rootIsoOfFixesTorus_equivariant i a j hj σ hi)
  have hdiff : ∀ x, Lie.targetMapLinear q.hom k x = x := by
    intro x
    have : Mono j.hom.hom := hj.1
    apply Lie.targetMapLinear_injective j k
    have htarget : Lie.targetMapLinear j k (Lie.targetMapLinear q.hom k x) =
        Lie.targetMapLinear σ.hom k (Lie.targetMapLinear j k x) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa only [lieKernelTargetLinear_val, Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun r : U ⟶ G => x.toMul.val ≫ r.hom.hom) hcomp
    rw [htarget, hLie]
  have hqid := eq_id_of_coordinateLinear_of_targetMapLinear_eq_self he.1 hlin hdiff
  change subgroup i a ≤ endomorphismFixedSubgroup σ.hom
  rw [← hj.2]
  apply (range_le_endomorphismFixedSubgroup_iff σ.hom j).mpr
  rw [← hcomp, hqid, Category.id_comp]

end FieldRigidity

end Langlands.GroupScheme.RelativeRoot
