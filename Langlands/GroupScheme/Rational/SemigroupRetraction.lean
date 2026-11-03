import Langlands.GroupScheme.Rational.SemigroupComparisonStatement

/-! # Semigroup intersection along equivariant retractions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {S G H : GroupScheme B}

/-- An inclusion and a retraction preserve the two actual actions on every test
scheme, and their composite on the retract is the identity. -/
def IsEquivariantRetraction (b : AutomorphicAction S G) (c : AutomorphicAction S H)
    (j : H ⟶ G) (r : G ⟶ H) : Prop :=
  j ≫ r = 𝟙 H ∧
    (∀ (T : Over B) (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) ∧
    (∀ (T : Over B) (s : T ⟶ S.X) (g : T ⟶ G.X),
      b.act s g ≫ r.hom.hom = c.act s (g ≫ r.hom.hom))

end AutomorphicAction

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G H : GroupScheme B}
    {F : SubgroupFunctor G} {E : SubgroupFunctor H} {j : H ⟶ G} {r : G ⟶ H}

/-- Subfunctors preserved in both directions by a retraction have the expected
inverse image along its section. -/
theorem comap_eq_of_retraction (hr : j ≫ r = 𝟙 H)
    (hj : E.map j ≤ F) (hF : F.map r ≤ E) : F.comap j = E := by
  apply le_antisymm
  · intro T x hx
    have hx' := hF T ⟨x ≫ j.hom.hom, hx, rfl⟩
    change (x ≫ j.hom.hom) ≫ r.hom.hom ∈ E.carrier T at hx'
    have he : (x ≫ j.hom.hom) ≫ r.hom.hom = x := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hr, Grp.id_hom_hom, Category.comp_id]
    rwa [he] at hx'
  · exact map_le_iff_le_comap.mp hj

/-- The retraction is surjective on the preserved subfunctors on every test. -/
theorem map_eq_of_retraction (hr : j ≫ r = 𝟙 H)
    (hj : E.map j ≤ F) (hF : F.map r ≤ E) : F.map r = E := by
  apply le_antisymm hF
  intro T x hx
  refine ⟨x ≫ j.hom.hom, hj T ⟨x, hx, rfl⟩, ?_⟩
  change (x ≫ j.hom.hom) ≫ r.hom.hom = x
  rw [Category.assoc, ← Grp.comp_hom_hom, hr, Grp.id_hom_hom, Category.comp_id]

end SubgroupFunctor

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (hFunctoriality : SemigroupFunctorialityStatement.{u}) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G) (r : G ⟶ H) (hr : b.IsEquivariantRetraction c j r)
    (A : AddSubsemigroup (characterLattice S))

include hFunctoriality hS hr

/-- Equivariant retractions give actual semigroup intersection equality for every
additive semigroup, assuming the independent general functoriality theorem. -/
theorem semigroup_comap_eq_of_equivariantRetraction :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A :=
  SubgroupFunctor.comap_eq_of_retraction hr.1
    (hFunctoriality k H G inferInstance inferInstance inferInstance inferInstance S hS
      c b j hr.2.1 A)
    (hFunctoriality k G H inferInstance inferInstance inferInstance inferInstance S hS
      b c r hr.2.2 A)

/-- The same retraction is surjective on actual semigroup subgroup points on
every test scheme, since its equivariant section also preserves the semigroup. -/
theorem semigroup_map_eq_of_equivariantRetraction :
    (semigroupSubgroup b A).map r = semigroupSubgroup c A :=
  SubgroupFunctor.map_eq_of_retraction hr.1
    (hFunctoriality k H G inferInstance inferInstance inferInstance inferInstance S hS
      c b j hr.2.1 A)
    (hFunctoriality k G H inferInstance inferInstance inferInstance inferInstance S hS
      b c r hr.2.2 A)

end RelativeRoot

end Langlands.GroupScheme
