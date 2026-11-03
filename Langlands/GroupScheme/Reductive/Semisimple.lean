import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Scheme-theoretic centres, semisimple groups and adjoint groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Center
variable {S : Scheme.{u}} {G H Z : GroupScheme S}

/-- An actual closed subgroup representing the full scheme-theoretic centre. -/
def IsSchemeTheoreticCenter (z : Z ⟶ G) : Prop :=
  IsClosedSubgroup z ∧ SubgroupFunctor.range z = center G

/-- A centre representative represents the all-test centre functor. -/
theorem IsSchemeTheoreticCenter.isRepresentedBy {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) : (center G).IsRepresentedBy z := by
  let : IsClosedImmersion z.hom.hom.left := hz.1
  exact ⟨Over.mono_of_mono_left _, hz.2⟩

/-- Its inclusion is central on every test scheme. -/
theorem IsSchemeTheoreticCenter.isCentral {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) : IsCentral z := by
  intro T x
  rw [← hz.2]
  exact ⟨x, rfl⟩

/-- Centrality of a point is preserved by an isomorphism of ambient group schemes. -/
theorem mem_center_comp_iso (e : G ≅ H) {T : Over S} {x : T ⟶ G.X}
    (hx : x ∈ (center G).carrier T) :
    x ≫ e.hom.hom.hom ∈ (center H).carrier T := by
  intro T' a y
  have h := hx T' a (y ≫ e.inv.hom.hom)
  have hm := h.map ((yonedaGrp.map e.hom).app (Opposite.op T')).hom
  change Commute ((a ≫ x) ≫ e.hom.hom.hom)
    ((y ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) at hm
  simpa only [Commute, SemiconjBy, Category.assoc, ← Grp.comp_hom_hom,
    e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] using hm

/-- The scheme-theoretic centre is invariant on all test points under isomorphisms. -/
theorem mem_center_comp_iso_iff (e : G ≅ H) {T : Over S} (x : T ⟶ G.X) :
    x ≫ e.hom.hom.hom ∈ (center H).carrier T ↔ x ∈ (center G).carrier T := by
  constructor
  · intro hx
    have h := mem_center_comp_iso e.symm hx
    change (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈ (center G).carrier T at h
    simpa only [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] using h
  · exact mem_center_comp_iso e

/-- A centre representative transports by postcomposition with an ambient isomorphism. -/
theorem IsSchemeTheoreticCenter.comp_iso {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) (e : G ≅ H) :
    IsSchemeTheoreticCenter (z ≫ e.hom) := by
  refine ⟨hz.1.comp_iso e, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change (y ≫ z.hom.hom) ≫ e.hom.hom.hom ∈ (center H).carrier T
    apply mem_center_comp_iso e
    exact hz.isCentral T y
  · intro hx
    have hx' := mem_center_comp_iso e.symm hx
    change x ≫ e.inv.hom.hom ∈ (center G).carrier T at hx'
    rw [← hz.2] at hx'
    obtain ⟨y, hy⟩ := hx'
    change (T ⟶ Z.X) at y
    change y ≫ z.hom.hom = x ≫ e.inv.hom.hom at hy
    refine ⟨y, ?_⟩
    change y ≫ (z.hom.hom ≫ e.hom.hom.hom) = x
    rw [← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom,
      e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- The full centre has an actual finite scheme representative, retaining nilpotents. -/
def HasFiniteCenter (G : GroupScheme S) : Prop :=
  ∃ (Z : GroupScheme S) (z : Z ⟶ G), IsSchemeTheoreticCenter z ∧ IsFinite Z.X.hom

/-- Finiteness of the scheme-theoretic centre is invariant under isomorphism. -/
theorem HasFiniteCenter.of_iso (e : G ≅ H) (h : HasFiniteCenter H) : HasFiniteCenter G := by
  obtain ⟨Z, z, hz, hfin⟩ := h
  exact ⟨Z, z ≫ e.inv, hz.comp_iso e.symm, hfin⟩

end Center

section Field
variable {k : Type u} [Field k]
variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A semisimple field group is connected reductive with finite scheme-theoretic centre. -/
structure IsSemisimple (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  isConnectedReductive : IsConnectedReductive G
  hasFiniteCenter : HasFiniteCenter G

/-- An adjoint field group is semisimple and has trivial scheme-theoretic centre. -/
structure IsAdjoint (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  isSemisimple : IsSemisimple G
  center_eq_bot : center G = ⊥

/-- Semisimplicity is invariant under isomorphisms of field group schemes. -/
theorem IsSemisimple.of_iso (e : G ≅ H) (h : IsSemisimple H) : IsSemisimple G :=
  ⟨h.isConnectedReductive.of_iso e, h.hasFiniteCenter.of_iso e⟩

/-- The full semisimplicity comparison under isomorphism. -/
theorem isSemisimple_iff_of_iso (e : G ≅ H) : IsSemisimple G ↔ IsSemisimple H :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/-- Adjointness is invariant under isomorphisms of field group schemes. -/
theorem IsAdjoint.of_iso (e : G ≅ H) (h : IsAdjoint H) : IsAdjoint G := by
  refine ⟨h.isSemisimple.of_iso e, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    have hx' := mem_center_comp_iso e hx
    rw [h.center_eq_bot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx'
    have hm := congrArg (fun y => y ≫ e.inv.hom.hom) hx'
    change x = 1
    simpa only [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id, MonObj.one_comp] using hm
  · intro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    rw [hx]
    exact (center G).carrier T |>.one_mem

/-- The full adjointness comparison under isomorphism. -/
theorem isAdjoint_iff_of_iso (e : G ≅ H) : IsAdjoint G ↔ IsAdjoint H :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

end Field
end Langlands.GroupScheme
