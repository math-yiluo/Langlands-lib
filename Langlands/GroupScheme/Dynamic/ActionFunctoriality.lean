import Langlands.GroupScheme.Dynamic.Action
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Equivariant functoriality of abstract dynamic subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H G K : GroupScheme B}

/-- An actual group homomorphism intertwines two actions on every test scheme. -/
def IsEquivariant (a : AutomorphicAction H G) (b : AutomorphicAction H K)
    (f : G ⟶ K) : Prop :=
  ∀ {T : Over B} (h : T ⟶ H.X) (g : T ⟶ G.X),
    a.act h g ≫ f.hom.hom = b.act h (g ≫ f.hom.hom)

namespace IsEquivariant

variable {a : AutomorphicAction (Gm B).toGrp G}
    {b : AutomorphicAction (Gm B).toGrp K} {f : G ⟶ K}
    (hf : a.IsEquivariant b f)

include hf

/-- The image orbit is the image of the source orbit. -/
theorem orbit_comp_hom {T : Over B} (g : T ⟶ G.X) :
    b.orbit (g ≫ f.hom.hom) = a.orbit g ≫ f.hom.hom := by
  exact (hf (snd T (Gm B).X) (fst T (Gm B).X ≫ g)).symm

/-- Composing an orbit extension with an equivariant homomorphism extends the image orbit. -/
theorem isOrbitExtension_comp_hom {T : Over B} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme B ⟶ G.X} (he : a.IsOrbitExtension g e) :
    b.IsOrbitExtension (g ≫ f.hom.hom) (e ≫ f.hom.hom) := by
  rw [IsOrbitExtension, ← Category.assoc, he, hf.orbit_comp_hom]

/-- Equivariant homomorphisms preserve limits of orbits. -/
theorem hasLimit_comp_hom {T : Over B} {g l : T ⟶ G.X} (hl : a.HasLimit g l) :
    b.HasLimit (g ≫ f.hom.hom) (l ≫ f.hom.hom) := by
  obtain ⟨e, he, rfl⟩ := hl
  exact ⟨e ≫ f.hom.hom, hf.isOrbitExtension_comp_hom he, Dynamic.evalZero_comp e _⟩

/-- The parabolic functor maps into the target parabolic functor. -/
theorem parabolic_le_comap : a.parabolic ≤ b.parabolic.comap f := by
  rintro T g ⟨e, he⟩
  exact ⟨e ≫ f.hom.hom, hf.isOrbitExtension_comp_hom he⟩

/-- The fixed functor maps into the target fixed functor. -/
theorem centralizer_le_comap : a.centralizer ≤ b.centralizer.comap f := by
  intro T g hg
  rw [SubgroupFunctor.mem_comap, mem_centralizer, hf.orbit_comp_hom,
    a.mem_centralizer.mp hg, Category.assoc]

/-- The identity-limit functor maps into the target identity-limit functor. -/
theorem unipotent_le_comap : a.unipotent ≤ b.unipotent.comap f := by
  intro T g hg
  have h := hf.hasLimit_comp_hom ((a.mem_unipotent).mp hg)
  rw [MonObj.one_comp] at h
  exact h

/-- A monomorphic equivariant homomorphism reflects fixed points. -/
theorem centralizer_eq_comap_of_mono [Mono f.hom.hom] :
    a.centralizer = b.centralizer.comap f := by
  refine le_antisymm hf.centralizer_le_comap fun T g hg => ?_
  rw [SubgroupFunctor.mem_comap, mem_centralizer, hf.orbit_comp_hom,
    ← Category.assoc] at hg
  exact a.mem_centralizer.mpr ((cancel_mono _).mp hg)

/-- Along an equivariant closed embedding every extension of an image orbit lifts. -/
theorem exists_isOrbitExtension_of_isClosedSubgroup (hfc : IsClosedSubgroup f)
    {T : Over B} {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme B ⟶ K.X}
    (he : b.IsOrbitExtension (g ≫ f.hom.hom) e) :
    ∃ e', a.IsOrbitExtension g e' ∧ e' ≫ f.hom.hom = e := by
  have : IsClosedImmersion f.hom.hom.left := hfc
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  obtain ⟨e', he'⟩ := AffineLine.exists_lift_of_unitInclusion f.hom.hom e (a.orbit g) (by
    rw [← hf.orbit_comp_hom]
    exact he.symm)
  refine ⟨e', ?_, he'⟩
  rw [IsOrbitExtension, ← cancel_mono f.hom.hom, Category.assoc, he',
    ← hf.orbit_comp_hom]
  exact he

/-- A limit of an image point lifts along an equivariant closed embedding. -/
theorem exists_hasLimit_of_isClosedSubgroup (hfc : IsClosedSubgroup f)
    {T : Over B} {g : T ⟶ G.X} {l : T ⟶ K.X}
    (hl : b.HasLimit (g ≫ f.hom.hom) l) :
    ∃ l', a.HasLimit g l' ∧ l' ≫ f.hom.hom = l := by
  obtain ⟨e, he, rfl⟩ := hl
  obtain ⟨e', he', rfl⟩ := hf.exists_isOrbitExtension_of_isClosedSubgroup hfc he
  exact ⟨Dynamic.evalZero e', ⟨e', he', rfl⟩, (Dynamic.evalZero_comp e' _).symm⟩

/-- An equivariant closed embedding preserves and reflects the stated limit. -/
theorem hasLimit_comp_hom_iff (hfc : IsClosedSubgroup f)
    {T : Over B} {g l : T ⟶ G.X} :
    b.HasLimit (g ≫ f.hom.hom) (l ≫ f.hom.hom) ↔ a.HasLimit g l := by
  refine ⟨fun hl => ?_, hf.hasLimit_comp_hom⟩
  have : IsClosedImmersion f.hom.hom.left := hfc
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  obtain ⟨l', hl', h⟩ := hf.exists_hasLimit_of_isClosedSubgroup hfc hl
  rwa [(cancel_mono f.hom.hom).mp h] at hl'

/-- The parabolic functor is the preimage along an equivariant closed embedding. -/
theorem parabolic_eq_comap_of_isClosedSubgroup (hfc : IsClosedSubgroup f) :
    a.parabolic = b.parabolic.comap f := by
  refine le_antisymm hf.parabolic_le_comap fun T g hg => ?_
  obtain ⟨e, he⟩ := hg
  obtain ⟨e', he', -⟩ := hf.exists_isOrbitExtension_of_isClosedSubgroup hfc he
  exact ⟨e', he'⟩

/-- The identity-limit functor is the preimage along an equivariant closed embedding. -/
theorem unipotent_eq_comap_of_isClosedSubgroup (hfc : IsClosedSubgroup f) :
    a.unipotent = b.unipotent.comap f := by
  refine le_antisymm hf.unipotent_le_comap fun T g hg => ?_
  have h : b.HasLimit (g ≫ f.hom.hom) (1 ≫ f.hom.hom) := by
    rw [MonObj.one_comp]
    exact hg
  exact (hf.hasLimit_comp_hom_iff hfc).mp h

/-- The fixed functor is the preimage along an equivariant closed embedding. -/
theorem centralizer_eq_comap_of_isClosedSubgroup (hfc : IsClosedSubgroup f) :
    a.centralizer = b.centralizer.comap f := by
  have : IsClosedImmersion f.hom.hom.left := hfc
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  exact hf.centralizer_eq_comap_of_mono

/-- Intersecting the target parabolic with the range gives the source parabolic image. -/
theorem range_inf_parabolic (hfc : IsClosedSubgroup f) :
    SubgroupFunctor.range f ⊓ b.parabolic = a.parabolic.map f := by
  rw [hf.parabolic_eq_comap_of_isClosedSubgroup hfc, SubgroupFunctor.map_comap]

/-- Intersecting the target identity-limit functor with the range gives the source image. -/
theorem range_inf_unipotent (hfc : IsClosedSubgroup f) :
    SubgroupFunctor.range f ⊓ b.unipotent = a.unipotent.map f := by
  rw [hf.unipotent_eq_comap_of_isClosedSubgroup hfc, SubgroupFunctor.map_comap]

/-- Intersecting the target fixed functor with the range gives the source fixed image. -/
theorem range_inf_centralizer (hfc : IsClosedSubgroup f) :
    SubgroupFunctor.range f ⊓ b.centralizer = a.centralizer.map f := by
  rw [hf.centralizer_eq_comap_of_isClosedSubgroup hfc, SubgroupFunctor.map_comap]

end IsEquivariant

end Langlands.GroupScheme.AutomorphicAction
