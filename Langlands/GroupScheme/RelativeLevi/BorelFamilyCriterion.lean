import Langlands.GroupScheme.RelativeLevi.BorelRangeTransport
import Langlands.GroupScheme.RelativeLevi.BorelLocus
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli

/-! # Borel families and the image of their parameter morphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace RelativeLevi

variable {S : Scheme.{u}} {P G G' : GroupScheme S}

/-- An ambient isomorphism does not change the Borel locus of a family. -/
theorem borelLocus_comp_iso (i : P ⟶ G) (e : G ≅ G') :
    borelLocus (i ≫ e.hom) = borelLocus i := by
  ext s
  change IsGeometricBorelSubgroup
      ((baseChange (S.fromSpecResidueField s)).map (i ≫ e.hom)) ↔
    IsGeometricBorelSubgroup ((baseChange (S.fromSpecResidueField s)).map i)
  rw [Functor.map_comp]
  exact isGeometricBorelSubgroup_comp_iso_iff _
    ((baseChange (S.fromSpecResidueField s)).mapIso e)

end RelativeLevi

namespace TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T : Over S}
variable {P : GroupScheme M.left}

/-- Evaluating a monic actual subgroup family gives a monic inclusion. -/
theorem mono_familyHom (j : P ⟶ (baseChange M.hom).obj G)
    (hj : Mono j.hom.hom) (a : T ⟶ M) :
    Mono (familyHom j a).hom.hom := by
  let : Mono j.hom.hom := hj
  let : Mono ((baseChange a.left).map j).hom.hom := by
    change Mono ((Over.pullback a.left).map j.hom.hom)
    infer_instance
  let e := Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G
  change Mono (((baseChange a.left).map j).hom.hom ≫ ((Grp.forget _).mapIso e).hom)
  exact mono_comp _ _

/-- Equality with the evaluated all-test range transfers relative Borelness
from a supplied Borel subgroup to the evaluated monic family. -/
theorem isRelativeBorelSubgroup_familyHom_of_evaluate_eq
    (j : P ⟶ (baseChange M.hom).obj G) (hj : Mono j.hom.hom) (a : T ⟶ M)
    {B : GroupScheme T.left} {i : B ⟶ (baseChange T.hom).obj G}
    (hi : IsRelativeBorelSubgroup i)
    (h : evaluate j a = SubgroupFunctor.range i) :
    IsRelativeBorelSubgroup (familyHom j a) :=
  hi.of_range_eq (mono_familyHom j hj a) h.symm

/-- The Borel locus of an evaluated parabolic family is the inverse image of
the original Borel locus under its parameter morphism. -/
theorem borelLocus_familyHom (j : P ⟶ (baseChange M.hom).obj G)
    (hG : IsReductive G) (hj : IsRelativeParabolicSubgroup j) (a : T ⟶ M) :
    RelativeLevi.borelLocus (familyHom j a) =
      a.left ⁻¹' RelativeLevi.borelLocus j := by
  exact (RelativeLevi.borelLocus_comp_iso ((baseChange a.left).map j)
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G)).trans
      (RelativeLevi.borelLocus_baseChange j (hG.baseChange M.hom) hj a.left)

/-- An evaluated relative-parabolic family is Borel exactly when its parameter
morphism has image in the Borel locus. -/
theorem isRelativeBorelSubgroup_familyHom_iff
    (j : P ⟶ (baseChange M.hom).obj G)
    (hG : IsReductive G) (hj : IsRelativeParabolicSubgroup j) (a : T ⟶ M) :
    IsRelativeBorelSubgroup (familyHom j a) ↔
      Set.range a.left ⊆ RelativeLevi.borelLocus j := by
  have hL := borelLocus_familyHom j hG hj a
  constructor
  · intro hi x hx
    obtain ⟨t, rfl⟩ := hx
    have ht : t ∈ RelativeLevi.borelLocus (familyHom j a) := hi.residueFiber t
    rwa [hL] at ht
  · intro ha
    have hf : ∀ t : T.left, IsGeometricBorelSubgroup
        (RelativeLevi.residueFiberHom (familyHom j a) t) := by
      intro t
      have ht : a.left t ∈ RelativeLevi.borelLocus j := ha ⟨t, rfl⟩
      have hm : t ∈ RelativeLevi.borelLocus (familyHom j a) := by
        rw [hL]
        exact ht
      exact hm
    let : Smooth P.X.hom := hj.smooth
    let : IsAffineHom P.X.hom := hj.isAffineHom
    refine ⟨⟨?_, ?_, mono_familyHom j hj.mono a,
      fun t => (hf t).isParabolicSubgroup⟩, hf⟩
    · change Smooth (pullback.snd P.X.hom a.left)
      infer_instance
    · change IsAffineHom (pullback.snd P.X.hom a.left)
      exact MorphismProperty.pullback_snd _ _ hj.isAffineHom

/-- A parameter classifying a supplied Borel subgroup has image in the Borel
locus of the original relative-parabolic family. -/
theorem range_subset_borelLocus_of_evaluate_eq
    (j : P ⟶ (baseChange M.hom).obj G)
    (hG : IsReductive G) (hj : IsRelativeParabolicSubgroup j) (a : T ⟶ M)
    {B : GroupScheme T.left} {i : B ⟶ (baseChange T.hom).obj G}
    (hi : IsRelativeBorelSubgroup i)
    (h : evaluate j a = SubgroupFunctor.range i) :
    Set.range a.left ⊆ RelativeLevi.borelLocus j :=
  (isRelativeBorelSubgroup_familyHom_iff j hG hj a).mp
    (isRelativeBorelSubgroup_familyHom_of_evaluate_eq j hj.mono a hi h)

/-- Evaluate an actual relative-parabolic family at a parameter with image
in its Borel locus, retaining the actual inclusion and its Borel property. -/
def relativeBorelFamilyAt (j : P ⟶ (baseChange M.hom).obj G)
    (hG : IsReductive G) (hj : IsRelativeParabolicSubgroup j) (a : T ⟶ M)
    (ha : Set.range a.left ⊆ RelativeLevi.borelLocus j) :
    {i : (baseChange a.left).obj P ⟶ (baseChange T.hom).obj G //
      IsRelativeBorelSubgroup i} :=
  ⟨familyHom j a, (isRelativeBorelSubgroup_familyHom_iff j hG hj a).mpr ha⟩

@[simp]
theorem relativeBorelFamilyAt_val (j : P ⟶ (baseChange M.hom).obj G)
    (hG : IsReductive G) (hj : IsRelativeParabolicSubgroup j) (a : T ⟶ M)
    (ha : Set.range a.left ⊆ RelativeLevi.borelLocus j) :
    (relativeBorelFamilyAt j hG hj a ha).val = familyHom j a := rfl

end TorusSubgroupModuli

end Langlands.GroupScheme
