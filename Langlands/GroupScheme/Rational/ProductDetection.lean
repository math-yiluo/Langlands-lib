import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # Character detection from an epimorphic subgroup product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H Z D : GroupScheme S}

/-- The scheme morphism that multiplies the images of two subgroup homomorphisms.
The product is taken in schemes over the base; no centrality is needed to define the map. -/
def subgroupProductMap (i : Z ⟶ G) (d : D ⟶ G) : Z.X ⊗ D.X ⟶ G.X :=
  (fst Z.X D.X ≫ i.hom.hom) * (snd Z.X D.X ≫ d.hom.hom)

/-- A morphism to a commutative group is trivial if it is trivial on two subgroups whose
multiplication map is an epimorphism of schemes over the base. -/
theorem comp_eq_one_of_epi_subgroupProductMap (i : Z ⟶ G) (d : D ⟶ G)
    [Epi (subgroupProductMap i d)] (f : G ⟶ H) [IsCommMonObj H.X]
    (hi : i ≫ f = 1) (hd : d ≫ f = 1) : f = 1 := by
  have hi' : i.hom.hom ≫ f.hom.hom = 1 := by
    simpa only [Grp.comp_hom_hom, Grp.Hom.hom_one, Mon.Hom.hom_one] using
      congrArg (fun g => g.hom.hom) hi
  have hd' : d.hom.hom ≫ f.hom.hom = 1 := by
    simpa only [Grp.comp_hom_hom, Grp.Hom.hom_one, Mon.Hom.hom_one] using
      congrArg (fun g => g.hom.hom) hd
  apply Grp.hom_ext
  rw [Grp.Hom.hom_one, Mon.Hom.hom_one]
  apply (cancel_epi (subgroupProductMap i d)).mp
  simp only [subgroupProductMap, MonObj.mul_comp, Category.assoc, hi', hd',
    MonObj.comp_one, mul_one]

/-- A nonzero character is nonzero on a subgroup which, together with an actual derived
subgroup, has epimorphic multiplication map. -/
theorem IsDerivedSubgroup.characterRestrict_ne_zero_of_epi_subgroupProductMap
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (i : Z ⟶ G)
    [Epi (subgroupProductMap i d)] (χ : rationalCharacters G) (hχ : χ ≠ 0) :
    characterRestrict i χ ≠ 0 := by
  intro hi
  apply hχ
  exact congrArg Additive.ofMul (comp_eq_one_of_epi_subgroupProductMap i d χ.toMul
    (congrArg Additive.toMul hi)
    (congrArg Additive.toMul (hd.characterRestrict_eq_zero χ)))

end Langlands.GroupScheme
