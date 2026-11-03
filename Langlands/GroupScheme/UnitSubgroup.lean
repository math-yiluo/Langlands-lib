import Langlands.GroupScheme.Reductive.Basic

/-! # The represented identity subgroup -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section TrivialSubgroup

variable {B : Scheme.{u}} (G : GroupScheme B)

/-- The canonical unit represents the all-test identity subgroup. -/
theorem bot_isRepresentedBy_kernelUnit :
    (⊥ : SubgroupFunctor G).IsRepresentedBy (kernelUnit G) := by
  refine ⟨⟨fun {T} x y _ => toUnit_unique x y⟩, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change y ≫ (kernelUnit G).hom.hom = toUnit T ≫ (kernelUnit G).hom.hom
    exact congrArg (fun f : T ⟶ (Grp.trivial (Over B)).X =>
      f ≫ (kernelUnit G).hom.hom) (toUnit_unique y (toUnit T))
  · intro hx
    have hx : x = 1 := hx
    exact ⟨toUnit T, hx.symm⟩

/-- The identity section of a separated group scheme is a closed subgroup. -/
theorem kernelUnit_isClosedSubgroup [IsSeparated G.X.hom] :
    IsClosedSubgroup (kernelUnit G) := by
  change IsClosedImmersion η[G.X].left
  have he : η[G.X].left ≫ G.X.hom = 𝟙 B := η[G.X].w
  have : IsClosedImmersion (η[G.X].left ≫ G.X.hom) :=
    he.symm ▸ (inferInstance : IsClosedImmersion (𝟙 B))
  exact .of_comp _ G.X.hom

end TrivialSubgroup


variable {S : Scheme.{u}}

/-- The unit homomorphism has precisely the identity points on every test. -/
theorem range_kernelUnit (G : GroupScheme S) :
    SubgroupFunctor.range (kernelUnit G) = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change y ≫ η[G.X] = 1
    rw [toUnit_unique y (toUnit T)]
    rfl
  · intro hx
    have hx' : x = 1 := by
      simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hx
    exact ⟨toUnit T, hx'.symm⟩


end Langlands.GroupScheme
