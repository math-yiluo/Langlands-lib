import Langlands.Sheaf.Equivariant.LocalActionDiscretePart
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG uR w

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)
variable {R : Type uR} [CommRing R]

/-- Finite limits of discrete module sheaves are discrete, without a refinement
hypothesis: intersect the fixing subgroups of the finitely many projections. -/
theorem isDiscrete_of_finite_isLimit
    {D₀ : Type} [SmallCategory D₀] [FinCategory D₀]
    {D : D₀ ⥤ Sheaf J (ModuleCat.{w} R)} {c : Cone D} (hc : IsLimit c)
    (hD : ∀ d, L.IsDiscrete (D.obj d).obj) : L.IsDiscrete c.pt.obj := by
  classical
  intro U H a ha s
  choose N hNH hN using fun d => hD d U H a ha ((c.π.app d).hom.app (op U) s)
  refine ⟨H ⊓ OpenSubgroup.iInfOfFinite N, inf_le_left, fun h hh => ?_⟩
  apply Concrete.isLimit_ext
    (D ⋙ sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op U))
    (isLimitOfPreserves (sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op U)) hc)
  intro d
  change (c.π.app d).hom.app (op U) (c.pt.obj.map (a h).unop.op s) =
    (c.π.app d).hom.app (op U) s
  exact ((c.π.app d).hom.naturality_apply (a h).unop.op s).trans
    (hN d h (OpenSubgroup.iInfOfFinite_le N d (inf_le_right (a := H) hh)))

/-- The discrete-sheaf property is closed under finite limits for every local
action system. -/
instance discreteSheafProperty_isClosedUnderFiniteLimits :
    (L.discreteSheafProperty (ModuleCat.{w} R) J).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape D₀ _ _ :=
    { limitsOfShape_le := by
        rintro _ ⟨p⟩
        exact isDiscrete_of_finite_isLimit L J p.isLimit p.prop_diag_obj }

/-- The inclusion of discrete module sheaves preserves finite limits with no
finite equivariant refinement assumption. -/
theorem discreteSheafInclusionFiniteLimits :
    PreservesFiniteLimits (L.discreteSheafInclusion (ModuleCat.{w} R) J) :=
  inferInstance

/-- The ambient sheaf limit of a finite diagram of discrete module sheaves,
regarded as a discrete module sheaf. -/
def discreteSheafLimit {D₀ : Type} [SmallCategory D₀] [FinCategory D₀]
    (D : D₀ ⥤ L.DiscreteSheaf (ModuleCat.{w} R) J) :
    L.DiscreteSheaf (ModuleCat.{w} R) J :=
  ⟨limit (D ⋙ L.discreteSheafInclusion (ModuleCat.{w} R) J),
    isDiscrete_of_finite_isLimit L J (limit.isLimit _) fun d => (D.obj d).property⟩

end Langlands.Sheaf.Equivariant
