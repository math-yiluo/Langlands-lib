import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! # Epimorphisms and projective lifting in the actual inertia block -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj ZeroObject

namespace Langlands.SmoothRep

universe uG uV

variable {H : Type uG} [Group H] [TopologicalSpace H]

/-- A categorical zero smooth representation has a subsingleton carrier. -/
theorem subsingleton_of_isZero {A : SmoothRep.{0, uG, uV} ℂ H}
    (hA : IsZero A) : Subsingleton A := by
  have hv (v : A) : v = 0 := by
    have h := congrArg (fun f : A ⟶ A => hom f v) (hA.eq_of_src (𝟙 A) 0)
    exact h
  exact ⟨fun x y => (hv x).trans (hv y).symm⟩

end Langlands.SmoothRep

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalInertiaLiftingTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))

/-- The all-subquotients inertia block contains zero, without assumptions on its base. -/
instance rationalInertiaBlockProperty_containsZero :
    (rationalInertiaBlockProperty G π).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro D hD h
    have := SmoothRep.subsingleton_of_isZero
      (isZero_zero (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)))
    have := Langlands.CuspidalSupport.subsingleton_of_isSubquotient h
    have := hD
    exact False.elim ((bot_ne_top : (⊥ : Subrepresentation D.representation) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _)))

/-- Closure under actual subquotients implies closure under categorical subobjects. -/
instance rationalInertiaBlockProperty_isClosedUnderSubobjects :
    (rationalInertiaBlockProperty G π).IsClosedUnderSubobjects where
  prop_of_mono f _ hA :=
    rationalInertiaBlockProperty_of_isSubquotient hA
      (SmoothRep.IsSubrepresentation.isSubquotient
        ⟨f, (SmoothRep.mono_iff_injective f).1 inferInstance⟩)

/-- Closure under actual subquotients implies closure under categorical quotients. -/
instance rationalInertiaBlockProperty_isClosedUnderQuotients :
    (rationalInertiaBlockProperty G π).IsClosedUnderQuotients where
  prop_of_epi f _ hA :=
    rationalInertiaBlockProperty_of_isSubquotient hA
      (SmoothRep.IsQuotient.isSubquotient
        ⟨f, (SmoothRep.epi_iff_surjective f).1 inferInstance⟩)

/-- The full inclusion sends block epimorphisms to ambient epimorphisms. -/
instance rationalInertiaBlock_preservesEpimorphisms :
    (rationalInertiaBlockProperty G π).ι.PreservesEpimorphisms :=
  ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory _

/-- Epimorphisms in the actual inertia block are precisely the surjective maps. -/
theorem rationalInertiaBlock_epi_iff_surjective
    {A B : RationalInertiaBlock G π} (f : A ⟶ B) :
    Epi f ↔ Function.Surjective (SmoothRep.hom f.hom) := by
  constructor
  · intro _
    exact (SmoothRep.epi_iff_surjective
      ((rationalInertiaBlockProperty G π).ι.map f)).1 inferInstance
  · intro hf
    exact (rationalInertiaBlockProperty G π).ι.epi_of_epi_map
      ((SmoothRep.epi_iff_surjective f.hom).2 hf)

/-- The full inclusion sends block monomorphisms to ambient monomorphisms. -/
instance rationalInertiaBlock_preservesMonomorphisms :
    (rationalInertiaBlockProperty G π).ι.PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

/-- Monomorphisms in the actual inertia block are precisely the injective maps. -/
theorem rationalInertiaBlock_mono_iff_injective
    {A B : RationalInertiaBlock G π} (f : A ⟶ B) :
    Mono f ↔ Function.Injective (SmoothRep.hom f.hom) := by
  constructor
  · intro _
    exact (SmoothRep.mono_iff_injective
      ((rationalInertiaBlockProperty G π).ι.map f)).1 inferInstance
  · intro hf
    exact (rationalInertiaBlockProperty G π).ι.mono_of_mono_map
      ((SmoothRep.mono_iff_injective f.hom).2 hf)

/-- A chosen lift in the actual full block, from ambient projectivity. -/
def rationalInertiaBlockProjectiveLift
    (P : RationalInertiaBlock G π) [Projective P.obj]
    {X Y : RationalInertiaBlock G π} (f : P ⟶ Y) (q : X ⟶ Y) [Epi q] : P ⟶ X :=
  by
    have : Epi q.hom := (SmoothRep.epi_iff_surjective q.hom).2
      ((rationalInertiaBlock_epi_iff_surjective G π q).1 inferInstance)
    exact ObjectProperty.homMk (Projective.factorThru f.hom q.hom)

/-- The chosen block lift has the required composite. -/
@[simp]
theorem rationalInertiaBlockProjectiveLift_comp
    (P : RationalInertiaBlock G π) [Projective P.obj]
    {X Y : RationalInertiaBlock G π} (f : P ⟶ Y) (q : X ⟶ Y) [Epi q] :
    rationalInertiaBlockProjectiveLift G π P f q ≫ q = f := by
  have : Epi q.hom := (SmoothRep.epi_iff_surjective q.hom).2
    ((rationalInertiaBlock_epi_iff_surjective G π q).1 inferInstance)
  apply ObjectProperty.hom_ext
  exact Projective.factorThru_comp f.hom q.hom

/-- Ambient projectivity supplies projectivity in the actual inertia block. -/
theorem rationalInertiaBlock_projective_of_projective
    (P : RationalInertiaBlock G π) (hP : Projective P.obj) : Projective P := by
  have := hP
  exact ⟨fun f q _ => ⟨rationalInertiaBlockProjectiveLift G π P f q,
    rationalInertiaBlockProjectiveLift_comp G π P f q⟩⟩

end Langlands.CuspidalSupport
