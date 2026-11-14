import Langlands.GroupScheme.Reductive.RelativeDerivedGroupStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # Inputs for the relative derived group -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme
namespace RelativeDerived

variable {S : Scheme.{u}} {G D A : GroupScheme S}

/-- The admissibility predicate used, locally, by `RelativeDerivedGroupStatement`. -/
def IsAdmissible (d : D ⟶ G) : Prop :=
  IsClosedSubgroup d ∧ (SubgroupFunctor.range d).IsNormal ∧ IsReductive D ∧
    (∀ s : S, IsSemisimple (geometricFiber D s)) ∧
    ∃ (Q : GroupScheme S) (q : G ⟶ Q),
      RelativeTorus.IsTorus Q ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q

/-- A point which is in the abstract commutator subgroup after an fppf cover. -/
def LocallyCommutator {T : Over S} (x : T ⟶ G.X) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left,
    ∀ i : 𝒰.I₀, (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ x ∈
      _root_.commutator (Over.mk (𝒰.f i ≫ T.hom) ⟶ G.X)

/-- Fppf covers are jointly effective epimorphic, with no quasi-compactness assumption. -/
theorem effectiveEpiFamily_fppfCover {T : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T) :
    EffectiveEpiFamily 𝒰.X 𝒰.f := by
  apply (Sieve.effectiveEpimorphic_family _ _).mp
  rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) (yoneda.obj Y)).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck 𝒰.mem₀)

/-- Morphisms over the base can be compared on any fppf cover of their source. -/
theorem fppfCover_hom_ext {T Y : Over S}
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left)
    (f g : T ⟶ Y)
    (h : ∀ i : 𝒰.I₀,
      (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ f =
      (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) ≫ g) : f = g := by
  let := effectiveEpiFamily_fppfCover 𝒰
  apply Over.OverMorphism.ext
  exact EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f f.left g.left
    (fun i => congrArg (fun a => a.left) (h i))

/-- Homomorphisms map fppf-local commutators to fppf-local commutators. -/
theorem LocallyCommutator.map {T : Over S} {x : T ⟶ D.X}
    (hx : LocallyCommutator x) (d : D ⟶ G) :
    LocallyCommutator (x ≫ d.hom.hom) := by
  obtain ⟨𝒰, h𝒰⟩ := hx
  refine ⟨𝒰, fun i => ?_⟩
  let f := ((yonedaGrp.map d).app
    (Opposite.op (Over.mk (𝒰.f i ≫ T.hom)))).hom
  have hm : f ((Over.homMk (𝒰.f i) rfl) ≫ x) ∈
      (_root_.commutator (Over.mk (𝒰.f i ≫ T.hom) ⟶ D.X)).map f :=
    Subgroup.mem_map.mpr ⟨_, h𝒰 i, rfl⟩
  have hle : (_root_.commutator _).map f ≤ _root_.commutator _ := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact hle hm

/-- Every homomorphism to a commutative group kills fppf-local commutators. -/
theorem LocallyCommutator.comp_eq_one {T : Over S} {x : T ⟶ G.X}
    (hx : LocallyCommutator x) [IsCommMonObj A.X] (φ : G ⟶ A) :
    x ≫ φ.hom.hom = 1 := by
  obtain ⟨𝒰, h𝒰⟩ := hx
  apply fppfCover_hom_ext 𝒰
  intro i
  rw [MonObj.comp_one]
  let f : (Over.mk (𝒰.f i ≫ T.hom) ⟶ G.X) →*
      (Over.mk (𝒰.f i ≫ T.hom) ⟶ A.X) :=
    ((yonedaGrp.map φ).app (Opposite.op (Over.mk (𝒰.f i ≫ T.hom)))).hom
  have hle : _root_.commutator (Over.mk (𝒰.f i ≫ T.hom) ⟶ G.X) ≤ f.ker := by
    change _root_.commutator _ ≤ Subgroup.comap f ⊥
    rw [← Subgroup.map_le_iff_le_comap, map_commutator_eq]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (by rw [← _root_.commutator_def, commutator_eq_bot])
  exact hle (h𝒰 i)

end RelativeDerived

/-- The geometric existence part of the relative derived-group theorem. -/
def RelativeDerivedGroupExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (D : GroupScheme S) (d : D ⟶ G), RelativeDerived.IsAdmissible d

/-- Every relative semisimple group equals its fppf commutator subsheaf. -/
def RelativeSemisimpleFppfPerfectStatement : Prop :=
  ∀ (S : Scheme.{u}) (D : GroupScheme S), IsReductive D →
    (∀ s : S, IsSemisimple (geometricFiber D s)) →
    ∀ (T : Over S) (x : T ⟶ D.X), RelativeDerived.LocallyCommutator x

end Langlands.GroupScheme
