import Langlands.Representation.Category.SmoothCoproducts
import Langlands.CategoryTheory.Renard.HomCoproductDecomposition
import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite generation and actual smooth coproducts -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Langlands.CategoryTheory.Renard

namespace Langlands.SmoothRep

universe uG uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} [DecidableEq I]
  (A : I → SmoothRep.{0, uG, max uI uV} ℂ G)

@[simp]
theorem directSumι_comp_π_self (i : I) :
    directSumι A i ≫ directSumπ A i = 𝟙 (A i) := by
  apply ObjectProperty.hom_ext
  ext v
  change DirectSum.component ℂ I (fun i => A i) i
    (DirectSum.lof ℂ I (fun i => A i) i v) = v
  exact DirectSum.component.lof_self ℂ (M := fun i => A i) i v

theorem directSumι_comp_π_of_ne {i j : I} (h : i ≠ j) :
    directSumι A i ≫ directSumπ A j = 0 := by
  apply ObjectProperty.hom_ext
  ext v
  change DirectSum.component ℂ I (fun i => A i) j
    (DirectSum.lof ℂ I (fun i => A i) i v) = 0
  simp [DirectSum.component.of, h]

/-- Equality of maps into the actual direct sum can be tested by its actual
coordinate projections. -/
theorem directSum_hom_ext {P : SmoothRep.{0, uG, max uI uV} ℂ G}
    {f g : P ⟶ directSum A}
    (h : ∀ i, f ≫ directSumπ A i = g ≫ directSumπ A i) : f = g := by
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext v
  apply DFinsupp.ext
  intro i
  exact congrArg (fun k => hom k v) (h i)

/-- A morphism from an actually finitely generated group-algebra module to a
smooth direct sum has only finitely many nonzero coordinate morphisms. -/
theorem finite_support_hom_directSum
    (P : SmoothRep.{0, uG, max uI uV} ℂ G)
    [Module.Finite (MonoidAlgebra ℂ G) P.representation.asModule]
    (f : P ⟶ directSum A) :
    ∃ T : Finset I, ∀ i ∉ T, f ≫ directSumπ A i = 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp
    (inferInstance : Module.Finite (MonoidAlgebra ℂ G) P.representation.asModule)
  let T := s.biUnion (fun v =>
    (hom f (P.representation.asModuleEquiv v)).support)
  refine ⟨T, fun i hi => ?_⟩
  let L := Representation.IntertwiningMap.equivLinearMapAsModule
    _ _ (hom (f ≫ directSumπ A i))
  have hL : L = 0 := by
    apply LinearMap.ext_on hs
    intro v hv
    change (show DFinsupp (fun i => A i) from
      hom f (P.representation.asModuleEquiv v)) i = 0
    apply DFinsupp.notMem_support_iff.mp
    intro hiv
    exact hi (Finset.mem_biUnion.mpr ⟨v, hv, hiv⟩)
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  ext v
  exact congrArg (fun k => k (P.representation.asModuleEquiv.symm v)) hL

/-- Every map from a finitely generated smooth representation to the actual
direct sum is a finite sum of its component morphisms. -/
theorem finite_decomposition_hom_directSum
    (P : SmoothRep.{0, uG, max uI uV} ℂ G)
    [Module.Finite (MonoidAlgebra ℂ G) P.representation.asModule]
    (f : P ⟶ directSum A) :
    ∃ T : Finset I, (∀ i ∉ T, f ≫ directSumπ A i = 0) ∧
      f = ∑ i ∈ T, (f ≫ directSumπ A i) ≫ directSumι A i := by
  classical
  obtain ⟨T, hT⟩ := finite_support_hom_directSum A P f
  refine ⟨T, hT, directSum_hom_ext A (fun j => ?_)⟩
  rw [Preadditive.sum_comp]
  by_cases hj : j ∈ T
  · rw [Finset.sum_eq_single j]
    · rw [Category.assoc, directSumι_comp_π_self, Category.comp_id]
    · intro i _ hij
      rw [Category.assoc, directSumι_comp_π_of_ne A hij, comp_zero]
    · exact fun h => False.elim (h hj)
  · rw [hT j hj]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Category.assoc, directSumι_comp_π_of_ne A (fun h : i = j => hj (h ▸ hi)),
      comp_zero]

/-- The actual integer-module Hom cofan on the actual smooth direct sum is a
coproduct when the source is finitely generated over its group algebra. -/
def homDirectSumIsColimit
    (P : SmoothRep.{0, uG, max uI uV} ℂ G)
    [Module.Finite (MonoidAlgebra ℂ G) P.representation.asModule] :
    IsColimit (Cofan.mk ((preadditiveCoyonedaInt P).obj (directSum A))
      (fun i => (preadditiveCoyonedaInt P).map (directSumι A i))) :=
  homCofanIsColimitOfFiniteDecomposition (directSumCofan A) (directSumπ A)
    (directSumι_comp_π_self A)
    (fun _ _ h => directSumι_comp_π_of_ne A h)
    (finite_decomposition_hom_directSum A P)

/-- Finite group-algebra generation implies preservation of this coproduct by
the actual integer-module Hom functor. -/
theorem hom_preservesDirectSum
    (P : SmoothRep.{0, uG, max uI uV} ℂ G)
    [Module.Finite (MonoidAlgebra ℂ G) P.representation.asModule] :
    PreservesColimit (Discrete.functor A) (preadditiveCoyonedaInt P) := by
  apply preservesColimit_of_preserves_colimit_cocone (directSumIsColimit A)
  exact (isColimitMapCoconeCofanMkEquiv _ A (directSumι A)).symm
    (homDirectSumIsColimit A P)

section FullSubcategory

variable (Q : ObjectProperty (SmoothRep.{0, uG, max uI uV} ℂ G))
  (B : I → Q.FullSubcategory)
  (hB : Q (directSum (fun i => (B i).obj)))

/-- The actual direct-sum cofan inside any full smooth subcategory containing
its direct-sum vertex. -/
def fullSubcategoryDirectSumCofan : Cofan B :=
  Cofan.mk ⟨directSum (fun i => (B i).obj), hB⟩
    (fun i => ObjectProperty.homMk (directSumι (fun i => (B i).obj) i))

/-- The ambient direct-sum universal property restricts to the full
subcategory. -/
def fullSubcategoryDirectSumIsColimit :
    IsColimit (fullSubcategoryDirectSumCofan Q B hB) := by
  let A := fun i => (B i).obj
  refine Cofan.IsColimit.mk _
    (fun c => ObjectProperty.homMk
      ((directSumIsColimit A).desc (Cofan.mk c.pt.obj (fun i => (c.inj i).hom))))
    ?_ ?_
  · intro c i
    apply ObjectProperty.hom_ext
    exact (directSumIsColimit A).fac
      (Cofan.mk c.pt.obj (fun i => (c.inj i).hom)) ⟨i⟩
  · intro c m hm
    apply ObjectProperty.hom_ext
    apply (directSumIsColimit A).uniq
      (Cofan.mk c.pt.obj (fun i => (c.inj i).hom))
    rintro ⟨i⟩
    exact congrArg (fun f => f.hom) (hm i)

/-- The actual integer-module Hom cofan in a full smooth subcategory is a
coproduct when its source is finitely generated over the actual group algebra.
The only closure input is membership of this actual direct sum. -/
def homFullSubcategoryDirectSumIsColimit (P : Q.FullSubcategory)
    [Module.Finite (MonoidAlgebra ℂ G) P.obj.representation.asModule] :
    IsColimit (Cofan.mk
      ((preadditiveCoyonedaInt P).obj (fullSubcategoryDirectSumCofan Q B hB).pt)
      (fun i => (preadditiveCoyonedaInt P).map
        ((fullSubcategoryDirectSumCofan Q B hB).inj i))) := by
  let A := fun i => (B i).obj
  let π : ∀ i, (fullSubcategoryDirectSumCofan Q B hB).pt ⟶ B i :=
    fun i => ObjectProperty.homMk (directSumπ A i)
  apply homCofanIsColimitOfFiniteDecomposition
    (fullSubcategoryDirectSumCofan Q B hB) π
  · intro i
    apply ObjectProperty.hom_ext
    exact directSumι_comp_π_self A i
  · intro i j hij
    apply ObjectProperty.hom_ext
    exact directSumι_comp_π_of_ne A hij
  · intro f
    obtain ⟨T, hT, hx⟩ := finite_decomposition_hom_directSum A P.obj f.hom
    refine ⟨T, ?_, ?_⟩
    · intro i hi
      apply ObjectProperty.hom_ext
      exact hT i hi
    · apply ObjectProperty.hom_ext
      exact hx.trans (Q.ι.map_sum
        (fun i => (f ≫ π i) ≫ (fullSubcategoryDirectSumCofan Q B hB).inj i) T).symm

include hB in
/-- The actual integer-module Hom functor preserves a coproduct in a full
smooth subcategory whose actual direct sum belongs to the subcategory. -/
theorem hom_preservesFullSubcategoryDirectSum (P : Q.FullSubcategory)
    [Module.Finite (MonoidAlgebra ℂ G) P.obj.representation.asModule] :
    PreservesColimit (Discrete.functor B) (preadditiveCoyonedaInt P) := by
  apply preservesColimit_of_preserves_colimit_cocone
    (fullSubcategoryDirectSumIsColimit Q B hB)
  exact (isColimitMapCoconeCofanMkEquiv _ B
    ((fullSubcategoryDirectSumCofan Q B hB).inj)).symm
    (homFullSubcategoryDirectSumIsColimit Q B hB P)

end FullSubcategory

omit [DecidableEq I] in
/-- On a full smooth subcategory closed under these actual direct sums, finite
group-algebra generation implies preservation of all `I`-indexed coproducts. -/
theorem hom_preservesFullSubcategoryCoproducts
    (Q : ObjectProperty (SmoothRep.{0, uG, max uI uV} ℂ G))
    (hQ : ∀ (B : I → Q.FullSubcategory) [d : DecidableEq I],
      Q (@directSum G _ _ I d (fun i => (B i).obj)))
    (P : Q.FullSubcategory)
    [Module.Finite (MonoidAlgebra ℂ G) P.obj.representation.asModule] :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyonedaInt P) := by
  classical
  have : ∀ (B : I → Q.FullSubcategory),
      PreservesColimit (Discrete.functor B) (preadditiveCoyonedaInt P) :=
    fun B => hom_preservesFullSubcategoryDirectSum Q B (hQ B) P
  exact preservesColimitsOfShape_of_discrete _

end Langlands.SmoothRep
