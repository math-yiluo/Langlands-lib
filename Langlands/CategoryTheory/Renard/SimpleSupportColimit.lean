import Langlands.CategoryTheory.Renard.SimpleSupportColimitStatements
import Langlands.CategoryTheory.Renard.SimpleSubquotientSum
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Renard A.IX: coproducts and colimits of supported objects

Proof of the colimit-closure assertion on printed268/PDF274 of the French
edition dated 9 July 2026. The images of the coproduct injections are
quotients of the summands whose sum is the whole coproduct, so the
arbitrary-sum identity of A.VI.3 applies. A colimit cocone vertex is a
quotient of the coproduct of the diagram objects.
-/

universe w t v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

section General

variable {C : Type u} [Category.{v} C]

/-- The canonical morphism from the coproduct of the objects of a diagram to
the vertex of a colimit cocone is an epimorphism. Only the coproduct indexed
by the objects of `J` is used. -/
theorem epi_sigmaDesc_of_isColimit {J : Type w} [Category.{t} J] {F : J ⥤ C}
    {c : Cocone F} (hc : IsColimit c) [HasCoproduct fun j => F.obj j] :
    Epi (Sigma.desc fun j => c.ι.app j) := by
  constructor
  intro Z g h hgh
  apply hc.hom_ext
  intro j
  simpa using Sigma.ι (fun j => F.obj j) j ≫= hgh

end General

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Support passes to quotients. -/
theorem HasSimpleSupport.of_epi {S : Set (ObjectClass C)} {X Y : C} (p : X ⟶ Y) [Epi p]
    (hX : HasSimpleSupport S X) : HasSimpleSupport S Y :=
  (simpleSubquotientClasses_subset_of_epi p).trans hX

/-- Support passes to subobjects. -/
theorem HasSimpleSupport.of_mono {S : Set (ObjectClass C)} {X Y : C} (m : X ⟶ Y) [Mono m]
    (hY : HasSimpleSupport S Y) : HasSimpleSupport S X :=
  (simpleSubquotientClasses_subset_of_mono m).trans hY

variable [HasCoproducts.{w} C]

/-- The arrow of the sum of the images of the coproduct injections is an
epimorphism: the coproduct map of these images has a section. -/
theorem epi_subobjectSum_imageSubobject_arrow {I : Type w} (F : I → C) :
    Epi (subobjectSum fun i => imageSubobject (Sigma.ι F i)).arrow := by
  let G : I → Subobject (∐ F) := fun i => imageSubobject (Sigma.ι F i)
  let s : (∐ F) ⟶ ∐ fun i => (G i : C) :=
    Sigma.desc fun i => factorThruImageSubobject (Sigma.ι F i) ≫ Sigma.ι (fun i => (G i : C)) i
  have hs : (s ≫ subobjectSumπ G) ≫ (subobjectSum G).arrow = 𝟙 (∐ F) := by
    rw [Category.assoc, subobjectSumπ_arrow]
    ext i
    simp [s, G, subobjectSumDesc, imageSubobject_arrow_comp]
  exact epi_of_epi_fac hs

/-- The images of the coproduct injections have the whole coproduct as their sum. -/
theorem subobjectSum_imageSubobject_sigmaι {I : Type w} (F : I → C) :
    subobjectSum (fun i => imageSubobject (Sigma.ι F i)) = ⊤ := by
  have := epi_subobjectSum_imageSubobject_arrow F
  have : IsIso (subobjectSum fun i => imageSubobject (Sigma.ι F i)).arrow :=
    isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

end Abelian

/-- In the source setting, every simple subquotient class of an actual
`w`-indexed coproduct occurs in one of its summands. -/
theorem simpleSubquotientClasses_sigma_subset {C : Type u} [Category.{v} C] [Abelian C]
    (hG : IsSourceGrothendieck.{w} C) (hAB6 : SourceAB6 C) {I : Type w} (F : I → C) :
    letI : HasCoproducts.{w} C := hG.1
    simpleSubquotientClasses (∐ F) ⊆ ⋃ i, simpleSubquotientClasses (F i) := by
  let : HasCoproducts.{w} C := hG.1
  let G : I → Subobject (∐ F) := fun i => imageSubobject (Sigma.ι F i)
  have := epi_subobjectSum_imageSubobject_arrow F
  intro q hq
  have hq' := simpleSubquotientClasses_subset_of_epi (subobjectSum G).arrow hq
  rw [simpleSubquotientSum C hG hAB6 (∐ F) I G] at hq'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq'
  exact Set.mem_iUnion.mpr
    ⟨i, simpleSubquotientClasses_subset_of_epi (factorThruImageSubobject (Sigma.ι F i)) hi⟩

/-- Renard A.IX, coproduct case: an actual `w`-indexed coproduct of
supported objects is supported. -/
theorem simpleSupportCoproduct (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportCoproductStatement.{w} C := by
  intro hG hAB6 S _ I F hF q hq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (simpleSubquotientClasses_sigma_subset hG hAB6 F hq)
  exact hF i hi

/-- Renard A.IX, colimit case: the vertex of every actual colimit cocone of
a diagram of supported objects is supported. -/
theorem simpleSupportColimit (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportColimitStatement.{w,t} C := by
  intro hG hAB6 S hS J _ F c hc hF
  let : HasCoproducts.{w} C := hG.1
  have := epi_sigmaDesc_of_isColimit hc
  exact HasSimpleSupport.of_epi (Sigma.desc fun j => c.ι.app j)
    (simpleSupportCoproduct C hG hAB6 S hS J (fun j => F.obj j) hF)

/-- Renard A.IX: coproduct and actual colimit closure of supported objects. -/
theorem simpleSupportColimitClosure (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportColimitClosureStatement.{w,t} C :=
  ⟨simpleSupportCoproduct C, simpleSupportColimit C⟩

end Langlands.Renard
