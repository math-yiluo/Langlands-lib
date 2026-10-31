import Langlands.Cohomology.FiniteClosedSupportSheafStatement
import Langlands.Cohomology.CechFlasque
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Abelian sheaves with finite closed support: proof

Let `F` be an abelian sheaf on a topological space `X` whose stalks vanish outside a finite set
`S` of closed points. For an open `U`, the set `S ∩ U` is closed, so `U` and the open complement
of `S ∩ U` cover `X`. Their overlap misses `S`, so every section over it is zero. A section over
`U` therefore glues with zero to a section over their union, which contains every open; this gives
surjectivity of every restriction map. Global-section detection of the zero sheaf follows by restricting along `U ≤ ⊤`
and passing to stalks.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Langlands.Cohomology.FiniteClosedSupportSheaf

open Langlands.Cohomology.Cech

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) {S : Set X}

/-- If `S` is a finite set of closed points, then `S ∩ U` is closed for every set `U`. -/
lemma isClosed_inter (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X)) (U : Set X) :
    IsClosed (S ∩ U) := by
  have := (hS.inter_of_left U).isClosed_biUnion (f := fun x => ({x} : Set X))
    fun x hx => hcl x hx.1
  simpa only [Set.biUnion_of_singleton] using this

/-- The open complement of `S ∩ U`. -/
def complOpen (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X)) (U : Opens X) :
    Opens X :=
  ⟨(S ∩ (U : Set X))ᶜ, (isClosed_inter hS hcl U).isOpen_compl⟩

/-- `U` and the open complement of `S ∩ U` cover the whole space. -/
lemma le_sup_complOpen (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X))
    (U V : Opens X) : V ≤ U ⊔ complOpen hS hcl U := by
  intro x _
  by_cases hx : x ∈ U
  · exact Or.inl hx
  · exact Or.inr fun h => hx h.2

/-- Every section over an open disjoint from `S` is zero, because its germs lie in zero stalks. -/
lemma eq_zero_of_forall_not_mem
    (hz : ∀ x, x ∉ S →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj))
    {V : Opens X} (hV : ∀ x ∈ V, x ∉ S) (s : F.1.obj (op V)) : s = 0 := by
  apply TopCat.Presheaf.section_ext F V s 0
  intro x hx
  have : Subsingleton (F.presheaf.stalk x) :=
    AddCommGrpCat.subsingleton_of_isZero (hz x (hV x hx))
  exact Subsingleton.elim _ _

/-- Every section over `U` is the restriction of a section over `U ⊔ complOpen U`, obtained by
gluing it with zero on the open complement of `S ∩ U`. -/
lemma exists_res_eq (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hz : ∀ x, x ∉ S →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj))
    (U : Opens X) (s : F.1.obj (op U)) :
    ∃ t : F.1.obj (op (U ⊔ complOpen hS hcl U)), res le_sup_left t = s := by
  obtain ⟨t, ht, -⟩ := exists_glue₂ F s (0 : F.1.obj (op (complOpen hS hcl U))) (by
    rw [map_zero]
    exact eq_zero_of_forall_not_mem F hz (V := U ⊓ complOpen hS hcl U)
      (fun x hx hxS => hx.2 ⟨hxS, hx.1⟩) _)
  exact ⟨t, ht⟩

/-- Every restriction map of `F` is surjective. -/
lemma surjective_res (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hz : ∀ x, x ∉ S →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj))
    {V U : Opens X} (h : V ≤ U) : Function.Surjective (res (P := F.1) h) := by
  intro s
  obtain ⟨t, ht⟩ := exists_res_eq F hS hcl hz V s
  refine ⟨res (le_sup_complOpen hS hcl V U) t, ?_⟩
  rw [res_res]
  exact ht

/-- `F` is flasque. -/
lemma isFlasque (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hz : ∀ x, x ∉ S →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj)) :
    TopCat.Presheaf.IsFlasque F.obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_res F hS hcl hz (leOfHom i.unop)

/-- If the global sections of `F` vanish, then `F` is a zero object. -/
lemma isZero_of_isZero_top (hS : S.Finite) (hcl : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hz : ∀ x, x ∉ S →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj))
    (h : IsZero (F.obj.obj (op (⊤ : Opens X)))) : IsZero F := by
  have := isFlasque F hS hcl hz
  have hP : IsZero F.obj :=
    Functor.isZero _ fun U => h.of_epi (F.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op)
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro x
  exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_isZero hP

end Langlands.Cohomology.FiniteClosedSupportSheaf

namespace Langlands.Cohomology

open FiniteClosedSupportSheaf

/-- An abelian sheaf whose nonzero stalks lie in a finite set of closed points is flasque, and its
global-section object is zero exactly when the sheaf is zero. -/
theorem finiteClosedSupportSheaf : FiniteClosedSupportSheafStatement.{u} := by
  intro X F S hS hcl hz
  refine ⟨isFlasque F hS hcl hz, isZero_of_isZero_top F hS hcl hz, fun h => ?_⟩
  exact ((TopCat.Sheaf.forget AddCommGrpCat X).map_isZero h).obj _

end Langlands.Cohomology
