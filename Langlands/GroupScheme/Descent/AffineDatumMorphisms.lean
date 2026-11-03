import Langlands.GroupScheme.Descent.AffineDatumGroup
import Langlands.GroupScheme.Descent.FpqcHomDescent

/-! # Morphisms and comparisons for actual affine descent solutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

namespace Solution

variable {B S : Scheme.{u}} {p : S ⟶ B}
    [Flat p] [Surjective p] [QuasiCompact p]
    {G H I : GroupScheme S} {D : Datum p G} {E : Datum p H} {K : Datum p I}

/-- The solution comparison detects equality of actual descended morphisms. -/
theorem hom_ext (s : Solution D) (t : Solution E) {a b : s.obj ⟶ t.obj}
    (h : (baseChange p).map a ≫ t.iso.hom =
      (baseChange p).map b ≫ t.iso.hom) : a = b := by
  apply Grp.hom_ext
  apply (Over.pullback p).map_injective
  exact congrArg (fun f => f.hom.hom) ((cancel_mono t.iso.hom).mp h)

/-- Descending an identity preserves the actual identity. -/
@[simp] theorem descendHom_id (s : Solution D) :
    descendHom s s (𝟙 G) (compatible_id D) = 𝟙 s.obj := by
  symm
  apply descendHom_unique s s (𝟙 G) (compatible_id D)
  simp

/-- Descending compatible morphisms preserves composition. -/
theorem descendHom_comp (s : Solution D) (t : Solution E) (r : Solution K)
    (f : G ⟶ H) (g : H ⟶ I) (hf : Compatible D E f) (hg : Compatible E K g) :
    descendHom s r (f ≫ g) (hf.comp hg) =
      descendHom s t f hf ≫ descendHom t r g hg := by
  symm
  apply descendHom_unique s r (f ≫ g) (hf.comp hg)
  rw [Functor.map_comp, Category.assoc, baseChange_descendHom,
    ← Category.assoc, baseChange_descendHom, Category.assoc]

/-- A compatible actual isomorphism descends to an actual isomorphism. -/
def descendIso (s : Solution D) (t : Solution E) (e : G ≅ H)
    (he : Compatible D E e.hom) : s.obj ≅ t.obj where
  hom := descendHom s t e.hom he
  inv := descendHom t s e.inv (he.inv e)
  hom_inv_id := by
    apply hom_ext s s
    rw [Functor.map_comp, Category.assoc, baseChange_descendHom,
      ← Category.assoc, baseChange_descendHom, Category.assoc, e.hom_inv_id,
      Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]
  inv_hom_id := by
    apply hom_ext t t
    rw [Functor.map_comp, Category.assoc, baseChange_descendHom,
      ← Category.assoc, baseChange_descendHom, Category.assoc, e.inv_hom_id,
      Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The descended isomorphism recovers the given isomorphism through both solutions. -/
theorem baseChange_descendIso (s : Solution D) (t : Solution E) (e : G ≅ H)
    (he : Compatible D E e.hom) :
    (baseChange p).mapIso (descendIso s t e he) ≪≫ t.iso = s.iso ≪≫ e := by
  apply Iso.ext
  exact baseChange_descendHom s t e.hom he

/-- Two solutions of the same actual datum have a canonical isomorphism. -/
def comparison (s t : Solution D) : s.obj ≅ t.obj :=
  descendIso s t (Iso.refl G) (compatible_id D)

/-- The canonical comparison respects the original pullback identifications. -/
theorem comparison_hom (s t : Solution D) :
    (baseChange p).map (comparison s t).hom ≫ t.iso.hom = s.iso.hom := by
  simpa only [comparison, descendIso, Iso.refl_hom, Category.comp_id] using
    baseChange_descendHom s t (𝟙 G) (compatible_id D)

/-- The pullback identifications determine the comparison isomorphism uniquely. -/
theorem existsUnique_comparison (s t : Solution D) :
    ∃! e : s.obj ≅ t.obj,
      (baseChange p).map e.hom ≫ t.iso.hom = s.iso.hom := by
  refine ⟨comparison s t, comparison_hom s t, ?_⟩
  intro e he
  apply Iso.ext
  apply hom_ext s t
  exact he.trans (comparison_hom s t).symm

variable (s : Solution D) (C : GroupScheme B)
    (f : G ⟶ (baseChange p).obj C) (hf : Compatible D (canonicalDatum p C) f)

/-- Descend a compatible arrow to a group scheme already defined over the base. -/
def descendTo : s.obj ⟶ C :=
  descendHom s (canonicalSolution p C) f hf

/-- Base change of the descended arrow recovers the supplied arrow. -/
theorem baseChange_descendTo :
    (baseChange p).map (descendTo s C f hf) = s.iso.hom ≫ f := by
  simpa only [descendTo, canonicalSolution, Iso.refl_hom, Category.comp_id] using
    baseChange_descendHom s (canonicalSolution p C) f hf

include hf in
/-- The supplied compatible arrow has exactly one descent through this solution. -/
theorem existsUnique_descendTo :
    ∃! a : s.obj ⟶ C, (baseChange p).map a = s.iso.hom ≫ f := by
  simpa only [canonicalSolution, Iso.refl_hom, Category.comp_id] using
    existsUnique_descendHom s (canonicalSolution p C) f hf

/-- Changing the solution changes the descended arrow by its canonical comparison. -/
theorem comparison_hom_descendTo (t : Solution D) :
    (comparison s t).hom ≫ descendTo t C f hf = descendTo s C f hf := by
  apply hom_ext s (canonicalSolution p C)
  change (baseChange p).map ((comparison s t).hom ≫ descendTo t C f hf) ≫ 𝟙 _ =
    (baseChange p).map (descendTo s C f hf) ≫ 𝟙 _
  simp only [Category.comp_id, Functor.map_comp, baseChange_descendTo]
  rw [← Category.assoc, comparison_hom]

end Solution

namespace Datum

variable {B S : Scheme.{u}} {p : S ⟶ B}
    [IsAffine B] [IsAffine S] [Flat p] [Surjective p]
    {G H : GroupScheme S}
    [IsAffine G.X.left] [IsAffine H.X.left]
    (D : Datum p G) (E : Datum p H)

/-- Construct the actual descended morphism between the constructed affine solutions. -/
def affineHom (f : G ⟶ H) (hf : Compatible D E f) :
    D.affineSolution.obj ⟶ E.affineSolution.obj :=
  Solution.descendHom D.affineSolution E.affineSolution f hf

/-- Pullback identifies the constructed affine morphism with the original morphism. -/
theorem baseChange_affineHom (f : G ⟶ H) (hf : Compatible D E f) :
    (baseChange p).map (D.affineHom E f hf) ≫ E.affineSolution.iso.hom =
      D.affineSolution.iso.hom ≫ f :=
  Solution.baseChange_descendHom D.affineSolution E.affineSolution f hf

/-- Construct an actual isomorphism from a compatible isomorphism of affine data. -/
def affineIso (e : G ≅ H) (he : Compatible D E e.hom) :
    D.affineSolution.obj ≅ E.affineSolution.obj :=
  Solution.descendIso D.affineSolution E.affineSolution e he

variable (C : GroupScheme B)

/-- Construct the descended arrow from affine datum effectivity and compatibility alone. -/
def affineHomTo (f : G ⟶ (baseChange p).obj C)
    (hf : Compatible D (canonicalDatum p C) f) : D.affineSolution.obj ⟶ C :=
  Solution.descendTo D.affineSolution C f hf

/-- The constructed arrow has exactly the given pullback after the solution comparison. -/
theorem baseChange_affineHomTo (f : G ⟶ (baseChange p).obj C)
    (hf : Compatible D (canonicalDatum p C) f) :
    (baseChange p).map (D.affineHomTo C f hf) = D.affineSolution.iso.hom ≫ f :=
  Solution.baseChange_descendTo D.affineSolution C f hf

/-- There is exactly one such descended arrow; no supplied solution is an input. -/
theorem existsUnique_affineHomTo (f : G ⟶ (baseChange p).obj C)
    (hf : Compatible D (canonicalDatum p C) f) :
    ∃! a : D.affineSolution.obj ⟶ C,
      (baseChange p).map a = D.affineSolution.iso.hom ≫ f :=
  Solution.existsUnique_descendTo D.affineSolution C f hf

end Datum

end Langlands.GroupScheme.Descent
