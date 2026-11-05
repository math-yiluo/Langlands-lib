import Langlands.AlgebraicGeometry.Picard.FormalLineBundleSystem

/-! # Actual module systems on adic thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open Picard.FormalLineBundle

/-- Actual module sheaves on the quotient-spectrum thickenings, together with
specified ordinary-pullback transition isomorphisms. -/
structure FormalModuleSystem {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) where
  obj (n : ℕ) : (adicSpace f I n).Modules
  transition (n : ℕ) :
    (Scheme.Modules.pullback (adicTransition f I n)).obj (obj (n + 1)) ≅ obj n

namespace FormalModuleSystem

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {I : Ideal R}

/-- The ordinary restrictions of an actual module sheaf, with the canonical
transition induced by composition of pullbacks. -/
def ofModule (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (M : X.Modules) : FormalModuleSystem f I where
  obj n := (Scheme.Modules.pullback (adicProjection f I n)).obj M
  transition n :=
    (Scheme.Modules.pullbackComp (adicTransition f I n) (adicProjection f I (n + 1))).app M ≪≫
      (Scheme.Modules.pullbackCongr (adicTransition_projection f I n)).app M

/-- A single comparison of whole actual systems, with all transition squares. -/
structure Comparison (F G : FormalModuleSystem f I) where
  component (n : ℕ) : F.obj n ≅ G.obj n
  commutes (n : ℕ) :
    (Scheme.Modules.pullback (adicTransition f I n)).map (component (n + 1)).hom ≫
        (G.transition n).hom =
      (F.transition n).hom ≫ (component n).hom

/-- Identity comparison of actual module systems. -/
def Comparison.refl (F : FormalModuleSystem f I) : Comparison F F where
  component n := Iso.refl (F.obj n)
  commutes n := by simp

/-- Composition preserves every transition square. -/
def Comparison.trans {F G H : FormalModuleSystem f I}
    (e : Comparison F G) (d : Comparison G H) : Comparison F H where
  component n := e.component n ≪≫ d.component n
  commutes n := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [d.commutes, ← Category.assoc, e.commutes, Category.assoc]

/-- Algebraization retains a comparison of the whole restriction system. -/
def IsAlgebraization (M : X.Modules) (F : FormalModuleSystem f I) : Prop :=
  Nonempty (Comparison (ofModule f I M) F)

/-- A module sheaf algebraizes its own ordinary restrictions. -/
lemma isAlgebraization_ofModule (M : X.Modules) :
    IsAlgebraization M (ofModule f I M) :=
  ⟨Comparison.refl _⟩

end FormalModuleSystem

end Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Modules

namespace FormalLineBundleSystem

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {I : Ideal R}

/-- Forget local rank one while retaining actual transition isomorphisms. -/
def toModuleSystem (F : FormalLineBundleSystem f I) : FormalModuleSystem f I where
  obj n := (F.obj n).obj
  transition n := (LineBundle.forget _).mapIso (F.transition n)

set_option backward.isDefEq.respectTransparency false

private lemma restrictionModuleSquare {Y Z : Scheme.{u}}
    (j : Y ⟶ X) (k : Z ⟶ Y) (l : Z ⟶ X) (h : k ≫ j = l)
    (L : LineBundle X) :
    (Scheme.Modules.pullback k).map ((LineBundle.pullbackForgetIso j).app L).hom ≫
      (((Scheme.Modules.pullbackComp k j).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr h).app L.obj).hom) =
      (((LineBundle.pullbackComp k j).app L ≪≫
        ObjectProperty.isoMk _ (Y := (LineBundle.pullback l).obj L)
          ((Scheme.Modules.pullbackCongr h).app L.obj)).hom).hom ≫
        ((LineBundle.pullbackForgetIso l).app L).hom := by
  change (Scheme.Modules.pullback k).map
      (𝟙 ((Scheme.Modules.pullback j).obj L.obj)) ≫
        (((Scheme.Modules.pullbackComp k j).app L.obj).hom ≫
          ((Scheme.Modules.pullbackCongr h).app L.obj).hom) =
      (((Scheme.Modules.pullbackComp k j).app L.obj).hom ≫
        ((Scheme.Modules.pullbackCongr h).app L.obj).hom) ≫
          𝟙 ((Scheme.Modules.pullback l).obj L.obj)
  rw [(Scheme.Modules.pullback k).map_id ((Scheme.Modules.pullback j).obj L.obj)]
  simp only [Category.id_comp, Category.comp_id]

/-- Forgetting a restriction system agrees with ordinary module restriction,
with identity component maps. -/
def ofLineBundleModuleComparison (L : LineBundle X) :
    FormalModuleSystem.Comparison (ofLineBundle f I L).toModuleSystem
      (FormalModuleSystem.ofModule f I L.obj) where
  component n := (LineBundle.pullbackForgetIso (FormalLineBundle.adicProjection f I n)).app L
  commutes n := restrictionModuleSquare _ _ _ (FormalLineBundle.adicTransition_projection f I n) L

/-- Forgetting a compatible comparison retains every transition square. -/
def Comparison.toModuleComparison {F G : FormalLineBundleSystem f I}
    (e : Comparison F G) :
    FormalModuleSystem.Comparison F.toModuleSystem G.toModuleSystem where
  component n := (LineBundle.forget _).mapIso (e.component n)
  commutes n := congrArg (fun q ↦ q.hom) (e.commutes n)

/-- A compatible module comparison between actual line-bundle systems lifts
through the full subcategory without changing any component map. -/
def Comparison.ofModuleComparison {F G : FormalLineBundleSystem f I}
    (e : FormalModuleSystem.Comparison F.toModuleSystem G.toModuleSystem) :
    Comparison F G where
  component n := ObjectProperty.isoMk _ (e.component n)
  commutes n := by
    apply ObjectProperty.hom_ext
    exact e.commutes n

/-- Module algebraization with local rank one supplies actual line-bundle
algebraization and preserves the original transition squares. -/
lemma isAlgebraization_of_module {F : FormalLineBundleSystem f I}
    {M : X.Modules} (hM : IsLocallyFreeRankOne M)
    (h : FormalModuleSystem.IsAlgebraization M F.toModuleSystem) :
    IsAlgebraization (⟨M, hM⟩ : LineBundle X) F := by
  obtain ⟨e⟩ := h
  exact ⟨Comparison.ofModuleComparison
    ((ofLineBundleModuleComparison (f := f) (I := I) ⟨M, hM⟩).trans e)⟩

end FormalLineBundleSystem

end Langlands.AlgebraicGeometry.Picard
