import Langlands.CategoryTheory.Renard.IsomorphismPrincipleStatements

/-!
# Proof of Renard A.III.3

The Hom equivalences determine actual object isomorphisms by Yoneda. Naturality
in the source of the functors makes these isomorphisms into a natural isomorphism.
-/

open CategoryTheory

universe vC vM uC uM

namespace Langlands.Renard.IsomorphismPrinciple

private def isoOfHomEquiv {M : Type uM} [Category.{vM} M] (X Y : M)
    (e : ∀ Z : M, (Z ⟶ X) ≃ (Z ⟶ Y))
    (hn : ∀ (Z Z' : M) (g : Z' ⟶ Z) (f : Z ⟶ X),
      e Z' (g ≫ f) = g ≫ e Z f) : X ≅ Y :=
  Yoneda.ext X Y
    (fun {Z} => e Z)
    (fun {Z} => (e Z).symm)
    (fun {Z} f => (e Z).symm_apply_apply f)
    (fun {Z} f => (e Z).apply_symm_apply f)
    (fun {Z Z'} g f => hn Z Z' g f)

/-- Renard A.III.3: natural represented Hom equivalences give an object isomorphism. -/
theorem objectStatement : ObjectStatement.{vM, uM} := by
  intro M _ X Y e hn
  exact ⟨isoOfHomEquiv X Y e hn⟩

/-- Renard A.III.3: naturality in both Hom variables gives a functor isomorphism. -/
theorem functorStatement : FunctorStatement.{vC, vM, uC, uM} := by
  intro C _ M _ F G e hZ hX
  refine ⟨NatIso.ofComponents
    (fun X => isoOfHomEquiv (F.obj X) (G.obj X) (e X) (hZ X)) ?_⟩
  intro X X' a
  change F.map a ≫ e X' (F.obj X') (𝟙 (F.obj X')) =
    e X (F.obj X) (𝟙 (F.obj X)) ≫ G.map a
  calc
    F.map a ≫ e X' (F.obj X') (𝟙 (F.obj X')) =
        e X' (F.obj X) (F.map a) := by
      simpa only [Category.comp_id] using
        (hZ X' (F.obj X') (F.obj X) (F.map a) (𝟙 (F.obj X'))).symm
    _ = e X (F.obj X) (𝟙 (F.obj X)) ≫ G.map a := by
      simpa only [Category.id_comp] using
        hX X X' a (F.obj X) (𝟙 (F.obj X))

/-- The exact closed aggregate of both Renard A.III.3 isomorphism principles. -/
theorem isomorphismPrincipleStatements :
    IsomorphismPrincipleStatements.{vC, vM, uC, uM} :=
  ⟨objectStatement.{vM, uM}, functorStatement.{vC, vM, uC, uM}⟩

end Langlands.Renard.IsomorphismPrinciple
