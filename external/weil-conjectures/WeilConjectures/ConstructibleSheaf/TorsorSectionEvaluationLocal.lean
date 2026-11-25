/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.TorsorGraphEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorNormalizedGraphEvaluation

/-!
# Evaluation on etale objects admitting a torsor section

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-section-evaluation-local)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Normalized evaluation is bijective on an etale object with a map to the torsor.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-section-evaluation-local)

Proof:
Write Y for the total space of c. Since Y is connected and nonempty, the supplied
constant trivialization identifies F(Y) with A and identifies the restriction of F
on Y with the locally constant function sheaf with value F(Y). The map f gives a
section of W times_V Y over W. The torsor isomorphism splits this product into
translates of that section, indexed by P. Evaluation on the chosen section therefore
identifies equivariant locally constant functions with locally constant functions
on W with value F(Y): extend such a function on each translate using the P action.
These formulas are inverse, including on the empty W. Under the constant
trivialization, a section of F(W) is locally a restriction of a section x of F(Y).
Naturality of alpha along f and diagonal normalization show that its evaluation
on the chosen section is exactly x on each such open. Equality of locally constant
functions is local, so alpha is the inverse of the evaluation identification.
No descent along W times_V Y to an arbitrary W is asserted here; f is essential.
-/
theorem Scheme.GaloisCover.sectionEvaluation_bijective_of_section
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A))
    (α : F.obj ⟶ c.sectionRepresentationPresheaf ℓ F)
    (hα : c.SectionEvaluationNormalized ℓ F α) (W : V.Etaleᵒᵖ)
    (f : W.unop ⟶ c.sectionObject) :
    Function.Bijective (α.app W) := by
  have hgraph := c.graphEvaluation_injective ℓ (c.sectionRepresentation ℓ F) W.unop f
  let β (T : V.Etaleᵒᵖ) : F.obj.obj T →ₗ[ULift.{u + 1} (ZMod ℓ)]
      LocallyConstant (c.sectionSpace T.unop) (F.obj.obj (Opposite.op c.sectionObject)) :=
    { toFun s := (α.app T s).val
      map_add' a b := by
        change (α.app T (a + b)).val = _
        rw [map_add]
        rfl
      map_smul' r a := by
        change (α.app T (r • a)).val = _
        rw [map_smul]
        rfl }
  have hβ (T T' : V.Etaleᵒᵖ) (g : T ⟶ T') (s : F.obj.obj T)
      (x : c.sectionSpace T'.unop) :
      β T' (F.obj.map g s) x = β T s (c.sectionRestriction g.unop x) := by
    have hn := ConcreteCategory.congr_hom (α.naturality g) s
    exact congrArg (fun t : c.equivariantSections ℓ (c.sectionRepresentation ℓ F) T'.unop ↦
      t.val x) hn
  have hcomp := c.ordinaryGraphEvaluation_bijective ℓ P F A h β hβ hα W f
  exact hcomp.of_comp_left hgraph

end AlgebraicGeometry
