/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
import WeilConjectures.ConstructibleSheaf.TorsorOrdinaryEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorOrdinaryEvaluationEquivariant

/-!
# Evaluation of torsor-trivialized sheaves in their sections over the cover

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-section-evaluation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- There is a normalized evaluation morphism into equivariant locally constant functions.
This asserts existence and naturality of the evaluation map, not its bijectivity.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-section-evaluation)

Proof:
Write Y for the total space. Restrict F to the small etale site of Y. The inverse-image
comparison for an etale morphism identifies this restriction with c*F. The given constant
trivialization, and connectedness and nonemptiness of Y, identify F(Y) with the constant
value A: global locally constant functions on Y are constant. Under this identification,
the constant section associated to x in F(Y) is the restriction of x. Thus the restriction
of F to Y is canonically the locally constant function sheaf with value F(Y), independently
of the initial trivialization. For W over V, restrict a section s of F(W) to W times_V Y,
regarded as an etale Y-scheme. Read it in this function sheaf to obtain a locally constant
function with values in F(Y). Under a deck transformation g of the second factor, this
function changes by restriction along g inverse on F(Y). This follows by restricting a
constant section x along g: its new constant value is F(g inverse)(x). Hence the function
is equivariant for sectionRepresentation. The assignments are linear, with scalars
transported through ULift.ringEquiv, and restriction of functions commutes with restriction
of s, giving a natural transformation. At W=Y, pullback along the diagonal is the original
section x, so evaluation there has the stated normalization. The construction also works
for the zero module and the identity torsor. -/
theorem Scheme.GaloisCover.exists_sectionEvaluation
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    (h : Nonempty ((c.π)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj F ≅
      (constantSheaf c.P.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj A)) :
    ∃ α : F.obj ⟶ c.sectionRepresentationPresheaf ℓ F,
      c.SectionEvaluationNormalized ℓ F α := by
  obtain ⟨β, hβ, hΔ⟩ := c.exists_ordinarySectionEvaluation ℓ P F A h
  have heq := c.ordinarySectionEvaluation_equivariant ℓ P F A h β hβ hΔ
  let α : F.obj ⟶ c.sectionRepresentationPresheaf ℓ F :=
    { app := fun W ↦ ModuleCat.ofHom
        { toFun := fun s ↦ ⟨β W s, heq W s⟩
          map_add' := by intro s t; apply Subtype.ext; exact map_add (β W) s t
          map_smul' := by intro r s; apply Subtype.ext; exact map_smul (β W) r s }
      naturality := by
        intro W W' f
        ext s
        apply Subtype.ext
        apply LocallyConstant.ext
        intro x
        exact hβ W W' f s x }
  exact ⟨α, hΔ⟩

end AlgebraicGeometry
