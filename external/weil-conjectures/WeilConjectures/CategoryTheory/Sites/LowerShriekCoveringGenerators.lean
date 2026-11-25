/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability

/-!
# A left adjoint from corepresentable evaluations on covering generators

Source: Stacks Project, Sites, Tag 09YX, lemma-existence-lower-shriek.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A geometric inverse image has a left adjoint if its evaluations on a covering set
of site objects are corepresentable.

Source: Stacks Project, Sites, Tag 09YX, lemma-existence-lower-shriek.
(auxiliary; not a blueprint node)

Proof:
1. Yoneda and the sheafification adjunction identify evaluation on V with maps from
its sheafified representable h_V#. The assumed natural bijections therefore identify
Hom(G_V,F) with Hom(h_V#,R(F)). Let i_V be the image of the identity of G_V.
Naturality says that the bijection sends a to R(a) composed with i_V.
2. Construct coproducts and coequalizers of sheaves by sheafifying the objectwise
presheaf constructions. Their universal properties follow from sheafification.
3. For a set-indexed family of objects in E, take coproducts of h_V# and of G_V.
The product of the preceding bijections gives the representing bijection for these
coproducts, including the empty coproduct, with unit induced by the i_V.
4. Define the image of any arrow between these coproducts by its unique representing
map. The characterization R(L(a)) composed with i_A = i_B composed with a proves
identity and composition laws and compatibility of all representing bijections.
5. By lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation, every sheaf H
is a coequalizer of two such coproducts, since E covers every site object. Define L_H
as the corresponding coequalizer of their images. This needs no subcanonicity.
6. Maps from L_H to F form the equalizer of the two maps between the representing
Hom sets. Compatibility in step 4 identifies it with Hom(H,R(F)). The resulting
bijection is natural in F by uniqueness of factorization through the coequalizer.
7. Its value on the identity gives i_H. Define L on arrows by the unique equation
R(L(c)) composed with i_H = i_H' composed with c. Uniqueness proves the functor laws
and naturality in H. These bijections yield the claimed adjunction. -/
theorem exists_leftAdjoint_of_covering_corepresentable_evaluations
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (K : Precoverage D) [K.HasIsos] [K.IsStableUnderComposition]
    [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (R : Sheaf J.toGrothendieck (Type (max u v w)) ⥤
      Sheaf K.toGrothendieck (Type (max u v w)))
    (fStar : Sheaf K.toGrothendieck (Type (max u v w)) ⥤
      Sheaf J.toGrothendieck (Type (max u v w)))
    (hadj : R ⊣ fStar) [PreservesFiniteLimits R]
    (E : Set D)
    (hcover : ∀ V : D, ∃ S : Presieve V, S ∈ K V ∧
      ∀ (W : D) (g : W ⟶ V), S g → W ∈ E)
    (hrep : ∀ V ∈ E, ∃ G : Sheaf J.toGrothendieck (Type (max u v w)),
      Nonempty (coyoneda.obj (op G) ≅
        R ⋙ (sheafSections K.toGrothendieck (Type (max u v w))).obj (op V))) :
    ∃ L : Sheaf K.toGrothendieck (Type (max u v w)) ⥤
      Sheaf J.toGrothendieck (Type (max u v w)), Nonempty (L ⊣ R) := by
  have _ := hadj
  have hdefined : ∀ H : Sheaf K.toGrothendieck (Type (max u v w)),
      R.leftAdjointObjIsDefined H :=
    leftAdjointObjIsDefined_of_covering_corepresentable_evaluations
      J K R E hcover hrep
  have htop : R.leftAdjointObjIsDefined = ⊤ := by
    ext H
    simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
    exact hdefined H
  have : R.IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top htop
  exact ⟨R.leftAdjoint, ⟨Adjunction.ofIsRightAdjoint R⟩⟩

end CategoryTheory
