/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.RegularEpi

/-!
# A coequalizer presentation using covering representables

Source: Stacks Project, Sites, Tag 00WS, lemma-sheaf-coequalizer-representable.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u w

open CategoryTheory.Limits

namespace CategoryTheory

/-- For a covering family of site objects, every set-valued sheaf is covered by a
coproduct of sheafified representables indexed by that family.

Source: Stacks Project, Sites, Tag 00WS, first paragraph (the construction of the
coproduct and its locally surjective map).
(auxiliary; not a blueprint node)

Take the coproduct of sheafified representables indexed by pairs `(V,t)` with
`V ∈ E` and `t ∈ H(V)`. The sheafification adjunction and Yoneda give its map to
`H`. If two arrows out of `H` agree after that map, they agree on every section
at every object of `E`. Naturality gives equality after restriction to the assumed
cover of any object; separatedness of the target sheaf gives equality globally.
This proves the epimorphism assertion directly, including empty coverings. -/
private theorem exists_coveringRepresentable_epi
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (E : Set C)
    (hE : ∀ U : C, ∃ R : Precoverage.ZeroHypercover.{max u w} J U,
      ∀ i : R.I₀, R.X i ∈ E)
    (H : Sheaf J.toGrothendieck (Type (max u w))) :
    ∃ (I : Type (max u w)) (V : I → E)
      (P : Sheaf J.toGrothendieck (Type (max u w)))
      (ι : ∀ j : I, (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
        (uliftYoneda.{w}.obj (V j).val) ⟶ P),
      Nonempty (IsColimit (Cofan.mk P ι)) ∧ ∃ q : P ⟶ H, Epi q := by
  classical
  let I : Type (max u w) := Σ V : E, H.obj.obj (Opposite.op V.val)
  let V : I → E := Sigma.fst
  let F : I → Sheaf J.toGrothendieck (Type (max u w)) := fun j ↦
    (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
      (uliftYoneda.{w}.obj (V j).val)
  let a : ∀ j : I, F j ⟶ H := fun j ↦
    ((sheafificationAdjunction J.toGrothendieck (Type (max u w))).homEquiv _ _).symm
      (uliftYonedaEquiv.{w}.symm j.2)
  let q : ∐ F ⟶ H := Sigma.desc a
  refine ⟨I, V, ∐ F, Sigma.ι F, ⟨coproductIsCoproduct F⟩, q, ?_⟩
  constructor
  intro G f g hfg
  have heq (j : I) : a j ≫ f = a j ≫ g := by
    have hh := congrArg (fun k ↦ Sigma.ι F j ≫ k) hfg
    simpa only [q, ← Category.assoc, Sigma.ι_comp_desc] using hh
  have hsections (W : E) (t : H.obj.obj (Opposite.op W.val)) :
      f.hom.app (Opposite.op W.val) t = g.hom.app (Opposite.op W.val) t := by
    have hh := congrArg
      ((sheafificationAdjunction J.toGrothendieck (Type (max u w))).homEquiv _ _)
      (heq ⟨W, t⟩)
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right] at hh
    simp only [a, Equiv.apply_symm_apply] at hh
    have hh' := congrArg uliftYonedaEquiv.{w} hh
    simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply,
      sheafToPresheaf, ObjectProperty.ι_obj, ObjectProperty.ι_map, V, Sigma.fst] using hh'
  apply (sheafToPresheaf J.toGrothendieck (Type (max u w))).map_injective
  ext U t
  obtain ⟨R, hR⟩ := hE U.unop
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp G.property
    |>.isSheafFor_of_mem_precoverage R.mem₀).isSeparatedFor.ext
  rintro W k ⟨i⟩
  change G.obj.map (R.f i).op (f.hom.app U t) =
    G.obj.map (R.f i).op (g.hom.app U t)
  rw [← f.hom.naturality_apply, ← g.hom.naturality_apply]
  exact hsections ⟨R.X i, hR i⟩ (H.obj.map (R.f i).op t)

/-- Every set sheaf is a coequalizer of two coproducts of sheafified representables from
any covering set of site objects. The two `IsColimit (Cofan.mk ...)` assertions mean that
`P₀` and `P₁` are those coproducts; the final `IsColimit` is the coequalizer universal
property: for each sheaf `K`, composition with `q` bijects maps `H ⟶ K` with maps
`a : P₀ ⟶ K` satisfying `d₀ ≫ a = d₁ ≫ a`.
The `uliftYoneda` is just the representable presheaf with its Hom sets raised to the
universe of the sheaf values, with restriction by precomposition.

Source: Stacks Project, Sites, Tag 00WS, lemma-sheaf-coequalizer-representable.
(auxiliary; not a blueprint node)

Proof:
1. Sheafification and Yoneda identify maps from the sheafification of `h_V` to a sheaf
   `T` with elements of `T(V)`, sending the identity section to the chosen element.
   Use lem-weil-pbc-sheafification-plus-theorem, def-weil-pbc-sheafification and
   lem-galois-yoneda-hom-bijection. No subcanonicity assumption is needed.
2. For `T`, index by pairs `(V,t)` with `V ∈ E` and `t ∈ T(V)`. Sheafify the presheaf
   disjoint union of these representables. Maps out of the disjoint union are precisely
   families of maps out of its summands; the sheafification adjunction gives the same
   universal property after sheafification, proving the coproduct assertion, even for
   an empty index set. The maps of step 1 induce `q_T : P(T) ⟶ T`, taking `(V,t,f)` to
   `T(f)(t)`. Use def-weil-pbc-category-colimit and the sheafification inputs of step 1.
3. Given `s ∈ T(W)`, take a covering of `W` by objects `V_i ∈ E`. Its restriction to
   `V_i` lifts via the identity in the summand `(V_i,T(f_i)(s))`. Thus `q_T` is locally
   surjective and hence epi by lem-weil-pbc-site-sheaf-sets-epi-locally-surjective.
4. Set `P₀ = P(H)` and `q = q_H`. Form the sectionwise kernel pair `G` of `q`, with
   projections `r,s`, using lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Apply the
   same construction to `G`, obtaining `P₁ = P(G)` and an epi `e : P₁ ⟶ G`. Set
   `d₀ = e ≫ r`, `d₁ = e ≫ s`; the kernel-pair equation gives `d₀ ≫ q = d₁ ≫ q`.
5. By lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer, the epi `q` is the
   coequalizer of `r,s`.
6. If `a` equalizes `d₀,d₁`, cancel the epi `e` to see that it equalizes `r,s`.
   Step 5 gives a unique factorization through `q`. Conversely, composition with `q`
   always equalizes `d₀,d₁`. This is exactly the required coequalizer property. -/
theorem exists_coveringRepresentable_coequalizer
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (E : Set C)
    (hE : ∀ U : C, ∃ R : Precoverage.ZeroHypercover.{max u w} J U,
      ∀ i : R.I₀, R.X i ∈ E)
    (H : Sheaf J.toGrothendieck (Type (max u w))) :
    ∃ (I₀ I₁ : Type (max u w)) (V₀ : I₀ → E) (V₁ : I₁ → E)
      (P₀ P₁ : Sheaf J.toGrothendieck (Type (max u w)))
      (ι₀ : ∀ j : I₀, (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
        (uliftYoneda.{w}.obj (V₀ j).val) ⟶ P₀)
      (ι₁ : ∀ j : I₁, (presheafToSheaf J.toGrothendieck (Type (max u w))).obj
        (uliftYoneda.{w}.obj (V₁ j).val) ⟶ P₁),
      Nonempty (IsColimit (Cofan.mk P₀ ι₀)) ∧
      Nonempty (IsColimit (Cofan.mk P₁ ι₁)) ∧
      ∃ (d₀ d₁ : P₁ ⟶ P₀) (q : P₀ ⟶ H) (hq : d₀ ≫ q = d₁ ≫ q),
        Nonempty (IsColimit (Cofork.ofπ q hq)) := by
  obtain ⟨I₀, V₀, P₀, ι₀, hP₀, hq₀⟩ :=
    exists_coveringRepresentable_epi J E hE H
  obtain ⟨q₀, hq₀⟩ := hq₀
  let K := pullback q₀ q₀
  let r : K ⟶ P₀ := pullback.fst q₀ q₀
  let s : K ⟶ P₀ := pullback.snd q₀ q₀
  obtain ⟨I₁, V₁, P₁, ι₁, hP₁, he⟩ :=
    exists_coveringRepresentable_epi J E hE K
  obtain ⟨e, he⟩ := he
  let d₀ : P₁ ⟶ P₀ := e ≫ r
  let d₁ : P₁ ⟶ P₀ := e ≫ s
  let q : P₀ ⟶ H := q₀
  have hq : d₀ ≫ q = d₁ ≫ q := by
    dsimp [d₀, d₁, q, r, s]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have : Epi q := hq₀
  have : IsRegularEpi q := IsRegularEpiCategory.regularEpiOfEpi q
  have hcoeq : Nonempty (IsColimit (Cofork.ofπ q hq)) := by
    have : Epi e := he
    let hc := (IsKernelPair.of_hasPullback q).toCoequalizer'
    have equalizes (t : Cofork d₀ d₁) : r ≫ t.π = s ≫ t.π := by
      apply (cancel_epi e).1
      simpa only [← Category.assoc] using t.condition
    refine ⟨Cofork.IsColimit.mk _
      (fun t ↦ hc.desc (Cofork.ofπ t.π (equalizes t))) ?_ ?_⟩
    · intro t
      exact Cofork.IsColimit.π_desc hc
    · intro t m hm
      apply Cofork.IsColimit.hom_ext hc
      exact hm.trans (Cofork.IsColimit.π_desc hc
        (t := Cofork.ofπ t.π (equalizes t))).symm
  exact ⟨I₀, I₁, V₀, V₁, P₀, P₁, ι₀, ι₁, hP₀, hP₁, d₀, d₁, q, hq, hcoeq⟩

end CategoryTheory
