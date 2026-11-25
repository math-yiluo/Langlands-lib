/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LowerStarOpenStalk

/-!
# Sheaves with finite stalks on a one-point scheme are finite locally constant

Let `Y` be a scheme with exactly one point and `H` a sheaf of modules over a finite ring on the
small étale site of `Y` whose geometric stalks are finite.
Then `H` is finite locally constant. For `Y = Spec k` this is the statement that a discrete
Galois module with finite underlying set is trivialised by a finite separable extension of `k`.

Every étale `Y`-scheme is discrete, so its points are open. Fix a geometric point `ȳ` of `Y`.
The finitely many elements of the stalk `H_ȳ` are germs of sections over a common étale
neighbourhood, which may be shrunk to a single point `V`. Every nonempty étale `W ⟶ V` is
surjective, hence a covering, so the sections of `H` over a one-point `W` inject into every
stalk of `W`; lifting `ȳ` to `W` shows that restriction `H(V) ⟶ H(W)` is surjective for one-point
`W` over `V`, and injective for nonempty `W`. Consequently the restriction of `H` to `V` is the
constant sheaf with value `H(V)`: the map from the constant presheaf is locally injective and
locally surjective. As `V ⟶ Y` is surjective, `H` is locally constant.

## Main statements

- `AlgebraicGeometry.Etale.injective_toPresheafFiber_of_subsingleton`: sections over a one-point
  étale scheme inject into stalks.
- `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_of_subsingleton`: a sheaf of modules with
  finite stalks on a one-point scheme is finite locally constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ]

/-- **Sections over a one-point étale scheme inject into stalks.** For any sheaf `M` of modules
on the small étale site of `X` and an étale `X`-scheme `W` with at most one point, two sections
over `W` with the same germ at a geometric point agree: they agree on a nonempty étale
`W' ⟶ W`, which is surjective, hence a covering. -/
lemma injective_toPresheafFiber_of_subsingleton {X : Scheme.{u}}
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) {W : X.Etale}
    [Subsingleton W.left] (w : (pointSmallEtale s).fiber.obj W) :
    Function.Injective ((pointSmallEtale s).toPresheafFiber W w M.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro a b hab
  obtain ⟨Y, f, y, -, hf⟩ := ((pointSmallEtale s).toPresheafFiber_eq_iff' W w a b).1 hab
  let S : Sieve W :=
    { arrows W' g := M.obj.map g.op a = M.obj.map g.op b
      downward_closed {W W'} g hg g' := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg,
          ConcreteCategory.comp_apply] }
  refine Sheaf.isSeparated M W S ?_ a b fun _ _ h ↦ h
  rw [mem_smallEtaleTopology_iff]
  intro x
  exact ⟨Y, f, hf, y.left (IsLocalRing.closedPoint Ω), Subsingleton.elim _ _⟩

section OnePoint

variable {Y : Scheme.{u}} [Subsingleton Y] (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- An étale scheme over a scheme with at most one point is discrete. -/
lemma discreteTopology_of_etale_of_subsingleton (V : Y.Etale) : DiscreteTopology V.left := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · have : IsEmpty V.left := ⟨fun v ↦ IsEmpty.false (α := Y) (V.hom v)⟩
    infer_instance
  · have : Unique Y := uniqueOfSubsingleton y
    exact discreteTopology_of_etale_of_unique V

omit [Subsingleton Y] in
/-- Restriction from a one-point neighbourhood to one-point étale schemes over it is surjective.
Let `V` be an étale `Y`-scheme with at most one point and `v` a geometric point of `V` at which
every germ of `H` is the germ of a section over `V`. Then for every étale `g : W ⟶ V` with `W`
having at most one point, every section of `H` over `W` is the restriction of a section over
`V`: lift `v` to `W` and compare germs there. -/
lemma exists_map_eq_of_subsingleton {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {s : Spec (.of Ω) ⟶ Y} {V : Y.Etale} [Subsingleton V.left]
    (v : (pointSmallEtale s).fiber.obj V)
    (hv : ∀ p : ToType ((pointSmallEtale s).sheafFiber.obj H),
      ∃ m : ToType (H.obj.obj (op V)), (pointSmallEtale s).toPresheafFiber V v H.obj m = p)
    {W : Y.Etale} [Subsingleton W.left] (g : W ⟶ V) (τ : ToType (H.obj.obj (op W))) :
    ∃ m : ToType (H.obj.obj (op V)), H.obj.map g.op m = τ := by
  rcases isEmpty_or_nonempty W.left with hW | ⟨⟨w₀⟩⟩
  · have := subsingleton_obj_of_isEmpty H (W := W)
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed g.left v.left w₀
    (Subsingleton.elim _ _)
  let w : (pointSmallEtale s).fiber.obj W := CategoryTheory.Over.homMk l (by
    change l ≫ W.hom = s
    have hg : g.left ≫ V.hom = W.hom := CategoryTheory.Over.w ((Etale.forget Y).map g)
    rw [← hg, ← Category.assoc, hl]
    exact CategoryTheory.Over.w v)
  have hw : (pointSmallEtale s).fiber.map g w = v := CategoryTheory.Over.OverMorphism.ext hl
  obtain ⟨m, hm⟩ := hv ((pointSmallEtale s).toPresheafFiber W w H.obj τ)
  refine ⟨m, injective_toPresheafFiber_of_subsingleton H s w ?_⟩
  rw [(pointSmallEtale s).toPresheafFiber_w_apply, hw, hm]

/-- A one-point étale neighbourhood of a geometric point over which all germs of `H` are
realised by sections, when the stalk is finite. -/
lemma exists_subsingleton_surjective_toPresheafFiber {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) [Finite (ToType ((pointSmallEtale s).sheafFiber.obj H))] :
    ∃ (V : Y.Etale) (_ : Subsingleton V.left) (v : (pointSmallEtale s).fiber.obj V),
      ∀ p : ToType ((pointSmallEtale s).sheafFiber.obj H),
        ∃ m : ToType (H.obj.obj (op V)), (pointSmallEtale s).toPresheafFiber V v H.obj m = p := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale s
  have hrep (p : ToType (Φ.sheafFiber.obj H)) : ∃ (E : Φ.fiber.Elements)
      (σ : ToType (H.obj.obj (op E.1))), Φ.toPresheafFiber E.1 E.2 H.obj σ = p := by
    obtain ⟨V, v, σ, hσ⟩ := Φ.toPresheafFiber_jointly_surjective p
    exact ⟨Φ.fiber.elementsMk V v, σ, hσ⟩
  choose E σ hσ using hrep
  classical
  have := Fintype.ofFinite (ToType (Φ.sheafFiber.obj H))
  obtain ⟨E₀, hE₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image E)
  set V₀ := E₀.1
  set v₀ : Φ.fiber.obj V₀ := E₀.2
  let f (p : ToType (Φ.sheafFiber.obj H)) : E₀ ⟶ E p :=
    (hE₀ (Finset.mem_image_of_mem E (Finset.mem_univ p))).some
  have := discreteTopology_of_etale_of_subsingleton V₀
  let O : V₀.left.Opens := ⟨{v₀.left (IsLocalRing.closedPoint Ω)}, isOpen_discrete _⟩
  obtain ⟨v, hv⟩ := exists_pointSmallEtale_fiber_ofOpens s v₀ O (by
    rintro _ ⟨z, rfl⟩
    have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    rw [@Subsingleton.elim (Spec (.of Ω)) this z (IsLocalRing.closedPoint Ω)]
    rfl)
  have : Subsingleton (Etale.ofOpens V₀ O).left := by
    change Subsingleton O
    exact ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  refine ⟨Etale.ofOpens V₀ O, this, v, fun p ↦
    ⟨H.obj.map (Etale.ofOpensι V₀ O ≫ (f p).1).op (σ p), ?_⟩⟩
  have := Φ.toPresheafFiber_w_apply (Etale.ofOpensι V₀ O ≫ (f p).1) v H.obj (σ p)
  rw [CategoryTheory.Functor.map_comp_apply, hv, (f p).2] at this
  exact this.trans (hσ p)

/-- **Sheaves with finite stalks on a one-point scheme are finite locally constant.** Let `Y` be
a scheme with at most one point, for instance the spectrum of a field, and `H` a sheaf of modules
on the small étale site of `Y` whose geometric stalks are finite. Then `H` is
finite locally constant: it is constant on a one-point étale neighbourhood of a geometric point
over which all germs are realised by sections. -/
theorem isFiniteLocallyConstantSheaf_of_subsingleton
    (hH : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (ToType ((pointSmallEtale s).sheafFiber.obj H))) :
    IsFiniteLocallyConstantSheaf H := by
  have hfin : IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) H :=
    ⟨fun Ω _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff _).2
      (have := hH Ω s
      Module.Finite.of_finite)⟩
  suffices IsLocallyConstantSheaf H from {}
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · -- over the empty scheme every sheaf is constant, trivialised by the empty cover
    exact ⟨⟨⟨Cover.mkOfCovers PEmpty (fun _ ↦ Y) (fun _ ↦ 𝟙 Y) (fun y ↦ isEmptyElim y)
      (fun _ ↦ inferInstance), fun i ↦ i.elim⟩⟩⟩
  let s := Y.algClosurePoint y₀
  have := hH _ s
  obtain ⟨V, _, v, hv⟩ := exists_subsingleton_surjective_toPresheafFiber H s
  have : Etale V.hom := V.prop
  -- the restriction `K` of `H` to `V`, a sheaf on the small étale site of `S = V.left`
  set S := V.left
  let K := (localizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).obj H
  let T : S.Etale := Scheme.Etale.mk (𝟙 S)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let N : ModuleCat.{u + 1} Λ := K.obj.obj (op T)
  -- the map from the constant presheaf `N`
  let c : (Functor.const S.Etaleᵒᵖ).obj N ⟶ K.obj :=
    { app T' := K.obj.map (hT.from T'.unop).op
      naturality T₁ T₂ g := by
        change 𝟙 _ ≫ K.obj.map (hT.from T₂.unop).op = K.obj.map (hT.from T₁.unop).op ≫ _
        rw [Category.id_comp, ← Functor.map_comp]
        congr 1
        exact Quiver.Hom.unop_inj (hT.hom_ext _ _) }
  -- the restriction of `V` to itself as an étale `Y`-scheme maps back to `V`
  let V' : Y.Etale := (MorphismProperty.Over.map ⊤ V.prop).obj T
  let g' : V' ⟶ V := MorphismProperty.Over.homMk (𝟙 S) (by simp [V', T])
  have : Subsingleton V'.left := inferInstanceAs (Subsingleton S)
  -- `K(T) ⟶ K(T')` is surjective for one-point `T'`
  have hsurj (T' : S.Etale) [Subsingleton T'.left] (τ : ToType (K.obj.obj (op T'))) :
      ∃ n : N, c.app (op T') n = τ := by
    let W : Y.Etale := (MorphismProperty.Over.map ⊤ V.prop).obj T'
    have : Subsingleton W.left := inferInstanceAs (Subsingleton T'.left)
    let g : W ⟶ V := MorphismProperty.Over.homMk T'.hom rfl
    obtain ⟨m, hm⟩ := exists_map_eq_of_subsingleton H v hv g τ
    have hcomp : ((MorphismProperty.Over.map ⊤ V.prop).map (hT.from T') ≫ g' : W ⟶ V) = g :=
      MorphismProperty.Over.Hom.ext
        (CategoryTheory.Over.w ((Scheme.Etale.forget S).map (hT.from T')))
    refine ⟨H.obj.map g'.op m, ?_⟩
    change H.obj.map ((MorphismProperty.Over.map ⊤ V.prop).map (hT.from T')).op
      (H.obj.map g'.op m) = τ
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hcomp]
    exact hm
  -- `K(T) ⟶ K(T')` is injective for nonempty `T'`
  have hinj (T' : S.Etale) [Nonempty T'.left] (n n' : N) (h : c.app (op T') n = c.app (op T') n') :
      n = n' := by
    let R : Sieve T :=
      { arrows T'' g := K.obj.map g.op n = K.obj.map g.op n'
        downward_closed {W W'} g hg g' := by
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg,
            ConcreteCategory.comp_apply] }
    refine Sheaf.isSeparated K T R ?_ n n' fun _ _ h ↦ h
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨t⟩ := ‹Nonempty T'.left›
    exact ⟨T', hT.from T', h, t, @Subsingleton.elim S ‹_› _ _⟩
  have hW : (Scheme.smallEtaleTopology S).W c := by
    rw [GrothendieckTopology.W_iff_isLocallyBijective]
    have hdisc := discreteTopology_of_etale_of_subsingleton (Y := Y)
    refine ⟨⟨fun {T₀} n n' h ↦ ?_⟩, ⟨fun {T'} τ ↦ ?_⟩⟩
    · rw [mem_smallEtaleTopology_iff]
      intro t
      have : Nonempty T₀.unop.left := ⟨t⟩
      refine ⟨T₀.unop, 𝟙 _, ?_, ⟨t, rfl⟩⟩
      obtain rfl := hinj T₀.unop n n' h
      rfl
    · rw [mem_smallEtaleTopology_iff]
      intro t
      have : DiscreteTopology T'.left :=
        hdisc ((MorphismProperty.Over.map ⊤ V.prop).obj T')
      let O : T'.left.Opens := ⟨{t}, isOpen_discrete _⟩
      have : Subsingleton (Etale.ofOpens T' O).left := by
        change Subsingleton O
        exact ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
      obtain ⟨n, hn⟩ := hsurj (Etale.ofOpens T' O) (K.obj.map (Etale.ofOpensι T' O).op τ)
      refine ⟨Etale.ofOpens T' O, Etale.ofOpensι T' O, ⟨n, hn⟩, ⟨⟨t, rfl⟩, rfl⟩⟩
  have : IsIso ((presheafToSheaf (Scheme.smallEtaleTopology S) (ModuleCat.{u + 1} Λ)).map c) :=
    ((Scheme.smallEtaleTopology S).W_iff c).1 hW
  have hK : K.IsConstant S.smallEtaleTopology :=
    Sheaf.isConstant_of_iso _ ((sheafificationIso K) ≪≫
      (asIso ((presheafToSheaf (Scheme.smallEtaleTopology S) (ModuleCat.{u + 1} Λ)).map c)).symm)
  have hK' : ((V.hom)^*[ModuleCat.{u + 1} Λ].obj H).IsConstant S.smallEtaleTopology :=
    Sheaf.isConstant_congr _
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) V.hom V.prop).app H).symm
  obtain ⟨v₀⟩ : Nonempty V.left := ⟨v.left (IsLocalRing.closedPoint _)⟩
  exact ⟨⟨⟨Cover.mkOfCovers PUnit (fun _ ↦ V.left) (fun _ ↦ V.hom)
    (fun y ↦ ⟨⟨⟩, v₀, Subsingleton.elim _ _⟩) (fun _ ↦ V.prop),
    fun _ ↦ (isConstant_over_iff_upperStar _ _ _).2 hK'⟩⟩⟩

end OnePoint

end Etale

end AlgebraicGeometry
