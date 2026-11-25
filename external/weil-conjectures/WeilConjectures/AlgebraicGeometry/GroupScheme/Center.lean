/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Kernel

/-!
# The centre of a group scheme over an algebraically closed field

Let `G` be a group scheme locally of finite type over an algebraically closed field `k` of
characteristic zero (the setting of the blueprint). Its centre `Z(G)`
(`AlgebraicGeometry.GrpObj.center`) is constructed as the intersection of the centralizers
`C_G(g)` of its rational points `g`: the closed subscheme of `G` cut out by the supremum of their
ideal sheaves. A morphism `x : X ⟶ G` factors through `Z(G)` if and only if it commutes with every
rational point of `G` (`AlgebraicGeometry.GrpObj.exists_comp_centerι_iff`), so `Z(G)` is a closed
subgroup scheme.

This is the centre of `G` because `G(k)` is schematically dense in `G`: `G` is reduced (Cartier's
theorem, `k` of characteristic zero) and its rational points are its closed points, which are dense
(`k` algebraically closed, `G` locally of finite type). Without these hypotheses the intersection
of the centralizers of the rational points can be larger than the centre (for instance over a
finite field, or for a non-reduced `G` in characteristic `p`), so the construction is only made
under them. For `G` connected `Z(G)` is the kernel of the adjoint representation
(`WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.AdjointCenter`).

Over an algebraically closed field, a morphism from a reduced scheme locally of finite type factors
through a closed subscheme as soon as its rational points do
(`AlgebraicGeometry.exists_comp_eq_of_forall_points`): the rational points are the closed points,
and they are dense.

## Main definitions

- `AlgebraicGeometry.GrpObj.center`: the centre `Z(G)` of a group scheme locally of finite type
  over an algebraically closed field of characteristic zero, with its inclusion
  `AlgebraicGeometry.GrpObj.centerι : Z(G) ⟶ G`, a closed immersion and a homomorphism.

## Main statements

- `AlgebraicGeometry.GrpObj.exists_comp_centerι_iff`: the `X`-points of `Z(G)` are the
  `X`-points of `G` commuting with the rational points of `G`.
- `AlgebraicGeometry.exists_comp_eq_of_forall_points`, `AlgebraicGeometry.ext_of_forall_points`:
  over an algebraically closed field, morphisms from reduced schemes locally of finite type are
  detected on rational points.

## Blueprint

- `lemma-stable-subspaces-center`: the centre `Z(G)` of an algebraic group.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-! ### Morphisms from reduced schemes -/

/-- A morphism from a reduced scheme which lands set-theoretically in the image of a closed
immersion factors through it: the base change of the closed immersion is a surjective closed
immersion into a reduced scheme, hence an isomorphism. -/
theorem IsClosedImmersion.exists_comp_eq_of_isReduced {X Y Z : Scheme.{u}} (i : X ⟶ Z)
    [IsClosedImmersion i] (y : Y ⟶ Z) [IsReduced Y] (h : Set.range y ⊆ Set.range i) :
    ∃ l : Y ⟶ X, l ≫ i = y := by
  have : IsClosedImmersion (pullback.snd i y) :=
    MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
  have : Surjective (pullback.snd i y) := by
    refine ⟨fun y₀ ↦ ?_⟩
    obtain ⟨x₀, hx₀⟩ := h ⟨y₀, rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x₀ y₀ hx₀
    exact ⟨z, hz⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i y)
  exact ⟨inv (pullback.snd i y) ≫ pullback.fst i y, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Reduced schemes are detected on rational points.** Over an algebraically closed field, a
morphism `y : Y ⟶ W` from a reduced scheme locally of finite type factors through a closed
immersion `i : Z ⟶ W` as soon as all its rational points do: the preimage of `Z` is closed and
contains all closed points of the Jacobson space `Y`. -/
theorem exists_comp_eq_of_forall_points {Y W Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [IsReduced Y.left] (i : Z ⟶ W) [IsClosedImmersion i.left]
    (y : Y ⟶ W) (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ Y, ∃ q : 𝟙_ _ ⟶ Z, q ≫ i = p ≫ y) :
    ∃ l : Y ⟶ Z, l ≫ i = y := by
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hS : IsClosed (y.left ⁻¹' Set.range i.left) :=
    i.left.isClosedEmbedding.isClosed_range.preimage y.left.continuous
  have hrange : Set.range y.left ⊆ Set.range i.left := by
    rintro _ ⟨x, rfl⟩
    by_contra hx
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hS.isOpen_compl.isLocallyClosed
    obtain ⟨q, hq⟩ := h (GrpObj.sectionOfIsClosed Y c hcl)
    obtain ⟨a⟩ : Nonempty (Spec (.of k)) := inferInstance
    refine hc ⟨q.left a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hq, Over.comp_left, Scheme.Hom.comp_apply,
      GrpObj.sectionOfIsClosed_left_apply]
  obtain ⟨l, hl⟩ := IsClosedImmersion.exists_comp_eq_of_isReduced i.left y.left hrange
  refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
  rw [← Over.w i, reassoc_of% hl, Over.w y]

/-- Over an algebraically closed field, two morphisms from a reduced scheme locally of finite type
to a group scheme are equal if they agree on rational points: their equalizer is a closed
subscheme containing all rational points. -/
theorem ext_of_forall_points {Y W : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    [IsReduced Y.left] [GrpObj W] {f g : Y ⟶ W}
    (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ Y, p ≫ f = p ≫ g) : f = g := by
  have := GrpObj.isClosedImmersion_eqLocusι f g
  obtain ⟨l, hl⟩ := exists_comp_eq_of_forall_points (GrpObj.eqLocusι f g) (𝟙 Y) fun p ↦
    ⟨GrpObj.eqLocusLift f g p (h p), by rw [GrpObj.eqLocusLift_eqLocusι, Category.comp_id]⟩
  rw [← Category.id_comp f, ← Category.id_comp g, ← hl, Category.assoc, Category.assoc,
    GrpObj.eqLocusι_comp_eq]

end AlgClosed

/-- A morphism factors through a closed immersion of schemes over `k` if and only if its kernel
contains the kernel of the closed immersion. -/
theorem exists_comp_eq_iff_ker_le {k : Type u} [Field k] {X Y Z : Over (Spec (.of k))}
    (i : Z ⟶ Y) [IsClosedImmersion i.left] (x : X ⟶ Y) :
    (∃ l : X ⟶ Z, l ≫ i = x) ↔ i.left.ker ≤ x.left.ker := by
  refine ⟨?_, fun h ↦ ⟨Over.homMk (IsClosedImmersion.lift i.left x.left h) ?_,
    Over.OverMorphism.ext (IsClosedImmersion.lift_fac i.left x.left h)⟩⟩
  · rintro ⟨l, rfl⟩
    exact Scheme.Hom.le_ker_comp l.left i.left
  · rw [← Over.w i, IsClosedImmersion.lift_fac_assoc, Over.w x]

/-! ### The centre -/

namespace GrpObj

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- The ideal sheaf of the centre: the supremum of the ideal sheaves of the centralizers of the
rational points. It is only defined for `k` algebraically closed of characteristic zero and `G`
locally of finite type, where it cuts out the centre `Z(G)` (see `center`). -/
noncomputable def centerIdeal [IsAlgClosed k] [CharZero k] [LocallyOfFiniteType G.hom] :
    G.left.IdealSheafData :=
  ⨆ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (centralizerι g).left.ker

variable [IsAlgClosed k] [CharZero k] [LocallyOfFiniteType G.hom]

/-- The centre `Z(G)` of a group scheme `G` locally of finite type over an algebraically closed
field `k` of characteristic zero, a closed subgroup scheme of `G`. It is constructed as the
intersection of the centralizers `C_G(g)` of the rational points `g` of `G`, so its `X`-points are
the `X`-points of `G` commuting with all rational points (`exists_comp_centerι_iff`). This is the
centre of `G` because `G(k)` is schematically dense in `G`: `G` is reduced (Cartier, `k` of
characteristic zero) and its rational points are its closed points, which are dense (`k`
algebraically closed, `G` locally of finite type). Over a general field this intersection can be
strictly larger than the centre, hence the hypotheses. (blueprint: `lemma-stable-subspaces-center`,
`lemma-stable-subspaces-center--2`) -/
noncomputable def center : Over (Spec (.of k)) :=
  Over.mk ((centerIdeal G).subschemeι ≫ G.hom)

/-- The inclusion `Z(G) ⟶ G` of the centre. -/
noncomputable def centerι : center G ⟶ G :=
  Over.homMk (centerIdeal G).subschemeι rfl

instance : IsClosedImmersion (centerι G).left :=
  inferInstanceAs (IsClosedImmersion (centerIdeal G).subschemeι)

instance : Mono (centerι G) :=
  (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono (centerIdeal G).subschemeι))

variable {G}

/-- **The points of the centre.** An `X`-point of `G` factors through the centre `Z(G)` if and only
if it commutes with all rational points of `G`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem exists_comp_centerι_iff {X : Over (Spec (.of k))} (x : X ⟶ G) :
    (∃ l : X ⟶ center G, l ≫ centerι G = x) ↔
      ∀ g : 𝟙_ (Over (Spec (.of k))) ⟶ G, (toUnit X ≫ g) * x = x * (toUnit X ≫ g) := by
  rw [exists_comp_eq_iff_ker_le]
  change (centerIdeal G).subschemeι.ker ≤ _ ↔ _
  rw [Scheme.IdealSheafData.ker_subschemeι, centerIdeal, iSup_le_iff]
  refine forall_congr' fun g ↦ ?_
  rw [← exists_comp_eq_iff_ker_le, exists_comp_centralizerι_iff]

theorem centerι_comp_commute {X : Over (Spec (.of k))} (l : X ⟶ center G)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (toUnit X ≫ g) * (l ≫ centerι G) = (l ≫ centerι G) * (toUnit X ≫ g) :=
  (exists_comp_centerι_iff _).1 ⟨l, rfl⟩ g

variable (G)

theorem exists_one_comp_centerι :
    ∃ e : 𝟙_ (Over (Spec (.of k))) ⟶ center G, e ≫ centerι G = η[G] :=
  (exists_comp_centerι_iff _).2 fun g ↦ by
    rw [show (η[G] : 𝟙_ _ ⟶ G) = 1 by rw [Hom.one_def, toUnit_unit, Category.id_comp], mul_one,
      one_mul]

theorem exists_mul_comp_centerι : ∃ m : center G ⊗ center G ⟶ center G,
    m ≫ centerι G = (centerι G ⊗ₘ centerι G) ≫ μ[G] :=
  (exists_comp_centerι_iff _).2 fun g ↦ by
    have h₁ := centerι_comp_commute (fst (center G) (center G)) g
    have h₂ := centerι_comp_commute (snd (center G) (center G)) g
    rw [← lift_fst_comp_snd_comp, ← Hom.mul_def, ← mul_assoc, h₁, mul_assoc, h₂, mul_assoc]

theorem exists_inv_comp_centerι : ∃ i : center G ⟶ center G,
    i ≫ centerι G = centerι G ≫ ι[G] :=
  (exists_comp_centerι_iff _).2 fun g ↦ by
    have h : Commute (toUnit (center G) ≫ g) (centerι G) := by
      have h' := centerι_comp_commute (𝟙 (center G)) g
      rw [Category.id_comp] at h'
      exact h'
    rw [← Hom.inv_def]
    exact h.inv_right.eq

/-- The centre is a group scheme, through which the group law of `G` factors. -/
noncomputable instance instGrpObjCenter : GrpObj (center G) :=
  GrpObj.ofMono (centerι G) (exists_one_comp_centerι G) (exists_mul_comp_centerι G)
    (exists_inv_comp_centerι G)

/-- The inclusion of the centre is a homomorphism of group schemes. -/
instance isMonHom_centerι : IsMonHom (centerι G) :=
  GrpObj.isMonHom_ofMono _ _ _ _

instance : LocallyOfFiniteType (center G).hom := by
  rw [← Over.w (centerι G)]
  infer_instance

instance [QuasiCompact G.hom] : QuasiCompact (center G).hom := by
  rw [← Over.w (centerι G)]
  infer_instance

end GrpObj

end AlgebraicGeometry
