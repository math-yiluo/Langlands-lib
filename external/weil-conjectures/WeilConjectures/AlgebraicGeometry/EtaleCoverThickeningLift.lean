/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Lifting an etale cover and finite-source comparison through a thickening

Source: Stacks Project Tag 04DZ; finite splitting descent, step 1 and the
pullback comparison at the start of step 2.
(blueprint: lem-weil-pbc-etale-cover-thickening-lift)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lift an etale covering of a thickening, together with the comparison maps on
its pullback of an arbitrary source.

Source: Stacks Project Tag 04DZ; steps 1--2 of
`lem-weil-pbc-finite-splitting-closed-immersion-descent`.
(blueprint: lem-weil-pbc-etale-cover-thickening-lift)

Proof: The restriction of r to U is a surjective closed immersion, hence a
universal homeomorphism. Essential surjectivity of its etale base-change functor
lifts each old cover object to an etale object over U, with an isomorphism from
its pullback to the old object. Compose the inverse isomorphism with the first
pullback projection to obtain t. This is a surjective closed immersion.
These lifts cover U: lift a point to U_R, use the old covering, and map its
point through t. Form p on the finite-source pullbacks by the universal
property. Associativity of pullbacks and restriction identifies p with the
base change of t, so p is also a surjective closed immersion. The equation
is the first projection equation of this pullback map. If the old covering
is empty then U_R, and therefore U, is empty and the empty family suffices.
No splitting hypothesis or finiteness hypothesis on f is needed. -/
theorem exists_etale_cover_thickening_lift
    {X Y R : Scheme.{u}} (f : X ⟶ Y)
    (r : R ⟶ Y) [IsClosedImmersion r] [Surjective r] (U : Y.Opens)
    (𝒯 : Cover.{u} etalePrecoverage (r ⁻¹ᵁ U).toScheme) :
    ∃ 𝒮 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
      ∃ (k : 𝒯.I₀) (t : 𝒯.X k ⟶ 𝒮.X i)
        (p : pullback (𝒯.f k) (pullback.snd f r ∣_ (r ⁻¹ᵁ U)) ⟶
          pullback (𝒮.f i) (f ∣_ U)),
        IsClosedImmersion t ∧ Surjective t ∧
        IsClosedImmersion p ∧ Surjective p ∧
        p ≫ pullback.fst (𝒮.f i) (f ∣_ U) =
          pullback.fst (𝒯.f k) (pullback.snd f r ∣_ (r ⁻¹ᵁ U)) ≫ t := by
  classical
  let q := r ∣_ U
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := r.surjective x.1
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change r y ∈ U
      rw [hy]
      exact x.2
    · apply Subtype.ext
      simpa only [q, morphismRestrict_base_coe] using hy
  let T : 𝒯.I₀ → (r ⁻¹ᵁ U).toScheme.Etale := fun k ↦ Etale.mk (𝒯.f k)
  let S : 𝒯.I₀ → U.toScheme.Etale := fun k ↦ q.Etale.objPreimage (T k)
  let e (k : 𝒯.I₀) : pullback (S k).hom q ≅ 𝒯.X k :=
    (Etale.forget _ ⋙ Over.forget _).mapIso (q.Etale.objObjPreimageIso (T k))
  let t (k : 𝒯.I₀) := (e k).inv ≫ pullback.fst (S k).hom q
  have ht (k : 𝒯.I₀) : t k ≫ (S k).hom = 𝒯.f k ≫ q := by
    dsimp [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have he : (e k).inv ≫ pullback.snd (S k).hom q = 𝒯.f k :=
      (q.Etale.objObjPreimageIso (T k)).inv.w
    rw [he]
  have (k : 𝒯.I₀) : IsClosedImmersion (t k) := by dsimp [t]; infer_instance
  have (k : 𝒯.I₀) : Surjective (t k) := by dsimp [t]; infer_instance
  have : JointlySurjective etalePrecoverage :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  have hcover : ∀ x : U.toScheme, ∃ k y, (S k).hom y = x := by
    intro x
    obtain ⟨z, hz⟩ := q.surjective x
    obtain ⟨k, y, hy⟩ := 𝒯.exists_eq z
    refine ⟨k, t k y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply, hy]
    exact hz
  let 𝒮 : Cover.{u} etalePrecoverage U.toScheme :=
    Cover.mkOfCovers 𝒯.I₀ (fun k ↦ (S k).left) (fun k ↦ (S k).hom) hcover
      (fun k ↦ (S k).prop)
  let g := pullback.snd f r ∣_ (r ⁻¹ᵁ U)
  let A := pullback.snd f r ⁻¹ᵁ (r ⁻¹ᵁ U)
  have hA : A = pullback.fst f r ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓
      pullback.snd f r ⁻¹ᵁ (r ⁻¹ᵁ U) := by
    simp only [← Scheme.Hom.comp_preimage, pullback.condition]
    exact (inf_idem _).symm
  let v := (pullback.fst f r).resLE (f ⁻¹ᵁ U) A
    (by rw [hA]; exact inf_le_left)
  have hsq : IsPullback v g (f ∣_ U) q := by
    have hh := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f r)
      (US := U) (UT := r ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl hA
    dsimp only [A, v, g, q] at hh ⊢
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hh
  refine ⟨𝒮, fun i ↦ ?_⟩
  let p : pullback (𝒯.f i) g ⟶ pullback (𝒮.f i) (f ∣_ U) :=
    pullback.lift (pullback.fst (𝒯.f i) g ≫ t i)
      (pullback.snd (𝒯.f i) g ≫ v) (by
        change (pullback.fst (𝒯.f i) g ≫ t i) ≫ (S i).hom = _
        rw [Category.assoc, ht, ← Category.assoc, pullback.condition,
          Category.assoc, ← hsq.w, ← Category.assoc])
  have hp : IsPullback p (pullback.fst (𝒯.f i) g)
      (pullback.fst (𝒮.f i) (f ∣_ U)) (t i) := by
    apply IsPullback.of_right _ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (𝒮.f i) (f ∣_ U)).flip
    rw [pullback.lift_snd]
    change IsPullback (pullback.snd (𝒯.f i) g ≫ v)
      (pullback.fst (𝒯.f i) g) (f ∣_ U) (t i ≫ (S i).hom)
    rw [ht]
    exact ((IsPullback.of_hasPullback (𝒯.f i) g).paste_vert hsq.flip).flip
  have : IsClosedImmersion p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip inferInstance
  have : Surjective p :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip inferInstance
  exact ⟨i, t i, p, inferInstance, inferInstance, inferInstance, inferInstance,
    pullback.lift_fst _ _ _⟩


end AlgebraicGeometry.Scheme
