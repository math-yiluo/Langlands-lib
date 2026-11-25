/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GmConstantSheaf
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative

/-!
# The pullback of the sheaf of roots of unity

For `g : X ⟶ Y` with `n` invertible on `Y`, the comparison map `g^* μₙ ⟶ μₙ`
(`AlgebraicGeometry.Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf`) is an isomorphism
(`AlgebraicGeometry.Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit`), and
these maps are compatible with composition
(`AlgebraicGeometry.Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp`).

When `Y` carries an `n`-th root of unity `ζ` whose powers have invertible differences, both
`μₙ` on `Y` and on `X` are trivialized by `ζ`, and the comparison map corresponds to the
identification `g^* (ℤ/n) ≅ ℤ/n` of constant sheaves. In general this holds after the étale
cover of `Y` adjoining such a root of unity (`AlgebraicGeometry.primitiveRootsCover`), which
suffices.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} (n : ℕ)

/-- The comparison maps `g^* μₙ ⟶ μₙ` are compatible with composition. -/
lemma upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Etale.upperStarComp _ a b).hom.app (Z.rootsOfUnitySheaf n) ≫
        (Etale.upperStar _ a).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n b) ≫
          upperStarRootsOfUnitySheafToRootsOfUnitySheaf n a =
      upperStarRootsOfUnitySheafToRootsOfUnitySheaf n (a ≫ b) := by
  refine equalizer.hom_ext ?_
  have hn := (Etale.upperStarComp AddCommGrpCat.{u + 1} a b).hom.naturality
    (kernel.ι (n • 𝟙 Z.gmSheaf))
  simp only [Category.assoc, upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι,
    ← Functor.map_comp_assoc]
  rw [Functor.map_comp_assoc, ← upperStarGmSheafToGmSheaf_comp a b, reassoc_of% hn]
  rfl

/-- The homomorphism `ℤ/n ⟶ 𝔾ₘ(X)`, `a ↦ ζ ^ a`, to the sections of `𝔾ₘ` over the terminal
object. -/
noncomputable def zmodToGmSections (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) ⟶ gmSections X :=
  (X.zmodToGmPresheaf n ζ hζ).app (op (⊤_ X.Etale))

lemma constantSheafAdj_homEquiv_constantZModToGmSheaf (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv _ _
      (X.constantZModToGmSheaf n ζ hζ) = zmodToGmSections n ζ hζ := by
  rw [Adjunction.homEquiv_unit]
  simp only [constantSheafAdj, Adjunction.comp_unit_app, sheafificationAdjunction_unit_app]
  rw [Category.assoc]
  change _ ≫ ((toSheafify _ _ ≫ (X.constantZModToGmSheaf n ζ hζ).hom).app (op _)) = _
  rw [toSheafify_constantZModToGmSheaf, constantPresheafAdj_unit_app]
  exact Category.id_comp _

lemma zmodToGmSections_natCast (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (k : ℕ) :
    (zmodToGmSections n ζ hζ).hom (ULift.up (k : ZMod n)) = gmSection (ζ ^ k) := by
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  refine (X.zmodToGmPresheaf_app_natCast n ζ hζ _ k).trans ?_
  simp [gmSection]

lemma zmodToGmSections_comp_gmSectionsPullback [NeZero n] (g : X ⟶ Y) (ζ : Γ(Y, ⊤)ˣ)
    (hζ : ζ ^ n = 1) :
    zmodToGmSections n ζ hζ ≫ gmSectionsPullback g =
      zmodToGmSections n (Units.map g.appTop.hom.toMonoidHom ζ)
        (by rw [← map_pow, hζ, map_one]) := by
  ext ⟨a⟩
  rw [← ZMod.natCast_zmod_val a]
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [zmodToGmSections_natCast, zmodToGmSections_natCast, gmSectionsPullback_gmSection, map_pow]

/-- The comparison `g^* μₙ ⟶ μₙ` corresponds to the identification `g^* (ℤ/n) ≅ ℤ/n` of constant
sheaves through the maps `θ_ζ : ℤ/n ⟶ μₙ`, `a ↦ ζ ^ a`. -/
lemma upperStar_map_constantZModToRootsOfUnitySheaf_comp [NeZero n] (g : X ⟶ Y)
    (ζ : Γ(Y, ⊤)ˣ) (hζ : ζ ^ n = 1) :
    (Etale.upperStar _ g).map (Y.constantZModToRootsOfUnitySheaf n ζ hζ) ≫
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g =
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app _ ≫
        X.constantZModToRootsOfUnitySheaf n (Units.map g.appTop.hom.toMonoidHom ζ)
          (by rw [← map_pow, hζ, map_one]) := by
  refine equalizer.hom_ext ?_
  simp only [Category.assoc, upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]
  rw [← Functor.map_comp_assoc]
  erw [kernel.lift_ι, kernel.lift_ι]
  rw [← ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv _ _).symm_apply_apply (Y.constantZModToGmSheaf n ζ hζ),
    ← ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv _ _).symm_apply_apply (X.constantZModToGmSheaf n _ _),
    constantSheafAdj_homEquiv_constantZModToGmSheaf,
    constantSheafAdj_homEquiv_constantZModToGmSheaf,
    upperStar_map_constantSheafAdj_homEquiv_symm_comp, zmodToGmSections_comp_gmSectionsPullback]

/-- If `Y` carries an `n`-th root of unity whose powers have invertible differences, the
comparison `g^* μₙ ⟶ μₙ` is an isomorphism. -/
lemma isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit_sub [NeZero n] (g : X ⟶ Y)
    (ζ : Γ(Y, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(Y, ⊤)) ^ i - (ζ : Γ(Y, ⊤)) ^ j)) :
    IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) := by
  have := Y.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub n ζ hζ hζ'
  have := X.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub n
    (Units.map g.appTop.hom.toMonoidHom ζ) (by rw [← map_pow, hζ, map_one])
    (fun i hi j hj hij ↦ by simpa [← map_pow, ← map_sub] using (hζ' i hi j hj hij).map g.appTop.hom)
  have h := upperStar_map_constantZModToRootsOfUnitySheaf_comp n g ζ hζ
  rw [← cancel_epi (inv ((Etale.upperStar _ g).map (Y.constantZModToRootsOfUnitySheaf n ζ hζ))),
    IsIso.inv_hom_id_assoc] at h
  rw [h]
  infer_instance

lemma isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp_of_eq {X' Y' : Scheme.{u}}
    (qX : X' ⟶ X) (g : X ⟶ Y) (g' : X' ⟶ Y') (qY : Y' ⟶ Y) (e : qX ≫ g = g' ≫ qY)
    (h₁ : IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n qY))
    (h₂ : IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g')) :
    IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n (qX ≫ g)) := by
  rw [e, ← upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp]
  infer_instance

/-- A morphism of étale sheaves which becomes an isomorphism after pullback along a surjective
étale morphism is an isomorphism. -/
lemma isIso_of_isIso_upperStar_map (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X' : Scheme.{u}}
    (q : X' ⟶ X) [Etale q] (hq : Function.Surjective q.base)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G) (h : IsIso ((Etale.upperStar A q).map φ)) :
    IsIso φ := by
  refine Etale.isIso_of_isIso_localizationRestriction A _ (fun _ : Unit ↦ q)
    (by rw [Set.iUnion_const]; exact Set.range_eq_univ.2 hq) fun _ ↦ ?_
  let r := Etale.upperStarIsoLocalizationRestriction A q inferInstance
  have h' := r.hom.naturality φ
  rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h'
  rw [← h']
  infer_instance

lemma isIso_upperStar_map_upperStarRootsOfUnitySheafToRootsOfUnitySheaf {X' : Scheme.{u}}
    (q : X' ⟶ X) [Etale q] (g : X ⟶ Y)
    (h : IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n (q ≫ g))) :
    IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} q).map
      (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g)) := by
  rw [← upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp, ← Category.assoc] at h
  have := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf n q
  have := IsIso.of_isIso_comp_right (((Etale.upperStarComp _ q g (q ≫ g) rfl).hom.app
    (Y.rootsOfUnitySheaf n) ≫ (Etale.upperStar _ q).map
      (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g)))
    (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n q)
  exact IsIso.of_isIso_comp_left ((Etale.upperStarComp _ q g (q ≫ g) rfl).hom.app _) _

/-- **The pullback of `μₙ` is `μₙ`.** For `g : X ⟶ Y` with `n` invertible on `Y`, the comparison
`g^* μₙ ⟶ μₙ` is an isomorphism. After the étale cover of `Y` adjoining a primitive `n`-th root of
unity this is
`AlgebraicGeometry.Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit_sub`,
and the comparison maps are compatible with composition. -/
theorem isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit [NeZero n] (g : X ⟶ Y)
    (hn : IsUnit (n : Γ(Y, ⊤))) :
    IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) := by
  have : Etale (primitiveRootsCover Γ(Y, ⊤) n) :=
    etale_primitiveRootsCover _ _ (NeZero.ne n) hn
  have : Surjective (primitiveRootsCover Γ(Y, ⊤) n) :=
    ⟨surjective_primitiveRootsCover Γ(Y, ⊤) n hn⟩
  let qY := pullback.fst Y.toSpecΓ (primitiveRootsCover Γ(Y, ⊤) n)
  let ζ : Γ(pullback Y.toSpecΓ (primitiveRootsCover Γ(Y, ⊤) n), ⊤)ˣ :=
    ((PrimitiveRootsAlgebra.isUnit_zeta Γ(Y, ⊤) n (Nat.pos_of_ne_zero (NeZero.ne n))).map
      ((Scheme.ΓSpecIso (.of (PrimitiveRootsAlgebra Γ(Y, ⊤) n))).inv ≫
        (pullback.snd Y.toSpecΓ (primitiveRootsCover Γ(Y, ⊤) n)).appTop).hom).unit
  have hζ : ζ ^ n = 1 := by
    ext
    simp only [ζ, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one, ← map_pow,
      PrimitiveRootsAlgebra.zeta_pow, map_one]
  have hζ' : ∀ i < n, ∀ j < n, i ≠ j → IsUnit ((ζ : Γ(pullback Y.toSpecΓ
      (primitiveRootsCover Γ(Y, ⊤) n), ⊤)) ^ i - (ζ : Γ(pullback Y.toSpecΓ
      (primitiveRootsCover Γ(Y, ⊤) n), ⊤)) ^ j) := by
    intro i hi j hj hij
    simpa only [ζ, IsUnit.unit_spec, ← map_pow, ← map_sub] using
      (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow Γ(Y, ⊤) n hi hj hij).map
        ((Scheme.ΓSpecIso (.of (PrimitiveRootsAlgebra Γ(Y, ⊤) n))).inv ≫
          (pullback.snd Y.toSpecΓ (primitiveRootsCover Γ(Y, ⊤) n)).appTop).hom
  have hcomp := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp_of_eq n
    (pullback.fst g qY) g (pullback.snd g qY) qY pullback.condition
    (isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf n qY)
    (isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit_sub n _ ζ hζ hζ')
  exact isIso_of_isIso_upperStar_map _ (pullback.fst g qY) (pullback.fst g qY).surjective _
    (isIso_upperStar_map_upperStarRootsOfUnitySheafToRootsOfUnitySheaf n _ g hcomp)

end AlgebraicGeometry.Scheme
