/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.SectionCohomologyUntwistedComparisons
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus

/-! # Tensor-unit comparisons for raw section cohomology

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-section-cohomology-unit-comparisons).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem unit_nonvanishing (Y : Scheme.{u}) (b : Γ(Y, ⊤)) :
    nonvanishingLocus (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b) = Y.basicOpen b := by
  set_option backward.isDefEq.respectTransparency.types false in
    ext x
    rw [mem_nonvanishingLocus_iff_generatesAt]
    exact generatesAt_iff_mem_basicOpen (isFreeGenerator_one ⊤)
      (by
        rw [presheaf_map_id_apply]
        exact unitSectionsEquiv_eq_smul_one b) trivial

private noncomputable def unitPowIso (Y : Scheme.{u}) :
    ∀ n : ℕ, (𝟙_ Y.Modules).tensorPow n ≅ 𝟙_ Y.Modules
  | 0 => Iso.refl _
  | n + 1 => (Iso.refl _ ⊗ᵢ unitPowIso Y n) ≪≫ λ_ _

private noncomputable def unitTwistIso {Y : Scheme.{u}} (G : Y.Modules) (n : ℕ) :
    G ⊗ (𝟙_ Y.Modules).tensorPow n ≅ G :=
  (Iso.refl G ⊗ᵢ unitPowIso Y n) ≪≫ ρ_ G

private theorem unitPowIso_section (Y : Scheme.{u}) (b : Γ(Y, ⊤)) (n : ℕ)
    (V : Y.Opens) :
    (unitPowIso Y n).hom.app V
      (tensorPowSectionOne (homOfGlobalSection (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b))
        n V) = unitSectionsEquiv V ((Y.presheaf.map (homOfLE le_top).op).hom b ^ n) := by
  set_option backward.isDefEq.respectTransparency.types false in
    induction n with
    | zero => simp [unitPowIso, tensorPowSectionOne_zero]
    | succ n ih =>
      rw [tensorPowSectionOne_succ]
      dsimp only [tensorPow]
      simp only [unitPowIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Hom.comp_app,
        ConcreteCategory.comp_apply, tensorHom_app_tmulSection, Hom.id_app]
      rw [ih]
      simp only [ConcreteCategory.id_apply]
      change (λ_ (𝟙_ Y.Modules)).hom.app V
        (tmulSection ((homOfGlobalSection (𝟙_ Y.Modules)
          (unitSectionsEquiv ⊤ b)).app V (1 : Γ(Y, V)))
          (unitSectionsEquiv V ((Y.presheaf.map (homOfLE le_top).op).hom b ^ n))) = _
      rw [homOfGlobalSection_app_one, presheaf_map_unitSectionsEquiv,
        leftUnitor_hom_app_tmulSection]
      change ((Y.presheaf.map (homOfLE le_top).op).hom b) *
        ((Y.presheaf.map (homOfLE le_top).op).hom b) ^ n =
          ((Y.presheaf.map (homOfLE le_top).op).hom b) ^ (n + 1)
      exact (pow_succ' _ _).symm

private theorem unitTwistIso_section {Y : Scheme.{u}} (G : Y.Modules)
    (b : Γ(Y, ⊤)) (n : ℕ) :
    (ρ_ G).inv ≫ G ◁ tensorPowSection
        (homOfGlobalSection (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ b)) n ≫
          (unitTwistIso G n).hom =
      (ρ_ G).inv ≫ G ◁ homOfGlobalSection (𝟙_ Y.Modules)
        (unitSectionsEquiv ⊤ (b ^ n)) ≫ (ρ_ G).hom := by
  set_option backward.isDefEq.respectTransparency.types false in
    apply hom_ext
    intro V
    ext z
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    rw [rightUnitor_inv_app, whiskerLeft_app_tmulSection]
    simp only [unitTwistIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Hom.comp_app,
      ConcreteCategory.comp_apply, tensorHom_app_tmulSection, Hom.id_app]
    rw [unitPowIso_section, rightUnitor_hom_app_tmulSection]
    rw [whiskerLeft_app_tmulSection]
    change _ • z = (ρ_ G).hom.app V (tmulSection z
      ((homOfGlobalSection (𝟙_ Y.Modules) (unitSectionsEquiv ⊤ (b ^ n))).app V (1 : Γ(Y, V))))
    rw [homOfGlobalSection_app_one, presheaf_map_unitSectionsEquiv,
      rightUnitor_hom_app_tmulSection, map_pow]

/-- Evaluation of a pushforward resolution agrees with derived sections on the inverse
image open, compatibly with restriction and multiplication by a tensor power of a function.

Source: Stacks Project, Tag 01E4, Lemma 20.7.3, and Tag 01E1, restriction of injectives.
(blueprint: lem-pc-section-cohomology-unit-comparisons).

Proof: Put Y = f inverse W and G = F restricted to Y. Restrict I termwise to Y.
Restriction is exact and preserves injectives, so this is a resolution of G. Evaluation
of pushforward identifies its sections on Y with the section complex K(W). Restricting
again to D(b) identifies sections with K(D(a)), because pullback commutes with the
nonvanishing locus. Compute the derived section functors using these resolutions;
exact evaluation of presheaves and forgetting scalars commute with homology. This gives
the additive comparison
e. The tensor powers of the tensor unit have canonical isomorphisms to the unit,
constructed recursively with the unitors. Tensoring these with G gives isomorphisms
G tensor unit^n to G. Apply derived sections on Y and on U and then the preceding
comparisons to obtain c and d. Naturality of the derived section comparison for
restriction gives the second equation. Degreewise, the map induced by tensoring with
s^n is multiplication by b^n, under the unitors. The section comparisons are semilinear
for pullback of functions, and hence on homology multiplication by b^n corresponds
to the a^n action restricted along the structure-sheaf restriction. This is the first
equation. No compactness, separation, affineness, or quasi-coherence is needed: this
is only an identification of resolutions and their scalar and restriction maps.
For a=0 the open U and the target complex are empty; the same comparisons still apply.
For n=0 the scalar is 1 and the tensor-power comparison is the right unitor. -/
theorem sectionCohomology_unit_comparisons {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F)
    (q : ℕ) (W : T.Opens) (a : Γ(T, W)) :
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let L := 𝟙_ Y.Modules
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    ∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus L s →
      ∃ e : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G ≃+
          P.obj (op (T.basicOpen a)),
      ∃ c : ∀ n : ℕ,
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
          (G ⊗ L.tensorPow n : Y.Modules) ≃+ P.obj (op W),
      ∃ d : ∀ n : ℕ,
        (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj
          (G ⊗ L.tensorPow n : Y.Modules) ≃+ P.obj (op (T.basicOpen a)),
      (∀ (n : ℕ) (z : (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G),
        d n ((RingedSpace.openModuleCohomology Y.toRingedSpace q U).map
          (((ρ_ G).inv ≫ G ◁ tensorPowSection (homOfGlobalSection L s) n) :
            G ⟶ (G ⊗ L.tensorPow n : Y.Modules)) z) = a ^ n • e z) ∧
      (∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj
          (G ⊗ L.tensorPow n : Y.Modules)),
        d n ((RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
          (homOfLE (le_top : U ≤ ⊤))).app (G ⊗ L.tensorPow n : Y.Modules) ξ) =
            (P.map (homOfLE (T.basicOpen_le a)).op).hom (c n ξ)) := by
  set_option backward.isDefEq.respectTransparency.types false in
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let L := 𝟙_ Y.Modules
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(L, ⊤) := unitSectionsEquiv ⊤ b
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    dsimp only
    intro U hU
    have hUb : U = Y.basicOpen b := by
      apply SetLike.coe_injective
      exact hU.trans (unit_nonvanishing Y b)
    have hImage : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ T.basicOpen a := by
      rw [hUb]
      change (f ⁻¹ᵁ W).ι ''ᵁ (f ⁻¹ᵁ W).toScheme.basicOpen
        ((f ⁻¹ᵁ W).topIso.inv ((f.app W).hom a)) = _
      rw [Scheme.Opens.ι_image_basicOpen_topIso_inv, ← Scheme.preimage_basicOpen]
    obtain ⟨e, t, hscalar, hres⟩ :=
      sectionCohomology_untwisted_comparisons f F I q W (T.basicOpen a)
        (T.basicOpen_le a) U hImage
    let HT := RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤
    let HU := RingedSpace.openModuleCohomology Y.toRingedSpace q U
    let c (n : ℕ) := ((HT.mapIso (unitTwistIso G n)).addCommGroupIsoToAddEquiv).trans t
    let d (n : ℕ) := ((HU.mapIso (unitTwistIso G n)).addCommGroupIsoToAddEquiv).trans e
    refine ⟨e, c, d, ?_, ?_⟩
    · intro n z
      change e (HU.map (unitTwistIso G n).hom
        (HU.map ((ρ_ G).inv ≫ G ◁ tensorPowSection (homOfGlobalSection L s) n) z)) = _
      rw [← ConcreteCategory.comp_apply, ← HU.map_comp]
      rw [Category.assoc, unitTwistIso_section]
      simpa only [map_pow] using hscalar (a ^ n) z
    · intro n ξ
      let α := RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
        (homOfLE (le_top : U ≤ ⊤))
      change e (HU.map (unitTwistIso G n).hom (α.app _ ξ)) =
        (P.map (homOfLE (T.basicOpen_le a)).op).hom
          (t (HT.map (unitTwistIso G n).hom ξ))
      rw [← ConcreteCategory.comp_apply, ← α.naturality, ConcreteCategory.comp_apply]
      exact hres _

end AlgebraicGeometry.Scheme.Modules
