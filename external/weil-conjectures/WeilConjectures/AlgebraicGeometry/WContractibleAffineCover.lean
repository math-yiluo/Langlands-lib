/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WContractible

/-! # Coverings by w-contractible affines

Source: the Weil conjectures blueprint, `chap-The-pro-etale-site`,
`sk-thm-pe-weakly-contractible-basis/det-pe-wcb-cover.md`
(blueprint: theorem-enough-affine-weakly-contractible-objects--1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every small pro-etale object has a pro-etale covering by spectra of w-contractible
rings, with each covering map factoring through an affine open by a faithfully flat
ind-etale ring map. The isomorphism `e` identifies the covering object with `Spec D`;
`j` identifies `Spec B` with an affine open of the target.

Source: the Weil conjectures blueprint, `det-pe-wcb-cover.md`
(blueprint: theorem-enough-affine-weakly-contractible-objects--1).

Proof:
1. Index by all affine opens `Spec B` of `U.left`. For each `B`, the strict cover
   `theorem-existence-contractible-covers--1` gives a faithfully flat ind-etale algebra `C` that is
   w-local with strictly henselian maximal local rings. Thus it is w-strictly local
   by `definition-w-local-w-strictly-local`. Apply `example-locally-constant-functions-w-local--1`
   to a Stonean cover of its component space, obtaining a faithfully flat ind-Zariski map
   `C` to a w-contractible ring `D`. By `lemma-stability`, the composite
   `B` to `D` is ind-etale. It is faithfully flat: exactness after tensoring with `D`
   reflects to exactness after tensoring with `C`, and then to exactness over `B`, by
   `def-weil-pbc-faithfully-flat-ring-map`.
2. The map `Spec D` to `Spec B` is weakly etale by
   `proposition-etale-implications`. The affine open immersion into `U.left` is
   etale by `lem-weil-pbc-open-immersion-etale`, hence weakly etale by the same
   comparison. The map from `U.left` to `X` is weakly etale by
   `definition-small-pro-etale-site--1`. Composition preserves weak etaleness by
   `lem-weil-pbc-weakly-etale-composition-base-change`, so these give objects and
   morphisms of `X.ProEt` with the displayed factorization.
3. For any affine open `V` of `U.left`, choose its own index. Its corresponding
   `Spec D` factors through `V`, so its pullback to `V` is itself and is affine.
   Faithful flatness makes its image all of `V` by
   `lem-weil-pbc-faithfully-flat-surjective-spectrum`. This single affine open
   satisfies the finite refinement condition of `definition-small-pro-etale-site--1`.
   Consequently the family belongs to `precoverage X U`.
-/
theorem exists_wContractible_affine_cover (X : Scheme.{u}) (U : X.ProEt) :
    ∃ (I : Type u) (W : I → X.ProEt) (f : ∀ i : I, W i ⟶ U),
      Presieve.ofArrows W f ∈ precoverage X U ∧
      ∀ i : I, ∃ (D : CommRingCat.{u}), IsWContractibleRing D ∧
        ∃ (e : Spec D ≅ (W i).left) (B : CommRingCat.{u})
          (φ : B ⟶ D) (j : Spec B ⟶ U.left),
          IsOpenImmersion j ∧ φ.hom.FaithfullyFlat ∧ φ.hom.IndEtale ∧
          e.hom ≫ (f i).left = Spec.map φ ≫ j := by
  classical
  let A := U.left.affineOpenCover
  choose D hD hAlg hind hff hw using fun j : A.I₀ ↦ exists_isWContractibleRing (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let (j : A.I₀) : Algebra (A.X j) (D j) := hAlg j
  let φ (j : A.I₀) : A.X j ⟶ CommRingCat.of (D j) :=
    CommRingCat.ofHom (algebraMap (A.X j) (D j))
  have hwp (j : A.I₀) : WeaklyEtale (Spec.map (φ j)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).mpr (hind j))
  have hsp (j : A.I₀) : Surjective (Spec.map (φ j)) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (hff j))).2
  let C := A.openCover.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (A.X j)) :=
    .singleton (Spec.map (φ j))
      (Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (hwp j))
  let B := C.bind E
  have hB (i : B.I₀) : WeaklyEtale (B.f i) :=
    Scheme.Cover.map_prop (Scheme.Cover.forgetQc B) i
  let W (i : B.I₀) : X.ProEt := ProEt.mk (B.f i ≫ U.hom)
  let f (i : B.I₀) : W i ⟶ U := MorphismProperty.Over.homMk (B.f i)
  refine ⟨B.I₀, W, f, ?_, ?_⟩
  · change (Presieve.ofArrows W f).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage U.left
    rw [Presieve.map_ofArrows]
    exact B.mem₀
  · rintro ⟨j, i⟩
    refine ⟨CommRingCat.of (D j), hw j, Iso.refl _, A.X j, φ j, A.f j,
      inferInstance, ?_, ?_, ?_⟩
    · exact RingHom.faithfullyFlat_algebraMap_iff.mpr (hff j)
    · exact (RingHom.IndEtale.algebraMap_iff _ _).mpr (hind j)
    · exact Category.id_comp _

end AlgebraicGeometry.Scheme.ProEt
