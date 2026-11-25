/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.PrincipalQuotientMultiplicationImage

/-! # Principal thickening sections as degree-zero cohomology of the quotient

## References

* Stacks Project, Tags 01IH and 01QP (quotient structure sheaves), and Tag 01DZ, Section 20.2
  (degree-zero cohomology)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem closed_structure_quotient {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let a := MonoidalCategory.whiskerRight j.ker.toModulesι O ≫
      (MonoidalCategory.leftUnitor O).hom
    ∃ e : cokernel (image.ι a) ≅
        (Modules.pushforward j).obj (SheafOfModules.unit Z.ringCatSheaf),
      cokernel.π (image.ι a) ≫ e.hom =
        SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
  classical
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let a := MonoidalCategory.whiskerRight j.ker.toModulesι O ≫
      (MonoidalCategory.leftUnitor O).hom
  let adj₀ := Classical.choice (Modules.nonempty_tensorPullbackAdjunction j)
  let adj₁ := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
  let c := adj₀.leftAdjointUniq adj₁
  have hε := Modules.tensorPullbackObjUnitToUnit_isIso j
  have : IsIso (Modules.tensorPullbackObjUnitToUnit j) := hε.1
  let ε := (c.app O).hom ≫ Modules.tensorPullbackObjUnitToUnit j
  obtain ⟨η, hη, _⟩ := Modules.closedImmersion_unit_quotient j
  have he : cokernel.π (image.ι a) ≫ η O = adj₀.unit.app O := (hη O).2.2.1
  have : IsIso (η O) := (hη O).2.2.2
  refine ⟨asIso (η O) ≪≫ (Modules.pushforward j).mapIso (asIso ε), ?_⟩
  change cokernel.π (image.ι a) ≫ η O ≫ (Modules.pushforward j).map ε = _
  rw [← Category.assoc, he]
  dsimp only [ε]
  rw [Functor.map_comp, ← Category.assoc]
  rw [show adj₀.unit.app O ≫ (Modules.pushforward j).map (c.app O).hom =
    adj₁.unit.app O from Adjunction.unit_leftAdjointUniq_hom_app adj₀ adj₁ O]
  exact hε.2

set_option backward.isDefEq.respectTransparency false in
private theorem thickening_multiplication_image
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) (n : ℕ) :
    let j := FiniteEtale.Adic.openThickeningMap (Ideal.Quotient.mk (Ideal.span {g})) W n
    let O : W.toScheme.Modules := SheafOfModules.unit W.toScheme.ringCatSheaf
    let p := Modules.smulHom O ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))
    let a := MonoidalCategory.whiskerRight j.ker.toModulesι O ≫
      (MonoidalCategory.leftUnitor O).hom
    ∃ d : image p ≅ image a, d.hom ≫ image.ι a = image.ι p := by
  -- Keep the quotient-ring instances inside q when rewriting the defining ideal.
  let q (I : Ideal R) := pullback.fst W.ι (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk I)))
  let O : W.toScheme.Modules := SheafOfModules.unit W.toScheme.ringCatSheaf
  let a (I : Ideal R) := MonoidalCategory.whiskerRight (q I).ker.toModulesι O ≫
    (MonoidalCategory.leftUnitor O).hom
  change ∃ d : image _ ≅ image (a (FiniteEtale.Adic.ideal
    (Ideal.Quotient.mk (Ideal.span {g})) n)), d.hom ≫ image.ι _ = image.ι _
  have hI : FiniteEtale.Adic.ideal (Ideal.Quotient.mk (Ideal.span {g})) n =
      Ideal.span {g ^ (n + 1)} := by
    rw [FiniteEtale.Adic.ideal, Ideal.mk_ker, Ideal.span_singleton_pow]
  rw [hI]
  have h := Modules.principal_quotient_multiplication_image R W.ι
    (SheafOfModules.unit W.toScheme.ringCatSheaf) (g ^ (n + 1))
  rw [map_pow] at h
  exact h

private theorem structure_pushforward_map {X Z Z' : Scheme.{u}}
    (j : Z ⟶ X) (j' : Z' ⟶ X) (h : Z' ⟶ Z) (hh : h ≫ j = j') :
    ∃ t : (Modules.pushforward j).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
        (Modules.pushforward j').obj (SheafOfModules.unit Z'.ringCatSheaf),
      SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom ≫ t =
        SheafOfModules.unitToPushforwardObjUnit j'.toRingCatSheafHom ∧
      ∀ a : Γ(Z, ⊤), t.app ⊤ a = h.appTop a := by
  subst j'
  refine ⟨(Modules.pushforward j).map
    (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
      (Modules.pushforwardComp h j).hom.app (SheafOfModules.unit Z'.ringCatSheaf), ?_, ?_⟩
  · ext U
    rfl
  · intro a
    rfl

private theorem zero_sections_naturality {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (x : Modules.H M 0) :
    Modules.H.zeroLinearEquiv N (Modules.H.map φ 0 x) =
      φ.app ⊤ (Modules.H.zeroLinearEquiv M x) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x).symm

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of the principal ideal inclusion has the sections of the thickening,
naturally for maps over the ambient open. -/
theorem principal_thickening_cokernel_sections
    (R : Type u) [CommRing R] (g : R) (W : (Spec (.of R)).Opens) :
    let p := fun n : ℕ ↦ Modules.smulHom (SheafOfModules.unit W.toScheme.ringCatSheaf)
      ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))
    let i := fun n : ℕ ↦ image.ι (p n)
    ∃ e : ∀ n : ℕ, Modules.H (cokernel (i n)) 0 ≃+
        Γ(FiniteEtale.Adic.openThickening
          (Ideal.Quotient.mk (Ideal.span {g})) W n, ⊤),
      (∀ n (a : Γ(W.toScheme, ⊤)),
        e n (Modules.H.map (cokernel.π (i n)) 0
          ((Modules.H.zeroLinearEquiv _).symm a)) =
        (FiniteEtale.Adic.openThickeningMap
          (Ideal.Quotient.mk (Ideal.span {g})) W n).appTop a) ∧
      (∀ (n m : ℕ) (κ : image (p m) ⟶ image (p n))
        (h : FiniteEtale.Adic.openThickening
            (Ideal.Quotient.mk (Ideal.span {g})) W n ⟶
          FiniteEtale.Adic.openThickening (Ideal.Quotient.mk (Ideal.span {g})) W m)
        (hk : κ ≫ i n = i m),
        h ≫ FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W m =
          FiniteEtale.Adic.openThickeningMap
            (Ideal.Quotient.mk (Ideal.span {g})) W n →
        ∀ x, e n (Modules.H.map
          (cokernel.map (i m) (i n) κ (𝟙 _) (by simpa using hk.symm)) 0 x) =
          h.appTop (e m x)) := by
  classical
  let O : W.toScheme.Modules := SheafOfModules.unit W.toScheme.ringCatSheaf
  let p := fun n : ℕ ↦ Modules.smulHom O
    ((((ΓSpecIso (.of R)).inv ≫ W.ι.appTop) g) ^ (n + 1))
  let i := fun n : ℕ ↦ image.ι (p n)
  let j := fun n : ℕ ↦ FiniteEtale.Adic.openThickeningMap
    (Ideal.Quotient.mk (Ideal.span {g})) W n
  have hclosed (n : ℕ) : IsClosedImmersion (j n) := by
    have : IsClosedImmersion (FiniteEtale.Adic.baseMap
        (Ideal.Quotient.mk (Ideal.span {g})) n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    dsimp only [j, FiniteEtale.Adic.openThickeningMap]
    infer_instance
  have hex (n : ℕ) :
      ∃ E : cokernel (i n) ≅
          (Modules.pushforward (j n)).obj
            (SheafOfModules.unit (FiniteEtale.Adic.openThickening
              (Ideal.Quotient.mk (Ideal.span {g})) W n).ringCatSheaf),
        cokernel.π (i n) ≫ E.hom =
          SheafOfModules.unitToPushforwardObjUnit (j n).toRingCatSheafHom := by
    have := hclosed n
    obtain ⟨d, hd⟩ := thickening_multiplication_image R g W n
    obtain ⟨b, hb⟩ := closed_structure_quotient (j n)
    let c := cokernel.mapIso (i n) _ d (Iso.refl O)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hd.symm)
    refine ⟨c ≪≫ b, ?_⟩
    change cokernel.π (i n) ≫ c.hom ≫ b.hom = _
    rw [← Category.assoc]
    simpa only [c, cokernel.mapIso_hom, cokernel.π_desc, Iso.refl_hom,
      Category.id_comp] using hb
  choose E hE using hex
  let e := fun n : ℕ ↦ (Modules.H.zeroLinearEquiv (cokernel (i n))).toAddEquiv.trans
    (Modules.appLinearEquivOfIso (E n) ⊤).toAddEquiv
  refine ⟨e, ?_, ?_⟩
  · intro n a
    change (E n).hom.app ⊤
      (Modules.H.zeroLinearEquiv _ (Modules.H.map (cokernel.π (i n)) 0
        ((Modules.H.zeroLinearEquiv O).symm a))) = _
    rw [zero_sections_naturality, LinearEquiv.apply_symm_apply]
    exact congrArg (fun f ↦ f.app ⊤ a) (hE n)
  · intro n m κ h hk hh x
    let q := cokernel.map (i m) (i n) κ (𝟙 O)
      (by simpa only [Category.comp_id] using hk.symm)
    obtain ⟨t, ht, htTop⟩ := structure_pushforward_map (j m) (j n) h hh
    have hsquare : q ≫ (E n).hom = (E m).hom ≫ t := by
      apply (cancel_epi (cokernel.π (i m))).mp
      rw [← Category.assoc, cokernel.π_desc]
      rw [Category.id_comp, ← Category.assoc, hE m, ht, hE n]
    change (E n).hom.app ⊤ (Modules.H.zeroLinearEquiv _ (Modules.H.map q 0 x)) =
      h.appTop ((E m).hom.app ⊤ (Modules.H.zeroLinearEquiv _ x))
    rw [zero_sections_naturality]
    have hs := congrArg (fun f ↦ f.app ⊤ (Modules.H.zeroLinearEquiv _ x)) hsquare
    exact hs.trans (htTop _)

end AlgebraicGeometry.Scheme
