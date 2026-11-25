/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Naturality of one tensor-Hom evaluation component

Source: Stacks Project, sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-tensor-hom-uncurry-component-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

-- Reassociate before applying a componentwise projection equation.
private theorem comp_projection {C : Type*} [Category* C]
    {A A' H H' B B' : C} (a : A' ⟶ A) (f : A ⟶ H) (g : H ⟶ H')
    (π : H ⟶ B) (π' : H' ⟶ B') (k : B ⟶ B') (h : g ≫ π' = π ≫ k) :
    (a ≫ f ≫ g) ≫ π' = a ≫ (f ≫ π) ≫ k := by
  simp only [Category.assoc, h]

set_option backward.isDefEq.respectTransparency true in
private theorem uncurry_natural {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A A' T T' N N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (a : T' ⟶ T) (b : A' ⟶ A) (c : N ⟶ N')
    (f : T ⟶ SheafOfModules.homObj (R := R) A N) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (β_ T' A').hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A' T' N').symm
      (a ≫ f ≫ SheafOfModules.homObjMap (R := R) b c) =
    (a ⊗ₘ b) ≫ ((β_ T A).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) A T N).symm f) ≫ c := by
  have := SheafOfModules.isMonoidal_W R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_assoc]
  apply congrArg ((β_ T' A').hom ≫ ·)
  apply (SheafOfModules.tensorHomEquiv (R := R) A' T' N').injective
  simp only [Equiv.apply_symm_apply, tensorHom_def, Category.assoc,
    SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R),
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R),
    SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R)]
  simp only [SheafOfModules.homObjMap_comp_homObjMap (R := R), Category.comp_id]

-- Naturality for any Hom complex, before choosing the scheme's resolution.
set_option backward.isDefEq.respectTransparency true in
private theorem hom_uncurry_natural {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (P P' L L' N N' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a : P' ⟶ P) (b : L' ⟶ L) (c : N ⟶ N')
    (φ : P ⟶ homComplex (R := R) L N) (p q n : ℤ) (h : q + p = n) :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
    (β_ (P'.X p) (L'.X q)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) (L'.X q) (P'.X p) (N'.X n)).symm
        ((a ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := R))).map
          (X := (op L, N)) (Y := (op L', N')) (b.op, c)).f p ≫ π L' N' p q n h) =
      (a.f p ⊗ₘ b.f q) ≫ ((β_ (P.X p) (L.X q)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := R) (L.X q) (P.X p) (N.X n)).symm
          (φ.f p ≫ π L N p q n h)) ≫ c.f n := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))
  have hm := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := R))).2.2 L L' N N' b c p q n h
  change ((Functor.uncurry.obj (homComplexFunctor (R := R))).map
    (X := (op L, N)) (Y := (op L', N')) (b.op, c)).f p ≫ π L' N' p q n h =
      π L N p q n h ≫ SheafOfModules.homObjMap (R := R) (b.f q) (c.f n) at hm
  have hp := comp_projection (a.f p) (φ.f p) _
    (π L N p q n h) (π L' N' p q n h) _ hm
  have hu := uncurry_natural R (L.X q) (L'.X q) (P.X p) (P'.X p)
    (N.X n) (N'.X n) (a.f p) (b.f q) (c.f n) (φ.f p ≫ π L N p q n h)
  have he := congrArg (fun t : P'.X p ⟶
      SheafOfModules.homObj (R := R) (L'.X q) (N'.X n) ↦
    (β_ (P'.X p) (L'.X q)).hom ≫
      (SheafOfModules.tensorHomEquiv (R := R) (L'.X q) (P'.X p) (N'.X n)).symm t) hp
  exact he.trans hu

/-- Evaluation on a single degree pair commutes with simultaneous chain maps.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, functoriality of the
Hom-total-tensor comparison; cohomology.tex, Tag 08DJ, componentwise evaluation.
(blueprint: lem-pc-tensor-hom-uncurry-component-naturality).

Proof: Let π be the chosen product projections of homComplex_exists and set
I = schemeHomKInjectiveResolution X. Its map specification gives
Hom(b,I(c)).f p followed by π(L',I(M'),p,q,n) equal to
π(L,I(M),p,q,n) followed by homObjMap(b.f q,I(c).f n).
Precompose this equation by a.f p followed by φ.f p. Apply the inverse
sheaf tensor-Hom equivalence. Naturality in its free variable precomposes
uncurrying by L'^q tensor a.f p; naturality in its Hom source precomposes
by b.f q tensor P^p; naturality in its target postcomposes by I(c).f n.
The two whiskerings combine to b.f q tensor a.f p. Naturality of the
braiding moves that tensor map past the symmetry and changes its order
to a.f p tensor b.f q. The definition of schemeTensorHomUncurryComponent
then identifies both sides with the displayed equality. No coproduct,
differential, localization, or flatness argument enters this calculation.
Identity maps give the original component; a zero map in any variable
gives zero on both sides by the additivity of internal Hom and tensor.
The argument uses only q+p=n, and applies in every integer degree. -/
theorem schemeTensorHomUncurryComponent_natural (X : Scheme.{u})
    (P P' L L' M M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : P' ⟶ P) (b : L' ⟶ L) (c : M ⟶ M')
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    schemeTensorHomUncurryComponent X P' L' M'
        (a ≫ φ ≫ (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
          (X := (op L, (schemeHomKInjectiveResolution X).obj M))
          (Y := (op L', (schemeHomKInjectiveResolution X).obj M'))
          (b.op, (schemeHomKInjectiveResolution X).map c)) p q n h =
      (a.f p ⊗ₘ b.f q) ≫ schemeTensorHomUncurryComponent X P L M φ p q n h ≫
        ((schemeHomKInjectiveResolution X).map c).f n := by
  exact hom_uncurry_natural X.sheaf P P' L L'
    ((schemeHomKInjectiveResolution X).obj M) ((schemeHomKInjectiveResolution X).obj M')
    a b ((schemeHomKInjectiveResolution X).map c) φ p q n h

end AlgebraicGeometry
