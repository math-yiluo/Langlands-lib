/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImagePullbackCoordinates

/-! # Finite-free basis columns of the direct-image coefficient comparison

Source: Stacks Project, Tags 0B56 and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

private theorem mate_columns_private
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ C} {R : C ⥤ A} {L' : B ⥤ D} {R' : D ⥤ B}
    {E : A ⥤ B} {U : B ⥤ A} {E' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (b : L' ⋙ U' ≅ U ⋙ L) (θ : E ⋙ L' ≅ L ⋙ E')
    (δ : R' ⋙ U ≅ U' ⋙ R)
    (hδ : ∀ (X : B) (Y : D) (t : L'.obj X ⟶ Y),
      adj.homEquiv _ _ (b.inv.app X ≫ U'.map t) =
        U.map (adj'.homEquiv X Y t) ≫ δ.hom.app Y)
    {I : Type*}
    (cW : ∀ (X : A) (_ : I), X ⟶ U.obj (E.obj X))
    (cZ : ∀ (X : C) (_ : I), X ⟶ U'.obj (E'.obj X))
    (hcZ : ∀ {X Y : C} (f : X ⟶ Y) (i : I),
      cZ X i ≫ U'.map (E'.map f) = f ≫ cZ Y i)
    (hpull : ∀ X i, L.map (cW X i) ≫ b.inv.app (E.obj X) ≫
      U'.map (θ.hom.app X) = cZ (L.obj X) i)
    (M : C) (i : I) :
    cW (R.obj M) i ≫
      U.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ.hom)).app M) ≫
      δ.hom.app (E'.obj M) = R.map (cZ M i) := by
  have ht' : adj'.homEquiv _ _
      (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M)) =
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ.hom)).app M := by
    apply (adj'.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ θ.hom) M).symm
  rw [← ht']
  have hs := hδ
    (E.obj (R.obj M)) (E'.obj ((𝟭 C).obj M))
    (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M))
  change cW (R.obj M) i ≫
    (U.map (adj'.homEquiv (E.obj (R.obj M)) (E'.obj ((𝟭 C).obj M))
      (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M))) ≫
      δ.hom.app (E'.obj ((𝟭 C).obj M))) = _
  rw [← hs]
  rw [← adj.homEquiv_naturality_left]
  have hp := congrArg (fun f ↦ f ≫ U'.map (E'.map (adj.counit.app M)))
    (hpull (R.obj M) i)
  have hcomp :
      L.map (cW (R.obj M) i) ≫ b.inv.app (E.obj (R.obj M)) ≫
        U'.map (θ.hom.app (R.obj M) ≫ E'.map (adj.counit.app M)) =
      adj.counit.app M ≫ cZ M i := by
    calc
      _ = cZ (L.obj (R.obj M)) i ≫ U'.map (E'.map (adj.counit.app M)) := by
        simpa only [Functor.map_comp, Category.assoc] using hp
      _ = _ := hcZ (adj.counit.app M) i
  rw [hcomp]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    adj.right_triangle_components, Category.id_comp]

/-- In finite-free coordinates the restricted canonical mate has the direct images
of the basis inclusions as its columns. This does not assert invertibility.
Source: Stacks Project, sites-cohomology.tex, Tags 0B56 and 0944.
(blueprint: lem-sp-finite-free-direct-image-columns).

Proof: choose the given basis of S_W over R_W and pull it back using the specified
coefficient identifications to obtain the basis on Z. On module sheaves the maps
(x_i) to sum e_i tensor x_i and e_i tensor x to the i-th coordinate are inverse
by the tensor balancing relations. They are natural in the module, respect
restrictions, and yield the isomorphisms after passing to complexes and localizing:
finite sums preserve quasi-isomorphisms, so these compute the universal scalar
extensions on every unbounded complex. This includes rank zero.
The balancing map in the definition is the conjugate of the actual restriction
comparison. The tensor-unit normalization of the scalar adjunctions and the
identity-on-sections normalization of the restriction comparison identify it with
the balanced pullback map. Apply the scalar-restriction adjunct identity of
proEtaleRingSheafChangeAdjunction to the defining transpose of comparison.
On the i-th basis summand that transpose is the R-counit followed by the i-th
basis inclusion on Z: both send a local pure tensor to its counit image tensor e_i.
The naturality of the R-adjunction identifies its adjunct with Rq of that inclusion.
These are equations of actual module-derived maps before forgetting any further
scalars; no faithfulness on derived Hom sets is used. -/
theorem finiteFreeDirectImage_columns {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d))))
    (M : DerivedCategory (proEtaleRingModules Z R.source)) :
    ∃ (eW : (⨁ fun _ : Fin d ↦
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M) ≅
        (proEtaleRingRestrictScalars a.target).mapDerivedCategory.obj
          ((sW.presentation a.target).derived.obj
            ((proEtaleRingDerivedDirectImage q R.target R.source R.identification).obj M)))
      (eZ : (⨁ fun _ : Fin d ↦ M) ≅
        (proEtaleRingRestrictScalars a.source).mapDerivedCategory.obj
          ((sZ.presentation a.source).derived.obj M)),
      ∀ i : Fin d,
        biproduct.ι _ i ≫ eW.hom ≫
          (proEtaleRingRestrictScalars a.target).mapDerivedCategory.map
            ((comparison sW sZ a).app M) ≫
          (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
            a.target a.source R.identification S.identification a.comm).hom.app
              ((sZ.presentation a.source).derived.obj M) =
        (proEtaleRingDerivedDirectImage q R.target R.source R.identification).map
          (biproduct.ι _ i ≫ eZ.hom) := by
  obtain ⟨eW, eZ, β, hsource, hβ, hnat, hpull⟩ :=
    finiteFreeDirectImage_pullbackCoordinates q sW sZ R S a d hfree
  have heq : β = balancing sW sZ a :=
    finiteFreeDirectImage_balancingComputed sW sZ a β hsource hβ
  subst β
  refine ⟨eW _, eZ M, fun i ↦ ?_⟩
  simpa only [comparison, Category.assoc] using mate_columns_private
    (proEtaleRingDerivedAdjunction q R.target R.source R.identification)
    (proEtaleRingDerivedAdjunction q S.target S.source S.identification)
    (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)
    (balancing sW sZ a)
    (proEtaleRingRestrictionDerivedDirectImage q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)
    (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).2.2
    (fun X i ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eW X).hom)
    (fun X i ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eZ X).hom)
    (fun {X Y} f i ↦ by simpa only [Category.assoc] using hnat f i) hpull M i

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage

namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
/-- Public export of the private `mate_columns_private` (used by `import all` importers;
linter.privateModule). -/
alias mate_columns := mate_columns_private

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
