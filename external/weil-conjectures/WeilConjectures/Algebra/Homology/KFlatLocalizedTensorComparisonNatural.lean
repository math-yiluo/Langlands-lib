/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.BaseTensorCohomologyFunctor
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # The coefficient comparison on K-flat complexes

Source: Stacks Project, Tags 06Y6, 0BYJ, and 0DJ7.
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat
private theorem exists_coefficientExtensionNaturalMap
    (A E C : Type u) [CommRing A] [CommRing E] [CommRing C]
    (f : A →+* E) (g : E →+* C) :
    ∃ β : (extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ) ⟶
      (extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex (.up ℤ) ⋙
        (restrictScalars.{u} g).mapHomologicalComplex (.up ℤ),
      ∀ (P : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) (x : E) (p : P.X j),
        (β.app P).f j (x ⊗ₜ[A, f] p) = g x ⊗ₜ[A, g.comp f] p := by
  let L := extendScalars.{u, u, u} f
  let M := extendScalars.{u, u, u} (g.comp f)
  let G := restrictScalars.{u} g
  let adj := extendRestrictScalarsAdj.{u, u, u} f
  let adj' := extendRestrictScalarsAdj.{u, u, u} (g.comp f)
  let α : 𝟭 (ModuleCat.{u} A) ⟶ M ⋙ G ⋙ restrictScalars f :=
    adj'.unit ≫ Functor.whiskerLeft M (restrictScalarsComp f g).hom
  let β : L ⟶ M ⋙ G :=
    { app := fun X ↦ (adj.homEquiv _ _).symm (α.app X)
      naturality := by
        intro X Y a
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa only [Equiv.apply_symm_apply, Functor.id_map, Functor.comp_map]
          using α.naturality a }
  refine ⟨β.mapHomologicalComplex (.up ℤ), ?_⟩
  intro P j x p
  let _ : Module A (G.obj (M.obj (P.X j))) := Module.compHom _ f
  change ((adj.homEquiv _ _).symm (α.app (P.X j))) (x ⊗ₜ[A, f] p) = _
  change (ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f
    (α.app (P.X j))) (x ⊗ₜ[A, f] p) = _
  erw [ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change g x • ((1 : C) ⊗ₜ[A, g.comp f] p) = _
  rw [ExtendScalars.smul_tmul, mul_one]

private theorem kFlat_of_acyclic_tensor
    {A : Type u} [CommRing A] (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro V hV
  obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor V Q (curriedTensor _))).2 (hQ V hV)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

omit [HasDerivedCategory (ModuleCat.{u} A)] in
/-- The localized coefficient comparison is natural on K-flat complexes.

Source: Stacks Project, Tag 06Y6 (derived change of rings), Tag 0BYJ
(associativity), and perfect.tex, equation-bc before Tag 0DJ7.

Proof: obtain the ordinary tensor-algebra-valued cohomology functor and its
natural comparison from exists_baseTensorCohomologyFunctor. Transpose the
A-to-C extension unit through the A-to-E adjunction, where E=A-tensor-R-B, to
construct the natural ordinary coefficient chain map. Take homology, compose
with the exact restriction homology isomorphism and the ordinary comparison,
then transpose through the E-to-C adjunction. This gives the natural comparison
from the E-to-C extension of the source functor to homology of C-extension.
The chain coefficient map equals each model's ordinaryToLocalized map on
pure tensors, hence everywhere. Adjunction naturality, the ordinary comparison
component equation and localized_eq identify its model component with
localizedComparison.
Precompose by tensorRight Q on the K-flat input category. The acyclic-tensor
hypothesis on Q gives categorical K-flatness through the homotopy acyclic
criterion and braiding, hence tensorRight Q preserves quasi-isomorphisms.
The ordinary source functor inverts them, and extension to C preserves
isomorphisms. For the target, compose the inverse monoidal tensorator of
C-extension with identity tensor t. Tensorator naturality and whisker exchange
prove its naturality in the input complex. Take homology and compose with the
previous comparison. Extend the ordinary model isomorphism to C; associativity
and the component equation give the displayed equality. No flatness of C, no
invertibility of t and no K-flatness of N is used. Zero rings, zero complexes and
unbounded complexes
are covered by the same maps and tensor generator equations.
(blueprint: lem-pc-kflat-localized-tensor-comparison-natural). -/
theorem exists_kFlatLocalizedTensorComparison_natural
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    (i : ℤ) :
    let m := fun U : CochainComplex.KFlat (ModuleCat.{u} A) ↦
      baseDerivedTensorCohomologyModel R A B (U.obj ⊗ Q) C
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let T := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
    ∃ (S : CochainComplex.KFlat (ModuleCat.{u} A) ⥤ ModuleCat.{u} C)
      (η : S ⟶ T),
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).WKFlat.IsInvertedBy S ∧
      ∀ U : CochainComplex.KFlat (ModuleCat.{u} A),
        ∃ e : (extendScalars (algebraMap (A ⊗[R] B) C)).obj ((m U).cohomology i) ≅
          S.obj U,
          e.hom ≫ η.app U = (m U).localizedComparison i ≫
            HomologicalComplex.homologyMap
              ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) i := by
  classical
  dsimp only
  let m := fun P : CochainComplex (ModuleCat.{u} A) ℤ ↦
    baseDerivedTensorCohomologyModel R A B P C
  let E := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  let G := restrictScalars.{u} (algebraMap (A ⊗[R] B) C)
  let L := extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let HC := HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
  obtain ⟨H, σ, e, hH, he⟩ := exists_baseTensorCohomologyFunctor R A B C i
  obtain ⟨β, hβ⟩ := exists_coefficientExtensionNaturalMap A (A ⊗[R] B) C
    (algebraMap A (A ⊗[R] B)) (algebraMap (A ⊗[R] B) C)
  let δ : E ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (.up ℤ) i ⟶
      F ⋙ HC ⋙ G :=
    { app := fun P ↦ HomologicalComplex.homologyMap (β.app P) i ≫
        ((F.obj P).sc i |>.mapHomologyIso G).hom
      naturality := by
        intro P P' f
        change HomologicalComplex.homologyMap (E.map f) i ≫
          (HomologicalComplex.homologyMap (β.app P') i ≫
            ((F.obj P').sc i |>.mapHomologyIso G).hom) =
          (HomologicalComplex.homologyMap (β.app P) i ≫
            ((F.obj P).sc i |>.mapHomologyIso G).hom) ≫
              G.map (HomologicalComplex.homologyMap (F.map f) i)
        rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          β.naturality f, HomologicalComplex.homologyMap_comp, Category.assoc]
        have hn : HomologicalComplex.homologyMap
            ((G.mapHomologicalComplex (.up ℤ)).map (F.map f)) i ≫
              ((F.obj P').sc i |>.mapHomologyIso G).hom =
            ((F.obj P).sc i |>.mapHomologyIso G).hom ≫
              G.map (HomologicalComplex.homologyMap (F.map f) i) :=
          ShortComplex.mapHomologyIso_hom_naturality
            ((HomologicalComplex.shortComplexFunctor _ _ i).map (F.map f)) G
        dsimp only [Functor.comp_map]
        rw [hn, Category.assoc] }
  let adj := extendRestrictScalarsAdj.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let ρ : H ⋙ L ⟶ F ⋙ HC :=
    { app := fun P ↦ (adj.homEquiv _ _).symm ((σ ≫ δ).app P)
      naturality := by
        intro P P' f
        apply (adj.homEquiv _ _).injective
        dsimp only [Functor.comp_map]
        change adj.homEquiv _ _ (L.map (H.map f) ≫ _) = _
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa only [Equiv.apply_symm_apply, Functor.comp_map]
          using (σ ≫ δ).naturality f }
  have hρ (P : CochainComplex (ModuleCat.{u} A) ℤ) :
      (L.mapIso (e P)).hom ≫ ρ.app P = (m P).localizedComparison i := by
    have hb : β.app P = (m P).ordinaryToLocalized := by
      ext j : 1
      apply ExtendScalars.hom_ext
      intro p
      exact (hβ P j 1 p).trans ((m P).ordinaryToLocalized_tmul j 1 p).symm
    apply (adj.homEquiv _ _).injective
    change adj.homEquiv _ _ (L.map (e P).hom ≫ ρ.app P) = _
    rw [adj.homEquiv_naturality_left]
    simp only [ρ, Equiv.apply_symm_apply, NatTrans.comp_app, δ,
      ← Category.assoc, he P, hb]
    change _ = adj.unit.app _ ≫ G.map ((m P).localizedComparison i)
    exact ((m P).localized_eq i).symm
  let J := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ tensorRight Q
  let S := J ⋙ H ⋙ L
  let τ : J ⋙ F ⟶ CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ F ⋙ tensorRight N :=
    { app := fun U ↦ (Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)
      naturality := by
        intro U V f
        change F.map (f.hom ▷ Q) ≫
          (Functor.Monoidal.μIso F V.obj Q).inv ≫ (F.obj V.obj ◁ t) =
          ((Functor.Monoidal.μIso F U.obj Q).inv ≫ (F.obj U.obj ◁ t)) ≫
            (F.map f.hom ▷ N)
        simp only [Functor.Monoidal.μIso_inv, Category.assoc]
        rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
        congr 1
        exact (whisker_exchange (F.map f.hom) t).symm }
  refine ⟨S, Functor.whiskerLeft J ρ ≫ Functor.whiskerRight τ HC, ?_, ?_⟩
  · intro U V f hf
    have hq := (CochainComplex.kFlat_iff_preservesQuasiIso Q).1
      (kFlat_of_acyclic_tensor Q hQ)
    have hJ : QuasiIso (J.map f) := hq.2 _ hf
    have : IsIso (H.map (J.map f)) := hH _ hJ
    change IsIso (L.map (H.map (J.map f)))
    infer_instance
  · intro U
    refine ⟨L.mapIso (e (U.obj ⊗ Q)), ?_⟩
    change (L.mapIso (e (U.obj ⊗ Q))).hom ≫
      (ρ.app (U.obj ⊗ Q) ≫ HomologicalComplex.homologyMap (τ.app U) i) = _
    rw [← Category.assoc, hρ]


end ModuleCat
