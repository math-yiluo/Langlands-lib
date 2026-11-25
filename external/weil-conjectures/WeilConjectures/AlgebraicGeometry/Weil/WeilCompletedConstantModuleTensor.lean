/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Ordinary tensor comparison for completed constant modules

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
section Normalization

universe vC uC vD uD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

-- An automorphism of the tensor unit acts naturally on every object.
private def unitAction (a : 𝟙_ D ≅ 𝟙_ D) : 𝟭 D ≅ 𝟭 D :=
  NatIso.ofComponents (fun Y ↦
    (λ_ Y).symm ≪≫ whiskerRightIso a Y ≪≫ λ_ Y) (by
      intro Y Z f
      dsimp
      simp only [whiskerRightIso_hom, Category.assoc]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        leftUnitor_naturality])

private theorem unitAction_unit (a : 𝟙_ D ≅ 𝟙_ D) :
    (unitAction a).hom.app (𝟙_ D) = a.hom := by
  change (λ_ (𝟙_ D)).inv ≫ a.hom ▷ (𝟙_ D) ≫ (λ_ (𝟙_ D)).hom = _
  rw [unitors_equal, rightUnitor_naturality, ← unitors_equal, Iso.inv_hom_id_assoc]

private def curryTensorIso (G : C ⥤ D)
    (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D) :
    (Functor.postcompose₂.obj G).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ e.app (M, N)) (by
    intro N N' g
    have h := e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, g)
    change G.map (𝟙 M ⊗ₘ g) ≫ _ = _ ≫ (G.map (𝟙 M) ⊗ₘ G.map g) at h
    change G.map (M ◁ g) ≫ _ = _ ≫ (G.obj M ◁ G.map g)
    simpa only [G.map_id, id_tensorHom, Iso.app_hom] using h)) (by
      intro M M' f
      apply NatTrans.ext
      funext N
      have h := e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N)
      change G.map (f ⊗ₘ 𝟙 N) ≫ _ = _ ≫ (G.map f ⊗ₘ G.map (𝟙 N)) at h
      change G.map (f ▷ N) ≫ _ = _ ≫ (G.map f ▷ G.obj N)
      simpa only [G.map_id, tensorHom_id, Iso.app_hom, NatIso.ofComponents_hom_app] using h)

private theorem normalizeTensorIso (G : C ⥤ D) (c : 𝟙_ D ⟶ G.obj (𝟙_ C))
    [IsIso c] (e : tensor C ⋙ G ≅ G.prod G ⋙ tensor D) :
    ∃ τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ≅
        (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D),
      c ≫ G.map (ρ_ (𝟙_ C)).inv ≫ (τ.hom.app (𝟙_ C)).app (𝟙_ C) =
        (λ_ (𝟙_ D)).inv ≫ (c ⊗ₘ c) := by
  let z := asIso c ≪≫ G.mapIso (ρ_ (𝟙_ C)).symm ≪≫ e.app (𝟙_ C, 𝟙_ C)
  let w := (λ_ (𝟙_ D)).symm ≪≫ tensorIso (asIso c) (asIso c)
  let a := w ≪≫ z.symm
  let σ := unitAction a
  let e' : tensor C ⋙ G ≅ G.prod G ⋙ tensor D :=
    e ≪≫ Functor.isoWhiskerLeft (G.prod G ⋙ tensor D) σ
  refine ⟨curryTensorIso G e', ?_⟩
  have hz : z.hom ≫ σ.hom.app (G.obj (𝟙_ C) ⊗ G.obj (𝟙_ C)) = w.hom := by
    have hn : z.hom ≫ σ.hom.app (G.obj (𝟙_ C) ⊗ G.obj (𝟙_ C)) =
        σ.hom.app (𝟙_ D) ≫ z.hom := by
      simpa using σ.hom.naturality z.hom
    rw [hn]
    rw [show σ.hom.app (𝟙_ D) = a.hom from unitAction_unit a]
    simp [a]
  simpa [z, w, e', curryTensorIso, Category.assoc] using hz

end Normalization

namespace AlgebraicGeometry.Scheme

private theorem completedOne_isIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) : IsIso (completedKoszulOne X d) := by
  let M := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
  let α := adicDatumScalar X d
  let adj := adicDatumOrdinaryAdjunction X α
  let e (N : adicDatumModules X d) :
      ((completedKoszulConstant X d).obj (ModuleCat.of A A) ⟶ N) ≃ N.sections :=
    ((adj.homEquiv M N).trans
      (PresheafOfModules.sheafificationHomEquiv (adicLisseConstantUnit X A))).trans
        (PresheafOfModules.unitHomEquiv _)
  have he (N : adicDatumModules X d)
      (f : (completedKoszulConstant X d).obj (ModuleCat.of A A) ⟶ N) :
      e N f = N.unitHomEquiv (completedKoszulOne X d ≫ f) := by
    apply PresheafOfModules.sections_ext
    intro U
    dsimp only [e, Equiv.trans_apply]
    change ((PresheafOfModules.sheafificationHomEquiv (adicLisseConstantUnit X A))
      (adj.homEquiv M N f)).app U (1 : A) =
        f.val.app U ((completedKoszulOne X d).val.app U
          (1 : (adicDatumRing X d).obj.obj U))
    rw [Adjunction.homEquiv_unit]
    change f.val.app U ((adj.unit.app M).val.app U
      (completedConstantGenerator X A (ModuleCat.of A A) U 1)) =
        f.val.app U ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U))
    have hu : adj.unit.app M = adicDatumOrdinaryUnit X α M :=
      (adicDatumOrdinaryAdjunction_exists X α).choose_spec M
    rw [hu]
    exact congrArg (f.val.app U)
      (((adicDatumOrdinaryUnit_exists X α M).exists.choose_spec U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1)).trans
          ((completedKoszulOne_exists X d).exists.choose_spec U).symm)
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hf : (fun f ↦ completedKoszulOne X d ≫ f) =
      N.unitHomEquiv.symm ∘ e N := by
    funext f
    exact N.unitHomEquiv.injective (by simp [he])
  rw [hf]
  exact N.unitHomEquiv.symm.bijective.comp (e N).bijective

private theorem extension_obj (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : completedConstantModules X R) :
    (completedConstantExtension X φ).obj M = SheafOfModules.changeOfRings φ M :=
  (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    φ).choose_spec.choose M

private theorem extension_map (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : completedConstantModules X R} (f : M ⟶ N) :
    (completedConstantExtension X φ).map f = eqToHom (extension_obj X φ M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (extension_obj X φ N).symm :=
  (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    φ).choose_spec.choose_spec.choose f

private theorem extension_tensor (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.isMonoidal_W_independentCoefficients S
    letI := SheafOfModules.monoidalCategory S
    let E := completedConstantExtension X φ
    Nonempty (tensor (completedConstantModules X R) ⋙ E ≅
      E.prod E ⋙ tensor (completedConstantModules X S)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory S
  let E := completedConstantExtension X φ
  obtain ⟨b⟩ := SheafOfModules.scalarExtension_constraint_coherence R S φ
  refine ⟨NatIso.ofComponents (fun MN ↦
    eqToIso (extension_obj X φ (MN.1 ⊗ MN.2)) ≪≫ b.tensorIso MN.1 MN.2 ≪≫
      tensorIso (eqToIso (extension_obj X φ MN.1)).symm
        (eqToIso (extension_obj X φ MN.2)).symm) ?_⟩
  intro MN PQ fg
  change E.map (fg.1 ⊗ₘ fg.2) ≫ _ = _ ≫ (E.map fg.1 ⊗ₘ E.map fg.2)
  dsimp only [E]
  rw [extension_map X φ (fg.1 ⊗ₘ fg.2), extension_map X φ fg.1,
    extension_map X φ fg.2]
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, tensorIso_hom,
    eqToIso.inv, Category.assoc, tensorHom_comp_tensorHom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (b.natural MN.1 MN.2 PQ.1 PQ.2 fg.1 fg.2)]
  simp only [tensorHom_comp_tensorHom]

private theorem constant_tensor (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicLisseConstantRing X A)
    letI := SheafOfModules.monoidalCategory (adicLisseConstantRing X A)
    let F := adicLisseConstantModules X A
    Nonempty (tensor (ModuleCat.{u + 1} A) ⋙ F ≅
      F.prod F ⋙ tensor (completedConstantModules X (adicLisseConstantRing X A))) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicLisseConstantRing X A)
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing X A)
  let P : ModuleCat.{u + 1} A ⥤ _root_.PresheafOfModules.{u + 1}
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⋙ forget₂ CommRingCat RingCat) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
  let S := PresheafOfModules.sheafification (adicLisseConstantUnit X A)
  let p : tensor (ModuleCat.{u + 1} A) ⋙ P ≅ P.prod P ⋙ tensor _ :=
    NatIso.ofComponents (fun MN ↦
      PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
        intro U V f
        apply ModuleCat.MonoidalCategory.tensor_ext (R := A)
        intro x y
        rfl)) (by
          intro MN PQ fg
          ext U : 1
          apply ModuleCat.MonoidalCategory.tensor_ext (R := A)
          intro x y
          rfl)
  obtain ⟨e, _⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
    (R := adicLisseConstantRing X A) (adicLisseConstantUnit X A)
  exact ⟨Functor.isoWhiskerRight p S ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (P.prod P) e.symm⟩

/-- Completed constant extension preserves the ordinary module tensor product,
with its regular coefficient map normalized by the section `1 tensor 1`.

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW.
(blueprint: lem-weil-pbc-completed-constant-module-tensor).

Proof: the constant module presheaf functor identifies sectionwise tensor products.
Apply the tensor comparison for module sheafification along the locally bijective
constant-ring sheafification unit. Apply ordinary scalar extension along the
compatible-residue ring map. Its balanced tensor comparison takes
`s tensor (x tensor y)` to `(s tensor x) tensor (1 tensor y)`; its inverse
multiplies the two scalars. The balancing relations show that these maps are
well defined, mutually inverse and natural in both modules. The sheafification
universal property preserves these equations and naturality. Their composite
is the asserted natural isomorphism. To check the normalization, evaluate a map
from the regular module at the section 1. The inverse right unitor sends 1 to
`1 tensor 1`. Each constant sheafification unit preserves 1, and ordinary scalar
extension sends it to `1 tensor 1`. The comparison therefore gives the tensor
of the two specified regular-module maps. The inverse left unitor has the same
value at 1. Maps from the regular module are determined by this section, proving
the equation. This uses neither complexes nor a site equivalence, and works for
the zero ring and on the empty site. -/
theorem completedConstantModuleTensor
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) :
    let O := adicDatumRing X d
    let G := completedKoszulConstant X d
    let c := completedKoszulOne X d
    letI := SheafOfModules.isMonoidal_W_independentCoefficients O
    letI := SheafOfModules.monoidalCategory O
    ∃ τ : (Functor.postcompose₂.obj G).obj (curriedTensor _) ≅
        (((Functor.whiskeringLeft₂ _).obj G).obj G).obj (curriedTensor _),
      c ≫ G.map (ρ_ (ModuleCat.of A A)).inv ≫
        (τ.hom.app (ModuleCat.of A A)).app (ModuleCat.of A A) =
          (λ_ (𝟙_ (adicDatumModules X d))).inv ≫ (c ⊗ₘ c) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicLisseConstantRing X A)
  let := SheafOfModules.monoidalCategory (adicLisseConstantRing X A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  let F := adicLisseConstantModules X A
  let E := completedConstantExtension X (adicDatumScalar X d)
  obtain ⟨p⟩ := constant_tensor X A
  obtain ⟨q⟩ := extension_tensor X (adicDatumScalar X d)
  let e : tensor (ModuleCat.{u + 1} A) ⋙ (F ⋙ E) ≅
      (F ⋙ E).prod (F ⋙ E) ⋙ tensor (adicDatumModules X d) :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight p E ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (F.prod F) q
  have := completedOne_isIso X d
  exact normalizeTensorIso (completedKoszulConstant X d) (completedKoszulOne X d) e

end AlgebraicGeometry.Scheme
