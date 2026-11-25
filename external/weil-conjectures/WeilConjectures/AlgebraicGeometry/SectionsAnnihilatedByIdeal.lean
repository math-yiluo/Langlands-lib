/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.AnnihilatorSubsheaf
import WeilConjectures.AlgebraicGeometry.AnnihilatorAffineCriterion
import WeilConjectures.AlgebraicGeometry.AnnihilatorQuasicoherent
import WeilConjectures.AlgebraicGeometry.AnnihilatorStalkLocalLift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # The subsheaf of sections annihilated by an ideal

Source: Stacks Project, Properties, Lemma 01PO and Definition 01PP
(blueprint: lem-weil-pbc-sections-annihilated-by-ideal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

private theorem annihilator_stalkMap_germ (X : Scheme.{u}) {G F : X.Modules}
    (ι : G ⟶ F) (x : X) (U : X.Opens) (hx : x ∈ U) (t : Γ(G, U)) :
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom
        (G.presheaf.germ U x hx t) = F.presheaf.germ U x hx (ι.app U t) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ι.mapPresheaf t

private theorem annihilator_stalkMap_injective (X : Scheme.{u}) {G F : X.Modules}
    (ι : G ⟶ F) [Mono ι] (x : X) :
    Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom := by
  have : Mono ι.val := (SheafOfModules.forget X.ringCatSheaf).map_mono ι
  have hm := (RingedSpace.module_stalk_exact X.toRingedSpace ι).1
    (fun U ↦ PresheafOfModules.injective_of_mono ι.val (op U)) x
  exact (ModuleCat.mono_iff_injective _).mp hm

/-- The subsheaf of sections annihilated by a quasi-coherent ideal of finite type.
Source: Stacks Project, Properties, Lemma 01PO and Definition 01PP
(blueprint: lem-weil-pbc-sections-annihilated-by-ideal).

The quasi-coherent ideal is `J : X.IdealSheafData` (quasi-coherence is built in), with
ideal sheaf `J.toModules ⊆ 𝒪_X` via `J.toModulesι`; finite type is Mathlib's
`SheafOfModules.IsFiniteType` of `J.toModules`. Its sections over an open `V` are
`J.idealOfOpens V` (`range_toModulesι_app_eq_idealOfOpens`), over an affine open `J.ideal U`.
The image of the inclusion on every open is specified by local annihilation, so `G`
is the subsheaf in the node, rather than an arbitrary quasi-coherent submodule.
The stalk clause uses `RingedSpace.moduleStalkFunctor`. It expresses annihilation by
the ideal stalk through all germs of ideal sections: every element of `J_x` is such a
germ, and its image in `𝒪_{X,x}` is the germ of the section. The stalk maps of both
inclusions are injective.

Proof:
1. `exists_annihilator_subsheaf` constructs the submodule presheaf explicitly and
proves gluing by separatedness of F. Its inclusion is sectionwise injective.
2. `annihilator_affine_criterion` identifies the affine image by ideal extension
along restriction and separatedness on an affine cover. This step needs neither
finite type of the ideal nor quasi-coherence of F.
3. `annihilator_subsheaf_quasicoherent` supplies quasi-coherence from the affine
image formula, using the finite-generator principal-open localization argument.
4. `RingedSpace.module_stalk_exact` makes both inclusion stalk maps injective.
A germ from G is annihilated by every ideal germ: intersect the two representative
opens, restrict the ideal section there, and apply the sectionwise image formula.
5. `annihilator_stalk_local_lift` gives a locally annihilated representative of an
annihilated stalk element. Lift that representative through the sectionwise image
formula and take its germ. The quasi-coherence and local-lifting inputs remain
separate named theorems whose proofs are open.
-/
theorem sections_annihilated_by_ideal
    (X : Scheme.{u}) (J : X.IdealSheafData) [J.toModules.IsFiniteType]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (ι : G ⟶ F),
      Mono ι ∧ G.IsQuasicoherent ∧
      (∀ (U : X.Opens) (s : Γ(F, U)),
        s ∈ Set.range (ι.app U) ↔
          ∀ (V : X.Opens) (h : V ≤ U), ∀ a ∈ J.idealOfOpens V,
            a • F.presheaf.map (homOfLE h).op s = 0) ∧
      (∀ (U : X.affineOpens) (s : Γ(F, U.1)),
        s ∈ Set.range (ι.app U.1) ↔ ∀ a ∈ J.ideal U, a • s = 0) ∧
      (∀ x : X,
        Function.Injective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map J.toModulesι).hom ∧
        Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom ∧
        ∀ s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F,
          s ∈ Set.range ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom ↔
            ∀ (U : X.Opens) (hx : x ∈ U), ∀ a ∈ J.idealOfOpens U,
              X.presheaf.germ U x hx a • s = 0) := by
  obtain ⟨G, ι, hmono, himage⟩ := exists_annihilator_subsheaf X J F
  have : Mono ι := hmono
  have haffine : ∀ (U : X.affineOpens) (s : Γ(F, U.1)),
      s ∈ Set.range (ι.app U.1) ↔ ∀ a ∈ J.ideal U, a • s = 0 := by
    intro U s
    exact (himage U.1 s).trans (annihilator_affine_criterion X J F U s)
  refine ⟨G, ι, hmono, annihilator_subsheaf_quasicoherent X J F G ι haffine,
    himage, haffine, ?_⟩
  intro x
  refine ⟨annihilator_stalkMap_injective X J.toModulesι x,
    annihilator_stalkMap_injective X ι x, ?_⟩
  intro s
  constructor
  · rintro ⟨q, rfl⟩ U hx a ha
    obtain ⟨V, hxV, t, rfl⟩ := G.presheaf.exists_germ_eq q
    rw [annihilator_stalkMap_germ]
    have hlocal := (himage V (ι.app V t)).mp ⟨t, rfl⟩
    have ha' : X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a ∈
        J.idealOfOpens (U ⊓ V) := by
      change a ∈ (J.idealOfOpens U : Set Γ(X, U)) at ha
      rw [← J.range_toModulesι_app_eq_idealOfOpens] at ha
      obtain ⟨b, rfl⟩ := ha
      change _ ∈ (J.idealOfOpens (U ⊓ V) : Set Γ(X, U ⊓ V))
      rw [← J.range_toModulesι_app_eq_idealOfOpens]
      refine ⟨J.toModules.presheaf.map (homOfLE inf_le_left).op b, ?_⟩
      exact ConcreteCategory.congr_hom
        (J.toModulesι.mapPresheaf.naturality (homOfLE inf_le_left).op) b
    have hxUV : x ∈ U ⊓ V := ⟨hx, hxV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hxUV a,
      ← F.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hxUV]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) F.val]
    rw [hlocal (U ⊓ V) inf_le_right _ ha', map_zero]
  · intro hs
    obtain ⟨U, hx, t, ht, hlocal⟩ := annihilator_stalk_local_lift X J F x s hs
    obtain ⟨q, hq⟩ := (himage U t).mpr hlocal
    refine ⟨G.presheaf.germ U x hx q, ?_⟩
    rw [annihilator_stalkMap_germ, hq, ht]

end AlgebraicGeometry
