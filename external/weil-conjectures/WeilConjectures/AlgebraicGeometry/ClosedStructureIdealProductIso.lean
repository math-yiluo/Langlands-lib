/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # A normalized closed structure ideal-product comparison

Source: Stacks Project, Tag 01QY, affine quotient calculation.
(blueprint: lem-pc-closed-structure-ideal-product-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The chosen and abelian images have the same section range on every open, without
quasi-coherence or affineness assumptions.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem image_range_eq_abelian {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) :
    Set.range ((image.ι φ).app U) = Set.range ((Abelian.image.ι φ).app U) := by
  let e := Abelian.imageIsoImage φ
  have he : Function.Surjective (e.hom.app U) :=
    (Modules.appLinearEquivOfIso e U).surjective
  have hf : e.hom ≫ image.ι φ = Abelian.image.ι φ :=
    Abelian.imageIsoImage_hom_comp_image_ι φ
  rw [← hf, Modules.Hom.comp_app]
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨a, rfl⟩ := he t
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨e.hom.app U a, rfl⟩

open MonoidalCategory Opposite in
open scoped TensorProduct in
/-- The image of any map out of a quasi-coherent tensor product is generated on an
affine open by the images of pure tensor sections. The target is an arbitrary
quasi-coherent module; the map need not be ideal multiplication.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem tensor_image_range_affine {X : Scheme.{u}} {J M N : X.Modules}
    (ψ : J ⊗ M ⟶ N) [J.IsQuasicoherent] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : X.affineOpens) :
    Set.range ((image.ι ψ).app U.1) =
      (AddSubgroup.closure {s | ∃ (a : Γ(J, U.1)) (t : Γ(M, U.1)),
        s = ψ.app U.1 (Modules.tmulSection a t)} : Set Γ(N, U.1)) := by
  have : (J ⊗ M).IsQuasicoherent :=
    (Modules.quasiCoherent_tensor_product_affine_sections J M).1
  rw [image_range_eq_abelian ψ U.1,
    ((Modules.quasiCoherent_cokernel_image ψ).2.2.2.2.2.2.2.2 U).1]
  let H := AddSubgroup.closure {s | ∃ (a : Γ(J, U.1)) (t : Γ(M, U.1)),
    s = ψ.app U.1 (Modules.tmulSection a t)}
  apply Set.Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    obtain ⟨z, rfl⟩ :=
      (Modules.quasiCoherent_tensor_product_affine_sections J M).2 U.1 U.2 |>.2 s
    induction z using TensorProduct.inductionOn with
    | tmul a t =>
      rw [Modules.tensorSectionsMap_tmul]
      exact AddSubgroup.subset_closure ⟨a, t, rfl⟩
    | add z z' hz hz' =>
      simp only [map_add]
      exact H.add_mem hz hz'
  · change H ≤ (ψ.val.app (op U.1)).hom.range.toAddSubgroup
    apply (AddSubgroup.closure_le _).mpr
    rintro s ⟨a, t, rfl⟩
    exact ⟨Modules.tmulSection a t, rfl⟩

/-- Equality of arbitrary morphisms is equivalent to equality on affine sections.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem hom_eq_iff_affine {X : Scheme.{u}} {M N : X.Modules}
    (φ ψ : M ⟶ N) :
    φ = ψ ↔ ∀ V : X.affineOpens, ∀ s : Γ(M, V.1), φ.app V.1 s = ψ.app V.1 s := by
  constructor
  · rintro rfl V s
    rfl
  intro h
  apply Modules.hom_ext
  intro W
  ext s
  change φ.app W s = ψ.app W s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    rw [← Modules.Hom.app_presheaf_map, ← Modules.Hom.app_presheaf_map]
    exact h i.1 _

/-- Subobject order is equivalent to affine section-range inclusion. No quasi-coherence
is assumed on any of the three modules.
Source: Stacks Project, proof of Lemma 01YP
(blueprint: lem-weil-pbc-closed-immersion-ideal-power-image). -/
private theorem subobject_le_iff_affine_range {X : Scheme.{u}} {M N P : X.Modules}
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j] :
    Subobject.mk i ≤ Subobject.mk j ↔
      ∀ V : X.affineOpens, Set.range (i.app V.1) ⊆ Set.range (j.app V.1) := by
  constructor
  · intro h V s hs
    obtain ⟨t, rfl⟩ := hs
    let f := Subobject.ofMkLEMk i j h
    refine ⟨f.app V.1 t, ?_⟩
    exact congrArg (fun q ↦ q.app V.1 t) (Subobject.ofMkLEMk_comp h)
  intro h
  have hz : i ≫ cokernel.π j = 0 := by
    apply (hom_eq_iff_affine _ _).mpr
    intro V s
    obtain ⟨t, ht⟩ := h V ⟨s, rfl⟩
    change (cokernel.π j).app V.1 (i.app V.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app V.1 t) (cokernel.condition j)
  let k : M ⟶ Abelian.image j := kernel.lift (cokernel.π j) i hz
  let l : M ⟶ N := k ≫ inv (Abelian.factorThruImage j)
  apply Subobject.mk_le_mk_of_comm l
  change k ≫ inv (Abelian.factorThruImage j) ≫ j = i
  calc
    k ≫ inv (Abelian.factorThruImage j) ≫ j =
        k ≫ inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
      congrArg (fun q ↦ k ≫ inv (Abelian.factorThruImage j) ≫ q)
        (Abelian.image.fac j).symm
    _ = k ≫ Abelian.image.ι j := by rw [IsIso.inv_hom_id_assoc]
    _ = i := kernel.lift_ι _ _ hz

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Identify the pushforward of the extended ideal with its ambient ideal product,
including the compatibility with the inclusions into the closed structure module.
Source: Stacks Project, Tag 01QY (lemma-closed-immersion-pushforward).
(blueprint: lem-pc-closed-structure-ideal-product-iso)

Proof: On an affine open V = Spec A in X, its inverse image under the closed
immersion is Spec B, where B = A/K and the structure map pi : A -> B is surjective.
If L = I(V), the ideal of I.comap i on this inverse image is Ideal.map pi L.
Surjectivity makes pi(L) an ideal: a scalar b lifts to a in A, and b*pi(l) = pi(a*l).
Thus this extended ideal equals the B-submodule L B. The ambient product I H,
where H = i_* O_W, is the image of multiplication L tensor_A B -> B, and has
exactly the same sections L B. Both inclusions are injective: the upstairs ideal
inclusion is injective on sections, closed pushforward preserves this, and the
product inclusion is an image inclusion. On the affine basis their ranges agree.
The two subobjects of H consequently agree: a local lift through either inclusion
is unique, so the lifts agree on overlaps and glue by the sheaf axiom. The equal
subobjects give an isomorphism between their domains commuting with their monic
arrows into H. This is the displayed equation. The argument uses neither
Noetherianity nor integrality. It applies to the zero ideal, the unit ideal, and
the empty closed subscheme; all comparisons preserve the given inclusions. -/
theorem closed_structure_ideal_product_iso
    {X W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    (I : X.IdealSheafData) :
    ∃ e : (pushforward i).obj (I.comap i).toModules ≅
        idealModuleProduct I.toModulesι
          ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)),
      e.hom ≫ idealModuleProductι I.toModulesι
          ((pushforward i).obj (SheafOfModules.unit W.ringCatSheaf)) =
        (pushforward i).map (I.comap i).toModulesι := by
  classical
  let : MonoidalCategory W.Modules := SheafOfModules.monoidalCategory W.sheaf
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let G : W.Modules := SheafOfModules.unit W.ringCatSheaf
  let J := I.comap i
  let μ := J.toModulesι ▷ G ≫ (λ_ G).hom
  have hc : (ρ_ J.toModules).hom ≫ J.toModulesι = μ := by
    change (ρ_ J.toModules).hom ≫ J.toModulesι =
      J.toModulesι ▷ (𝟙_ W.Modules) ≫ (λ_ (𝟙_ W.Modules)).hom
    rw [MonoidalCategory.unitors_equal, MonoidalCategory.rightUnitor_naturality]
  let e : J.toModules ≅ idealModuleProduct J.toModulesι G :=
    CategoryTheory.Limits.image.isoStrongEpiMono
    (f := μ) (ρ_ J.toModules).hom J.toModulesι hc
  have he : e.hom ≫ idealModuleProductι J.toModulesι G = J.toModulesι :=
    CategoryTheory.Limits.image.isoStrongEpiMono_hom_comp_ι _ _ hc
  have := SheafOfModules.isQuasicoherent_unit (R := W.ringCatSheaf)
  let p := (pushforward i).map J.toModulesι
  let q := idealModuleProductι I.toModulesι ((pushforward i).obj G)
  have : Mono q := by dsimp [q, idealModuleProductι]; infer_instance
  have hp : Mono p := by dsimp [p]; infer_instance
  have hqc {Y : Scheme.{u}} (K : Y.IdealSheafData) : K.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := K.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
    have : ((SheafOfModules.pushforward K.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit K.subscheme.ringCatSheaf)).IsQuasicoherent :=
      isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated K.subschemeι _
    exact isQuasicoherent_kernel K.toPushforwardSubscheme
  have := hqc I
  have := hqc J
  have : ((pushforward i).obj G).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated i G
  have hprod_range {Y : Scheme.{u}} {K : Y.Modules}
      (a : K ⟶ SheafOfModules.unit Y.ringCatSheaf) (M : Y.Modules)
      [K.IsQuasicoherent] [M.IsQuasicoherent] (V : Y.affineOpens) :
      Set.range ((idealModuleProductι a M).app V.1) =
        (AddSubgroup.closure {s | ∃ (z : Γ(K, V.1)) (t : Γ(M, V.1)),
          s = (unitSectionsEquiv V.1).symm (a.app V.1 z) • t} : Set Γ(M, V.1)) := by
    let : MonoidalCategory Y.Modules := SheafOfModules.monoidalCategory Y.sheaf
    change Set.range ((image.ι (a ▷ M ≫ (λ_ M).hom)).app V.1) = _
    rw [Scheme.tensor_image_range_affine]
    have ht (z : Γ(K, V.1)) (t : Γ(M, V.1)) :
        (a ▷ M ≫ (λ_ M).hom).app V.1 (tmulSection z t) =
          (unitSectionsEquiv V.1).symm (a.app V.1 z) • t := by
      rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
      exact leftUnitor_hom_app_tmulSection' _ _
    simp_rw [ht]
  have hr (V : X.affineOpens) : Set.range (p.app V.1) = Set.range (q.app V.1) := by
    let U : W.affineOpens := ⟨i ⁻¹ᵁ V.1, V.2.preimage i⟩
    have hpX := I.range_toModulesι_app V
    have hpZ := J.range_toModulesι_app U
    have hideal : J.ideal U = Ideal.map (i.app V.1).hom (I.ideal V) := by
      dsimp [J]
      rw [IdealSheafData.ideal_comap_appLE I i V U le_rfl]
      simp only [U, Hom.appLE_eq_app]
    have hprod : Set.range (p.app V.1) =
        Set.range (((pushforward i).map (idealModuleProductι J.toModulesι G)).app V.1) := by
      have he' : (pushforward i).map e.hom ≫
          (pushforward i).map (idealModuleProductι J.toModulesι G) = p := by
        rw [← Functor.map_comp, he]
      have hs := (appLinearEquivOfIso ((pushforward i).mapIso e) V.1).surjective
      ext s
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨((pushforward i).map e.hom).app V.1 x, ?_⟩
        exact congrArg (fun f ↦ f.app V.1 x) he'
      · rintro ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := hs x
        refine ⟨y, ?_⟩
        rw [← he', Hom.comp_app]
        exact congrArg (fun t ↦
          ((pushforward i).map (idealModuleProductι J.toModulesι G)).app V.1 t) hy
    rw [hprod, pushforward_map_app]
    refine (hprod_range J.toModulesι G U).trans
      (Eq.trans ?_ (hprod_range I.toModulesι
        ((pushforward i).obj G) V).symm)
    apply congrArg (fun H : AddSubgroup Γ(G, U.1) ↦ (H : Set Γ(G, U.1)))
    apply congrArg AddSubgroup.closure
    ext s
    constructor
    · rintro ⟨z, t, rfl⟩
      have hz : J.toModulesι.app U.1 z ∈ J.ideal U :=
        (Set.ext_iff.mp hpZ _).mp ⟨z, rfl⟩
      rw [hideal] at hz
      obtain ⟨r, hr, hri⟩ :=
        (Ideal.mem_map_iff_of_surjective (i.app V.1).hom
          (i.app_surjective V.1 V.2)).mp hz
      obtain ⟨x, hx⟩ := (Set.ext_iff.mp hpX _).mpr hr
      refine ⟨x, t, ?_⟩
      change (show Γ(W, U.1) from J.toModulesι.app U.1 z) • t =
        i.app V.1 (I.toModulesι.app V.1 x) • t
      exact congrArg (fun r : Γ(W, U.1) ↦ r • t)
        (hri.symm.trans (congrArg (i.app V.1) hx.symm))
    · rintro ⟨x, t, rfl⟩
      have hx : I.toModulesι.app V.1 x ∈ I.ideal V :=
        (Set.ext_iff.mp hpX _).mp ⟨x, rfl⟩
      have hz : i.app V.1 (I.toModulesι.app V.1 x) ∈ J.ideal U := by
        rw [hideal]
        exact Ideal.mem_map_of_mem _ hx
      obtain ⟨z, hz⟩ := (Set.ext_iff.mp hpZ _).mpr hz
      refine ⟨z, t, ?_⟩
      change i.app V.1 (I.toModulesι.app V.1 x) • (show Γ(G, U.1) from t) =
        (show Γ(W, U.1) from J.toModulesι.app U.1 z) • (show Γ(G, U.1) from t)
      exact congrArg (fun r : Γ(W, U.1) ↦ r • (show Γ(G, U.1) from t)) hz.symm
  have hsub : Subobject.mk p = Subobject.mk q :=
    le_antisymm ((Scheme.subobject_le_iff_affine_range p q).mpr (fun V ↦ (hr V).subset))
      ((Scheme.subobject_le_iff_affine_range q p).mpr (fun V ↦ (hr V).symm.subset))
  refine ⟨Subobject.isoOfMkEqMk p q hsub, ?_⟩
  change (Subobject.isoOfMkEqMk p q hsub).hom ≫ q = p
  simp

end AlgebraicGeometry.Scheme.Modules
