/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # Coherence of the module pullback tensor comparison

Source: Stacks Project, Modules, Tag 01CD; Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-module-pullback-tensor-coherence).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance pullbackCoherenceModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

namespace Scheme.Modules

noncomputable section

open Opposite TopologicalSpace in
private theorem tensor_hom_ext {Y : Scheme.{uModel}} {M N H : Y.Modules}
    {a b : M ⊗ N ⟶ H}
    (h : ∀ (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  let := presheafMonoidalCategory Y
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) H).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul s t => exact h U.unop s t
  | add z w hz hw => simp only [map_add, hz, hw]

open Opposite TopologicalSpace in
private theorem tensor_triple_hom_ext {Y : Scheme.{uModel}} {M N L H : Y.Modules}
    {a b : (M ⊗ N) ⊗ L ⟶ H}
    (h : ∀ (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) (w : Γ(L, U)),
      a.app U (tmulSection (tmulSection s t) w) =
        b.app U (tmulSection (tmulSection s t) w)) : a = b := by
  let := presheafMonoidalCategory Y
  let := forgetToPresheafOfModulesLaxMonoidal Y
  apply tensor_hom_ext
  intro U s w
  let μ := Functor.LaxMonoidal.μ (forgetToPresheafOfModules Y) M N
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology Y)
    ((PresheafOfModules.toPresheaf _).map μ) (U := op U) s
  refine (H.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W i hi ↦ ?_
  obtain ⟨z, hz⟩ := hi
  have hz' : tensorSectionsMap M N W z = (M ⊗ N).presheaf.map i.op s := hz
  have hh (z : TensorProduct Γ(Y, W) Γ(M, W) Γ(N, W)) :
      a.app W (tmulSection (tensorSectionsMap M N W z) (L.presheaf.map i.op w)) =
        b.app W (tmulSection (tensorSectionsMap M N W z) (L.presheaf.map i.op w)) := by
    induction z using TensorProduct.inductionOn with
    | tmul s t => exact h W s t (L.presheaf.map i.op w)
    | add z z' hz hz' => simp only [map_add, add_tmulSection, hz, hz']
  change H.presheaf.map i.op (a.app U (tmulSection s w)) =
    H.presheaf.map i.op (b.app U (tmulSection s w))
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  have ht := tmulSection_map (leOfHom i) s w
  rw [Subsingleton.elim (homOfLE (leOfHom i)) i] at ht
  rw [ht]
  exact hz' ▸ hh z

open Opposite TopologicalSpace in
/-- The chosen tensor comparison commutes with the associator.
Source: Stacks Project, Modules, Tag 01CD; Cohomology, Tag 079U.
(blueprint: lem-pc-module-pullback-tensor-coherence).
Proof: apply the tensor-pullback adjunction to both composites. On a local triple
pure tensor (s tensor t) tensor w, the comparison section formula, naturality of
adjunction units, and the associator section formula send both composites to
pullback(s) tensor (pullback(t) tensor pullback(w)). Triple pure tensors locally
generate the iterated tensor sheaf: first use the tensor universal property and
sheafification for the inner pair, then for the outer pair. Thus the adjoint
maps agree, and injectivity of the hom-equivalence gives the stated equality.
This argument requires no flatness and also applies to zero modules or empty schemes. -/
private theorem tensorPullback_tensor_associativity {X Y : Scheme.{uModel}} (g : X ⟶ Y) :
    let P := tensorPullback g
    let e := Classical.choose (module_pullback_tensor g)
    ∀ M N L : Y.Modules,
      (e (M ⊗ N) L).hom ≫ (e M N).hom ▷ P.obj L ≫
          (α_ (P.obj M) (P.obj N) (P.obj L)).hom =
        P.map (α_ M N L).hom ≫ (e M (N ⊗ L)).hom ≫ P.obj M ◁ (e N L).hom := by
  classical
  let P := tensorPullback g
  let e := Classical.choose (module_pullback_tensor g)
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  have he (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
      (e M N).hom.app (g ⁻¹ᵁ U) ((adj.unit.app (M ⊗ N)).app U (tmulSection s t)) =
        tmulSection (M := P.obj M) (N := P.obj N) (U := g ⁻¹ᵁ U)
          ((adj.unit.app M).app U s) ((adj.unit.app N).app U t) :=
    (Classical.choose_spec (module_pullback_tensor g)).2 M N U s t
  have hn {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
      (P.map a).app (g ⁻¹ᵁ U) ((adj.unit.app M).app U s) =
        (adj.unit.app N).app U (a.app U s) :=
    congrArg (fun q ↦ q.app U s) (adj.unit_naturality a)
  dsimp only
  intro M N L
  apply (adj.homEquiv _ _).injective
  apply tensor_triple_hom_ext
  intro U s t w
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (α_ (P.obj M) (P.obj N) (P.obj L)).hom.app (g ⁻¹ᵁ U)
      (((e M N).hom ▷ P.obj L).app (g ⁻¹ᵁ U)
        ((e (M ⊗ N) L).hom.app (g ⁻¹ᵁ U)
          ((adj.unit.app ((M ⊗ N) ⊗ L)).app U (tmulSection (tmulSection s t) w)))) =
    (P.obj M ◁ (e N L).hom).app (g ⁻¹ᵁ U)
      ((e M (N ⊗ L)).hom.app (g ⁻¹ᵁ U)
        ((P.map (α_ M N L).hom).app (g ⁻¹ᵁ U)
          ((adj.unit.app ((M ⊗ N) ⊗ L)).app U (tmulSection (tmulSection s t) w))))
  rw [hn, associator_hom_app_tmulSection s t w, he M (N ⊗ L) U s (tmulSection t w),
    he (M ⊗ N) L U (tmulSection s t) w,
    whiskerRight_app_tmulSection, whiskerLeft_app_tmulSection,
    he M N U s t, he N L U t w, associator_hom_app_tmulSection]

open Opposite TopologicalSpace in
/-- The adjoint structure-sheaf comparison satisfies both unit diagrams.
Source: Stacks Project, Modules, Tag 01CD; Cohomology, Tag 079U.
(blueprint: lem-pc-module-pullback-tensor-coherence).
Proof: apply the pullback adjunction to the inverse-unit diagrams. Naturality
of its unit moves the pullback of the inverse unitor onto the original section.
The inverse unitor sends s to 1 tensor s (respectively s tensor 1); the recorded
comparison sends its pullback to the tensor of the two pulled-back sections.
The structure-sheaf comparison sends the pulled-back 1 to 1, by its adjunction
characterization and preservation of 1 by the scheme ring map. The result is
exactly the inverse unitor applied to the pulled-back s. Equality on every
section gives equality of the adjoint maps, and the hom-equivalence is injective.
No nonzero section or nonempty scheme is assumed. -/
private theorem tensorPullback_tensor_unitality {X Y : Scheme.{uModel}} (g : X ⟶ Y) :
    let P := tensorPullback g
    let e := Classical.choose (module_pullback_tensor g)
    (∀ M : Y.Modules, (λ_ (P.obj M)).inv =
      P.map (λ_ M).inv ≫ (e (𝟙_ Y.Modules) M).hom ≫
        tensorPullbackObjUnitToUnit g ▷ P.obj M) ∧
    (∀ M : Y.Modules, (ρ_ (P.obj M)).inv =
      P.map (ρ_ M).inv ≫ (e M (𝟙_ Y.Modules)).hom ≫
        P.obj M ◁ tensorPullbackObjUnitToUnit g) := by
  classical
  let P := tensorPullback g
  let e := Classical.choose (module_pullback_tensor g)
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  have he (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
      (e M N).hom.app (g ⁻¹ᵁ U) ((adj.unit.app (M ⊗ N)).app U (tmulSection s t)) =
        tmulSection (M := P.obj M) (N := P.obj N) (U := g ⁻¹ᵁ U)
          ((adj.unit.app M).app U s) ((adj.unit.app N).app U t) :=
    (Classical.choose_spec (module_pullback_tensor g)).2 M N U s t
  have hu := (tensorPullbackObjUnitToUnit_isIso g).2
  have hunit (U : Y.Opens) :
      (tensorPullbackObjUnitToUnit g).app (g ⁻¹ᵁ U)
        ((adj.unit.app (𝟙_ Y.Modules)).app U (unitSectionsEquiv U 1)) =
        unitSectionsEquiv (g ⁻¹ᵁ U) 1 := by
    have h := congrArg (fun q ↦ q.val.app (op U) (unitSectionsEquiv U 1)) hu
    change _ = g.app U 1 at h
    exact h.trans (show g.app U 1 = unitSectionsEquiv (g ⁻¹ᵁ U) 1 by
      exact (g.app U).hom.map_one)
  have hn {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
      (P.map a).app (g ⁻¹ᵁ U) ((adj.unit.app M).app U s) =
        (adj.unit.app N).app U (a.app U s) :=
    congrArg (fun q ↦ q.app U s) (adj.unit_naturality a)
  constructor
  · intro M
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext s
    change (λ_ (P.obj M)).inv.app (g ⁻¹ᵁ U.unop) ((adj.unit.app M).app U.unop s) =
      (tensorPullbackObjUnitToUnit g ▷ P.obj M).app (g ⁻¹ᵁ U.unop)
        ((e (𝟙_ Y.Modules) M).hom.app (g ⁻¹ᵁ U.unop)
          ((P.map (λ_ M).inv).app (g ⁻¹ᵁ U.unop) ((adj.unit.app M).app U.unop s)))
    rw [hn, leftUnitor_inv_app (show Γ(M, U.unop) from s)]
    rw [he (𝟙_ Y.Modules) M U.unop (unitSectionsEquiv U.unop 1)
      (show Γ(M, U.unop) from s)]
    rw [whiskerRight_app_tmulSection, hunit, leftUnitor_inv_app]
  · intro M
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext s
    change (ρ_ (P.obj M)).inv.app (g ⁻¹ᵁ U.unop) ((adj.unit.app M).app U.unop s) =
      (P.obj M ◁ tensorPullbackObjUnitToUnit g).app (g ⁻¹ᵁ U.unop)
        ((e M (𝟙_ Y.Modules)).hom.app (g ⁻¹ᵁ U.unop)
          ((P.map (ρ_ M).inv).app (g ⁻¹ᵁ U.unop) ((adj.unit.app M).app U.unop s)))
    rw [hn, rightUnitor_inv_app (show Γ(M, U.unop) from s)]
    rw [he M (𝟙_ Y.Modules) U.unop (show Γ(M, U.unop) from s)
      (unitSectionsEquiv U.unop 1)]
    rw [whiskerLeft_app_tmulSection, hunit, rightUnitor_inv_app]

end
end Scheme.Modules

/-- The recorded module pullback tensor comparison is coherent with a unit comparison.
Source: Stacks Project, Modules, Tag 01CD; Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-module-pullback-tensor-coherence).
Proof: identify F with tensor-formula pullback using hF and hmap. On local pure tensors,
the comparison sends a pullback of s tensor t to the tensor of their pullbacks, by the
section formula of module_pullback_tensor. Thus its two iterates on three factors agree
with the associator: both send a pure triple tensor to the same triple tensor. Equality
extends by linearity, the tensor universal property, and sheafification. The structure
sheaf is taken to the structure sheaf by multiplication after extension of scalars;
the inverse sends a local section a to a tensor 1. These maps are inverse by the balanced
tensor relations. The left and right unit diagrams reduce on pure tensors to 1 times s
and s times 1. Invert the recorded tensor comparisons and use this unit isomorphism to
form CoreMonoidal. Transport along the identification of F gives exactly the displayed
conjugation by eqToHom. No exactness of pullback is required. -/
theorem modulePullback_tensor_coherent {T X : Scheme.{uModel}} (g : T ⟶ X)
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    : ∃ mF : F.CoreMonoidal,
    ∀ M N, (mF.μIso M N).inv = eqToHom (hF _) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      (eqToHom (hF M).symm ⊗ₘ eqToHom (hF N).symm) := by
  classical
  let P := Scheme.Modules.tensorPullback g
  let e := Classical.choose (Scheme.Modules.module_pullback_tensor g)
  have he := (Classical.choose_spec (Scheme.Modules.module_pullback_tensor g)).1
  have hu := Scheme.Modules.tensorPullbackObjUnitToUnit_isIso g
  let := hu.1
  let c : P.CoreMonoidal := Functor.CoreMonoidal.mk'
    (asIso (Scheme.Modules.tensorPullbackObjUnitToUnit g)).symm
    (fun M N ↦ (e M N).symm)
    (by
      intro M N a L
      have hn := he M L N L a (𝟙 L)
      change P.map (a ⊗ₘ 𝟙 L) ≫ (e N L).hom =
        (e M L).hom ≫ (P.map a ⊗ₘ P.map (𝟙 L)) at hn
      rw [P.map_id, tensorHom_id a L] at hn
      exact (congrArg ((e M L).hom ≫ ·)
        (tensorHom_id (P.map a) (P.obj L))).symm.trans hn.symm)
    (by
      intro M N L a
      have hn := he L M L N (𝟙 L) a
      change P.map (𝟙 L ⊗ₘ a) ≫ (e L N).hom =
        (e L M).hom ≫ (P.map (𝟙 L) ⊗ₘ P.map a) at hn
      rw [P.map_id, id_tensorHom L a] at hn
      exact (congrArg ((e L M).hom ≫ ·)
        (id_tensorHom (P.obj L) (P.map a))).symm.trans hn.symm)
    (Scheme.Modules.tensorPullback_tensor_associativity g)
    (Scheme.Modules.tensorPullback_tensor_unitality g).1
    (Scheme.Modules.tensorPullback_tensor_unitality g).2
  let i : F ≅ P := NatIso.ofComponents (fun M ↦ eqToIso (hF M)) (by
    intro M N a
    dsimp [P]
    rw [hmap]
    simp
    rfl)
  let := c.toMonoidal
  refine ⟨Functor.Monoidal.coreMonoidalTransport i.symm, ?_⟩
  intro M N
  rfl

end AlgebraicGeometry
