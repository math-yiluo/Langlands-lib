/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.LocalModuleEpiGermLift
import WeilConjectures.AlgebraicGeometry.StalkInternalHomEvaluation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Germ comparison for an already descended local factorization

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third paragraph.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- If a lifted local map has already descended through the restricted source
epimorphism, the descended map induces the prescribed map on all section germs.
There is no finite presentation or finite free source assumption, and this result
neither constructs a generator lift nor kills relations nor constructs the descent.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third
paragraph, comparing the two finite-coordinate kernels after cokernel descent.
(blueprint: lem-weil-pbc-local-stalk-factorization-germ-comparison)

Proof: Restricting F first to U, then to V, then to W is canonically isomorphic
to restricting F to W, with identity maps on the section carriers. The analogous
identification for G changes θ into a morphism F|W to G|W; forget its sheaf proof
to obtain φ in internal Hom. Given a section s on Z inside W containing x, use
the epimorphism b and exists_local_module_epi_germ_lift to choose a representative
t on Z' inside Z whose image has the same germ as s. The canonical stalk internal
Hom evaluation respects that equality of germs. The factorization equation hθ,
evaluated at Z', identifies φ applied to b(t) with ψ(t). The formula hψ identifies
the latter's germ with χ of the germ of b(t). Use equality with the germ of s
once more. Every step is linear and natural; no finiteness or uniqueness is used.
For zero objects, the same epimorphism/germ argument still applies. -/
theorem exists_internalHom_of_local_stalk_factorization
    (X : RingedSpace.{u}) (F G : Modules X) (x : X)
    (U V W : Opens X) (hxW : x ∈ W) (i : V ⟶ U) (j : W ⟶ V)
    (A : SheafOfModules.{u} (((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U))
    (b : A ⟶ F.over U) [Epi b]
    (ψ : (SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).obj A ⟶ G.over V)
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G)
    (hψ : ∀ (Z : Opens X) (k : Z ⟶ V) (hxZ : x ∈ Z)
      (t : A.val.obj (op (Over.mk (k ≫ i)))),
      TopCat.Presheaf.germ G.val.presheaf Z x hxZ
        (ψ.val.app (op (Over.mk k)) t) =
      χ (TopCat.Presheaf.germ F.val.presheaf Z x hxZ
        (b.val.app (op (Over.mk (k ≫ i))) t)))
    (θ : (SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) j).obj
        ((SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).obj (F.over U)) ⟶
      (SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) j).obj (G.over V))
    (hθ : (SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) j).map
        ((SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).map b) ≫ θ =
      (SheafOfModules.overMap.{u} ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) j).map ψ) :
    ∃ (φ : (F.homObj G).val.obj (op W)),
      ∀ (Z : Opens X) (k : Z ⟶ W) (hxZ : x ∈ Z) (s : F.val.obj (op Z)),
        TopCat.Presheaf.germ G.val.presheaf Z x hxZ (φ.app (op (Over.mk k)) s) =
          χ (TopCat.Presheaf.germ F.val.presheaf Z x hxZ s) := by
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
  let T := SheafOfModules.overMap.{u} R j
  let eF := T.mapIso ((SheafOfModules.overFunctorMap R i).app F) ≪≫
    (SheafOfModules.overFunctorMap R j).app F
  let eG := (SheafOfModules.overFunctorMap R j).app G
  let φ : (F.homObj G).val.obj (op W) := (eF.inv ≫ θ ≫ eG.hom).val
  refine ⟨φ, ?_⟩
  intro Z k hxZ s
  obtain ⟨c, hc⟩ := exists_stalk_internalHom_linearMap X F G x
  obtain ⟨Z', hxZ', l, t, ht⟩ := exists_local_module_epi_germ_lift
    X F x U A b Z (k ≫ j ≫ i) hxZ s
  have heq : φ.app (op (Over.mk (l ≫ k)))
      (b.val.app (op (Over.mk ((l ≫ k) ≫ j ≫ i))) t) =
      ψ.val.app (op (Over.mk ((l ≫ k) ≫ j))) t := by
    have h := congrArg (fun f ↦ f.val.app (op (Over.mk (l ≫ k))) t) hθ
    exact h
  rw [← hc W hxW φ Z k hxZ s, ← ht,
    hc W hxW φ Z' (l ≫ k) hxZ']
  exact (congrArg (TopCat.Presheaf.germ G.val.presheaf Z' x hxZ') heq).trans
    (hψ Z' ((l ≫ k) ≫ j) hxZ' t)


end AlgebraicGeometry.RingedSpace
