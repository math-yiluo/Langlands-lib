/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
import WeilConjectures.AlgebraicGeometry.Modules.InverseImageStalkScalarTransport

/-!
# Stalks and germs of the tensor pullback of modules

Stalks of module sheaves are taken with the recorded stalk functor
`RingedSpace.moduleStalkFunctor`. Mathlib writes extension of
scalars as `O_{X,x} ⊗ G_{f(x)}`. This is the tensor product `G_{f(x)} ⊗ O_{X,x}` via its
canonical symmetry; the corresponding pure tensor is `1 ⊗ s_{f(x)}`.

## References

* Stacks Project, Sheaves, Lemma 6.26.4 (Tag 0098)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The stalk of tensor pullback is naturally the extension of scalars of the original
stalk along `f.stalkMap x`; a pulled-back section has germ `1 ⊗ s_{f(x)}`. -/
theorem exists_tensorPullback_stalk_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∃ e : tensorPullback f ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x ≅
        RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x) ⋙
          ModuleCat.extendScalars (f.stalkMap x).hom,
      ∀ (G : Y.Modules) (V : Y.Opens) (hx : f x ∈ V) (s : G.val.obj (op V)),
        (e.hom.app G)
            (TopCat.Presheaf.germ ((tensorPullback f).obj G).val.presheaf (f ⁻¹ᵁ V) x hx
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
                (op V) s)) =
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x), (f.stalkMap x).hom]
            (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s) := by
  obtain ⟨β, hβ⟩ := exists_inverseImage_stalk_scalar_transport f x
  obtain ⟨τ, hτ, _⟩ := SheafOfModules.stalkChangeOfRingsIso X.toTopCat
    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf) X.sheaf (tensorPullbackRingMap f) x
  let δ (G : Y.Modules) :
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).obj G) ≅
        (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj ((tensorPullback f).obj G) :=
    β G ≪≫ τ (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G)
  have hδ (G : Y.Modules) (V : Y.Opens) (hx : f x ∈ V) (s : G.val.obj (op V)) :
      (δ G).hom ((1 : X.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
        (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s)) =
      TopCat.Presheaf.germ ((tensorPullback f).obj G).val.presheaf (f ⁻¹ᵁ V) x hx
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
          (op V) s) := by
    change (τ _).hom ((β G).hom _) = _
    rw [hβ]
    have ht := hτ (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G) (f ⁻¹ᵁ V) hx
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f.base) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
          ((SheafOfModules.toSheaf _).obj G)).hom.app (op V) s)
      (1 : X.sheaf.obj.obj (op (f ⁻¹ᵁ V)))
    rw [Classical.choose_spec (exists_tensorPullbackAdjunction f)]
    simp only [map_one] at ht
    convert ht using 1
    rfl
  let d : RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x) ⋙
      ModuleCat.extendScalars (f.stalkMap x).hom ≅
      tensorPullback f ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x :=
    NatIso.ofComponents δ (by
      intro G H a
      apply ModuleCat.ExtendScalars.hom_ext
      intro m
      obtain ⟨V, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
      change (δ H).hom
        ((ModuleCat.extendScalars (f.stalkMap x).hom).map
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).map a)
          ((1 : X.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
            (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s))) =
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
          ((tensorPullback f).map a))
          ((δ G).hom ((1 : X.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
            (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s)))
      erw [ModuleCat.ExtendScalars.map_tmul]
      have ha :
          (RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).map a
            (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s) =
          TopCat.Presheaf.germ H.val.presheaf V (f x) hx (a.val.app (op V) s) := by
        exact TopCat.Presheaf.stalkFunctor_map_germ_apply V (f x) hx
          ((PresheafOfModules.toPresheaf _).map a.val) s
      rw [ha, hδ, hδ]
      have hn := congrArg (fun t ↦ t.val.app (op V) s)
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit_naturality a)
      have hb := TopCat.Presheaf.stalkFunctor_map_germ_apply (f ⁻¹ᵁ V) x hx
        ((PresheafOfModules.toPresheaf _).map ((tensorPullback f).map a).val)
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
          (op V) s)
      dsimp at hn
      exact (congrArg (TopCat.Presheaf.germ ((tensorPullback f).obj H).val.presheaf
        (f ⁻¹ᵁ V) x hx) hn.symm).trans hb.symm)
  refine ⟨d.symm, ?_⟩
  intro G V hx s
  have hh := congrArg (fun t ↦ (δ G).inv t) (hδ G V hx s)
  simpa [d] using hh.symm

end
end AlgebraicGeometry.Scheme.Modules
