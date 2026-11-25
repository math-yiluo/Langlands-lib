/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Affine rank-one extensions separate etale module sheaves

Source: Stacks Project, Tags 03EW and 04HR
(blueprint: lemma-finiteness-small-etale-topoi--1).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The extensions by zero of the constant rank-one module sheaves on affine etale
objects form a separating family. This needs neither finite coefficients nor a qcqs base.

Source: Stacks Project, Modules on Sites, Tag 03EW, proof of (3), and Topologies,
Tag 04HR (affine etale objects are cover-dense)
(blueprint: lemma-finiteness-small-etale-topoi--1).

Proof: suppose two module-sheaf maps agree after composition with every map from
one of these extensions. The extension-by-zero/pullback adjunction identifies maps
from the extension at U with maps from the constant rank-one module sheaf into the
restriction to U. The constant-sheaf adjunction and the free rank-one module identify
these maps with sections over the terminal object of U's small etale site, hence with
sections over U of the original sheaf. Thus the two maps agree on every section over
an affine etale object. Every etale object has an affine open covering, whose members
are again etale over the base. Naturality gives equality after restriction to all members
of this cover, and the target sheaf's separatedness gives equality on the original
section. This proves equality of all components, hence equality of the sheaf maps.
The family is indexed in Type (u + 1), the universe of the small etale site, so no
additional universe resizing is needed. On an empty base or with the zero ring the
sheaf category is trivial, and the same separatedness argument still applies. -/
theorem affine_etale_rankOne_isSeparating
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ObjectProperty.IsSeparating (ObjectProperty.ofObj
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (fun U : { U : X.Etale // IsAffine U.left } ↦
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) U.val.hom inferInstance).obj
          ((constantSheaf U.val.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ)))) := by
  classical
  intro F F' f g h
  have hlocal (U : { U : X.Etale // IsAffine U.left }) :
      f.hom.app (Opposite.op U.val) = g.hom.app (Opposite.op U.val) := by
    let j : U.val.left ⟶ X := U.val.hom
    let hEt : Etale j := inferInstance
    let T := MorphismProperty.Over.mk ⊤ (𝟙 U.val.left) (by infer_instance : Etale _)
    let R := Etale.localizationRestriction (ModuleCat.{u + 1} Λ) j hEt ⋙
      (sheafSections U.val.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (Opposite.op T)
    let adj : constantSheaf U.val.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) j hEt ⊣ R :=
      (constantSheafAdj U.val.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) (MorphismProperty.Over.mkIdTerminal @Etale U.val.left)).comp
        ((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j hEt).ofNatIsoRight
          (Etale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} Λ) j hEt))
    have hterm : (MorphismProperty.Over.map ⊤ hEt).obj T = U.val := by
      ext <;> rfl
    have heval : R.map f = R.map g := by
      apply ModuleCat.hom_ext
      ext x
      let a := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ x)
      have hh := congrArg (adj.homEquiv (ModuleCat.of Λ Λ) F')
        (h _ (ObjectProperty.ofObj_apply _ U) ((adj.homEquiv _ F).symm a))
      have ha : a ≫ R.map f = a ≫ R.map g := by
        simpa only [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] using hh
      have hx := congrArg (fun q ↦ q.hom (1 : Λ)) ha
      simpa [a] using hx
    change f.hom.app (Opposite.op _) = g.hom.app (Opposite.op _) at heval
    exact (congrArg (fun V : X.Etale ↦
      f.hom.app (Opposite.op V) = g.hom.app (Opposite.op V)) hterm).mp heval
  apply Sheaf.hom_ext
  apply (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense
    X.smallEtaleTopology (AffineEtale.Spec X) F.obj F'.obj F'.property).injective
  ext1
  funext U
  apply hlocal ⟨(AffineEtale.Spec X).obj U.unop, ?_⟩
  change IsAffine (Spec U.unop.left.unop)
  infer_instance

end AlgebraicGeometry.Scheme
