/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Naturality of the injective-resolution computation

Source: Stacks Project, Tag 0156, Lemma 13.20.1.
(blueprint: lem-sp-derived-injective-resolution-naturality).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- A commuting square of quasi-isomorphisms induces a quasi-isomorphism on cones.
Source: Stacks Project, Tag 014A (five lemma for distinguished triangles)
(blueprint: lem-sp-derived-injective-resolution-naturality).

Proof. Localize the morphism of mapping-cone triangles. Its first two components
are isomorphisms, hence so is its third component. Localization reflects
quasi-isomorphisms. -/
theorem quasiIso_map_of_quasiIso
    {K L I J : CochainComplex C ℤ} (f : K ⟶ L) (g : I ⟶ J)
    (a : K ⟶ I) (b : L ⟶ J) (h : f ≫ b = a ≫ g)
    [QuasiIso a] [QuasiIso b] : QuasiIso (map f g a b h) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1
  let φ := DerivedCategory.Q.mapTriangle.map (triangleMap f g a b h)
  exact CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ φ
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g)
    (by change IsIso (DerivedCategory.Q.map a); infer_instance)
    (by change IsIso (DerivedCategory.Q.map b); infer_instance)

end CochainComplex.mappingCone

namespace CochainComplex.Plus

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual mapping cone in the category of bounded-below cochain complexes. -/
noncomputable def mappingCone {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    CochainComplex.Plus C :=
  ⟨CochainComplex.mappingCone f.hom, by
    obtain ⟨n, hn⟩ := K.property
    obtain ⟨m, hm⟩ := L.property
    exact ⟨min (n - 1) m,
      CochainComplex.isStrictlyGE_mappingCone f.hom n m _ (by omega) (by omega)⟩⟩

end CochainComplex.Plus

namespace CategoryTheory.Functor

variable {B : Type u} [Category.{v} B] [Abelian B] [EnoughInjectives B]
variable {C : Type u'} [Category.{v'} C] [Abelian C]
variable [HasDerivedCategory B] [HasDerivedCategory C]
variable (G : B ⥤ C) [G.Additive]

end CategoryTheory.Functor
