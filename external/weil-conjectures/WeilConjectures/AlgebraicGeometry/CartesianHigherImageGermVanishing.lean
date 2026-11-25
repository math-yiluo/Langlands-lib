/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineSectionVanishing

/-! # Eventual vanishing of germs of relative higher direct images

Source: Stacks Project, Tag 0EYM, second proof.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/- A stage higher-image germ dying at the limit dies after a stage transition.
This is the kernel criterion for relative higher-image continuity, independently
of invertibility of any exchange map.
Source: Stacks Project, Tag 0EYM, second proof, part (2).
(blueprint: lem-sc-cartesian-higher-image-germ-vanishing)

Proof: represent the stage germ on an affine etale stage neighbourhood. Pullback
of sheaves and geometric stalks identify this representative with a germ on the
limit base. Locally lift the stage higher-image section to the cohomology
presheaf (Tag 03Q8). Its zero limit germ means that, after a further etale
refinement, its cohomology class is zero: both local lifting and local vanishing
are properties of sheafification. Descend these finitely presented affine etale
neighbourhoods and refinements to a common later stage (Tag 0EYL). Apply
cohomology continuity (Tag 09YQ) to the cartesian pullbacks of the neighbourhoods;
a stage class zero at the limit becomes zero at a later stage. The associated
higher-image section, and hence its germ, are zero at that stage. Pasting of
exchange and naturality of the presheaf comparison identify this restriction
with cartesianHigherImageTransition. Cofilteredness supplies a common stage and
handles parallel-arrow equalities; reindex by a directed set if necessary.
No torsion or smoothness is used, and q=0 and zero sheaves are included. -/
/-- (blueprint: lem-sc-cartesian-higher-image-germ-vanishing) -/
theorem exists_cartesianHigherImage_germ_eq_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (s : c.pt.left)
    (i : I) (x : ((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
      (cartesianHigherImageStage D c f F q i))
    (hx : (((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map
      (cartesianHigherImageLeg D c f F q i)) x = 0) :
    ∃ (j : I) (a : j ⟶ i),
      (((c.pt.left.uliftPointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).map
        (cartesianHigherImageTransition D c f F q a)) x = 0 := by
  classical
  let Φ := c.pt.left.uliftPointSmallEtale s
  let G := cartesianHigherImageStage D c f F q i
  let L := cartesianHigherImageLimit D c f F q
  let m : G ⟶ L := cartesianHigherImageLeg D c f F q i
  obtain ⟨U, v, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) x
  have hzero : Φ.toPresheafFiber U v L.obj (m.hom.app (Opposite.op U) z) =
      Φ.toPresheafFiber U v L.obj 0 := by
    rw [map_zero, ← Φ.toPresheafFiber_naturality_apply, hz]
    exact hx
  obtain ⟨W, g, w, hw, hW⟩ := (Φ.toPresheafFiber_eq_iff' U v _ _).mp hzero
  have hWzero : m.hom.app (Opposite.op W) (G.obj.map g.op z) = 0 := by
    rw [NatTrans.naturality_apply]
    simpa only [map_zero] using hW
  let A := Scheme.AffineEtale.Spec c.pt.left
  obtain ⟨T, t, ⟨a⟩, u, hu⟩ := Φ.jointly_surjective _
    (A.is_cover_of_isCoverDense c.pt.left.smallEtaleTopology W) w
  let V := A.obj a.obj
  have : IsAffine V.left := by
    dsimp only [V, A]
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  let v' := Φ.fiber.map a.lift u
  let zV := G.obj.map a.map.op (G.obj.map g.op z)
  have hzV : Φ.toPresheafFiber V v' G.obj zV = x := by
    rw [Φ.toPresheafFiber_w_apply, Φ.toPresheafFiber_w_apply]
    have hv : Φ.fiber.map a.map v' = w := by
      dsimp only [v']
      simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
        (congrArg (fun b ↦ Φ.fiber.map b u) a.fac).trans hu
    rw [hv, hw, hz]
  have hVzero : m.hom.app (Opposite.op V) zV = 0 := by
    dsimp only [zV]
    rw [NatTrans.naturality_apply, hWzero, map_zero]
  obtain ⟨j, b, hb⟩ := exists_cartesianHigherImage_affine_section_eq_zero
    D c hc f F q V i zV hVzero
  refine ⟨j, b, ?_⟩
  rw [← hzV]
  change Φ.presheafFiber.map
    (cartesianHigherImageTransition D c f F q b).hom
      (Φ.toPresheafFiber V v' G.obj zV) = 0
  rw [Φ.toPresheafFiber_naturality_apply, hb, map_zero]

end AlgebraicGeometry.Etale
