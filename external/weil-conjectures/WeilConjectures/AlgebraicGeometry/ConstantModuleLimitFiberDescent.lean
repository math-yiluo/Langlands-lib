/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstantModuleLimitAffineSectionDescent
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Descent of constant-module direct-image germs

Source: Stacks Project, Tag 09Z1, degree zero.
(blueprint: lem-weil-pbc-constant-module-limit-fiber-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Every germ of the constant-module direct image on the limit descends to a stage.

Source: Stacks Project, Tag 09Z1 in degree zero and Tag 09Z6, finite approximation.
(blueprint: lem-weil-pbc-constant-module-limit-fiber-descent).

Proof: Represent the germ on an affine etale neighborhood U of the point of X.
Base changing the inverse system to U preserves the scheme limit, affine transitions,
and qcqs structure maps. Reindex by a coinitial directed partial order (Tag 0032).
Pullback identifies every constant M-sheaf with the constant M-sheaf on the limit;
the transition maps become identities, so their colimit is constant M. Forget the
module coefficients and apply the degree-zero continuity isomorphism (Tag 09Z1).
Degree-zero higher direct image is ordinary direct image. Apply the geometric fiber:
it preserves filtered colimits, and every element of a filtered colimit of abelian
groups has a stage representative. Pull this representative back to the module fiber;
the module-to-abelian forgetful functor identifies their underlying elements.
The canonical comparison components are the adjunction units and the constant
pullback and direct-image composition comparisons, hence precisely
constantModulePushforwardMap. Forgetting coefficients commutes with these maps, so
the equality of underlying germs is an equality of module germs. Passing back
through the final reindexing gives a stage of the original category. No equality
of two representatives or injectivity of the comparison is used. The empty scheme
case is vacuous, and the zero module and singleton systems satisfy the same argument. -/
theorem exists_constantModule_limit_fiber_rep
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (s : X)
    (x : ((X.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) ν).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :
    ∃ (i : I) (y : ((X.uliftPointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
        ((constantSheaf (D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))),
      (((X.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
        (constantModulePushforwardMap Λ M _ _ (π.app i) (hπ i))) y = x := by
  classical
  let Φ := X.uliftPointSmallEtale s
  let B := (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1, u, u + 1}
  obtain ⟨U, u, z, hz⟩ := Φ.toPresheafFiber_jointly_surjective (P := B.obj) x
  let G := Scheme.AffineEtale.Spec X
  obtain ⟨V, f, ⟨a⟩, v, hv⟩ := Φ.jointly_surjective (Sieve.coverByImage G U)
    (G.is_cover_of_isCoverDense X.smallEtaleTopology U) u
  let w := Φ.fiber.map a.lift v
  let z' := B.obj.map a.map.op z
  have : IsAffine (G.obj a.obj).left := by
    change IsAffine (Scheme.Spec.obj a.obj.left)
    infer_instance
  obtain ⟨i, y, hy⟩ := exists_constantModule_limit_affine_section_rep
    Λ M D p hp ν π hπ hc (G.obj a.obj) z'
  let A := (lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
    ((constantSheaf (D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  refine ⟨i, Φ.toPresheafFiber (G.obj a.obj) w A.obj y, ?_⟩
  change Φ.presheafFiber.map
    (constantModulePushforwardMap Λ M _ _ (π.app i) (hπ i)).hom
      (Φ.toPresheafFiber (G.obj a.obj) w A.obj y) = x
  rw [Φ.toPresheafFiber_naturality_apply, hy]
  change Φ.toPresheafFiber (G.obj a.obj) w B.obj (B.obj.map a.map.op z) = x
  rw [Φ.toPresheafFiber_w_apply]
  have hw : Φ.fiber.map a.map w = u := by
    dsimp [w]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, a.fac]
    exact hv
  rw [hw]
  exact hz

end AlgebraicGeometry.Etale
