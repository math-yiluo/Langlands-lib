/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import all WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk

/-! # Invertibility of strict-local global germs

Source: Stacks Project, Tags 03QO and 03Q1.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The closed-point global germ is invertible for any separably closed point field. -/
private theorem globalGerm_isIso_at_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : s default = IsLocalRing.closedPoint R) : IsIso (globalGerm s) := by
  suffices h : ∀ F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u + 1},
      IsIso ((pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk (𝟙 _))
        (Over.homMk s (Category.comp_id s)) F.obj) by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun F ↦ ?_)
    unfold globalGerm
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      GrothendieckTopology.Point.toPresheafFiberNatTrans_app]
    change IsIso ((Sheaf.ΓNatIsoSheafSections _ _
      (MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) _)).hom.app F ≫
        (pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk (𝟙 _))
          (Over.homMk s (Category.comp_id s)) F.obj)
    let := h F
    infer_instance
  let : IsStrictlyHenselianLocalRing R := hR
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let : LocallySmall.{u} (Spec (.of R)).Etale := locallySmall_self _
  let Φ := pointSmallEtale s
  let T := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let t : Φ.fiber.obj T := Over.homMk s (Category.comp_id s)
  have hsec (X : (Spec (.of R)).Etale) (x : Φ.fiber.obj X) :
      ∃ g : T ⟶ X, Φ.fiber.map g t = x := by
    obtain ⟨σ, hσ, hsσ⟩ := strictlyHenselianSections_pointedSection hR X.hom x.left s x.w hs
    refine ⟨MorphismProperty.Over.homMk σ hσ, ?_⟩
    apply Over.OverMorphism.ext
    exact hsσ
  intro F
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b hab
    obtain ⟨Y, f, y, _, heq⟩ :=
      (Φ.toPresheafFiber_eq_iff' (P := F.obj) T t a b).mp hab
    obtain ⟨g, _⟩ := hsec Y y
    have hgf : g ≫ f = 𝟙 T := by
      apply MorphismProperty.Over.Hom.ext
      have hf' : f.left ≫ T.hom = Y.hom := f.w
      have hg' : g.left ≫ Y.hom = T.hom := g.w
      change g.left ≫ f.left = 𝟙 _
      have hf'' : f.left = Y.hom := by
        change f.left ≫ 𝟙 _ = Y.hom at hf'
        simpa only [Category.comp_id] using hf'
      rw [hf'']
      exact hg'
    have h := congrArg (F.obj.map g.op) heq
    simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
  · intro z
    obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) z
    obtain ⟨g, hg⟩ := hsec X x
    refine ⟨F.obj.map g.op a, ?_⟩
    rw [Φ.toPresheafFiber_w_apply, hg]
set_option backward.isDefEq.respectTransparency false in
/-- Global germs and pulled global germs are invertible over strict-local bases.

Source: Stacks Project, etale-cohomology.tex, Tags 03QO and 03Q1 (3).
(blueprint: lem-weil-pbc-strict-local-global-germ-iso)

Proof: For a pointed etale neighbourhood of the closed point of a strictly henselian
local scheme, shrink to an affine chart and localize at the marked prime. The local
weakly etale algebra is the base ring (Olivier's theorem), so the neighbourhood has a
section through the marked geometric point. Every germ is represented on a neighbourhood;
pull its representative back along this section for surjectivity. An equality of germs
holds on a common neighbourhood, and its section gives equality of global sections for
injectivity. This proves invertibility of the global germ, with its naturality supplied
by the germ naturality formula. The same argument works for a separably closed point
field: it uses only the marked field map, not algebraic closedness. For the pulled germ,
the inverse-image stalk identification identifies the germ with the original stalk at
the composite point. A local ring map sends the closed B-point to the closed A-point.
Apply the preceding pointed-section argument there with point field kappa(B); the
inverse-image germ compatibility identifies this isomorphism with `pulledGlobalGerm`.
Thus both natural transformations are componentwise isomorphisms and hence are isomorphisms.
No restriction on sheaves, properness or torsion is needed. -/
theorem strictLocal_globalGerm_isIso
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)]
    [CommRing B] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    (φ : A →+* B) [IsLocalHom φ] :
    let g := Spec.map (CommRingCat.ofHom φ)
    let t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    IsIso (pulledGlobalGerm g t) ∧ IsIso (globalGerm t) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  let t := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  have hA : IsStrictlyHenselianLocalRing A :=
    (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed A).2
      ⟨inferInstance, inferInstance⟩
  have hB : IsStrictlyHenselianLocalRing B :=
    (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed B).2
      ⟨inferInstance, inferInstance⟩
  have ht : t default = IsLocalRing.closedPoint B := by
    dsimp only [t]
    rw [Spec.map_apply]
    rw [Subsingleton.elim (default : Spec (.of (IsLocalRing.ResidueField B)))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField B))]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
  have htg : (t ≫ g) default = IsLocalRing.closedPoint A := by
    change g (t default) = _
    rw [ht]
    dsimp only [g]
    rw [Spec.map_apply]
    exact IsLocalRing.comap_closedPoint φ
  have := globalGerm_isIso_at_closedPoint hA (t ≫ g) htg
  have := globalGerm_isIso_at_closedPoint hB t ht
  constructor
  · unfold pulledGlobalGerm
    infer_instance
  · infer_instance

end AlgebraicGeometry.Etale
