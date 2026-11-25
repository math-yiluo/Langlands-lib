/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.AlgebraicGeometry.EtaleAbelianKanComparisonLocallySurjective

/-! # Local representatives for a supplied abelian inverse-image adjunction

Source: Stacks Project, Tag 09XN, local description of inverse-image sections.
(blueprint: lem-weil-pbc-etale-abelian-local-unit-representatives). -/

@[expose] public section

universe u
open CategoryTheory Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Every inverse-image section has unit representatives on an etale cover.
Source: Stacks Project, Tag 09XN, proof of lemma-describe-pullback, paragraph
beginning "By construction"; compatibility with abelian structure and units.
(blueprint: lem-weil-pbc-etale-abelian-local-unit-representatives).

Proof: Form the underlying-set inverse image by the left Kan extension along
base change followed by sheafification. The sheafification unit is locally
surjective. Thus, on an etale covering of T, the section is represented by an
element of the pointwise Kan extension. Its indexing category of pairs (W,a)
is filtered because base change preserves finite limits. Consequently each
colimit element comes from a single section of F(W). The Kan unit followed by
the sheafification unit is the inverse-image adjunction unit, so the image of
that section is precisely the displayed expression. The abelian inverse image
has this underlying set inverse image, with the same unit. Finally compare its
left adjoint with H by uniqueness of left adjoints to the fixed pushforward;
the comparison preserves the specified unit and restriction maps. Transport
both the given section and its local representatives through that comparison.
Extract a covering indexed in Type (u+1) using the small etale topology's cover
criterion. Empty schemes admit the empty cover; no global representative on a
prescribed covering object is asserted. -/
theorem etaleAbelian_local_unit_representatives
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    ∃ (I : Type (u + 1)) (Z : I → T.Etale)
      (z : ∀ i, Z i ⟶ Scheme.Etale.mk (𝟙 T))
      (W : I → X.Etale) (a : ∀ i, Z i ⟶ p.Etale.obj (W i))
      (s : ∀ i, F.obj.obj (op (W i))),
      Sieve.ofArrows Z z ∈ T.smallEtaleTopology (Scheme.Etale.mk (𝟙 T)) ∧
      ∀ i, (H.obj F).obj.map (z i).op t =
        (H.obj F).obj.map (a i).op ((hH.unit.app F).hom.app (op (W i)) (s i)) := by
  classical
  let P := etaleAbelianSetKan p F
  let G := etaleAbelianLargeSections (H.obj F)
  let q := etaleAbelianKanComparison p H hH F
  let α := p.Etale.op.leftKanExtensionUnit (etaleAbelianLargeSections F)
  let U := Scheme.Etale.mk (𝟙 T)
  let := etaleAbelianKanComparison_locally_surjective p H hH F
  have hcover := Presheaf.imageSieve_mem (CA := fun X ↦ X) T.smallEtaleTopology q (U := op U)
    (show G.obj (op U) from ULift.up t)
  have hrep (Z : T.Etale) (z : Z ⟶ U)
      (hz : Presheaf.imageSieve (CA := fun X ↦ X) q (U := U) (ULift.up t) z) :
      ∃ (W : X.Etale) (a : Z ⟶ p.Etale.obj W) (s : F.obj.obj (op W)),
        (H.obj F).obj.map z.op t =
          (H.obj F).obj.map a.op ((hH.unit.app F).hom.app (op W) s) := by
    obtain ⟨r, hr⟩ := hz
    obtain ⟨j, b, hb⟩ := CategoryTheory.Limits.Types.jointly_surjective _
      (p.Etale.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        (etaleAbelianLargeSections F) (op Z)) r
    change (etaleAbelianLargeSections F).obj j.left at b
    change P.map j.hom (α.app j.left b) = r at hb
    refine ⟨j.left.unop, j.hom.unop, b.down, ?_⟩
    have hunit : q.app (p.Etale.op.obj j.left) (α.app j.left b) =
        ULift.up ((hH.unit.app F).hom.app j.left b.down) := by
      exact ConcreteCategory.congr_hom (Functor.descOfIsLeftKanExtension_fac_app P α G
        (Functor.whiskerRight (Functor.whiskerRight (hH.unit.app F).hom
          (forget AddCommGrpCat.{u + 1})) uliftFunctor.{u + 2, u + 1}) j.left) b
    have he : G.map j.hom (ULift.up ((hH.unit.app F).hom.app j.left b.down)) =
        G.map z.op (ULift.up t) := by
      rw [← hunit, ← q.naturality_apply j.hom, hb]
      exact hr
    exact (congrArg ULift.down he).symm
  have hc := (Scheme.mem_smallEtaleTopology_iff _).mp hcover
  have hx (x : U.left) : ∃ (Z : T.Etale) (z : Z ⟶ U),
      (∃ y : Z.left, z.left y = x) ∧
      ∃ (W : X.Etale) (a : Z ⟶ p.Etale.obj W) (s : F.obj.obj (op W)),
        (H.obj F).obj.map z.op t =
          (H.obj F).obj.map a.op ((hH.unit.app F).hom.app (op W) s) := by
    obtain ⟨Z, z, hz, hy⟩ := hc x
    exact ⟨Z, z, hy, hrep Z z hz⟩
  choose Z z hpoint W a s he using hx
  refine ⟨U.left, Z, z, W, a, s, ?_, he⟩
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  exact Set.mem_iUnion.mpr ⟨x, hpoint x⟩
