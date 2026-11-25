/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily

/-!
# Ample families on group schemes: reduction to the identity component

Let `G` be a group scheme of finite type over an algebraically closed field `k`. Every connected
component of `G` contains a closed point, which is a `k`-rational point `g`, and left translation
by `g` maps the identity component `G°` isomorphically onto that component. Hence `G` is the
disjoint union of finitely many copies of `G°`, and an ample family on `G°` gives one on `G`.
This is the reduction to connected group schemes in the proof of Stacks 0BF7.

## Main definitions

- `AlgebraicGeometry.GrpObj.sigmaIdentityComponentIso`: the isomorphism
  `∐_{π₀(G)} G° ≅ G`, given on the component indexed by `c` by translation by a rational point
  of `c`.

## Main statements

- `AlgebraicGeometry.GrpObj.exists_isClosed_singleton_mk_eq`: every connected component of `G`
  contains a closed point.
- `AlgebraicGeometry.GrpObj.hasAmpleFamily_of_identityComponent`: if `G°` has an ample family,
  so has `G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- Left translation by a rational point `g` maps the identity point to `g`. -/
lemma GrpObj.mulLeft_left_onePoint (G : Over (Spec (.of k))) [GrpObj G]
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    (GrpObj.mulLeft G g).left (GrpObj.onePoint G) =
      g.left (show Spec (.of k) from ⟨⊥, Ideal.isPrime_bot⟩) := by
  have h : η[G] ≫ GrpObj.mulLeft G g = g := by
    rw [GrpObj.mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc,
      toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id,
      ← Category.id_comp η[G], ← toUnit_unique (toUnit _) (𝟙 _), ← Hom.one_def, mul_one]
  rw [GrpObj.onePoint, ← Scheme.Hom.comp_apply, ← Over.comp_left, h]

/-- Every connected component of a scheme `G` of finite type over a field contains a closed
point: it is closed in the quasi-compact space `G`. -/
lemma GrpObj.exists_isClosed_singleton_mk_eq (G : Over (Spec (.of k))) [QuasiCompact G.hom]
    (c : ConnectedComponents G.left) :
    ∃ x : G.left, IsClosed {x} ∧ ConnectedComponents.mk x = c := by
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  have := QuasiCompact.compactSpace_of_compactSpace G.hom
  obtain ⟨x, hx, hcl⟩ := isClosed_connectedComponent.exists_closed_singleton
    ⟨y, mem_connectedComponent⟩
  exact ⟨x, hcl, ConnectedComponents.coe_eq_coe'.mpr hx⟩

section AlgClosed

variable [IsAlgClosed k] (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]
  [QuasiCompact G.hom]

/-- A rational point in the connected component `c` of `G`. -/
noncomputable def GrpObj.pointOfConnectedComponents (c : ConnectedComponents G.left) :
    𝟙_ (Over (Spec (.of k))) ⟶ G :=
  GrpObj.sectionOfIsClosed G (GrpObj.exists_isClosed_singleton_mk_eq G c).choose
    (GrpObj.exists_isClosed_singleton_mk_eq G c).choose_spec.1

/-- The open immersion `G° ⟶ G` onto the connected component `c`: the inclusion of the identity
component followed by translation by a rational point of `c`. -/
noncomputable def GrpObj.identityComponentTranslate (c : ConnectedComponents G.left) :
    (GrpObj.identityComponent G).left ⟶ G.left :=
  (GrpObj.identityComponentι G).left ≫
    (GrpObj.mulLeft G (GrpObj.pointOfConnectedComponents G c)).left

instance (c : ConnectedComponents G.left) :
    IsOpenImmersion (GrpObj.identityComponentTranslate G c) :=
  have := GrpObj.isIso_mulLeft_left G (GrpObj.pointOfConnectedComponents G c)
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The translate of `G°` indexed by `c` is the connected component `c`. -/
lemma GrpObj.range_identityComponentTranslate (c : ConnectedComponents G.left) :
    Set.range (GrpObj.identityComponentTranslate G c) = ConnectedComponents.mk ⁻¹' {c} := by
  obtain ⟨hcl, hc⟩ := (GrpObj.exists_isClosed_singleton_mk_eq G c).choose_spec
  conv_rhs => rw [← hc, connectedComponents_preimage_singleton]
  rw [GrpObj.identityComponentTranslate, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    GrpObj.range_identityComponentι, GrpObj.image_mulLeft_connectedComponent_onePoint,
    GrpObj.mulLeft_left_onePoint, GrpObj.pointOfConnectedComponents,
    GrpObj.sectionOfIsClosed_left_apply]

/-- **A group scheme is a disjoint union of copies of its identity component.** Over an
algebraically closed field, a group scheme `G` of finite type is the disjoint union, indexed by its
connected components `c`, of the translates of `G°` by rational points of `c`. -/
noncomputable def GrpObj.sigmaIdentityComponentIso :
    (∐ fun _ : ConnectedComponents G.left ↦ (GrpObj.identityComponent G).left) ≅ G.left :=
  have : IsOpenImmersion (Sigma.desc (GrpObj.identityComponentTranslate G)) :=
    isOpenImmersion_sigmaDesc _ _ fun c c' hcc' ↦ by
      rw [Function.onFun_apply, GrpObj.range_identityComponentTranslate,
        GrpObj.range_identityComponentTranslate]
      exact Set.disjoint_singleton.mpr hcc' |>.preimage _
  have : Surjective (Sigma.desc (GrpObj.identityComponentTranslate G)) := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ : y ∈ Set.range (GrpObj.identityComponentTranslate G (.mk y)) := by
      rw [GrpObj.range_identityComponentTranslate]
      rfl
    exact ⟨Sigma.ι (fun _ : ConnectedComponents G.left ↦ (GrpObj.identityComponent G).left)
      (.mk y) x, by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc, hx]⟩⟩
  have : IsIso (Sigma.desc (GrpObj.identityComponentTranslate G)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  asIso (Sigma.desc (GrpObj.identityComponentTranslate G))

/-- **Reduction to connected group schemes.** If the identity component `G°` of a group scheme
`G` of finite type over an algebraically closed field has an ample family, so has `G`: it is
the disjoint union of finitely many copies of `G°`. -/
theorem GrpObj.hasAmpleFamily_of_identityComponent
    (h : (GrpObj.identityComponent G).left.HasAmpleFamily) : G.left.HasAmpleFamily :=
  have := finite_connectedComponents G
  (h.sigma (ConnectedComponents G.left)).of_iso (GrpObj.sigmaIdentityComponentIso G).symm

end AlgClosed

end AlgebraicGeometry
