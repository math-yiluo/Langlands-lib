/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Relative flatness is independent of a chosen pullback

Source: Stacks Project, Tags 01JX, 01U4 and 0097.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem flatOver_restrict
    {P Q T : Scheme.{u}} (e : P ⟶ Q) [IsOpenImmersion e]
    (b : Q ⟶ T) (M : Q.Modules) (hflat : M.IsFlatOver b) :
    ((Scheme.Modules.restrictFunctor e).obj M).IsFlatOver (e ≫ b) := by
  intro V U hU
  let U' : Q.affineOpens := ⟨e ''ᵁ U.1, U.2.image_of_isOpenImmersion e⟩
  have hU' : U'.1 ≤ b ⁻¹ᵁ V.1 :=
    (e.image_mono (show U.1 ≤ e ⁻¹ᵁ (b ⁻¹ᵁ V.1) from hU)).trans
      (e.image_preimage_le _)
  have hh := hflat V U' hU'
  convert hh using 1 <;> try rfl
  ext r m
  change (M.smul ((e.appIso U.1).inv.hom
    (((e ≫ b).appLE V.1 U.1 hU).hom r))).asHom.hom m =
      (M.smul ((b.appLE V.1 U'.1 hU').hom r)).asHom.hom m
  have he : U.1 ≤ e ⁻¹ᵁ U'.1 := (e.preimage_image_eq U.1).ge
  have hcomp := e.appLE_comp_appLE b V.1 U'.1 U.1 hU' he
  have hring : (e ≫ b).appLE V.1 U.1 hU ≫ (e.appIso U.1).inv =
      b.appLE V.1 U'.1 hU' := by
    rw [← hcomp, Category.assoc, ← Scheme.Hom.appIso_hom', Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg (fun t : Γ(T, V.1) ⟶ Γ(Q, U'.1) ↦ (M.smul (t.hom r)).asHom.hom m) hring

private theorem flatOver_tensorPullback_iso
    {P Q T : Scheme.{u}} (e : P ≅ Q) (b : Q ⟶ T) (M : Q.Modules)
    (hflat : M.IsFlatOver b) :
    ((Scheme.Modules.tensorPullback e.hom).obj M).IsFlatOver (e.hom ≫ b) := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction e.hom
  let δ := adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction e.hom)
  exact (flatOver_restrict e.hom b M hflat).of_iso (δ.app M).symm

private theorem flatOver_of_cartesian_model
    {P Q X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {b : P ⟶ T} {a' : Q ⟶ X} {b' : Q ⟶ T}
    (hp : IsPullback a b f g) (hq : IsPullback a' b' f g) (M : X.Modules)
    (hflat : ((Scheme.Modules.tensorPullback a').obj M).IsFlatOver b') :
    ((Scheme.Modules.tensorPullback a).obj M).IsFlatOver b := by
  let e : P ≅ Q := hp.isoPullback ≪≫ hq.isoPullback.symm
  have ha : e.hom ≫ a' = a := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hq.isoPullback_inv_fst, hp.isoPullback_hom_fst]
  have hb : e.hom ≫ b' = b := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hq.isoPullback_inv_snd, hp.isoPullback_hom_snd]
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom a'
  let δ' : Scheme.Modules.tensorPullback a ≅
      Scheme.Modules.tensorPullback a' ⋙ Scheme.Modules.tensorPullback e.hom :=
    eqToIso (congrArg (fun k ↦ Scheme.Modules.tensorPullback k) ha.symm) ≪≫ δ
  have hP := flatOver_tensorPullback_iso e b'
    ((Scheme.Modules.tensorPullback a').obj M) hflat
  refine Scheme.Modules.IsFlatOver.of_iso (δ'.app M).symm ?_
  simpa only [Functor.comp_obj, hb] using hP

/-- Two cartesian models of the same base change give equivalent relative-flatness tests.
Source: Stacks Project, schemes.tex, Tag 01JX; morphisms.tex, Tag 01U4;
sheaves.tex, Tag 0097.
(blueprint: lem-pc-pullback-model-flatness-comparison).

Proof: the two cartesian squares give a unique isomorphism e:P -> Q preserving both
projections. Tensor-pullback composition identifies a^*M with e^*((a')^*M).
For an affine source open U in P, its image under e is affine in Q; the inverse image
and direct image along e identify sections of these two modules. Naturality of the
structure-sheaf maps, and e followed by b' = b, identify their actions by the base
ring on every affine open V in T. Thus the section modules used in IsFlatOver are
linearly isomorphic over Gamma(T,V), and Module.Flat is invariant under this linear
isomorphism. This proves the forward implication; repeat using e inverse for the
reverse implication. Empty affine opens have zero section modules and cause no
exception. No flatness of f or g and no finite presentation of M is assumed. -/
theorem isFlatOver_tensorPullback_iff_of_isPullback
    {P Q X S T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {b : P ⟶ T} {a' : Q ⟶ X} {b' : Q ⟶ T}
    (hp : IsPullback a b f g) (hq : IsPullback a' b' f g) (M : X.Modules) :
    ((Scheme.Modules.tensorPullback a).obj M).IsFlatOver b ↔
      ((Scheme.Modules.tensorPullback a').obj M).IsFlatOver b' := by
  exact ⟨fun hflat ↦ flatOver_of_cartesian_model hq hp M hflat,
    fun hflat ↦ flatOver_of_cartesian_model hp hq M hflat⟩

end AlgebraicGeometry
