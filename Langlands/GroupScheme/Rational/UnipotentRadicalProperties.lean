import Langlands.GroupScheme.Rational.UnipotentRadicalDescent
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SmoothProducts
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Reflection of represented radical properties under field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- Normality of a represented subgroup is reflected by an fpqc change of base. -/
theorem isNormal_range_of_baseChange
    {S S' : Scheme.{u}} {G H : GroupScheme S} (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    (i : H ⟶ G) [Mono i.hom.hom]
    (h : ((range i).baseChange b).IsNormal) : (range i).IsNormal := by
  intro T g x _ hx
  let V : Over S' := (Over.pullback b).obj T
  let q : (Over.map b).obj V ⟶ T :=
    Over.homMk (pullback.fst T.hom b) pullback.condition
  have : EffectiveEpi q.left := by
    change EffectiveEpi (pullback.fst T.hom b)
    infer_instance
  let g' := (baseChangePointsEquiv b G V).symm (q ≫ g)
  let x' := (baseChangePointsEquiv b G V).symm (q ≫ x)
  have hx' : x' ∈ ((range i).baseChange b).carrier V := by
    rw [mem_baseChange]
    simpa only [x', MulEquiv.apply_symm_apply] using (range i).comp_mem q hx
  have hh := h V g' x' (Subgroup.mem_top _) hx'
  rw [mem_baseChange] at hh
  apply mem_range_of_comp_mem_range i q
  simpa only [map_mul, map_inv, g', x', MulEquiv.apply_symm_apply,
    MonObj.comp_mul, GrpObj.comp_inv] using hh

end SubgroupFunctor

section Geometry

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (H : GroupScheme S)

/-- Smoothness of the structure map is reflected by an fpqc change of base. -/
theorem smooth_of_baseChange [QuasiCompact b] [Flat b] [Surjective b]
    (h : Smooth ((GroupScheme.baseChange b).obj H).X.hom) : Smooth H.X.hom :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := H.X.hom) (g := b) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-- Connectedness is reflected by a surjective change of base. -/
theorem connectedSpace_of_baseChange [Surjective b]
    (h : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left) :
    ConnectedSpace H.X.left := by
  change ConnectedSpace (pullback H.X.hom b : Scheme.{u}) at h
  let : ConnectedSpace (pullback H.X.hom b : Scheme.{u}) := h
  exact (pullback.fst H.X.hom b).surjective.connectedSpace
    (pullback.fst H.X.hom b).continuous

end Geometry

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : U ⟶ G}

/-- The greatestness condition reflects from a field extension as soon as the
original inclusion is closed. -/
theorem IsUnipotentRadical.greatest_of_baseChange
    (hi : IsUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i)
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
    (hj : IsClosedSubgroup j) (hs : Smooth H.X.hom)
    (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H)
    (hn : (SubgroupFunctor.range j).IsNormal) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsClosedImmersion i.hom.hom.left := hclosed
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth H.X.hom := hs
  let : ConnectedSpace H.X.left := hc
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  apply SubgroupFunctor.le_range_of_baseChange_le b i
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
  exact hi.greatest ((GroupScheme.baseChange b).obj H)
    ((GroupScheme.baseChange b).map j) (hj.baseChange b)
    (show Smooth (pullback.snd H.X.hom b) from inferInstance)
    (H.connectedSpace_baseChange_of_smooth_affine b) hu.baseChange
    (by rw [SubgroupFunctor.range_baseChangeHom]; exact hn.baseChange b)

/-- A closed inclusion whose field-extension pullback is a represented radical
already satisfies the complete represented radical predicate. -/
theorem IsUnipotentRadical.of_baseChange
    (hi : IsUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (hclosed : IsClosedSubgroup i) : IsUnipotentRadical i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsClosedImmersion i.hom.hom.left := hclosed
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  refine ⟨hclosed, smooth_of_baseChange b U hi.smooth,
    connectedSpace_of_baseChange b U hi.connectedSpace,
    hi.isUnipotent.of_baseChange, ?_, hi.greatest_of_baseChange hclosed⟩
  apply SubgroupFunctor.isNormal_range_of_baseChange b i
  rw [← SubgroupFunctor.range_baseChangeHom]
  exact hi.isNormal

end Field

section SourceIso

variable {k : Type u} [Field k]
    {G U V : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G}

/-- An isomorphic source does not change the image on any relative test scheme. -/
theorem SubgroupFunctor.range_iso_precomp (e : V ≅ U) (i : U ⟶ G) :
    range (e.hom ≫ i) = range i := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [mem_range, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y ≫ e.hom.hom.hom, Category.assoc _ _ _⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ e.inv.hom.hom, ?_⟩
    simp only [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id_assoc]

/-- A represented radical transports through an isomorphism of its source. -/
theorem IsUnipotentRadical.precomp_iso (hi : IsUnipotentRadical i) (e : V ≅ U) :
    IsUnipotentRadical (e.hom ≫ i) := by
  let : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  let : Smooth U.X.hom := hi.smooth
  have hs : Smooth V.X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  have hr := SubgroupFunctor.range_iso_precomp e i
  refine ⟨(IsClosedSubgroup.of_iso e).comp hi.isClosedSubgroup, hs,
    (Scheme.homeoOfIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso e))).connectedSpace_iff.mpr hi.connectedSpace,
    hi.isUnipotent.of_iso e, ?_, ?_⟩
  · rw [hr]
    exact hi.isNormal
  · intro H j hj hsm hc hu hn
    rw [hr]
    exact hi.greatest H j hj hsm hc hu hn

end SourceIso

section FiniteGalois

open Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {U : GroupScheme (Spec (CommRingCat.of L))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}
    (hi : IsUnipotentRadical i)

/-- The previously constructed finite Galois inclusion is a complete
represented ground-field unipotent radical. -/
theorem IsUnipotentRadical.finiteGaloisInclusion_isUnipotentRadical :
    IsUnipotentRadical hi.finiteGaloisInclusion := by
  apply IsUnipotentRadical.of_baseChange (K := L)
    (hclosed := hi.finiteGaloisInclusion_isClosedSubgroup)
  rw [hi.baseChange_finiteGaloisInclusion]
  exact hi.precomp_iso hi.finiteGaloisSolution.iso

/-- An actual radical over the base, its inclusion, and an actual source
isomorphism recovering the supplied radical after finite Galois extension. -/
def IsUnipotentRadical.finiteGaloisRadical :
    Σ U₀ : GroupScheme (Spec (CommRingCat.of k)),
      Σ j : U₀ ⟶ G,
        {e : (GroupScheme.baseChange (algebraBaseMap k L)).obj U₀ ≅ U //
          IsUnipotentRadical j ∧
            (GroupScheme.baseChange (algebraBaseMap k L)).map j = e.hom ≫ i} :=
  ⟨hi.finiteGaloisSolution.obj, hi.finiteGaloisInclusion,
    hi.finiteGaloisSolution.iso, hi.finiteGaloisInclusion_isUnipotentRadical,
    hi.baseChange_finiteGaloisInclusion⟩

end FiniteGalois

end Langlands.GroupScheme
