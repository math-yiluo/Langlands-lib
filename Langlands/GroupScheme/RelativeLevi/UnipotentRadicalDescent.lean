import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalConstructions
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Cover transport for relative unipotent radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeLevi

private def squareIso {S S' T T' : Scheme.{u}}
    (a : T ⟶ S) (b : S' ⟶ S) (c : T' ⟶ T) (d : T' ⟶ S')
    (h : c ≫ a = d ≫ b) :
    GroupScheme.baseChange a ⋙ GroupScheme.baseChange c ≅
      GroupScheme.baseChange b ⋙ GroupScheme.baseChange d :=
  (Functor.mapGrpNatIso (Over.pullbackComp c a) ≪≫
    Functor.mapGrpCompIso).symm ≪≫
  eqToIso (congrArg (fun f => GroupScheme.baseChange f) h) ≪≫
  Functor.mapGrpNatIso (Over.pullbackComp d b) ≪≫ Functor.mapGrpCompIso

private theorem radical_square_iff {S S' : Scheme.{u}}
    {k K : Type u} [Field k] [Field K]
    (a : Spec (CommRingCat.of k) ⟶ S) (b : S' ⟶ S)
    (c : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (d : Spec (CommRingCat.of K) ⟶ S') (h : c ≫ a = d ≫ b)
    {U P : GroupScheme S} (r : U ⟶ P) :
    IsUnipotentRadical ((GroupScheme.baseChange c).map
        ((GroupScheme.baseChange a).map r)) ↔
      IsUnipotentRadical ((GroupScheme.baseChange d).map
        ((GroupScheme.baseChange b).map r)) := by
  let e := squareIso a b c d h
  have hn :
      (GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map r) ≫
          (e.app P).hom =
        (e.app U).hom ≫
          (GroupScheme.baseChange d).map ((GroupScheme.baseChange b).map r) :=
    e.hom.naturality r
  constructor
  · intro hr
    have ht := (hr.comp_iso (e.app P)).precomp_iso (e.app U).symm
    simpa only [Iso.symm_hom, hn, Iso.inv_hom_id_assoc] using ht
  · intro hr
    have ht := (hr.precomp_iso (e.app U)).comp_iso (e.app P).symm
    simpa only [Iso.symm_hom, ← Category.assoc, ← hn, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using ht

end RelativeLevi

variable {S S' : Scheme.{u}} {U P : GroupScheme S} {r : U ⟶ P}

/-- An etale base change preserves the full relative radical predicate.
Affineness is imposed on the ambient group, with no restriction on the base. -/
theorem IsRelativeUnipotentRadical.baseChange_etale
    (hr : IsRelativeUnipotentRadical r) [IsAffineHom P.X.hom]
    (b : S' ⟶ S) [Etale b] :
    IsRelativeUnipotentRadical ((GroupScheme.baseChange b).map r) := by
  let : Smooth U.X.hom := hr.smooth
  refine ⟨hr.isClosedSubgroup.baseChange b, ?_, ?_, ?_⟩
  · change Smooth (pullback.snd U.X.hom b)
    infer_instance
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hr.isNormal.baseChange b
  · intro t
    let k := S.residueField (b t)
    let K := S'.residueField t
    let : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
    let : Algebra.IsSeparable k K := inferInstance
    let e : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure K :=
      (IsAlgClosure.equivOfAlgebraic k K (AlgebraicClosure K)
        (AlgebraicClosure k)).symm
    let c := Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)
    have hc : c ≫ geometricPoint S (b t) = geometricPoint S' t ≫ b := by
      change (c ≫ toAlgebraicClosure k) ≫ S.fromSpecResidueField (b t) =
        (toAlgebraicClosure K ≫ S'.fromSpecResidueField t) ≫ b
      have he : c ≫ toAlgebraicClosure k =
          toAlgebraicClosure K ≫ Spec.map (b.residueFieldMap t) := by
        simp only [c, toAlgebraicClosure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
        exact RingHom.ext e.commutes
      rw [he, Category.assoc, b.SpecMap_residueFieldMap_fromSpecResidueField]
      exact (Category.assoc _ _ _).symm
    let : IsAffineHom (Langlands.GroupScheme.geometricFiber P (b t)).X.hom := by
      change IsAffineHom (pullback.snd P.X.hom (geometricPoint S (b t)))
      infer_instance
    exact (RelativeLevi.radical_square_iff (geometricPoint S (b t)) b c
      (geometricPoint S' t) hc r).mp
        ((hr.geometricFiber (b t)).baseChange_ringEquiv e.toRingEquiv)

/-- If an fpqc pullback of a closed subgroup is a relative radical, the
original subgroup is a relative radical. -/
theorem IsRelativeUnipotentRadical.of_baseChange
    [IsAffineHom P.X.hom] (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    (hr : IsRelativeUnipotentRadical ((GroupScheme.baseChange b).map r))
    (hc : IsClosedSubgroup r) : IsRelativeUnipotentRadical r := by
  let : IsClosedImmersion r.hom.hom.left := hc
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  refine ⟨hc, smooth_of_baseChange b U hr.smooth, ?_, ?_⟩
  · apply SubgroupFunctor.isNormal_range_of_baseChange b r
    rw [← SubgroupFunctor.range_baseChangeHom]
    exact hr.isNormal
  · intro s
    obtain ⟨t, rfl⟩ := b.surjective s
    let k := S.residueField (b t)
    let K := S'.residueField t
    let : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
    let c := algebraicClosureBaseMap k K
    have hcomp : c ≫ geometricPoint S (b t) = geometricPoint S' t ≫ b := by
      change (c ≫ toAlgebraicClosure k) ≫ S.fromSpecResidueField (b t) =
        (toAlgebraicClosure K ≫ S'.fromSpecResidueField t) ≫ b
      rw [algebraicClosureBaseMap_comp]
      change (toAlgebraicClosure K ≫ Spec.map (b.residueFieldMap t)) ≫
        S.fromSpecResidueField (b t) = _
      rw [Category.assoc, b.SpecMap_residueFieldMap_fromSpecResidueField]
      exact (Category.assoc _ _ _).symm
    let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
      (algebraicClosureEmbedding k K).toRingHom.toAlgebra
    let : IsAffineHom (Langlands.GroupScheme.geometricFiber P (b t)).X.hom := by
      change IsAffineHom (pullback.snd P.X.hom (geometricPoint S (b t)))
      infer_instance
    apply IsUnipotentRadical.of_baseChange (K := AlgebraicClosure K)
      (hclosed := hc.baseChange (geometricPoint S (b t)))
    exact (RelativeLevi.radical_square_iff (geometricPoint S (b t)) b c
      (geometricPoint S' t) hcomp r).mpr (hr.geometricFiber t)

namespace RelativeLevi

/-- The actual etale pullback radical, together with its inclusion and full
relative radical certificate. -/
def etaleBaseChangeRadical
    (hr : IsRelativeUnipotentRadical r) [IsAffineHom P.X.hom]
    (b : S' ⟶ S) [Etale b] :
    Σ V : GroupScheme S',
      {j : V ⟶ (GroupScheme.baseChange b).obj P // IsRelativeUnipotentRadical j} :=
  ⟨(GroupScheme.baseChange b).obj U, (GroupScheme.baseChange b).map r,
    hr.baseChange_etale b⟩

end RelativeLevi

end Langlands.GroupScheme
