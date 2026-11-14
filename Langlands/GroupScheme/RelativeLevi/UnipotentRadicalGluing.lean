import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalDescent
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent
import Langlands.GroupScheme.SubgroupFunctor.ClosedCoverDescent

/-! # Gluing relative unipotent radicals on etale covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SubgroupFunctor.CoverDescent

/-- Normality of the descended subgroup follows on every test from normality
of the local subgroup functors. -/
theorem isNormal_subgroup {S : Scheme.{u}} {P : GroupScheme S}
    {K : Precoverage Scheme.{u}} (𝒰 : Scheme.Cover.{u} K S)
    (F : ∀ i, SubgroupFunctor ((GroupScheme.baseChange (𝒰.f i)).obj P))
    (hF : ∀ i, (F i).IsNormal) : (subgroup 𝒰 F).IsNormal := by
  intro T g x hg hx i V a
  simpa only [MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv] using
    hF i V ((baseChangePointsEquiv (𝒰.f i) P V).symm (a ≫ g))
      ((baseChangePointsEquiv (𝒰.f i) P V).symm (a ≫ x))
      (Subgroup.mem_top _) (hx i V a)

end SubgroupFunctor.CoverDescent

/-- A point above the base point suffices to reflect the geometric radical
property of a closed inclusion. -/
theorem IsRelativeUnipotentRadical.geometricFiber_of_baseChange_at
    {S T : Scheme.{u}} {U P : GroupScheme S} {r : U ⟶ P}
    [IsAffineHom P.X.hom] (b : T ⟶ S)
    (hr : IsRelativeUnipotentRadical ((GroupScheme.baseChange b).map r))
    (hc : IsClosedSubgroup r) (t : T) :
    IsUnipotentRadical (RelativeLevi.geometricFiberHom r (b t)) := by
  let k := S.residueField (b t)
  let K := T.residueField t
  let : Algebra k K := (b.residueFieldMap t).hom.toAlgebra
  let c := algebraicClosureBaseMap k K
  have hcomp : c ≫ geometricPoint S (b t) = geometricPoint T t ≫ b := by
    change (c ≫ toAlgebraicClosure k) ≫ S.fromSpecResidueField (b t) =
      (toAlgebraicClosure K ≫ T.fromSpecResidueField t) ≫ b
    rw [algebraicClosureBaseMap_comp]
    change (toAlgebraicClosure K ≫ Spec.map (b.residueFieldMap t)) ≫
      S.fromSpecResidueField (b t) = _
    rw [Category.assoc, b.SpecMap_residueFieldMap_fromSpecResidueField]
    exact (Category.assoc _ _ _).symm
  let e : GroupScheme.baseChange (geometricPoint S (b t)) ⋙ GroupScheme.baseChange c ≅
      GroupScheme.baseChange b ⋙ GroupScheme.baseChange (geometricPoint T t) :=
    (Functor.mapGrpNatIso (Over.pullbackComp c (geometricPoint S (b t))) ≪≫
      Functor.mapGrpCompIso).symm ≪≫
    eqToIso (congrArg (fun f => GroupScheme.baseChange f) hcomp) ≪≫
    Functor.mapGrpNatIso (Over.pullbackComp (geometricPoint T t) b) ≪≫
      Functor.mapGrpCompIso
  have hn :
      (GroupScheme.baseChange c).map
          ((GroupScheme.baseChange (geometricPoint S (b t))).map r) ≫ (e.app P).hom =
        (e.app U).hom ≫ (GroupScheme.baseChange (geometricPoint T t)).map
          ((GroupScheme.baseChange b).map r) := e.hom.naturality r
  have ht := ((hr.geometricFiber t).precomp_iso (e.app U)).comp_iso (e.app P).symm
  have hbase : IsUnipotentRadical ((GroupScheme.baseChange c).map
      ((GroupScheme.baseChange (geometricPoint S (b t))).map r)) := by
    simpa only [Iso.symm_hom, ← Category.assoc, ← hn, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using ht
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  let : IsAffineHom (Langlands.GroupScheme.geometricFiber P (b t)).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom (geometricPoint S (b t)))
    infer_instance
  exact IsUnipotentRadical.of_baseChange (K := AlgebraicClosure K)
    (hclosed := hc.baseChange (geometricPoint S (b t))) hbase

namespace RelativeLevi

/-- Matching relative radicals on an etale cover have an actual global closed
representative carrying the full relative radical certificate. -/
def radicalRepresentativeEtale {S : Scheme.{u}} {P : GroupScheme S}
    [IsAffineHom P.X.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (U : ∀ i, GroupScheme (𝒰.X i))
    (r : ∀ i, U i ⟶ (GroupScheme.baseChange (𝒰.f i)).obj P)
    (hr : ∀ i, IsRelativeUnipotentRadical (r i))
    (hmatch : SubgroupFunctor.CoverDescent.IsMatching 𝒰
      (fun i => SubgroupFunctor.range (r i))) :
    {R : SubgroupFunctor.ClosedRepresentative
      (SubgroupFunctor.CoverDescent.subgroup 𝒰 (fun i => SubgroupFunctor.range (r i))) //
      IsRelativeUnipotentRadical R.hom} := by
  let F := fun i => SubgroupFunctor.range (r i)
  have hc : ∀ i, (F i).IsClosedRepresentable := by
    intro i
    let : IsClosedImmersion (r i).hom.hom.left := (hr i).isClosedSubgroup
    exact ⟨U i, r i, ⟨Over.mono_of_mono_left _, rfl⟩, (hr i).isClosedSubgroup⟩
  let R := SubgroupFunctor.CoverDescent.closedRepresentativeEtale 𝒰 F hmatch hc
  have hlocal (i : 𝒰.I₀) :
      IsRelativeUnipotentRadical ((GroupScheme.baseChange (𝒰.f i)).map R.hom) := by
    apply (hr i).of_range_eq (R.closed.baseChange (𝒰.f i))
    rw [SubgroupFunctor.range_baseChangeHom, R.represents.2,
      SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 F hmatch i]
  refine ⟨R, R.closed, smooth_of_etaleCover 𝒰 R.group (fun i => (hlocal i).smooth), ?_, ?_⟩
  · rw [R.represents.2]
    exact SubgroupFunctor.CoverDescent.isNormal_subgroup 𝒰 F (fun i => (hr i).isNormal)
  · intro s
    obtain ⟨i, t, rfl⟩ := 𝒰.exists_eq s
    exact (hlocal i).geometricFiber_of_baseChange_at (𝒰.f i) R.closed t

end RelativeLevi

end Langlands.GroupScheme
