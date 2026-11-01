import Langlands.AlgebraicGeometry.Picard.DualBaseChangeCoherence
import Langlands.AlgebraicGeometry.Picard.RationalDualPullbackBaseChange

/-! # Coherence of actual dual abelian-scheme and rational polarization pullback -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (compatibility : DualAbelianBaseChangeStatement.{u})
  {S : Scheme.{u}} (A : AbelianScheme S)
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

section DualIso

variable {B : AbelianScheme S}
  (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualAB" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation
  MA evaluationA stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dualBA" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation
  MB evaluationB stability composition unitCoherence associativity comparison symmetry
  hA geometryA MA evaluationA

/-- Dualize an actual abelian-scheme isomorphism between specified dual
evaluation constructions. Both inverse laws follow from actual dual functoriality. -/
def dualAbelianSchemeIsoFromEvaluation (e : A ≅ B) : DB ≅ DA where
  hom := dualAB e.hom
  inv := dualBA e.inv
  hom_inv_id := by
    rw [← dualAbelianSchemeMapFromEvaluation_comp, e.inv_hom_id,
      dualAbelianSchemeMapFromEvaluation_id]
  inv_hom_id := by
    rw [← dualAbelianSchemeMapFromEvaluation_comp, e.hom_inv_id,
      dualAbelianSchemeMapFromEvaluation_id]

end DualIso

section Identity

variable
  (hAi : HasDualScheme ((baseChange (𝟙 S)).obj A))
  (geometryAi : DualSchemeGeometry ((baseChange (𝟙 S)).obj A) hAi)
  (MAi : LineBundle ((relativeSpace ((baseChange (𝟙 S)).obj A).X.hom).obj
    (dualScheme ((baseChange (𝟙 S)).obj A) hAi)))
  (evaluationAi : tensorObj (poincareFamily ((baseChange (𝟙 S)).obj A) hAi).obj.carrier
    MAi.obj ≅ structureSheaf ((relativeSpace ((baseChange (𝟙 S)).obj A).X.hom).obj
      (dualScheme ((baseChange (𝟙 S)).obj A) hAi)))

local notation "betaI" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility (𝟙 S) A
  hA geometryA MA evaluationA hAi geometryAi MAi evaluationAi
local notation "dualId" => dualAbelianSchemeIsoFromEvaluation preservation stability
  composition unitCoherence associativity comparison symmetry
  (Functor.obj (baseChange (𝟙 S)) A) hAi geometryAi MAi evaluationAi
  hA geometryA MA evaluationA (baseChangeIdIso A)
local notation "DAi" => dualAbelianSchemeFromEvaluation
  (Functor.obj (baseChange (𝟙 S)) A) hAi geometryAi preservation MAi evaluationAi
  stability composition unitCoherence associativity comparison symmetry
local notation "pullI" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility (𝟙 S) A
  hA geometryA MA evaluationA hAi geometryAi MAi evaluationAi
local notation "mapI" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility (𝟙 S) A
  hA geometryA MA evaluationA hAi geometryAi MAi evaluationAi

/-- Canonical identity base change on the actual constructed dual is the
identity comparison followed by the dual of the actual identity comparison. -/
lemma dualAbelianBaseChangeIso_id :
    (betaI).hom = (baseChangeIdIso DA).hom ≫ (dualId).hom := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  rw [dualAbelianBaseChangeIso_hom]
  exact dualSchemeBaseChangeIso_id A stability universality hA hAi

/-- The actual integral dual-valued map at identity pullback is geometric
pullback along the canonical identity comparison. -/
lemma dualAbelianBaseChangeMap_id (lam : A ⟶ DA) :
    mapI lam = (baseChangeIdIso A).hom ≫ lam ≫ (dualId).hom := by
  have hn : (baseChange (𝟙 S)).map lam ≫ (baseChangeIdIso DA).hom =
      (baseChangeIdIso A).hom ≫ lam := baseChangeIdNatIso.hom.naturality lam
  change (baseChange (𝟙 S)).map lam ≫ (betaI).hom = _
  rw [dualAbelianBaseChangeIso_id, ← Category.assoc, hn, Category.assoc]

/-- Identity pullback of every actual rational dual-valued map is geometric
pullback by the canonical abelian-scheme identity comparison. -/
theorem rationalDualBaseChangeHom_id (lam : Hom0 A DA) :
    pullI lam =
      comp0 _ _ _ (comp0 _ _ _ (homToHom0 (baseChangeIdIso A).hom) lam)
        (homToHom0 (dualId).hom) := by
  induction lam using TensorProduct.inductionOn with
  | tmul q f =>
      simp only [rationalDualBaseChangeHom_apply, rationalBaseChangeHom_tmul,
        homToHom0_apply, comp0_tmul, one_mul, mul_one]
      exact congrArg (fun g => q ⊗ₜ[ℤ] g)
        (dualAbelianBaseChangeMap_id preservation stability composition unitCoherence
          associativity comparison symmetry universality compatibility A hA geometryA MA
          evaluationA hAi geometryAi MAi evaluationAi f)
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The actual identity comparison has geometric rational polarization multiplier
one for every rational dual-valued map. -/
theorem rationalDualBaseChangeHom_id_multiple
    (additivity : DualSchemeMapAdditivity preservation stability
      ((baseChange (𝟙 S)).obj A) A hAi hA)
    (lam : Hom0 A DA) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hAi hA geometryAi geometryA MAi evaluationAi MA evaluationA
      additivity 1 (homToHom0 (baseChangeIdIso A).hom) (pullI lam) lam := by
  change comp0 _ _ _
    (comp0 _ _ _ (homToHom0 (baseChangeIdIso A).hom) lam)
    (dualHom0 preservation composition unitCoherence associativity comparison symmetry
      stability hAi hA additivity MAi evaluationAi MA evaluationA geometryAi geometryA
      (homToHom0 (baseChangeIdIso A).hom)) = 1 • pullI lam
  rw [dualHom0_homToHom0, one_smul]
  exact (rationalDualBaseChangeHom_id preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility A hA geometryA MA
    evaluationA hAi geometryAi MAi evaluationAi lam).symm

end Identity

section Composition

variable {S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')
  (hAb : HasDualScheme ((baseChange b).obj A))
  (geometryAb : DualSchemeGeometry ((baseChange b).obj A) hAb)
  (MAb : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hAb)))
  (evaluationAb : tensorObj (poincareFamily ((baseChange b).obj A) hAb).obj.carrier
    MAb.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hAb)))
  (hAd : HasDualScheme ((baseChange (c ≫ b)).obj A))
  (geometryAd : DualSchemeGeometry ((baseChange (c ≫ b)).obj A) hAd)
  (MAd : LineBundle ((relativeSpace ((baseChange (c ≫ b)).obj A).X.hom).obj
    (dualScheme ((baseChange (c ≫ b)).obj A) hAd)))
  (evaluationAd : tensorObj (poincareFamily ((baseChange (c ≫ b)).obj A) hAd).obj.carrier
    MAd.obj ≅ structureSheaf ((relativeSpace ((baseChange (c ≫ b)).obj A).X.hom).obj
      (dualScheme ((baseChange (c ≫ b)).obj A) hAd)))
  (hAc : HasDualScheme ((baseChange c).obj ((baseChange b).obj A)))
  (geometryAc : DualSchemeGeometry ((baseChange c).obj ((baseChange b).obj A)) hAc)
  (MAc : LineBundle ((relativeSpace ((baseChange c).obj ((baseChange b).obj A)).X.hom).obj
    (dualScheme ((baseChange c).obj ((baseChange b).obj A)) hAc)))
  (evaluationAc : tensorObj
    (poincareFamily ((baseChange c).obj ((baseChange b).obj A)) hAc).obj.carrier
    MAc.obj ≅ structureSheaf
      ((relativeSpace ((baseChange c).obj ((baseChange b).obj A)).X.hom).obj
        (dualScheme ((baseChange c).obj ((baseChange b).obj A)) hAc)))

local notation "betaB" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
local notation "betaC" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility c
  (Functor.obj (baseChange b) A) hAb geometryAb MAb evaluationAb hAc geometryAc MAc evaluationAc
local notation "betaD" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility (c ≫ b) A
  hA geometryA MA evaluationA hAd geometryAd MAd evaluationAd
local notation "dualComp" => dualAbelianSchemeIsoFromEvaluation preservation stability
  composition unitCoherence associativity comparison symmetry
  (Functor.obj (baseChange (c ≫ b)) A) hAd geometryAd MAd evaluationAd
  hAc geometryAc MAc evaluationAc (baseChangeCompIso b c A)
local notation "DAb" => dualAbelianSchemeFromEvaluation (Functor.obj (baseChange b) A)
  hAb geometryAb preservation MAb evaluationAb stability composition unitCoherence
  associativity comparison symmetry
local notation "DAd" => dualAbelianSchemeFromEvaluation (Functor.obj (baseChange (c ≫ b)) A)
  hAd geometryAd preservation MAd evaluationAd stability composition unitCoherence
  associativity comparison symmetry
local notation "DAc" => dualAbelianSchemeFromEvaluation
  (Functor.obj (baseChange c) (Functor.obj (baseChange b) A))
  hAc geometryAc preservation MAc evaluationAc stability composition unitCoherence
  associativity comparison symmetry
local notation "pullB" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
local notation "pullC" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility c
  (Functor.obj (baseChange b) A) hAb geometryAb MAb evaluationAb hAc geometryAc MAc evaluationAc
local notation "pullD" => rationalDualBaseChangeHom preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility (c ≫ b) A
  hA geometryA MA evaluationA hAd geometryAd MAd evaluationAd
local notation "mapB" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hAb geometryAb MAb evaluationAb
local notation "mapC" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility c
  (Functor.obj (baseChange b) A) hAb geometryAb MAb evaluationAb hAc geometryAc MAc evaluationAc
local notation "mapD" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility (c ≫ b) A
  hA geometryA MA evaluationA hAd geometryAd MAd evaluationAd

/-- Successive actual dual comparisons agree with direct pullback after the
inverse base comparison and the dual inverse abelian-scheme comparison. -/
lemma dualAbelianBaseChangeIso_comp_inv :
    (baseChange c).map (betaB).hom ≫ (betaC).hom =
      (baseChangeCompIso b c DA).inv ≫ (betaD).hom ≫ (dualComp).inv := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  change (Over.pullback c).map (groupHom (betaB).hom).hom.hom ≫
      (groupHom (betaC).hom).hom.hom =
    (Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
      (groupHom (betaD).hom).hom.hom ≫
        dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd
  rw [dualAbelianBaseChangeIso_hom, dualAbelianBaseChangeIso_hom,
    dualAbelianBaseChangeIso_hom]
  exact dualSchemeBaseChangeIso_comp_inv A b c stability universality hA hAb hAd hAc

/-- The direct-to-successive comparison commutes with actual dual abelian
base change, with every evaluation construction retained. -/
lemma dualAbelianBaseChangeIso_comp :
    (baseChangeCompIso b c DA).hom ≫
        (baseChange c).map (betaB).hom ≫ (betaC).hom =
      (betaD).hom ≫ (dualComp).inv := by
  rw [dualAbelianBaseChangeIso_comp_inv preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility A hA geometryA MA evaluationA
    b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
    hAc geometryAc MAc evaluationAc]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Direct and successive actual integral dual-valued pullback commute with the
canonical source comparison and its contravariant dual inverse. -/
lemma dualAbelianBaseChangeMap_comp (lam : A ⟶ DA) :
    (baseChangeCompIso b c A).hom ≫ mapC (mapB lam) =
      mapD lam ≫ (dualComp).inv := by
  have hn : (baseChange (c ≫ b)).map lam ≫ (baseChangeCompIso b c DA).hom =
      (baseChangeCompIso b c A).hom ≫ (baseChange c).map ((baseChange b).map lam) :=
    (baseChangeCompNatIso b c).hom.naturality lam
  calc
    _ = ((baseChangeCompIso b c A).hom ≫
        (baseChange c).map ((baseChange b).map lam)) ≫
          ((baseChange c).map (betaB).hom ≫ (betaC).hom) := by
      simp only [dualAbelianBaseChangeMap, Functor.map_comp, Category.assoc]
    _ = ((baseChange (c ≫ b)).map lam ≫ (baseChangeCompIso b c DA).hom) ≫
          ((baseChange c).map (betaB).hom ≫ (betaC).hom) := by
      rw [← hn]
    _ = _ := by
      rw [Category.assoc,
        dualAbelianBaseChangeIso_comp preservation stability composition unitCoherence
          associativity comparison symmetry universality compatibility A hA geometryA MA
          evaluationA b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
          hAc geometryAc MAc evaluationAc]
      rfl

/-- Successive integral pullback is direct integral pullback transported by both
directions of the actual abelian-scheme base comparison. -/
lemma dualAbelianBaseChangeMap_comp_inv (lam : A ⟶ DA) :
    mapC (mapB lam) =
      (baseChangeCompIso b c A).inv ≫ mapD lam ≫ (dualComp).inv := by
  calc
    _ = (baseChangeCompIso b c A).inv ≫
        ((baseChangeCompIso b c A).hom ≫ mapC (mapB lam)) := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = _ := by
      rw [dualAbelianBaseChangeMap_comp preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility A hA geometryA MA
        evaluationA b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
        hAc geometryAc MAc evaluationAc]

/-- Pulling the successive integral map back by the direct-to-successive
comparison recovers the direct map. -/
lemma dualAbelianBaseChangeMap_comp_pullback (lam : A ⟶ DA) :
    ((baseChangeCompIso b c A).hom ≫ mapC (mapB lam)) ≫ (dualComp).hom =
      mapD lam := by
  rw [dualAbelianBaseChangeMap_comp preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility A hA geometryA MA
    evaluationA b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
    hAc geometryAc MAc evaluationAc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Direct and successive pullback commute on actual rational dual-valued
homomorphisms after the source and contravariant dual comparisons. -/
theorem rationalDualBaseChangeHom_comp (lam : Hom0 A DA) :
    comp0 _ _ _ (homToHom0 (baseChangeCompIso b c A).hom) (pullC (pullB lam)) =
      comp0 _ _ _ (pullD lam) (homToHom0 (dualComp).inv) := by
  induction lam using TensorProduct.inductionOn with
  | tmul q f =>
      simp only [rationalDualBaseChangeHom_apply, rationalBaseChangeHom_tmul,
        homToHom0_apply, comp0_tmul, one_mul, mul_one]
      exact congrArg (fun g => q ⊗ₜ[ℤ] g)
        (dualAbelianBaseChangeMap_comp preservation stability composition unitCoherence
          associativity comparison symmetry universality compatibility A hA geometryA MA
          evaluationA b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
          hAc geometryAc MAc evaluationAc f)
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Successive rational pullback is the direct map transported by the actual
inverse source comparison and its actual contravariant dual. -/
theorem rationalDualBaseChangeHom_comp_inv (lam : Hom0 A DA) :
    pullC (pullB lam) =
      comp0 _ _ _ (homToHom0 (baseChangeCompIso b c A).inv)
        (comp0 _ _ _ (pullD lam) (homToHom0 (dualComp).inv)) := by
  induction lam using TensorProduct.inductionOn with
  | tmul q f =>
      simp only [rationalDualBaseChangeHom_apply, rationalBaseChangeHom_tmul,
        homToHom0_apply, comp0_tmul, one_mul, mul_one]
      exact congrArg (fun g => q ⊗ₜ[ℤ] g)
        (dualAbelianBaseChangeMap_comp_inv preservation stability composition unitCoherence
          associativity comparison symmetry universality compatibility A hA geometryA MA
          evaluationA b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
          hAc geometryAc MAc evaluationAc f)
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The actual direct-to-successive comparison has rational geometric
polarization multiplier one. The dual is the existing constructed dualHom0. -/
theorem rationalDualBaseChangeHom_comp_multiple
    (additivity : DualSchemeMapAdditivity preservation stability
      ((baseChange (c ≫ b)).obj A) ((baseChange c).obj ((baseChange b).obj A)) hAd hAc)
    (lam : Hom0 A DA) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hAd hAc geometryAd geometryAc MAd evaluationAd MAc evaluationAc
      additivity 1 (homToHom0 (baseChangeCompIso b c A).hom) (pullD lam)
      (pullC (pullB lam)) := by
  change comp0 _ _ _
    (comp0 _ _ _ (homToHom0 (baseChangeCompIso b c A).hom) (pullC (pullB lam)))
    (dualHom0 preservation composition unitCoherence associativity comparison symmetry
      stability hAd hAc additivity MAd evaluationAd MAc evaluationAc geometryAd geometryAc
      (homToHom0 (baseChangeCompIso b c A).hom)) = 1 • pullD lam
  rw [dualHom0_homToHom0, one_smul]
  change comp0 _ _ _
    (comp0 _ _ _ (homToHom0 (baseChangeCompIso b c A).hom) (pullC (pullB lam)))
    (homToHom0 (dualComp).hom) = pullD lam
  rw [rationalDualBaseChangeHom_comp preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility A hA geometryA MA
    evaluationA b c hAb geometryAb MAb evaluationAb hAd geometryAd MAd evaluationAd
    hAc geometryAc MAc evaluationAc]
  rw [comp0_assoc, comp0_homToHom0, Iso.inv_hom_id, homToHom0_id, comp0_id0]

end Composition

end Langlands.AbelianScheme
