import Langlands.GroupScheme.Rational.CyclicConjugationCutoff
import Langlands.GroupScheme.RelativeUnipotent.RootWeightEquivariantMap

/-! # Actual root-weight terms as ambient intrinsic conjugation cutoffs -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

open Corepresented AffineLine

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]

/-- Powers in the coefficient torus are the actual coordinate cocharacter. -/
theorem torusPt_powers_eq (v : I → ℤ) (A : CommAlgCat.{u} (CommRingCat.of R))
    (s : Aˣ) :
    torusPt I A (fun k => s ^ v k) =
      unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) s ≫
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I v)).hom.hom := by
  apply (splitTorus.algebraPointsEquiv I A).injective
  rw [torusPt, MulEquiv.apply_symm_apply]
  funext k
  change s ^ v k = Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom
    (splitTorus.pointsEquiv I _
      (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) s ≫
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I v)).hom.hom) k)
  rw [splitTorus.pointsEquiv_exponentCocharacter, map_zpow]
  change s ^ v k = (Gm.affinePointsEquiv
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)) ^ v k
  rw [affinePointsEquiv_unitPoint]

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Corepresented AffineCorepresentation

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)
  {B : CommAlgCat.{u} (CommRingCat.of R)}
  (ψ : (algSpec (CommRingCat.of R)).obj (op B) ≅ G.X)

/-- The original actual term inclusion into the ambient group. -/
def ambientInclusion (d : ℕ) : W.groupScheme d ⟶ G := W.inclusion d ≫ j

/-- The actual positive-term inclusion is equivariant for the realized
cocharacter conjugation on every coefficient algebra. -/
theorem ambientInclusion_equivariant (v : I → ℤ) :
    TorusAction.IsEquivariant
      ((W.termPolynomialTorusAction j hroot hu 0).alongCocharacter v)
      (cyclicConjugationAction ψ (AffineRegularBorel.cocharacter t v))
      (affinePointsTransformation (W.ambientInclusion j 0)) := by
  intro A s x
  rw [cyclicConjugationAction_act]
  let x' : (algSpec (CommRingCat.of R)).obj (op A) ⟶ (W.groupScheme 0).X := x
  let s' := torusPt I A (fun k => s PUnit.unit ^ v k)
  have hi := W.torusAction_inclusion j hroot hu 0 s' x'
  have hc := C.torusAction_comp j hroot hu s' (x' ≫ (W.inclusion 0).hom.hom)
  have h := (congrArg (fun y => y ≫ j.hom.hom) hi).trans hc
  have ht : s' ≫ t.hom.hom =
      AffineLine.unitPoint (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (s PUnit.unit) ≫ (AffineRegularBorel.cocharacter t v).hom.hom := by
    dsimp only [s']
    rw [torusPt_powers_eq, Category.assoc]
    rfl
  rw [ht] at h
  simpa only [s', x', TorusAction.alongCocharacter, termPolynomialTorusAction,
    AutomorphicAction.affineTorusAction, affinePointsTransformation_apply, ambientInclusion,
    Grp.comp_hom_hom, Category.assoc] using h

variable (hj : IsClosedSubgroup j)
  (v : I → ℤ) (q : ℕ) (hq : 0 < q)
  (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k)

include hroot hu hj hq hw in
/-- Restricting the ambient intrinsic cutoff to the actual positive term gives
precisely the original unscaled root-weight cutoff, on every scheme test. -/
theorem ambientCutoff_comap (d : ℕ) :
    (cyclicConjugationCutoff ψ (AffineRegularBorel.cocharacter t v) (q * (d + 1))).comap
      (W.ambientInclusion j 0) = (W.subgroup d).comap (W.inclusion 0) := by
  have hf : IsClosedSubgroup (W.ambientInclusion j 0) :=
    (W.isClosedSubgroup_inclusion 0).comp hj
  have he := intrinsicWeightPreimage_eq_of_isClosedSubgroup
    (W.termChart 0) ψ (W.ambientInclusion j 0) hf
    ((W.termPolynomialTorusAction j hroot hu 0).alongCocharacter v)
    (cyclicConjugationAction ψ (AffineRegularBorel.cocharacter t v))
    (W.ambientInclusion_equivariant j hroot hu ψ v)
    (cyclicTail (fun _ : PUnit => (1 : ℤ)) (q * (d + 1)))
  exact he.trans (W.positiveIntrinsicCutoff_eq_comap j hroot hu v q hq hw d)

variable (hrep : (Dynamic.unipotent (AffineRegularBorel.cocharacter t v)).IsRepresentedBy
  (W.ambientInclusion j 0))

include hroot hu hj hq hw hrep in
/-- Each actual root-weight term has exactly the ambient intrinsic conjugation
cutoff as its range on ALL scheme tests. -/
theorem range_ambientInclusion_eq_cutoff (d : ℕ) :
    SubgroupFunctor.range (W.ambientInclusion j d) =
      cyclicConjugationCutoff ψ (AffineRegularBorel.cocharacter t v) (q * (d + 1)) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  have hc := W.ambientCutoff_comap j hroot hu ψ hj v q hq hw d
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy := W.toPositive_mem d T y
    rw [← hc] at hy
    change (y ≫ (W.toPositive d).hom.hom) ≫ (W.inclusion 0 ≫ j).hom.hom ∈
      (cyclicConjugationCutoff ψ (AffineRegularBorel.cocharacter t v) (q * (d + 1))).carrier T at hy
    rw [Category.assoc, ← Grp.comp_hom_hom, ← Category.assoc,
      W.toPositive_comp] at hy
    exact hy
  · intro hx
    have hxU := cyclicConjugationCutoff_le_unipotent ψ
      (AffineRegularBorel.cocharacter t v) (q * (d + 1))
      (Nat.mul_pos hq (Nat.zero_lt_succ d)) T hx
    rw [← hrep.2] at hxU
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxU
    have hym : y ∈ ((W.subgroup d).comap (W.inclusion 0)).carrier T := by
      rw [← hc]
      exact (show y ≫ (W.ambientInclusion j 0).hom.hom ∈ _ from hy ▸ hx)
    rw [SubgroupFunctor.mem_comap, ← (W.isRepresentedBy_inclusion d).2] at hym
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hym
    refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
    change z ≫ (W.inclusion d ≫ j).hom.hom = x
    rw [Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc]
    exact hy

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
