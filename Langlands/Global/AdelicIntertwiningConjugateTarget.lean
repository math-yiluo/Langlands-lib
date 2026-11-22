import Langlands.Global.AdelicEisensteinConjugateParabolicHeight
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicSubgroupNormalizedHaarTransport
import Langlands.Global.AdelicWeylSetAssociation

/-! # Rational conjugation of the target of an adelic intertwiner -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- Conjugating the target radical and multiplying the representative on the
left by the same rational point preserves the intertwining integral at the
corresponding left-translated argument. -/
theorem IsIwasawaCompact.intertwiningIntegral_conjugate_target (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (s w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    [IsClosedImmersion (j ≫ (G.innerIso s).hom).hom.hom.left]
    (hU : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU (j ≫ (G.innerIso s).hom) (s * w) φ lam (innerAdelicPoint F G s * g) =
      hK.intertwiningIntegral iU j w φ lam g := by
  let e := G.innerIso s
  let j' := j ≫ e.hom
  let V₀ := SubgroupFunctor.range j
  let V₁ := SubgroupFunctor.range j'
  let t := innerAdelicPoint F G s
  let wA := innerAdelicPoint F G w
  let wB := innerAdelicPoint F G (s * w)
  have hw : wB = t * wA := G.constantPoint_mul s w _
  let : IsClosedImmersion j'.hom.hom.left := inferInstanceAs
    (IsClosedImmersion (j ≫ (G.innerIso s).hom).hom.hom.left)
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V₀ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V₁ : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j'
  have hV : V₀ = V₁.comap e.hom :=
    SubgroupFunctor.range_eq_comap_of_iso_square e (Iso.refl V) (i := j) (i' := j') (by simp [j'])
  obtain ⟨a, ha, harat, hpres⟩ :=
    AdelicSubgroupPoints.exists_adelicSubgroupIso_of_eq_comap F e V₁ V₀ hV
  have hconj (v : AdelicSubgroupPoints.adelicPoints F G V₀) :
      (a v : AdelicGroupPoints F G) = t * (v : AdelicGroupPoints F G) * t⁻¹ :=
    (ha v).trans (affinePointsTarget_innerIso_hom F G s v)
  let Γ := intertwiningRationalSubgroup F p iU j wA
  let Γ' := intertwiningRationalSubgroup F p iU j' wB
  have hstab (v : AdelicSubgroupPoints.adelicPoints F G V₀) : a v ∈ Γ' ↔ v ∈ Γ := by
    change a v ∈ intertwiningRationalSubgroup F p iU j' wB ↔
      v ∈ intertwiningRationalSubgroup F p iU j wA
    rw [mem_intertwiningRationalSubgroup_iff, mem_intertwiningRationalSubgroup_iff, harat v, hconj, hw]
    have heq : (t * wA)⁻¹ * (t * (v : AdelicGroupPoints F G) * t⁻¹) * (t * wA) =
        wA⁻¹ * (v : AdelicGroupPoints F G) * wA := by group
    rw [heq]
  let E := LeftCosetSpace.measurableEquivOfMulEquiv a Γ Γ' hstab
  let : (AdelicSubgroupPoints.normalizedHaarMeasure F G V₁).IsMulLeftInvariant := by
    unfold AdelicSubgroupPoints.normalizedHaarMeasure
    infer_instance
  have hE : MeasurePreserving E (intertwiningMeasure F p iU j wA)
      (intertwiningMeasure F p iU j' wB) :=
    LeftCosetSpace.measurePreserving_discreteQuotientMeasure a Γ Γ' hstab
      (isDiscrete_intertwiningRationalSubgroup F p iU j wA)
      (isDiscrete_intertwiningRationalSubgroup F p iU j' wB) _ _ hpres
  have hcomp (x : LeftCosetSpace Γ) :
      hK.intertwiningIntegrand iU j' (s * w) φ lam (t * g) (E x) =
        hK.intertwiningIntegrand iU j w φ lam g x := by
    induction x using Quotient.inductionOn with
    | _ v =>
      change hK.intertwiningIntegrand iU j' (s * w) φ lam (t * g) (E (LeftCosetSpace.mk Γ v)) =
        hK.intertwiningIntegrand iU j w φ lam g (LeftCosetSpace.mk Γ v)
      calc
        _ = hK.parameterTwist φ lam (wB⁻¹ * (a v : AdelicGroupPoints F G) * (t * g)) :=
          hK.intertwiningIntegrand_mk iU j' (s * w) hU hφ lam (t * g) (a v)
        _ = hK.parameterTwist φ lam (wA⁻¹ * (v : AdelicGroupPoints F G) * g) := by
          rw [hconj, hw]
          congr 1
          group
        _ = _ := (hK.intertwiningIntegrand_mk iU j w hU hφ lam g v).symm
  change (∫ x, hK.intertwiningIntegrand iU j' (s * w) φ lam (t * g) x
        ∂intertwiningMeasure F p iU j' wB) =
    ∫ x, hK.intertwiningIntegrand iU j w φ lam g x ∂intertwiningMeasure F p iU j wA
  rw [← hE.integral_comp E.measurableEmbedding]
  simp_rw [hcomp]
  rfl

end AdelicGroupPoints

/-- Conjugating the target parabolic preserves the Weyl condition after left
multiplication of the representative and changes the normalized operator
only by the target height of the conjugating point. -/
def IntertwiningConjugateTargetStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left]
    (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left] (l' : M' ⟶ Q)
    (π' : Q ⟶ M') (w s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    let q' := q ≫ (G.innerIso s).hom
    ∀ [IsClosedImmersion q'.hom.hom.left] [IsClosedImmersion (iV ≫ q').hom.hom.left],
      IsWeylConjugation p l q l' w c → IsUnipotent U →
      ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
        (hQ : IsIwasawaCompact q K) (φ : AdelicGroupPoints F G → ℂ),
        IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ →
        IsWeylConjugation p l q' l' (s * w) c ∧
        ∃ hQ' : IsIwasawaCompact q' K, ∀ lam g,
          hK.intertwiningOperator hQ' iU l iV c π' (s * w) φ lam (innerAdelicPoint F G s * g) =
            hQ'.heightPower (-weylParameter l c π' lam) (innerAdelicPoint F G s) *
              hK.intertwiningOperator hQ iU l iV c π' w φ lam g

theorem intertwiningConjugateTarget : IntertwiningConjugateTargetStatement.{u} := by
  intro F _ _ G P M U Q M' V _ _ _ _ _ p _ iU l q _ iV _ l' π' w s c q' _ _
    hw hU K hK hQ φ hφ
  have hw' : IsWeylConjugation p l q' l' (s * w) c := ⟨hw.isIso, by
    simpa only [q', Category.assoc, innerIso_mul_inv, Iso.hom_inv_id_assoc] using hw.comp_eq⟩
  obtain ⟨hQ', hheight⟩ := eisensteinConjugateParabolicHeight F G Q q s K hQ
  refine ⟨hw', hQ', fun lam g => ?_⟩
  have hclosed : IsClosedImmersion ((iV ≫ q) ≫ (G.innerIso s).hom).hom.hom.left := by
    rw [Category.assoc]
    infer_instance
  have hI : hK.intertwiningIntegral iU (iV ≫ q') (s * w) φ lam (innerAdelicPoint F G s * g) =
      hK.intertwiningIntegral iU (iV ≫ q) w φ lam g := by
    dsimp only [q']
    simpa only [Category.assoc] using
      hK.intertwiningIntegral_conjugate_target iU (iV ≫ q) s w hU hφ lam g
  unfold IsIwasawaCompact.intertwiningOperator
  rw [hheight, hI]
  ring

end Langlands.Global
