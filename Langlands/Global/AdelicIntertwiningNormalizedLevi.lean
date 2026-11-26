import Langlands.Global.AdelicIntertwiningClosedQuotient
import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.Global.AdelicWeylPositiveTransport
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicInducedInnerProductIntegrable

/-! # Normalized left Levi translation of the adelic intertwining integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P}
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l' : M' ⟶ Q}
  (iU : U ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {c : M' ⟶ M} {π' : Q ⟶ M'}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  (hw : IsWeylConjugation p l q l' w c)
  (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal)
  (hi : IsClosedSubgroup (iU ≫ p)) (hVu : IsUnipotent V)

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))
local notation "H" => intertwiningAdelicStabilizer p iU (iV ≫ q) w
local notation "vMeasure" => intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)
local notation "vRep" => (fun x : LeftCosetSpace
  (intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)) =>
    ((Quotient.out x : Vₐ) : AdelicGroupPoints F G))
local notation "wA" => innerAdelicPoint F G w

/-- The forward Haar scale on the quotient of the target radical by the closed stabilizer. -/
def intertwiningLeviHaarFactor (m : AdelicGroupPoints F M') : ℂ :=
  haveI : LocallyCompactSpace Vₐ :=
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iV ≫ q)).locallyCompactSpace
  haveI : LocallyCompactSpace H :=
    (intertwiningStabilizer p iU (iV ≫ q) w
      (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) hi hVu).1.locallyCompactSpace
  let α := EisensteinConstantTerm.conjAdelic q iV hV (map F M' Q l' m)
  let hα := conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU hV m
  (((mulEquivHaarChar α / mulEquivHaarChar (subgroupAutomorphism H α hα) : ℝ≥0) : ℝ) : ℂ)

variable {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (hK' : IsIwasawaCompact q K) (hπ' : l' ≫ π' = 𝟙 M')
  (hVs : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left)
  (hUu : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
  (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)

include hVs hVc hUu hφc hφ hπ' in
/-- The normalized translation formula, with the three Haar factors isolated on the acting
Levi point. The assumed identity identifies the quotient scale with the ratio of the two
parabolic half moduli. -/
theorem IsIwasawaCompact.intertwiningOperator_normalized_levi
    (m : AdelicGroupPoints F M') (lam : ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G)
    (hHaar : intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
      parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c m)) =
      parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m)) :
    parameterPower F Q (-halfModulusParameter F Q) (map F M' Q l' m) *
        hK.intertwiningOperator hK' iU l iV c π' w φ lam (map F Q G q (map F M' Q l' m) * g) =
      hK'.heightPower (-weylParameter l c π' lam) g *
        ∫ x, (parameterPower F P (-halfModulusParameter F P) (map F M P l (map F M' M c m)) *
          φ (map F P G p (map F M P l (map F M' M c m)) * (wA⁻¹ * (vRep x) * g))) *
          hK.heightPower lam (wA⁻¹ * (vRep x) * g) ∂vMeasure := by
  let mQ := map F M' Q l' m
  let mP := map F M P l (map F M' M c m)
  let α := EisensteinConstantTerm.conjAdelic q iV hV mQ
  let hα := conjAdelic_mem_intertwiningAdelicStabilizer_iff iU iV hw hU hV m
  have hαact (x : Vₐ) : (α x).val = map F Q G q mQ * x.val * (map F Q G q mQ)⁻¹ := rfl
  have hchg := (intertwiningIntegralConjugation p iU (iV ≫ q) w hi hVs hVc hVu
    (map F Q G q mQ) α hα hαact K hK φ hφc hφ hUu lam g).1
  change hK.intertwiningIntegral iU (iV ≫ q) w φ lam (map F Q G q mQ * g) =
    intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
      (∫ x, hK.parameterTwist φ lam (wA⁻¹ * map F Q G q mQ * (vRep x) * g) ∂vMeasure) at hchg
  have hleft (x : AdelicGroupPoints F G) :
      wA⁻¹ * map F Q G q mQ * x = map F P G p mP * (wA⁻¹ * x) := by
    dsimp only [mQ, mP]
    rw [hw.adelic_comp_eq m]
    group
  have harg (x : AdelicGroupPoints F G) :
      wA⁻¹ * map F Q G q mQ * x * g = map F P G p mP * (wA⁻¹ * x * g) := by
    rw [hleft, mul_assoc]
  have hW (s : ComplexCharacterParameter F P) :
      parameterPower F Q (weylParameter l c π' s) mQ = parameterPower F P s mP := by
    rw [weylParameter_power]
    congr 1
    dsimp only [mQ, mP]
    rw [← map_comp_apply_of_hom, ← map_comp_apply_of_hom,
      ← Category.assoc l' π', hπ', Category.id_comp]
  have hcancel (S : GroupScheme (Spec (CommRingCat.of F)))
      (s : ComplexCharacterParameter F S) (x : AdelicGroupPoints F S) :
      parameterPower F S (-s) x * parameterPower F S s x = 1 := by
    simp only [parameterPower, map_neg, LinearMap.neg_apply, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero]
  have hscale : intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
      parameterPower F Q (-halfModulusParameter F Q) mQ =
      parameterPower F P (-halfModulusParameter F P) mP := by
    calc
      _ = parameterPower F Q (-halfModulusParameter F Q) mQ *
          (intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
            (parameterPower F P (-halfModulusParameter F P) mP *
              parameterPower F P (halfModulusParameter F P) mP)) := by rw [hcancel, mul_one, mul_comm]
      _ = (parameterPower F Q (-halfModulusParameter F Q) mQ *
          (intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
            parameterPower F P (halfModulusParameter F P) mP)) *
          parameterPower F P (-halfModulusParameter F P) mP := by ring
      _ = _ := by rw [hHaar, hcancel, one_mul]
  unfold IsIwasawaCompact.intertwiningOperator
  have hWneg : parameterPower F Q (-weylParameter l c π' lam) mQ =
      parameterPower F P (-lam) mP := by rw [← map_neg, hW]
  let f (x : AdelicGroupPoints F G) := φ (map F P G p mP * (wA⁻¹ * x * g)) *
    hK.heightPower lam (wA⁻¹ * x * g)
  have htwist (x : AdelicGroupPoints F G) :
      hK.parameterTwist φ lam (wA⁻¹ * map F Q G q mQ * x * g) =
        parameterPower F P lam mP * f x := by
    rw [harg, IsIwasawaCompact.parameterTwist, hK.heightPower_map_mul]
    dsimp only [f]
    ring
  simp_rw [mul_assoc (parameterPower F P (-halfModulusParameter F P) (map F M P l (map F M' M c m)))]
  change parameterPower F Q (-halfModulusParameter F Q) mQ *
      (hK'.heightPower (-weylParameter l c π' lam) (map F Q G q mQ * g) *
        hK.intertwiningIntegral iU (iV ≫ q) w φ lam (map F Q G q mQ * g)) =
    hK'.heightPower (-weylParameter l c π' lam) g *
      ∫ x, parameterPower F P (-halfModulusParameter F P) mP * f (vRep x) ∂vMeasure
  rw [hchg, hK'.heightPower_map_mul, hWneg]
  simp_rw [htwist, integral_const_mul]
  calc
    _ = hK'.heightPower (-weylParameter l c π' lam) g *
        (intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
          parameterPower F Q (-halfModulusParameter F Q) mQ) *
        (parameterPower F P (-lam) mP * parameterPower F P lam mP) *
        (∫ x, f (vRep x) ∂vMeasure) := by ring
    _ = _ := by rw [hscale, hcancel, mul_one, mul_assoc]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type} [Field F] [NumberField F]
  {L L' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]
  [IsAffine L'.X.left] [LocallyOfFiniteType L'.X.hom]

/-- An isomorphism of Levi groups carries their canonical split components into one another. -/
theorem map_mem_canonicalSubgroup (e : L ≅ L') {a : AdelicGroupPoints F L}
    (ha : a ∈ canonicalSubgroup F L) :
    map F L L' e.hom a ∈ canonicalSubgroup F L' := by
  rw [canonicalSubgroup_eq_imageSubgroup] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  rw [← imageSubgroup_eq_canonicalSubgroup
    ((isSplitComponent_canonicalComponent F L).comp_iso e)]
  exact ⟨t, ht, map_comp_apply_of_hom (p := e.hom) (canonicalComponent F L) t⟩

end Langlands.Global.RestrictionSplitCentre

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions RestrictionSplitCentre

variable {F : Type} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P}
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l' : M' ⟶ Q}
  (iU : U ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {c : M' ⟶ M} {π' : Q ⟶ M'}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  (hw : IsWeylConjugation p l q l' w c)
  (hU : (SubgroupFunctor.range iU).IsNormal) (hV : (SubgroupFunctor.range iV).IsNormal)
  (hi : IsClosedSubgroup (iU ≫ p)) (hVu : IsUnipotent V)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (hK' : IsIwasawaCompact q K) (hπ' : l' ≫ π' = 𝟙 M')
  (hVs : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left)
  (hUu : IsUnipotent U) {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ)
  (hφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ)

include hVs hVc hUu hφc hφ hπ' in
/-- Normalized translation gives equivariance on the canonical target split component. -/
theorem IsIwasawaCompact.intertwiningOperator_splitComponentEquivariant
    (he : IsSplitComponentEquivariant p l φ) (lam : ComplexCharacterParameter F P)
    (hHaar : ∀ m ∈ canonicalSubgroup F M',
      intertwiningLeviHaarFactor iU iV hw hU hV hi hVu m *
        parameterPower F P (halfModulusParameter F P) (map F M P l (map F M' M c m)) =
      parameterPower F Q (halfModulusParameter F Q) (map F M' Q l' m)) :
    IsSplitComponentEquivariant q l' (hK.intertwiningOperator hK' iU l iV c π' w φ lam) := by
  intro m hm g
  let : IsIso c := hw.isIso
  have hc : map F M' M c m ∈ canonicalSubgroup F M := map_mem_canonicalSubgroup (asIso c) hm
  let mQ := map F M' Q l' m
  have hφnorm (x : AdelicGroupPoints F G) :
      parameterPower F P (-halfModulusParameter F P) (map F M P l (map F M' M c m)) *
        φ (map F P G p (map F M P l (map F M' M c m)) * x) = φ x := by
    rw [he _ hc x, ← mul_assoc, ← InducedInnerProductIntegrable.parameterPower_add,
      neg_add_cancel, InducedInnerProductIntegrable.parameterPower_zero, one_mul]
  have hnorm := hK.intertwiningOperator_normalized_levi iU iV hw hU hV hi hVu hK' hπ'
    hVs hVc hUu hφc hφ m lam g (hHaar m hm)
  simp_rw [hφnorm] at hnorm
  have hEq : parameterPower F Q (-halfModulusParameter F Q) mQ *
      hK.intertwiningOperator hK' iU l iV c π' w φ lam (map F Q G q mQ * g) =
      hK.intertwiningOperator hK' iU l iV c π' w φ lam g := hnorm
  rw [← hEq, ← mul_assoc, ← InducedInnerProductIntegrable.parameterPower_add,
    add_neg_cancel, InducedInnerProductIntegrable.parameterPower_zero, one_mul]

end Langlands.Global.AdelicGroupPoints
