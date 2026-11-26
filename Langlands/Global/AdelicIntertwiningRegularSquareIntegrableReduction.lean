import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionReduction
import Langlands.Global.AdelicIntertwiningAutomorphyStatement
import Langlands.Global.AdelicIntertwiningScalarKernel
import Langlands.Global.AdelicIntertwiningSquareNorm
import Langlands.Global.AdelicIntertwiningLeviHaarBalance
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Dynamic.ParabolicLieDecomposition

/-! # Square integrability in the regular region -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

private theorem exists_radicalLeviCompact {F : Type} [Field F] [NumberField F]
    {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [Smooth G.X.hom] [IsAffine P.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {l : M ⟶ P} {iU : U ⟶ P}
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (g : AdelicGroupPoints F G) :
    ∃ (u : AdelicGroupPoints F U) (m : AdelicGroupPoints F M) (k : K),
      g = map F U G (iU ≫ p) u * (map F P G p (map F M P l m) * k.val) := by
  let χ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  have : Mono (iU ≫ p).hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion (l ≫ p).hom.hom.left :=
    r.isCompatible.levi.isClosedSubgroup.comp r.isCompatible.parabolic.isClosedSubgroup
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have hP : (Dynamic.parabolic χ).IsRepresentedBy p := ⟨inferInstance, r.parabolic_eq_splitComponentCocharacter⟩
  have hZ : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ p) := ⟨inferInstance, r.levi_eq_splitComponentCocharacter⟩
  have hR : (Dynamic.unipotent χ).IsRepresentedBy (iU ≫ p) := ⟨inferInstance, r.range_comp_radical_eq hU⟩
  have hιU : Dynamic.unipotentToParabolic hP hR = iU :=
    hP.hom_ext (Dynamic.unipotentToParabolic_comp hP hR)
  have hιL : Dynamic.centralizerToParabolic hP hZ = l :=
    hP.hom_ext (Dynamic.centralizerToParabolic_comp hP hZ)
  obtain ⟨x, k, hk, hx⟩ := hK.exists_eq g
  obtain ⟨u, m, hum⟩ := Dynamic.exists_eq_unipotent_mul_centralizer χ hP hZ hR x
  rw [hιU, hιL] at hum
  change x = map F U P iU u * map F M P l m at hum
  refine ⟨u, m, ⟨k, hk⟩, ?_⟩
  rw [← hx, hum, map_mul, mul_assoc, map_comp_apply_of_hom]

/-- Regular automorphy suffices for the square-integrability proposition. -/
def IntertwiningRegularSquareIntegrableReductionStatement : Prop :=
  IntertwiningUniformAutomorphyStatement.{0} → IntertwiningRegularSquareIntegrableStatement

/-- Derive the three conditions of the square-integrability predicate on a common regular
region. -/
theorem intertwiningRegularSquareIntegrable_of_automorphy :
    IntertwiningRegularSquareIntegrableReductionStatement := by
  classical
  intro hauto F _ _ G P M U Q M' V A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT
    q _ iV l' _ a' r' π' w c hG hUR hVR hMul hπ hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  have : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType Q.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := q) ‹IsClosedImmersion q.hom.hom.left›
  have : IsAffineHom V.X.hom := isAffineHom_of_isAffine _
  have : LocallyOfFiniteType V.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := iV ≫ q) ‹IsClosedImmersion (iV ≫ q).hom.hom.left›
  have : Smooth G.X.hom := hG.smooth
  have horiginal := hφ.1
  have hφc := horiginal.2.1.1
  have huφ : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => horiginal.1 x (Subgroup.mem_sup_left hx) g
  have hbal := intertwiningLeviHaarBalance F G P M U Q M' V A A' p iU l a r q iV l' a' r' w c hG hUR hVR hw
  obtain ⟨R₁, J, hJ, h₁⟩ := hauto F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c
    hG hUR r'.isCompatible.parabolic hVR r'.isCompatible.levi hMul hπ hw K hK hK' rho hsmooth hcalc
    φ hmax hrho horiginal
  obtain ⟨R₂, h₂⟩ := intertwiningScalarKernelIntegrable r hA hT hG hUR r'.isCompatible.parabolic
    hVR r'.isCompatible.levi hMul hw hK rho hsmooth hcalc hmax hrho
  refine ⟨max R₁ R₂, fun lam hlam => ?_⟩
  have htarget := (h₁ lam (fun α hα => (le_max_left R₁ R₂).trans_lt (hlam α hα))).1
  have hnorm := hK.intertwiningOperator_integrable_sq_norm iU iV hK' hUR.1.isNormal horiginal.1 hφ.2.1
    hw r.isCompatible.levi.isConnectedReductive r'.isCompatible.levi.isConnectedReductive hφc
    hUR.1.isUnipotent hVR.1.smooth hVR.1.connectedSpace hVR.1.isUnipotent hVR.1.isNormal
    ‹IsClosedImmersion (iU ≫ p).hom.hom.left› hπ (exists_radicalLeviCompact r hUR hK) hbal
    (by simpa only [sq_norm_normalizedLeviValue] using hφ.2.2) lam
    (h₂ lam (fun α hα => (le_max_right R₁ R₂).trans_lt (hlam α hα)))
  refine ⟨htarget, ?_, ?_⟩
  · exact hK.intertwiningOperator_splitComponentEquivariant iU iV hw hUR.1.isNormal hVR.1.isNormal
      ‹IsClosedImmersion (iU ≫ p).hom.hom.left› hVR.1.isUnipotent hK' hπ hVR.1.smooth
      hVR.1.connectedSpace hUR.1.isUnipotent hφc huφ hφ.2.1 lam (fun m _ => hbal m)
  · simpa only [sq_norm_normalizedLeviValue] using hnorm

end Langlands.Global
