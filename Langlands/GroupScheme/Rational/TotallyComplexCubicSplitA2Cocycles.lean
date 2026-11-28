import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Langlands.GroupScheme.Rational.CubicSplitTrialitarianTorusFactors
import Langlands.GroupScheme.Rational.NumberFieldCocycleComponentReduction
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexInnerTypeA
import Langlands.GroupScheme.Reductive.PinnedIsoAlignment

/-! # Cocycle vanishing through an anisotropic cubic-split trialitarian torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.CentralSimple

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
set_option maxRecDepth 4000

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {H J : GroupScheme (Spec (CommRingCat.of F))}

local notation "bL" => algebraBaseMap F L
local notation "BL" => GroupScheme.baseChange bL
local notation "U" => GaloisCocycle.cover F L

section Cartan

variable [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  [IsAffineHom J.X.hom] [LocallyOfFiniteType J.X.hom]

omit [FiniteDimensional F L] in
/-- A local group isomorphism on a finite Galois cover identifies the absolute Cartan matrices. -/
theorem LocalGroupIso.exists_cartanEquiv_of_finiteGaloisCover
    (g : LocalGroupIso H J U) (dH : TitsIndexData H) (dJ : TitsIndexData J) :
    ∃ e : dH.Vertex ≃ dJ.Vertex, ∀ a c, dH.cartan a c = dJ.cartan (e a) (e c) := by
  let E := SeparableClosure F
  let emb : L →ₐ[F] E := IsSepClosed.lift
  let : Algebra L E := emb.toRingHom.toAlgebra
  let : IsScalarTower F L E :=
    IsScalarTower.of_algebraMap_eq fun x => (emb.commutes x).symm
  let bE := algebraBaseMap F E
  let : IsAffineHom ((GroupScheme.baseChange bE).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom bE))
  let : IsAffineHom ((GroupScheme.baseChange bE).obj J).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd J.X.hom bE))
  let Eiso : (GroupScheme.baseChange bE).obj H ≅ (GroupScheme.baseChange bE).obj J :=
    (GaloisPointComparison.towerBaseChangeIso F L E H).symm ≪≫
      (GroupScheme.baseChange (algebraBaseMap L E)).mapIso g.toBaseChangeIso ≪≫
        GaloisPointComparison.towerBaseChangeIso F L E J
  obtain ⟨_, _, f, _, _, hf⟩ :=
    dH.pinning.toSplitPinning.exists_inner_comp_based dJ.pinning.toSplitPinning Eiso
  exact ⟨f.indexEquiv.subtypeEquiv hf, fun _ _ => f.toHom.pairing.symm⟩

end Cartan

variable {K : Type u} [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
  [NumberField F] [IsTotallyComplex F]

local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap F K)

section Twist

variable [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- A twisted type-A2 coefficient group has trivial cocycles when the actual
maximal torus carried through the twist splits over a cubic Galois extension. -/
theorem LocalGroupIso.isTrivial_of_innerTypeA2_cubicSplitTorus
    (g : LocalGroupIso H J U) (hscH : IsSimplyConnected H) (dH : TitsIndexData H)
    (hA : dH.HasInnerTypeA 2) (hdeg : Module.finrank F K = 3)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ H) (hi : IsMaximalTorus i) (hT : IsSplitTorus ((BC).obj T).toGrp)
    (ℓ : T.toGrp ⟶ J) (hℓ : (BL).map ℓ = (BL).map i ≫ g.toBaseChangeIso.hom)
    (hn : NumberFieldReducedNormLocalityStatement.{u}) (ζ : Cocycle J U) : ζ.IsTrivial := by
  let gL := g.toBaseChangeIso
  have hscJ := (isSimplyConnected_fieldExtension_iff (K := L) J).mp
    ((isSimplyConnectedFieldExtension F L H hscH).of_iso gL.symm)
  let hJ := hscJ.isSemisimple.isConnectedReductive
  let : IsAffineHom J.X.hom := hJ.isAffineHom
  let : Smooth J.X.hom := hJ.smooth
  let : Smooth H.X.hom := hscH.isSemisimple.isConnectedReductive.smooth
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus _ hi.1
  have hiL := (maximalTorusBaseChange F L H T i hi.1 hi.2.1).mp hi
  have hℓL : IsMaximalTorus (T := (CommGroupScheme.baseChange bL).obj T) ((BL).map ℓ) := by
    rw [hℓ]
    exact hiL.comp_iso gL
  obtain ⟨hs, hf, _⟩ := fieldExtension_fpqc F L
  let : Surjective bL := hs
  let : Flat bL := hf
  have hcl := IsClosedSubgroup.of_baseChange_of_isAffine bL hℓL.2.1
  have hmax := (maximalTorusBaseChange F L J T ℓ hi.1 hcl).mpr hℓL
  obtain ⟨dJ⟩ := titsIndexExistence F J hscJ.isSemisimple
  obtain ⟨v, hv⟩ := g.exists_cartanEquiv_of_finiteGaloisCover dH dJ
  obtain ⟨_, ⟨e, he⟩, _⟩ := hA
  obtain ⟨p, _, _⟩ := exists_galoisPinning_of_splitMaximalTorus hJ ℓ hmax hT
  let emb : K →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra K (SeparableClosure F) := emb.toRingHom.toAlgebra
  let : IsScalarTower F K (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq fun x => (emb.commutes x).symm
  obtain ⟨w, hw, _⟩ := p.exists_titsVertexComparison dJ
  let eJ := w.trans (v.symm.trans e)
  have hCartan (a c : p.base.support) :
      p.rootDatum.pairing a.val c.val = CartanMatrix.A 2 (eJ a) (eJ c) := by
    refine (hw a c).trans ?_
    simpa only [Equiv.apply_symm_apply, eJ, Equiv.trans_apply] using
      (hv (v.symm (w a)) (v.symm (w c))).symm.trans (he (v.symm (w a)) (v.symm (w c)))
  obtain ⟨d, hAbs, hd⟩ := p.exists_innerTypeA2_of_cubicPinning hscJ hdeg eJ hCartan
  exact isTrivial_innerTypeA_of_totallyComplex hn hscJ hAbs d 2 hd ζ

end Twist

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- A cocycle of an anisotropic trialitarian torus split by a cubic field
has trivial image in the ambient group over a totally imaginary number field. -/
theorem Cocycle.isTrivial_map_of_cubicSplitTrialitarianTorus
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a c, d.cartan a c = CartanMatrix.D 4 (e a) (e c))
    (hsc : IsSimplyConnected G) (han : IsAnisotropic G) (hdeg : Module.finrank F K = 3)
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) (hT : IsSplitTorus ((BC).obj T).toGrp)
    (hn : NumberFieldReducedNormLocalityStatement.{u}) (ζ : Cocycle T.toGrp U) :
    (ζ.map t).IsTrivial := by
  obtain ⟨T₁, T₂, H₁, H₂, _, _, _, _, d₁, d₂, p₁, p₂, i₁, i₂, j₁, j₂, act,
    ht₁, _, hTK, _, hsc₁, _, hA₁, hsc₂, ha₂, hA₂, hact, hfix, hprod⟩ :=
    exists_cubicSplitTrialitarianTorusFactors d e hD hsc han hdeg t ht hT
  let α := ζ.map p₁
  let β := ζ.map p₂
  have hβ : (β.map (i₂ ≫ j₂)).IsTrivial := by
    have h := isTrivial_innerTypeA_of_totallyComplex hn hsc₂ ha₂ d₂ 2 hA₂ (β.map i₂)
    obtain ⟨g, hg⟩ := h.map j₂
    refine ⟨g, fun a c => ?_⟩
    change β.toFun a c ≫ (i₂ ≫ j₂).hom.hom = _
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hg a c
  have hα : α.RealLocallyTrivial := fun w hw =>
    (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w) hw).elim
  refine Cocycle.isTrivial_of_component_cocycles_with_firstMap i₁ j₁ (i₂ ≫ j₂)
    hsc₁ act hact hfix (ζ.map t) α β ?_ hα hβ (fun _ _ => hprod _ _)
  intro J' g _ ℓ hℓ δ _
  exact g.isTrivial_of_innerTypeA2_cubicSplitTorus hsc₁ d₁ hA₁ hdeg i₁ ht₁ hTK ℓ hℓ hn δ

end Langlands.GroupScheme
