import Langlands.GroupScheme.Rational.QuadraticOppositeTorusCell
import Langlands.GroupScheme.Rational.QuadraticRealCocycleComparison
import Langlands.GroupScheme.Rational.DynamicCocharacterTower
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.RationalCocharacterRealization
import Langlands.GroupScheme.Rational.TypeD4StarOpposition
import Langlands.GroupScheme.Torus.CocharacterFieldTransport
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Reductive.InnerTitsObstructionTransport

/-! # Absolute pinnings adapted to a quadratic opposite-Borel torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open StarActionFiniteStage MultiplicativeTypeAbsoluteEquivalence
open Langlands.RootDatumNegation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000

section RegularDirection

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : T.toGrp ⟶ G)

local notation "E" => SeparableClosure F
local notation "c" => algebraBaseMap F E
local notation "GE" => Functor.obj (GroupScheme.baseChange c) G
local notation "TE" => Functor.obj (CommGroupScheme.baseChange c) T
local notation "tE" => CategoryTheory.Functor.map (GroupScheme.baseChange c) t

local instance upperAffine : IsAffineHom (GE).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom c))

local instance upperFiniteType : LocallyOfFiniteType (GE).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom c))

private theorem exists_regular_oppositeDirection
    (Q : IntermediateField F (SeparableClosure F)) [FiniteDimensional F Q] [IsGalois F Q]
    (hQ : Module.finrank F Q = 2) (hG : IsConnectedReductive G)
    (ht : IsQuadraticOppositeBorelTorus (Q := Q) t) :
    ∃ νE : cocharacterLattice (TE), IsGenericCocharacter (tE) νE ∧
      ∀ τ : E ≃ₐ[F] E,
        let νσ := cocharacterLattice.galoisRepresentation F E T τ νE
        Dynamic.unipotent (CommGroupScheme.groupHom νσ ≫ tE) =
          Dynamic.unipotent (CommGroupScheme.groupHom νE ≫ tE) ∨
        Dynamic.unipotent (CommGroupScheme.groupHom νσ ≫ tE) =
          Dynamic.unipotent (CommGroupScheme.groupHom (-νE) ≫ tE) := by
  let b := algebraBaseMap F Q
  let tQ := (GroupScheme.baseChange b).map t
  let : Smooth G.X.hom := hG.smooth
  have hGE := connectedReductiveFieldExtensionStatement F E G hG
  let : Smooth (GE).X.hom := hGE.smooth
  have hT := GaloisPinningData.isSplitTorus_separableClosure T ht.2.1.1
  have hMax := (maximalTorusBaseChange F E G T t ht.2.1.1 ht.2.1.2.1).mp ht.2.1
  obtain ⟨σ, ν, hσ, hC, hU⟩ := ht.exists_torusDynamicData hG
  let extendDirection := cocharacterLattice.towerExtension F Q E T
  let νE := extendDirection ν
  have hCE : Dynamic.centralizer (CommGroupScheme.groupHom νE ≫ tE) =
      SubgroupFunctor.range (tE) := centralizer_towerExtension t ν hC
  have hreg : IsGenericCocharacter (tE) νE :=
    RationalCocharacter.isGenericCocharacter_of_centralizer_eq_torusCentralizer
      hT (tE) νE (hCE.trans (maximalTorusCentralizer E (GE) hGE (TE) (tE) hMax).symm)
  refine ⟨νE, hreg, fun τ => ?_⟩
  let transport := SubgroupFunctor.towerBaseChange b (algebraBaseMap Q E)
    c (algebraBaseMap_tower Q E) G
  let U := Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ tQ)
  have hUpper : Dynamic.unipotent (CommGroupScheme.groupHom νE ≫ tE) = transport U :=
    unipotent_towerExtension t ν
  have hτ :=
    (unipotent_galoisRepresentation t τ νE).trans
      ((congrArg (SubgroupFunctor.galoisTransport F E G τ) hUpper).trans
        (SubgroupFunctor.towerBaseChange_galoisTransport Q G τ U).symm)
  rcases GaloisCocycle.quadratic_aut_eq_one_or hQ σ hσ (τ.restrictNormal Q) with hs | hs
  · refine Or.inl (hτ.trans ?_)
    change transport (SubgroupFunctor.galoisTransport F Q G (τ.restrictNormal Q) U) = _
    rw [hs, map_one]
    exact hUpper.symm
  · refine Or.inr (hτ.trans ?_)
    change transport (SubgroupFunctor.galoisTransport F Q G (τ.restrictNormal Q) U) = _
    rw [hs, show SubgroupFunctor.galoisTransport F Q G σ U =
      Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ tQ))
      from hU, ← groupHom_neg_comp_eq_oppositeCocharacter tQ ν]
    have hneg : Dynamic.unipotent (CommGroupScheme.groupHom (extendDirection (-ν)) ≫ tE) =
        transport (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ tQ)) :=
      unipotent_towerExtension t (-ν)
    rw [map_neg] at hneg
    exact hneg.symm

end RegularDirection

section Comparisons

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

private theorem exists_basedEquiv_sameGroup (p q : GaloisPinningData F E G) :
    ∃ e : RootPairing.Equiv p.toSplitPinning.rootDatum q.toSplitPinning.rootDatum,
      (∀ a, a ∈ p.toSplitPinning.base.support ↔ e.indexEquiv a ∈ q.toSplitPinning.base.support) ∧
      ∀ σ : E ≃ₐ[F] E, e.comp (p.starAction σ).val = (q.starAction σ).val.comp e := by
  let H := (GroupScheme.baseChange (algebraBaseMap F E)).mapIso (Iso.refl G)
  apply InnerFormStarForward.exists_basedEquiv_of_innerEquivalent_pullIso p q H
  intro σ
  have h : Descent.pullIso (galoisBaseMap F E σ) (galoisBaseMap_over F E σ)
      (galoisBaseMap_over F E σ) H = H := by
    apply Iso.ext
    exact Descent.pullHom_map _ _ _ _ (𝟙 G)
  rw [h]
  exact IsFppfInnerEquivalent.refl H

end Comparisons

section Pinning

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : T.toGrp ⟶ G)

local notation "E" => SeparableClosure F
local notation "c" => algebraBaseMap F E
local notation "GE" => Functor.obj (GroupScheme.baseChange c) G
local notation "TE" => Functor.obj (CommGroupScheme.baseChange c) T
local notation "tE" => CategoryTheory.Functor.map (GroupScheme.baseChange c) t

attribute [local instance] upperAffine upperFiniteType

/-- The root datum of the supplied opposite-Borel torus has a base with
the same Cartan and star action as the original index. Its ordinary
Galois action equals the star action up to simultaneous negation. -/
theorem exists_quadraticOppositeBorelPinning
    (Q : IntermediateField F (SeparableClosure F)) [FiniteDimensional F Q] [IsGalois F Q]
    (hQ : Module.finrank F Q = 2) (hsc : IsSimplyConnected G)
    (ht : IsQuadraticOppositeBorelTorus (Q := Q) t) (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 4) (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b)) :
    ∃ (p : GaloisPinningData F E G) (eT : p.torus ≅ T),
      CommGroupScheme.groupHom eT.hom ≫ t = p.inclusion ∧
      ∃ v : d.Vertex ≃ p.base.support,
        (∀ a b, p.rootDatum.pairing (v a).val (v b).val = d.cartan a b) ∧
        (∀ σ a, (v (d.star σ a)).val = (p.starAction σ).val.indexEquiv (v a).val) ∧
        ∀ σ : E ≃ₐ[F] E, p.galoisAction σ = (p.starAction σ).val ∨
          p.galoisAction σ = negAut p.toSplitPinning.rootDatum * (p.starAction σ).val := by
  let hG := hsc.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  have hGE := connectedReductiveFieldExtensionStatement F E G hG
  let : Smooth (GE).X.hom := hGE.smooth
  have hT := GaloisPinningData.isSplitTorus_separableClosure T ht.2.1.1
  have hMax := (maximalTorusBaseChange F E G T t ht.2.1.1 ht.2.1.2.1).mp ht.2.1
  obtain ⟨ν, hν, hOpp⟩ := exists_regular_oppositeDirection t Q hQ hG ht
  obtain ⟨J, hJ, P, hP, hRed⟩ := rootDatumExistence E (GE) hGE (TE) hT (tE) hMax
  let : Finite J := hJ
  let : P.IsReduced := hRed
  have hroot (a : J) : P.root a ∈ relativeRoots (tE) := by
    rw [relativeRoots_eq_roots, ← hP.2.1]
    exact Set.mem_range_self a
  have hν' (a : J) : P.root' a ν ≠ 0 := by
    change P.toLinearMap (P.root a) ν ≠ 0
    rw [hP.1]
    exact hν _ (hroot a)
  let Δ := IsRootDatumOf.regularCocharacterBase F E (P := P) ν hν'
  let p : GaloisPinningData F E G :=
    { torus := T
      inclusion := t
      isConnectedReductive := hGE
      isSplitTorus := hT
      isMaximalTorus := hMax
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hRed
      base := Δ
      pinning := RootPinning.ofSplitMaximalTorus hGE hT _ hMax P hP Δ }
  obtain ⟨f, hf, hstar⟩ := exists_basedEquiv_sameGroup d.pinning p
  let v : d.Vertex ≃ p.base.support := f.indexEquiv.subtypeEquiv hf
  have hcartan (a b : d.Vertex) : p.rootDatum.pairing (v a).val (v b).val = d.cartan a b :=
    f.toHom.pairing
  have hstars (σ : E ≃ₐ[F] E) (a : d.Vertex) :
      (v (d.star σ a)).val = (p.starAction σ).val.indexEquiv (v a).val :=
    congrArg (fun z : RootPairing.Equiv d.pinning.rootDatum p.rootDatum =>
      z.indexEquiv a.val) (hstar σ)
  refine ⟨p, Iso.refl _, by change 𝟙 T.toGrp ≫ t = t; exact Category.id_comp t,
    v, hcartan, hstars, fun σ => ?_⟩
  let A : P.Aut := p.galoisAction σ
  let νσ := cocharacterLattice.galoisRepresentation F E T σ ν
  have hPair (j : J) : latticePairing (TE) (P.root (A.indexEquiv j)) νσ =
      latticePairing (TE) (P.root j) ν := by
    have he : P.root (A.indexEquiv j) =
        characterLattice.galoisRepresentation F E T σ (P.root j) :=
      (A.root_weightMap_apply P P j).symm.trans
        (StarActionIndependence.galoisAction_weightMap_apply p σ (P.root j))
    rw [he, latticePairing_galoisRepresentation]
  have hPos (j : J) : Δ.IsPos j ↔ 0 < latticePairing (TE) (P.root j) ν :=
    IsRootDatumOf.regularCocharacterBase_isPos F E t hP ν hν' j
  have hSupport (C : P.Aut) (hc : ∀ j, Δ.IsPos (C.indexEquiv j) ↔ Δ.IsPos j) (j : J) :
      C.indexEquiv j ∈ Δ.support ↔ j ∈ Δ.support :=
    RootPairing.Base.mem_support_equiv_iff_of_isPos P Δ C.indexEquiv C.weightEquiv
      (fun i => (C.root_weightMap_apply P P i).symm) hc j
  have hSign (z : cocharacterLattice (TE))
      (hz : Dynamic.unipotent (CommGroupScheme.groupHom νσ ≫ tE) =
        Dynamic.unipotent (CommGroupScheme.groupHom z ≫ tE))
      (j : J) :
      0 < latticePairing (TE) (P.root (A.indexEquiv j)) z ↔ Δ.IsPos j := by
    rw [hPos, ← hPair j]
    exact ⟨RelativeRoot.positive_rootSupport_of_unipotent_le hT (tE) z νσ
      hz.symm.le _ (hroot (A.indexEquiv j)),
      RelativeRoot.positive_rootSupport_of_unipotent_le hT (tE) νσ z
        hz.le _ (hroot (A.indexEquiv j))⟩
  rcases hOpp σ with h | h
  · left
    apply (p.starAction_eq_galoisAction σ ?_).symm
    intro a
    exact (hSupport A
      (fun j => (hPos _).trans (hSign ν h j)) a).symm
  · right
    let q := v.symm.trans e
    have hq (a b : p.toSplitPinning.base.support) :
        p.toSplitPinning.rootDatum.pairing a.val b.val = CartanMatrix.D 4 (q a) (q b) := by
      obtain ⟨a₀, rfl⟩ := v.surjective a
      obtain ⟨b₀, rfl⟩ := v.surjective b
      change p.rootDatum.pairing (v a₀).val (v b₀).val =
        CartanMatrix.D 4 (e (v.symm (v a₀))) (e (v.symm (v b₀)))
      rw [v.symm_apply_apply, v.symm_apply_apply, hcartan, hD]
    have hOppPos (a : J) :
        Δ.IsPos ((negAut P * A).indexEquiv a) ↔ Δ.IsPos a := by
      have he : P.root ((negAut P * A).indexEquiv a) = -P.root (A.indexEquiv a) :=
        ((negAut P).root_weightMap_apply P P (A.indexEquiv a)).symm
      rw [hPos, he, map_neg, LinearMap.neg_apply, ← hSign (-ν) h a, map_neg]
    have hOppSupport (a : J) :
        A.indexEquiv a ∈ (Δ.map (negAut P)).support ↔ a ∈ Δ.support :=
      (mem_support_map_negAut P Δ _).trans (hSupport (negAut P * A) hOppPos a)
    have hst := p.starAction_eq_negAut_mul_of_D4_opposite
      (p.corootSpan_eq_top_of_simplyConnected hsc) q hq σ
      hOppSupport
    let star : P.Aut := (p.starAction σ).val
    have hs : star = negAut P * A := hst
    change A = negAut P * star
    rw [hs, ← mul_assoc, negAut_mul_self, one_mul]

end Pinning

end Langlands.GroupScheme
