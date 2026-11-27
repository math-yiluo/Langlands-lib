import Langlands.GroupScheme.Rational.NumberFieldQuadraticQuasiSplitToralReduction
import Langlands.GroupScheme.Rational.QuadraticOppositeTorusCell
import Langlands.GroupScheme.Rational.QuadraticRealCocycleComparison
import Langlands.GroupScheme.Rational.DynamicCocharacterTower
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.RationalCocharacterRealization
import Langlands.GroupScheme.Rational.RootFixedTorusSplitting
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.Torus.CocharacterAnisotropy
import Langlands.LinearAlgebra.RootDatumNegation

/-! # The torus of a quadratic opposite Borel pair with rigid Cartan matrix -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open StarActionFiniteStage MultiplicativeTypeAbsoluteEquivalence
open Langlands.RootDatumNegation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4500
set_option maxHeartbeats 1900000

private theorem galoisBaseMap_tower_commutes
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    (σ : L ≃ₐ[F] L) (τ : E ≃ₐ[F] E)
    (h : ∀ x, τ (algebraMap L E x) = algebraMap L E (σ x)) :
    algebraBaseMap L E ≫ galoisBaseMap F L σ =
      galoisBaseMap F E τ ≫ algebraBaseMap L E := by
  change Spec.map (CommRingCat.ofHom (algebraMap L E)) ≫
    Spec.map (CommRingCat.ofHom σ.toRingHom) =
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap L E))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun x => (h x).symm

section Direction

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [IsGalois F L]
  [Algebra L (SeparableClosure F)] [IsScalarTower F L (SeparableClosure F)]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : T.toGrp ⟶ G)

local notation "E" => SeparableClosure F
local notation "b" => algebraBaseMap F L
local notation "c" => algebraBaseMap F E
local notation "GE" => Functor.obj (GroupScheme.baseChange c) G
local notation "TE" => Functor.obj (CommGroupScheme.baseChange c) T
local notation "tE" => CategoryTheory.Functor.map (GroupScheme.baseChange c) t

private local instance : IsAffineHom (GE).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom c))

private theorem exists_regular_oppositeDirection
    (hG : IsConnectedReductive G) (ht : IsQuadraticOppositeBorelTorus L t) :
    ∃ (σ : L ≃ₐ[F] L) (ν : cocharacterLattice (TE)), σ ≠ 1 ∧
      IsGenericCocharacter (tE) ν ∧
      ∀ τ : E ≃ₐ[F] E,
        let ντ := cocharacterLattice.galoisRepresentation F E T τ ν
        (τ.restrictNormal L = 1 →
          Dynamic.unipotent (CommGroupScheme.groupHom ντ ≫ tE) =
            Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ tE)) ∧
        (τ.restrictNormal L = σ →
          Dynamic.unipotent (CommGroupScheme.groupHom ντ ≫ tE) =
            Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ tE)) := by
  let tL := (GroupScheme.baseChange b).map t
  let : Smooth G.X.hom := hG.smooth
  have hGE := connectedReductiveFieldExtensionStatement F E G hG
  let : Smooth (GE).X.hom := hGE.smooth
  have hT := GaloisPinningData.isSplitTorus_separableClosure T ht.2.1.1
  have hMax := (maximalTorusBaseChange F E G T t ht.2.1.1 ht.2.1.2.1).mp ht.2.1
  obtain ⟨σ, ν, hσ, hC, hU⟩ := ht.exists_torusDynamicData hG
  let extendDirection := cocharacterLattice.towerExtension F L E T
  let νE := extendDirection ν
  have hCE : Dynamic.centralizer (CommGroupScheme.groupHom νE ≫ tE) =
      SubgroupFunctor.range (tE) := centralizer_towerExtension t ν hC
  have hreg : IsGenericCocharacter (tE) νE :=
    RationalCocharacter.isGenericCocharacter_of_centralizer_eq_torusCentralizer
      hT (tE) νE (hCE.trans (maximalTorusCentralizer E (GE) hGE (TE) (tE) hMax).symm)
  refine ⟨σ, νE, hσ, hreg, fun τ => ?_⟩
  let transport := SubgroupFunctor.towerBaseChange b (algebraBaseMap L E)
    c (algebraBaseMap_tower L E) G
  let U := Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ tL)
  have hUpper : Dynamic.unipotent (CommGroupScheme.groupHom νE ≫ tE) = transport U :=
    unipotent_towerExtension t ν
  have hτ :=
    (unipotent_galoisRepresentation t τ νE).trans
      ((congrArg (SubgroupFunctor.galoisTransport F E G τ) hUpper).trans
        (SubgroupFunctor.towerBaseChange_descentTransport b (algebraBaseMap L E) c
          (algebraBaseMap_tower L E) G
          (galoisBaseMap F L (τ.restrictNormal L)) (galoisBaseMap_over F L (τ.restrictNormal L))
          (galoisBaseMap F E τ) (galoisBaseMap_over F E τ)
          (galoisBaseMap_tower_commutes (τ.restrictNormal L) τ
            (fun x => (τ.restrictNormal_commutes L x).symm)) U).symm)
  constructor
  · intro hs
    refine hτ.trans ?_
    change transport (SubgroupFunctor.galoisTransport F L G (τ.restrictNormal L) U) = _
    rw [hs, map_one]
    exact hUpper.symm
  · intro hs
    refine hτ.trans ?_
    change transport (SubgroupFunctor.galoisTransport F L G (τ.restrictNormal L) U) = _
    rw [hs, show SubgroupFunctor.galoisTransport F L G σ U =
      Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ tL))
      from hU, ← groupHom_neg_comp_eq_oppositeCocharacter tL ν]
    have hneg : Dynamic.unipotent (CommGroupScheme.groupHom (extendDirection (-ν)) ≫ tE) =
        transport (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ tL)) :=
      unipotent_towerExtension t (-ν)
    rw [map_neg] at hneg
    exact hneg.symm

end Direction

section Rigidity

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom]

private theorem aut_eq_one_of_rigid_base
    (p p₀ : SplitPinning H) (hH : IsSemisimple H)
    (hrigid : ∀ π : p₀.base.support ≃ p₀.base.support,
      (∀ a b, p₀.rootDatum.pairing (π a).val (π b).val = p₀.rootDatum.pairing a.val b.val) →
      π = Equiv.refl _) (A : p.rootDatum.Aut)
    (hA : ∀ a, a ∈ p.base.support ↔ A.indexEquiv a ∈ p.base.support) :
    A = 1 := by
  obtain ⟨_, _, e, _, _, he⟩ := StarActionIndependence.exists_conj_based p₀ p
  let v : p₀.base.support ≃ p.base.support := e.indexEquiv.subtypeEquiv he
  let π : p.base.support ≃ p.base.support := A.indexEquiv.subtypeEquiv hA
  let π₀ : p₀.base.support ≃ p₀.base.support := v.trans (π.trans v.symm)
  have hpair (a b : p₀.base.support) :
      p.rootDatum.pairing (v a).val (v b).val = p₀.rootDatum.pairing a.val b.val :=
    e.toHom.pairing
  have hπ₀ : π₀ = Equiv.refl _ := by
    apply hrigid
    intro a b
    rw [← hpair, ← hpair a b]
    change p.rootDatum.pairing (v (v.symm (π (v a)))).val (v (v.symm (π (v b)))).val = _
    rw [v.apply_symm_apply, v.apply_symm_apply]
    exact A.toHom.pairing
  have hfix (a : p.base.support) : A.indexEquiv a.val = a.val := by
    obtain ⟨b, rfl⟩ := v.surjective a
    have hb : v.symm (π (v b)) = b := DFunLike.congr_fun hπ₀ b
    exact congrArg Subtype.val ((Equiv.symm_apply_eq v).mp hb)
  apply StarActionIndependence.equiv_ext_of_weightMap
  intro χ
  change A.weightMap χ = χ
  apply hH.character_eq_of_fixed_roots p.isSplitTorus p.isMaximalTorus.2.1
    p.isRootDatum A.weightMap ?_ χ
  let f : characterLattice p.torus →ₗ[ℤ] characterLattice p.torus :=
    A.weightMap - LinearMap.id
  have hs : Submodule.span ℤ (p.rootDatum.root '' (p.base.support : Set p.rootIndex)) ≤ f.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    change A.weightMap (p.rootDatum.root a) - p.rootDatum.root a = 0
    rw [A.root_weightMap_apply, hfix ⟨a, ha⟩, sub_self]
  intro α hα
  rw [← p.isRootDatum.2.1] at hα
  obtain ⟨a, rfl⟩ := hα
  have h := hs (p.base.root_mem_span_int a)
  change A.weightMap (p.rootDatum.root a) - p.rootDatum.root a = 0 at h
  exact sub_eq_zero.mp h

end Rigidity

section Action

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
  [Algebra L (SeparableClosure F)] [IsScalarTower F L (SeparableClosure F)]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : T.toGrp ⟶ G)

local notation "E" => SeparableClosure F
local notation "c" => algebraBaseMap F E
local notation "GE" => Functor.obj (GroupScheme.baseChange c) G
local notation "TE" => Functor.obj (CommGroupScheme.baseChange c) T
local notation "tE" => CategoryTheory.Functor.map (GroupScheme.baseChange c) t

private local instance : IsAffineHom (GE).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom c))

private local instance : LocallyOfFiniteType (GE).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom c))

private theorem quadraticOppositeBorel_characterAction
    (ht : IsQuadraticOppositeBorelTorus L t) (d : TitsIndexData G)
    (hrigid : ∀ π : d.Vertex ≃ d.Vertex,
      (∀ a b, d.cartan (π a) (π b) = d.cartan a b) → π = Equiv.refl d.Vertex) :
    ∀ (τ : E ≃ₐ[F] E) (χ : characterLattice (TE)),
      (τ.restrictNormal L = 1 → characterLattice.galoisRepresentation F E T τ χ = χ) ∧
      (τ.restrictNormal L ≠ 1 → characterLattice.galoisRepresentation F E T τ χ = -χ) := by
  let hG := d.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  have hGE := connectedReductiveFieldExtensionStatement F E G hG
  let : Smooth (GE).X.hom := hGE.smooth
  have hSemi := isSemisimpleFieldExtension F E G d.isSemisimple
  have hT := GaloisPinningData.isSplitTorus_separableClosure T ht.2.1.1
  have hMax := (maximalTorusBaseChange F E G T t ht.2.1.1 ht.2.1.2.1).mp ht.2.1
  obtain ⟨σ, ν, hσ, hν, hOpp⟩ := exists_regular_oppositeDirection t hG ht
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
  intro τ χ
  let A : P.Aut := p.galoisAction τ
  let ντ := cocharacterLattice.galoisRepresentation F E T τ ν
  have hPair (a : J) : latticePairing (TE) (P.root (A.indexEquiv a)) ντ =
      latticePairing (TE) (P.root a) ν := by
    have he : P.root (A.indexEquiv a) =
        characterLattice.galoisRepresentation F E T τ (P.root a) :=
      (A.root_weightMap_apply P P a).symm.trans
        (StarActionIndependence.galoisAction_weightMap_apply p τ (P.root a))
    rw [he, latticePairing_galoisRepresentation]
  have hPos (a : J) : Δ.IsPos a ↔ 0 < latticePairing (TE) (P.root a) ν :=
    IsRootDatumOf.regularCocharacterBase_isPos F E t hP ν hν' a
  have hBased (C : P.Aut) (hc : ∀ a, Δ.IsPos (C.indexEquiv a) ↔ Δ.IsPos a) : C = 1 := by
    apply aut_eq_one_of_rigid_base p.toSplitPinning d.pinning.toSplitPinning hSemi hrigid C
    intro a
    exact (RootPairing.Base.mem_support_equiv_iff_of_isPos P Δ C.indexEquiv C.weightEquiv
      (fun i => (C.root_weightMap_apply P P i).symm) hc a).symm
  have hSign (z : cocharacterLattice (TE))
      (hz : Dynamic.unipotent (CommGroupScheme.groupHom ντ ≫ tE) =
        Dynamic.unipotent (CommGroupScheme.groupHom z ≫ tE))
      (a : J) :
      0 < latticePairing (TE) (P.root (A.indexEquiv a)) z ↔ Δ.IsPos a := by
    rw [hPos, ← hPair a]
    exact ⟨RelativeRoot.positive_rootSupport_of_unipotent_le hT (tE) z ντ
      hz.symm.le _ (hroot (A.indexEquiv a)),
      RelativeRoot.positive_rootSupport_of_unipotent_le hT (tE) ντ z
        hz.le _ (hroot (A.indexEquiv a))⟩
  have hχ : A.weightMap χ = characterLattice.galoisRepresentation F E T τ χ :=
    StarActionIndependence.galoisAction_weightMap_apply p τ χ
  constructor
  · intro hτ
    rw [← hχ, hBased A (fun a => (hPos _).trans (hSign ν ((hOpp τ).1 hτ) a))]
    rfl
  · intro hτ
    have hσ' := (GaloisCocycle.quadratic_aut_eq_one_or ht.1 σ hσ (τ.restrictNormal L)).resolve_left hτ
    have hOppPos (a : J) : Δ.IsPos ((negAut P * A).indexEquiv a) ↔ Δ.IsPos a := by
      have he : P.root ((negAut P * A).indexEquiv a) = -P.root (A.indexEquiv a) :=
        ((negAut P).root_weightMap_apply P P (A.indexEquiv a)).symm
      rw [hPos, he, map_neg, LinearMap.neg_apply, ← hSign (-ν) ((hOpp τ).2 hσ') a, map_neg]
    have hA : A = negAut P := by
      have h := congrArg (fun x : P.Aut => negAut P * x) (hBased (negAut P * A) hOppPos)
      simpa only [← mul_assoc, negAut_mul_self, one_mul, mul_one] using h
    rw [← hχ, hA, negAut_weightMap]

end Action

section Lattices

private theorem split_of_fixed_characters
    {k E : Type u} [Field k] [Field E] [Algebra k E] [IsAlgClosed E]
    [Algebra.IsAlgebraic k E]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T.toGrp)
    (hfix : ∀ (τ : E ≃ₐ[k] E)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)),
      characterLattice.galoisRepresentation k E T τ χ = χ) :
    IsSplitTorus T.toGrp := by
  let : IsAlgClosure k E := ⟨inferInstance, inferInstance⟩
  obtain ⟨M, _, _, _, _, hM⟩ := torusFiniteGaloisSplitting k T.toGrp hT
  let embedding : M →ₐ[k] E := IsAlgClosed.lift
  let : Algebra M E := embedding.toRingHom.toAlgebra
  let : IsScalarTower k M E := IsScalarTower.of_algebraMap_eq fun x =>
    (embedding.commutes x).symm
  let b := algebraBaseMap k M
  let j := algebraBaseMap M E
  let c := algebraBaseMap k E
  let hc := algebraBaseMap_tower (k := k) M E
  let TM := (CommGroupScheme.baseChange b).obj T
  let extend := towerCharacterOf b j T c hc
  have he : Function.Injective extend :=
    (characterLattice.congr (towerIsoOf b j T c hc).symm).injective.comp
      (hM.characterLattice_baseChange_bijective j TM).injective
  apply IsSplitTorus.of_galoisFixedCharacters hM
  intro σ χ
  let τ := σ.liftNormal E
  have h := towerCharacterOf_transport b j T c hc (galoisBaseMap k M σ)
    (galoisBaseMap_over k M σ) (galoisBaseMap k E τ) (galoisBaseMap_over k E τ)
    (galoisBaseMap_tower_commutes σ τ (σ.liftNormal_commutes E)) χ
  change extend (characterLattice.galoisRepresentation k M T σ χ) =
    characterLattice.galoisRepresentation k E T τ (extend χ) at h
  exact he (h.trans (hfix τ _))

private theorem anisotropic_of_inverted_characters
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (τ : E ≃ₐ[k] E)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
    (hinv : ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T),
      characterLattice.galoisRepresentation k E T τ χ = -χ) :
    IsAnisotropic T.toGrp := by
  apply isAnisotropic_of_cocharacter_eq_zero
  intro ν
  let b := algebraBaseMap k E
  let TE := (CommGroupScheme.baseChange b).obj T
  let νE := cocharacterLattice.baseChange b T ν
  apply cocharacterLattice.algebraBaseChange_injective k E T
  rw [map_zero]
  change νE = 0
  apply hT.isPerfPair_latticePairing.bijective_right.injective
  ext χ
  change latticePairing TE χ νE = latticePairing TE χ 0
  have h := latticePairing_galoisRepresentation k E T τ χ νE
  rw [hinv, show cocharacterLattice.galoisRepresentation k E T τ νE = νE from
    cocharacterLattice.galoisRepresentation_baseChange k E T τ ν, map_neg,
    LinearMap.neg_apply] at h
  change -latticePairing TE χ νE = latticePairing TE χ νE at h
  rw [map_zero]
  omega

end Lattices

section OppositeTorus

variable {F L : Type u} [Field F] [CharZero F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {t : T.toGrp ⟶ G}

/-- In a semisimple group with rigid Cartan matrix, the torus of a quadratic
opposite Borel pair splits over the quadratic field and has split rank zero
over the base field. -/
theorem IsQuadraticOppositeBorelTorus.split_anisotropic
    (ht : IsQuadraticOppositeBorelTorus L t) (d : TitsIndexData G)
    (hrigid : ∀ π : d.Vertex ≃ d.Vertex,
      (∀ a b, d.cartan (π a) (π b) = d.cartan a b) → π = Equiv.refl d.Vertex) :
    IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F L)).obj T.toGrp) ∧
      IsAnisotropic T.toGrp := by
  let E := SeparableClosure F
  let embedding : L →ₐ[F] E := IsAlgClosed.lift
  let : Algebra L E := embedding.toRingHom.toAlgebra
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x =>
    (embedding.commutes x).symm
  let : Algebra.IsAlgebraic L E := Algebra.IsAlgebraic.tower_top (K := F) L
  let b := algebraBaseMap F L
  let c := algebraBaseMap F E
  let TL := (CommGroupScheme.baseChange b).obj T
  let e := towerIsoOf b (algebraBaseMap L E) T c (algebraBaseMap_tower L E)
  have hAction := quadraticOppositeBorel_characterAction t ht d hrigid
  constructor
  · change IsSplitTorus TL.toGrp
    apply split_of_fixed_characters (E := E) (ht.2.1.1.baseChange (K := L))
    intro τ χ
    obtain ⟨ψ, rfl⟩ := (characterLattice.congr e).surjective χ
    have hτ : (τ.restrictScalars F).restrictNormal L = 1 := by
      ext x
      apply (algebraMap L E).injective
      rw [AlgEquiv.restrictNormal_commutes]
      exact τ.commutes x
    have h := characterLattice.galoisRepresentation_scalarExtension
      (algebraBaseMap_tower L E) T τ ψ
    rw [(hAction _ _).1 hτ] at h
    exact h.symm
  · obtain ⟨σ, _, _, hσ, _, _⟩ := ht.2.2
    let τ := σ.liftNormal E
    have hτ : τ.restrictNormal L = σ := by
      ext x
      apply (algebraMap L E).injective
      rw [AlgEquiv.restrictNormal_commutes]
      exact σ.liftNormal_commutes E x
    apply anisotropic_of_inverted_characters T τ
      (GaloisPinningData.isSplitTorus_separableClosure T ht.2.1.1)
    exact fun χ => (hAction τ χ).2 (ne_of_eq_of_ne hτ hσ)

end OppositeTorus

end Langlands.GroupScheme
