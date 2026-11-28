import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.Rational.DynamicCocharacterTower
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.StarOrbitRootSums
import Langlands.LinearAlgebra.RootDatumNegation

/-! # Descent of a Levi subgroup from a signed based action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

open Langlands.RootDatumNegation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (p : GaloisPinningData F E G)

local notation "b" => algebraBaseMap F E
local notation "GE" => Functor.obj (GroupScheme.baseChange b) G
local notation "P" => p.rootDatum
local notation "TE" => Functor.obj (CommGroupScheme.baseChange b) p.torus
local notation "tE" => CategoryTheory.Functor.map (GroupScheme.baseChange b) p.inclusion

private abbrev basedAction (σ : E ≃ₐ[F] E) : p.rootDatum.Aut := (p.starAction σ).val

omit [LocallyOfFiniteType G.X.hom] in
open scoped Classical in
/-- A cocharacter with one positive value on the complement of the face
and zero on its simple roots. -/
theorem exists_faceCocharacter (J : Set p.base.support) :
    ∃ (m : ℤ) (ν : cocharacterLattice TE), 0 < m ∧
      ∀ a : p.base.support,
        latticePairing TE (p.rootDatum.root a.val) ν = if a ∈ J then 0 else m := by
  classical
  obtain ⟨m, hm, ν, hν⟩ := p.isSplitTorus.exists_scaled_pairings
    (fun a : p.base.support => p.rootDatum.root a.val)
    p.toSplitPinning.linearIndependent_toRat_simpleRoot
    (fun a => if a ∈ J then 0 else 1)
  refine ⟨m, ν, hm, fun a => ?_⟩
  by_cases ha : a ∈ J <;> simpa [ha] using hν a

private theorem pairing_star_eq_of_simple
    (σ : E ≃ₐ[F] E) (ν : cocharacterLattice TE)
    (h : ∀ a : p.base.support,
      latticePairing TE (p.rootDatum.root (p.starSupport σ a).val) ν =
        latticePairing TE (p.rootDatum.root a.val) ν)
    (i : p.rootIndex) :
    latticePairing TE (p.rootDatum.root ((basedAction p σ).indexEquiv i)) ν =
      latticePairing TE (p.rootDatum.root i) ν := by
  let A : p.rootDatum.Aut := basedAction p σ
  let f := (latticePairing TE).flip ν
  change f (p.rootDatum.root (A.indexEquiv i)) = f (p.rootDatum.root i)
  rw [← A.root_weightMap_apply P P i]
  change (f.comp A.weightEquiv.toLinearMap) (p.rootDatum.root i) = f (p.rootDatum.root i)
  obtain ⟨m, _, _, hm⟩ := p.base.exists_root_eq_sum_int i
  rw [hm, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  change f (A.weightMap (p.rootDatum.root a)) = f (p.rootDatum.root a)
  rw [A.root_weightMap_apply P P a]
  exact h ⟨a, ha⟩

private theorem pairing_galois_eq_zero_iff
    (σ : E ≃ₐ[F] E) (ν : cocharacterLattice TE)
    (h : p.galoisAction σ = basedAction p σ ∨
      p.galoisAction σ = negAut P * basedAction p σ)
    (hν : ∀ a : p.base.support,
      latticePairing TE (p.rootDatum.root (p.starSupport σ a).val) ν =
        latticePairing TE (p.rootDatum.root a.val) ν)
    (i : p.rootIndex) :
    latticePairing TE (p.rootDatum.root i) (cocharacterLattice.galoisRepresentation F E p.torus σ ν) = 0 ↔
      latticePairing TE (p.rootDatum.root i) ν = 0 := by
  let A : p.rootDatum.Aut := p.galoisAction σ
  obtain ⟨j, hj⟩ := A.indexEquiv.surjective i
  have hPair : p.rootDatum.root (A.indexEquiv j) =
      characterLattice.galoisRepresentation F E p.torus σ (p.rootDatum.root j) :=
    (A.root_weightMap_apply P P j).symm.trans
      (StarActionIndependence.galoisAction_weightMap_apply p σ (p.rootDatum.root j))
  rw [← hj]
  conv_lhs => rw [hPair, latticePairing_galoisRepresentation]
  have hs := p.pairing_star_eq_of_simple σ ν hν j
  rcases h with h | h
  · rw [show A = basedAction p σ from h, hs]
  · rw [show A = negAut P * basedAction p σ from h]
    have hn : p.rootDatum.root ((negAut P * basedAction p σ).indexEquiv j) =
        -p.rootDatum.root ((basedAction p σ).indexEquiv j) :=
      ((negAut P).root_weightMap_apply P P ((basedAction p σ).indexEquiv j)).symm
    rw [hn, map_neg, LinearMap.neg_apply, neg_eq_zero, hs]

/-- A centralizer is Galois invariant when the ordinary Galois action
preserves the roots with zero cocharacter pairing. -/
theorem galoisTransport_centralizer_of_stable_zeroRoots
    (σ : E ≃ₐ[F] E) (ν : cocharacterLattice TE)
    (h : ∀ i : p.rootIndex,
      p.rootDatum.root' ((p.galoisAction σ).indexEquiv i) ν = 0 ↔
        p.rootDatum.root' i ν = 0) :
    SubgroupFunctor.galoisTransport F E G σ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)) =
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE) := by
  let : IsAffineHom (GE).X.hom := p.isConnectedReductive.isAffineHom
  let : Smooth (GE).X.hom := p.isConnectedReductive.smooth
  let : ConnectedSpace (GE).X.left := p.isConnectedReductive.connectedSpace
  let νσ := cocharacterLattice.galoisRepresentation F E p.torus σ ν
  have hz (α : characterLattice TE) (hα : α ∈ relativeRoots tE) :
      latticePairing TE α νσ = 0 ↔ latticePairing TE α ν = 0 := by
    have hr : α ∈ Set.range p.rootDatum.root := by
      simpa only [p.isRootDatum.2.1, relativeRoots_eq_roots] using hα
    obtain ⟨a, rfl⟩ := hr
    let A := p.galoisAction σ
    obtain ⟨j, hj⟩ := A.indexEquiv.surjective a
    have hjχ : p.rootDatum.root (A.indexEquiv j) =
        characterLattice.galoisRepresentation F E p.torus σ (p.rootDatum.root j) :=
      (A.root_weightMap_apply P P j).symm.trans
        (StarActionIndependence.galoisAction_weightMap_apply p σ (p.rootDatum.root j))
    rw [← hj]
    conv_lhs => rw [hjχ, latticePairing_galoisRepresentation]
    have he (i : p.rootIndex) : p.rootDatum.root' i ν =
        latticePairing TE (p.rootDatum.root i) ν :=
      LinearMap.congr_fun (LinearMap.congr_fun p.isRootDatum.1 (p.rootDatum.root i)) ν
    have hz := (h j).symm
    rw [he j, he (A.indexEquiv j)] at hz
    exact hz
  change SubgroupFunctor.galoisTransport F E G σ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map p.inclusion)) = _
  rw [← centralizer_galoisRepresentation p.inclusion σ ν]
  exact le_antisymm
    (dynamicCentralizer_le_of_root_zero_imp dynamicConnected p.isSplitTorus tE νσ ν
      (fun α hα => (hz α hα).mp))
    (dynamicCentralizer_le_of_root_zero_imp dynamicConnected p.isSplitTorus tE ν νσ
      (fun α hα => (hz α hα).mpr))

/-- If the based action preserves the values on the simple roots and the
ordinary action differs only by simultaneous negation, the cocharacter
centralizer is Galois invariant on all test schemes. -/
theorem galoisTransport_faceCentralizer
    (σ : E ≃ₐ[F] E) (ν : cocharacterLattice TE)
    (h : p.galoisAction σ = basedAction p σ ∨
      p.galoisAction σ = negAut P * basedAction p σ)
    (hν : ∀ a : p.base.support,
      latticePairing TE (p.rootDatum.root (p.starSupport σ a).val) ν =
        latticePairing TE (p.rootDatum.root a.val) ν) :
    SubgroupFunctor.galoisTransport F E G σ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)) =
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE) := by
  let : IsAffineHom (GE).X.hom := p.isConnectedReductive.isAffineHom
  let : Smooth (GE).X.hom := p.isConnectedReductive.smooth
  let : ConnectedSpace (GE).X.left := p.isConnectedReductive.connectedSpace
  let νσ := cocharacterLattice.galoisRepresentation F E p.torus σ ν
  have hz (α : characterLattice TE) (hα : α ∈ relativeRoots tE) :
      latticePairing TE α νσ = 0 ↔ latticePairing TE α ν = 0 := by
    have hr : α ∈ Set.range p.rootDatum.root := by
      simpa only [p.isRootDatum.2.1, relativeRoots_eq_roots] using hα
    obtain ⟨a, rfl⟩ := hr
    exact p.pairing_galois_eq_zero_iff σ ν h hν a
  change SubgroupFunctor.galoisTransport F E G σ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map p.inclusion)) = _
  rw [← centralizer_galoisRepresentation p.inclusion σ ν]
  exact le_antisymm
    (dynamicCentralizer_le_of_root_zero_imp dynamicConnected p.isSplitTorus tE νσ ν
      (fun α hα => (hz α hα).mp))
    (dynamicCentralizer_le_of_root_zero_imp dynamicConnected p.isSplitTorus tE ν νσ
      (fun α hα => (hz α hα).mpr))

omit [LocallyOfFiniteType G.X.hom] in
/-- A Galois-invariant cocharacter centralizer descends as an actual
connected reductive closed subgroup. -/
theorem exists_centralizer_descent [IsGalois F E]
    (ν : cocharacterLattice TE)
    (h : ∀ σ : E ≃ₐ[F] E, SubgroupFunctor.galoisTransport F E G σ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)) =
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)) :
    ∃ (M : GroupScheme (Spec (CommRingCat.of F))) (j : M ⟶ G),
      IsClosedSubgroup j ∧ IsConnectedReductive M ∧
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)).IsRepresentedBy
          ((GroupScheme.baseChange b).map j) := by
  let : IsAffineHom (GE).X.hom := p.isConnectedReductive.isAffineHom
  let : IsAffine (GE).X.left := isAffine_of_isAffineHom (GE).X.hom
  let χ := CommGroupScheme.groupHom ν ≫ tE
  let ME := Dynamic.Affine.centralizerScheme χ
  let jE : ME ⟶ GE := Dynamic.Affine.centralizerHom χ
  have hjE : IsClosedSubgroup jE := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hr : (Dynamic.centralizer χ).IsRepresentedBy jE :=
    Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hg (σ : E ≃ₐ[F] E) :
      SubgroupFunctor.range (radicalGaloisHom jE σ) = SubgroupFunctor.range jE := by
    have htransport : SubgroupFunctor.galoisTransport F E G σ (SubgroupFunctor.range jE) =
        SubgroupFunctor.range (radicalGaloisHom jE σ) :=
      SubgroupFunctor.descentTransport_range _ _ _ _ jE
    rw [← htransport, hr.2]
    exact h σ
  obtain ⟨M, j, e, _, hj, he⟩ :=
    Descent.GaloisInvariantClosedSubgroup.exists_descent hjE hg
  have hME := dynamicCentralizerReductive E GE p.isConnectedReductive χ ME jE hjE hr
  refine ⟨M, j, hj, IsConnectedReductive.of_fieldExtension (IsConnectedReductive.of_iso e hME), ?_⟩
  have : IsClosedImmersion ((GroupScheme.baseChange b).map j).hom.hom.left := hj.baseChange b
  exact ⟨Over.mono_of_mono_left _, by rw [he, SubgroupFunctor.range_iso_comp]; exact hr.2⟩

/-- The centralizer determined by a stable simple-root face descends as
an actual connected reductive closed subgroup. -/
theorem exists_faceCentralizer_descent [IsGalois F E]
    (ν : cocharacterLattice TE)
    (h : ∀ σ : E ≃ₐ[F] E, p.galoisAction σ = basedAction p σ ∨
      p.galoisAction σ = negAut P * basedAction p σ)
    (hν : ∀ (σ : E ≃ₐ[F] E) (a : p.base.support),
      latticePairing TE (p.rootDatum.root (p.starSupport σ a).val) ν =
        latticePairing TE (p.rootDatum.root a.val) ν) :
    ∃ (M : GroupScheme (Spec (CommRingCat.of F))) (j : M ⟶ G),
      IsClosedSubgroup j ∧ IsConnectedReductive M ∧
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)).IsRepresentedBy
          ((GroupScheme.baseChange b).map j) :=
  p.exists_centralizer_descent ν (fun σ => p.galoisTransport_faceCentralizer σ ν (h σ) (hν σ))

end Langlands.GroupScheme.GaloisPinningData
