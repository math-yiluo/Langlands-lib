import Langlands.GroupScheme.Rational.TypeE6BranchCocharacter
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.PinningGroupIsoTransport
import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.LocalGroupIsoCocharacterRefinement
import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistence
import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth

/-! # Matching the primitive branch lines of geometric E6 forms -/

noncomputable section

universe u
open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped BigOperators CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem LocalGroupIso.HasDiscrepancy.mem_torusCentralizer_of_cocharacterMatching
    {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}
    {e : LocalGroupIso G H U} {ξ : Cocycle G U}
    (he : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (χ : (Gm S).toGrp ⟶ G) (ψ : (Gm S).toGrp ⟶ H)
    (hmatch : ∀ (T : Over S) (a : T ⟶ U) (z : T ⟶ (Gm S).X),
      e.toFun a (z ≫ χ.hom.hom) = z ≫ ψ.hom.hom)
    {T : Over S} (a b : T ⟶ U) : ξ.toFun a b ∈ (torusCentralizer χ).carrier T := by
  intro W s z
  rw [← ξ.naturality]
  have h := he (s ≫ a) (s ≫ b) (z ≫ χ.hom.hom)
  rw [hmatch] at h
  have hc := (e.toFun (s ≫ a)).injective (h.trans (hmatch W (s ≫ a) z).symm)
  rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id] at hc
  exact (mul_inv_eq_iff_eq_mul).mp hc

namespace TitsIndexData

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

local notation "b" => algebraBaseMap k (SeparableClosure k)

set_option backward.isDefEq.respectTransparency false in
private theorem baseChange_typeE6BranchCocharacter (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (ν : cocharacterLattice d.splitTorus)
    (hν : cocharacterLattice.baseChange b d.pinning.torus (ν ≫ d.torusMap) =
      d.typeE6BranchCoweight e) :
    Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ d.splitInclusion) =
      CommGroupScheme.groupHom (d.typeE6BranchCoweight e) ≫ d.pinning.toSplitPinning.inclusion := by
  rw [← d.square, ← Category.assoc]
  change Dynamic.baseChangeCocharacter b
      (CommGroupScheme.groupHom (ν ≫ d.torusMap) ≫ d.pinning.inclusion) = _
  rw [Dynamic.baseChangeCocharacter_comp_hom, ← cocharacterLattice.groupHom_baseChange_dynamic,
    hν]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let two simply connected E6 forms be given with actual Tits indices and
distinguished short-arm vertices. An isomorphism over an algebraically closed
separable closure can be corrected by inner conjugation to match the rational
branch cocharacters pointwise on their common multiplicative group. -/
theorem exists_matching_typeE6BranchLines [IsAlgClosed (SeparableClosure k)]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hCartan : ∀ a c, d.cartan a c = CartanMatrix.E 6 (e a) (e c))
    (hsc : IsSimplyConnected G) (hmark : e.symm 1 ∈ d.distinguishedVertices)
    (dH : TitsIndexData H) (hscH : IsSimplyConnected H)
    (hmarkH : ∀ eH : dH.Vertex ≃ Fin 6,
      (∀ a c, dH.cartan a c = CartanMatrix.E 6 (eH a) (eH c)) →
      eH.symm 1 ∈ dH.distinguishedVertices)
    (f : (GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H) :
    ∃ (ν : cocharacterLattice d.splitTorus) (νH : cocharacterLattice dH.splitTorus)
      (n : Over.mk (𝟙 (Spec (CommRingCat.of (SeparableClosure k)))) ⟶ ((GroupScheme.baseChange b).obj H).X),
      IsClosedSubgroup (CommGroupScheme.groupHom ν ≫ d.splitInclusion) ∧
      IsClosedSubgroup (CommGroupScheme.groupHom νH ≫ dH.splitInclusion) ∧
      cocharacterLattice.baseChange b d.pinning.torus (ν ≫ d.torusMap) =
        d.typeE6BranchCoweight e ∧
      Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ d.splitInclusion) ≫
        f.hom ≫ (((GroupScheme.baseChange b).obj H).innerIso n).hom =
      Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom νH ≫ dH.splitInclusion) := by
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := d.pinning.isConnectedReductive.isAffineHom
  let : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := dH.pinning.isConnectedReductive.isAffineHom
  let p := d.pinning.toSplitPinning.mapGroupIso f
  let q := dH.pinning.toSplitPinning
  obtain ⟨n, φ, root, hn, hweight, hbase⟩ := StarActionIndependence.exists_conj_based p q
  let v : d.Vertex ≃ dH.Vertex := root.indexEquiv.subtypeEquiv hbase
  let eH : dH.Vertex ≃ Fin 6 := v.symm.trans e
  have hCartanH (a c : dH.Vertex) : dH.cartan a c = CartanMatrix.E 6 (eH a) (eH c) := by
    obtain ⟨a, rfl⟩ := v.surjective a
    obtain ⟨c, rfl⟩ := v.surjective c
    have hv : dH.cartan (v a) (v c) = d.cartan a c := root.toHom.pairing
    simpa only [eH, Equiv.trans_apply, Equiv.symm_apply_apply, hCartan] using hv
  obtain ⟨ν, hνc, hν⟩ := d.exists_typeE6BranchCocharacter e hCartan hsc hmark
  obtain ⟨νH, hνHc, hνH⟩ := dH.exists_typeE6BranchCocharacter eH hCartanH hscH (hmarkH eH hCartanH)
  have hφchar : (characterLattice.congr φ).toIntLinearEquiv = root.weightEquiv := by
    ext χ
    exact (hweight χ).symm
  have hφcochar := p.cocharacter_congr_eq_of_character_congr q root φ hφchar
  let α (i : Fin 6) : cocharacterLattice p.torus := p.rootDatum.coroot (e.symm i).val
  let β (i : Fin 6) : cocharacterLattice q.torus := q.rootDatum.coroot (eH.symm i).val
  have hcoroot (i : Fin 6) :
      cocharacterLattice.congr φ (α i) = β i := by
    have hmap := congrArg (fun f => f.toFun (α i)) hφcochar
    have h := root.coroot_coweightMap_apply p.rootDatum q.rootDatum
      (root.indexEquiv (e.symm i).val)
    have hv : (eH.symm i).val = root.indexEquiv (e.symm i).val := rfl
    have h' : root.coweightMap (β i) = α i := by
      change root.coweightMap (q.rootDatum.coroot (eH.symm i).val) = α i
      rw [hv]
      simpa only [Equiv.symm_apply_apply, α] using h
    refine hmap.trans ?_
    change root.coweightEquiv.symm.toFun (α i) = β i
    rw [← h']
    exact root.coweightEquiv.symm_apply_apply (β i)
  have hline : d.typeE6BranchCoweight e ≫ φ.hom = dH.typeE6BranchCoweight eH := by
    change (∑ i : Fin 6, Langlands.CartanE6Root.coefficients i • α i) ≫ φ.hom =
      ∑ i : Fin 6, Langlands.CartanE6Root.coefficients i • β i
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp]
    exact congrArg (Langlands.CartanE6Root.coefficients i • ·) (hcoroot i)
  refine ⟨ν, νH, n, hνc, hνHc, hν, ?_⟩
  rw [baseChange_typeE6BranchCocharacter d e ν hν, baseChange_typeE6BranchCocharacter dH eH νH hνH]
  rw [Category.assoc, ← Category.assoc d.pinning.toSplitPinning.inclusion]
  change CommGroupScheme.groupHom (d.typeE6BranchCoweight e) ≫
    p.inclusion ≫ (((GroupScheme.baseChange b).obj H).innerIso n).hom = _
  rw [hn, ← Category.assoc]
  change CommGroupScheme.groupHom (d.typeE6BranchCoweight e ≫ φ.hom) ≫ q.inclusion = _
  rw [hline]
  rfl

end TitsIndexData

/-- A cochain and a cocycle in the actual centralizer of a primitive split E6
branch line. The absolute coweight equation retains the Cartan numbering of
the original pinned group. -/
structure TypeE6BranchCentralizerCocycle
    {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    {U : Over (Spec (CommRingCat.of F))} (ξ : Cocycle G U) where
  cocharacter : cocharacterLattice d.splitTorus
  line_closed : IsClosedSubgroup (CommGroupScheme.groupHom cocharacter ≫ d.splitInclusion)
  coweight_eq : cocharacterLattice.baseChange (algebraBaseMap F (SeparableClosure F))
    d.pinning.torus (cocharacter ≫ d.torusMap) = d.typeE6BranchCoweight e
  centralizer : GroupScheme (Spec (CommRingCat.of F))
  inclusion : centralizer ⟶ G
  centralizer_closed : IsClosedSubgroup inclusion
  represents : (torusCentralizer (CommGroupScheme.groupHom cocharacter ≫
    d.splitInclusion)).IsRepresentedBy inclusion
  cochain : U ⟶ G.X
  cocycle : Cocycle centralizer U
  factorization : ∀ {T : Over (Spec (CommRingCat.of F))} (a b : T ⟶ U),
    (cocycle.map inclusion).toFun a b = (ξ.twist cochain).toFun a b

set_option backward.isDefEq.respectTransparency false in
/-- Marking the short-arm vertex in both the original group and its pure twist
puts each cocycle into the actual centralizer of the branch line on a finite
Galois refinement. -/
theorem exists_typeE6BranchCentralizerCocycle_of_marked_twist
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hCartan : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hsc : IsSimplyConnected G)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L))
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] (t : LocalGroupIso G H (GaloisCocycle.cover F L))
    (ht : t.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (hHsc : IsSimplyConnected H) (dH : TitsIndexData H)
    (hmark : e.symm 1 ∈ d.distinguishedVertices)
    (hmarkH : ∀ (eH : dH.Vertex ≃ Fin 6),
      (∀ a b, dH.cartan a b = CartanMatrix.E 6 (eH a) (eH b)) →
      eH.symm 1 ∈ dH.distinguishedVertices) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : Algebra L M)
      (_ : IsScalarTower F L M) (_ : FiniteDimensional F M) (_ : IsGalois F M),
      Nonempty (TypeE6BranchCentralizerCocycle d e
        (ξ.refine (GaloisCocycle.coverMap F L M))) := by
  let a := AutomorphicAction.conjugation (𝟙 G)
  let φ : L →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let j := (t.refine (ringTestMap F φ)).toBaseChangeIso
  obtain ⟨ν, νH, n, hνc, -, hν, hmatch⟩ :=
    d.exists_matching_typeE6BranchLines e hCartan hsc hmark dH hHsc hmarkH j
  let χ := CommGroupScheme.groupHom ν ≫ d.splitInclusion
  let ψ := CommGroupScheme.groupHom νH ≫ dH.splitInclusion
  obtain ⟨M, _, _, _, _, ιM, f, hf⟩ :=
    t.exists_finiteGalois_cocharacterMatching φ χ ψ n hmatch
  let : Algebra L M := ιM.toRingHom.toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (ιM.commutes x).symm
  let r := GaloisCocycle.coverMap F L M
  have hr : r = ringTestMap F ιM := Over.OverMorphism.ext rfl
  have hm : ((t.refine r).twist a f).HasDiscrepancy a ((ξ.refine r).twist f) :=
    LocalGroupIso.HasDiscrepancy.twist (ht.refine r) f
  have hc {T : Over (Spec (CommRingCat.of F))} (b c : T ⟶ GaloisCocycle.cover F M) :
      ((ξ.refine r).twist f).toFun b c ∈ (torusCentralizer χ).carrier T :=
    LocalGroupIso.HasDiscrepancy.mem_torusCentralizer_of_cocharacterMatching hm χ ψ
      (by
        intro W s z
        rw [hr]
        exact hf W s z) b c
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, i, hi, -, hrep⟩ := splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
    χ isSplitTorus_gm hsc.isSemisimple.isConnectedReductive.smooth
  let : Mono i.hom.hom := hrep.1
  have hval {T : Over (Spec (CommRingCat.of F))} (b c : T ⟶ GaloisCocycle.cover F M) :
      ∃ y : T ⟶ C.X, y ≫ i.hom.hom = ((ξ.refine r).twist f).toFun b c := by
    apply SubgroupFunctor.mem_range.mp
    rw [hrep.2]
    exact hc b c
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨⟨ν, hνc, hν, C, i, hi, hrep, f, ((ξ.refine r).twist f).lift i hval, ?_⟩⟩⟩
  intro T b c
  exact ((ξ.refine r).twist f).lift_toFun i hval b c

set_option backward.isDefEq.respectTransparency false in
/-- A global short-arm marking theorem supplies the marking of an actual
finite Galois pure twist. -/
theorem exists_typeE6BranchCentralizerCocycle
    (hmark : NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement.{u})
    {F : Type u} [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hCartan : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra F M) (_ : Algebra L M)
      (_ : IsScalarTower F L M) (_ : FiniteDimensional F M) (_ : IsGalois F M),
      Nonempty (TypeE6BranchCentralizerCocycle d e
        (ξ.refine (GaloisCocycle.coverMap F L M))) := by
  let a := AutomorphicAction.conjugation (𝟙 G)
  obtain ⟨H, t, hHa, ht⟩ := finiteGaloisTwistExistence F L G G inferInstance a ξ
  let : IsAffineHom H.X.hom := hHa
  let φ : L →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let j := (t.refine (ringTestMap F φ)).toBaseChangeIso
  have hHsc : IsSimplyConnected H :=
    (isSimplyConnected_fieldExtension_iff (K := SeparableClosure F) H).mp
      ((isSimplyConnected_iff_of_iso j).mp
        ((isSimplyConnected_fieldExtension_iff (K := SeparableClosure F) G).mpr hsc))
  have hHabs : IsAbsolutelyAlmostSimple H :=
    IsAbsolutelyAlmostSimple.of_fieldExtension (K := SeparableClosure F)
      ((habs.baseChange_of_algebraicExtension (K := SeparableClosure F)).of_iso j.symm)
  let : Smooth H.X.hom := hHsc.isSemisimple.isConnectedReductive.smooth
  obtain ⟨dH⟩ := titsIndexExistence F H hHsc.isSemisimple
  exact exists_typeE6BranchCentralizerCocycle_of_marked_twist d e hCartan hsc L ξ t ht hHsc dH
    (hmark F hF G d e hsc habs hCartan)
    (fun eH hCartanH => hmark F hF H dH eH hHsc hHabs hCartanH)

end Langlands.GroupScheme
