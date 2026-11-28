import Langlands.GroupScheme.Rational.GaloisBorelFaceCentralizer
import Langlands.GroupScheme.Rational.TorusCentralizerImage
import Langlands.GroupScheme.Reductive.TitsKernelTorus
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof

/-! # Derived groups of the descended Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.RootDatumNegation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (p : GaloisPinningData F E G)

local notation "b" => algebraBaseMap F E
local notation "BG" => GroupScheme.baseChange b
local notation "BC" => CommGroupScheme.baseChange b
local notation "GE" => Functor.obj BG G
local notation "TE" => Functor.obj BC p.torus
local notation "tE" => CategoryTheory.Functor.map BG p.inclusion
local notation "S" => Spec (CommRingCat.of F)

/-- An actual Levi subgroup recovered from a cocharacter centralizer over the
splitting field, together with its derived group and the induced maximal torus. -/
structure GaloisBorelFaceDerived (ν : cocharacterLattice TE) where
  levi : GroupScheme S
  inclusion : levi ⟶ G
  isClosed : IsClosedSubgroup inclusion
  isReductive : IsConnectedReductive levi
  isCentralizer : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)).IsRepresentedBy
    ((BG).map inclusion)
  leviTorusInclusion : p.torus.toGrp ⟶ levi
  leviTorus_comp : leviTorusInclusion ≫ inclusion = p.inclusion
  leviTorus_maximal : IsMaximalTorus leviTorusInclusion
  derived : GroupScheme S
  derivedInclusion : derived ⟶ levi
  isDerived : IsDerivedSubgroup derivedInclusion
  isSimplyConnected : IsSimplyConnected derived
  torus : CommGroupScheme S
  torusInclusion : torus.toGrp ⟶ derived
  torus_maximal : IsMaximalTorus torusInclusion
  torusMap : torus ⟶ p.torus
  torusMap_closed : IsClosedSubgroup (CommGroupScheme.groupHom torusMap)
  torus_square : torusInclusion ≫ derivedInclusion =
    CommGroupScheme.groupHom torusMap ≫ leviTorusInclusion

omit [LocallyOfFiniteType G.X.hom] in
private theorem range_le_descendedCentralizer
    {M : GroupScheme S} {i : M ⟶ G} (hi : IsClosedSubgroup i)
    (ν : cocharacterLattice TE)
    (hc : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)).IsRepresentedBy
      ((BG).map i)) : SubgroupFunctor.range p.inclusion ≤ SubgroupFunctor.range i := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F E
  let : Surjective b := hs
  let : Flat b := hf
  let : QuasiCompact b := hq
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.le_range_of_baseChange_le b i
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom, hc.2]
  exact (range_le_torusCentralizer (T := TE) tE).trans
    (torusCentralizer_le_dynamicCentralizer (T := TE) tE (CommGroupScheme.groupHom ν))

omit [LocallyOfFiniteType G.X.hom] in
private theorem isSimplyConnected_derived_face
    [Algebra.IsAlgebraic F E] (hsc : IsSimplyConnected G)
    {M D : GroupScheme S} (i : M ⟶ G) (d : D ⟶ M) (hM : IsConnectedReductive M)
    (hd : IsDerivedSubgroup d) (ν : cocharacterLattice TE)
    (hc : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ tE)).IsRepresentedBy
      ((BG).map i)) : IsSimplyConnected D := by
  let : IsAffineHom (GE).X.hom := p.isConnectedReductive.isAffineHom
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let χ := CommGroupScheme.groupHom ν ≫ tE
  let a := isSplitTorus_gm.dominantFactorization χ
  have ha : (torusCentralizer a.inclusion).IsRepresentedBy ((BG).map i) := by
    rw [← dynamicCentralizer_eq_torusCentralizer_image χ a]
    exact hc
  have hdE := hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b M)
  exact IsSimplyConnected.of_algebraicExtension
    (splitTorusCentralizerDerivedSimplyConnected E GE
      (isSimplyConnectedFieldExtension F E G hsc) a.image a.inclusion a.isSplitSubtorus
      ((BG).obj M) ((BG).map i) ha ((BG).obj D) ((BG).map d) hdE)

omit [LocallyOfFiniteType G.X.hom] in
/-- The derived group and torus of a descended cocharacter centralizer. -/
theorem exists_galoisBorelFaceDerived_of_invariantCentralizer [IsGalois F E] (hsc : IsSimplyConnected G)
    (ht : IsMaximalTorus p.inclusion) (ν : cocharacterLattice TE)
    (h : ∀ σ : E ≃ₐ[F] E, SubgroupFunctor.galoisTransport F E G σ
      (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ (BG).map p.inclusion)) =
      Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ (BG).map p.inclusion)) :
    Nonempty (GaloisBorelFaceDerived p ν) := by
  obtain ⟨M, i, hi, hM, hc⟩ := p.exists_centralizer_descent ν h
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let rep : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  have hr := range_le_descendedCentralizer p hi ν hc
  let tM : p.torus.toGrp ⟶ M := rep.factorHom p.inclusion hr
  have htM : tM ≫ i = p.inclusion := rep.factorHom_comp p.inclusion hr
  have hmax : IsMaximalTorus tM := IsMaximalTorus.of_comp hi (by rw [htM]; exact ht)
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth M.X.hom := hM.smooth
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability F M
  have hDsc := isSimplyConnected_derived_face p hsc i d hM hd ν hc
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let T₀ := commutativeSubgroupIntersection tM d
  let t₀ := commutativeSubgroupIntersectionSnd tM d
  let f : T₀ ⟶ p.torus := Additive.ofMul (commutativeSubgroupIntersectionFst tM d)
  exact ⟨⟨M, i, hi, hM, hc, tM, htM, hmax, D, d, hd, hDsc, T₀, t₀,
    isMaximalTorus_commutativeSubgroupIntersectionSnd_derived hM d hd tM hmax,
    f, isClosedSubgroup_commutativeSubgroupIntersectionFst tM d hd.1,
    (commutativeSubgroupIntersection_condition tM d).symm⟩⟩

/-- A Galois-stable cocharacter centralizer in a simply connected group
supplies an actual simply connected derived group over the original field. -/
theorem exists_galoisBorelFaceDerived [IsGalois F E] (hsc : IsSimplyConnected G)
    (ht : IsMaximalTorus p.inclusion) (ν : cocharacterLattice TE)
    (hs : ∀ σ : E ≃ₐ[F] E, p.galoisAction σ = (p.starAction σ).val ∨
      p.galoisAction σ = negAut p.toSplitPinning.rootDatum * (p.starAction σ).val)
    (hν : ∀ (σ : E ≃ₐ[F] E) (a : p.base.support),
      latticePairing TE (p.rootDatum.root (p.starSupport σ a).val) ν =
        latticePairing TE (p.rootDatum.root a.val) ν) :
    Nonempty (GaloisBorelFaceDerived p ν) :=
  exists_galoisBorelFaceDerived_of_invariantCentralizer p hsc ht ν
    (fun σ => p.galoisTransport_faceCentralizer σ ν (hs σ) (hν σ))

end Langlands.GroupScheme
