import Langlands.GroupScheme.AlgebraicFundamentalGroupCorootTransport
import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugatorExistence
import Langlands.GroupScheme.Reductive.RootDatumWeylProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusProof
import Langlands.GroupScheme.Rational.CoweightCocenterCharacters
import Langlands.GroupScheme.Torus.SplitDescent
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-! # Normalizing points act trivially modulo the coroot image -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a separably closed field every torus is split: it splits over a finite Galois
extension, which is trivial. -/
theorem toriAreSplit_of_isSepClosed (E : Type u) [Field E] [IsSepClosed E] :
    ToriAreSplit E := by
  intro T hT
  obtain ⟨K, hK, hAlg, _, hGal, hsplitK⟩ := torusFiniteGaloisSplitting E T hT
  let : Field K := hK
  let : Algebra E K := hAlg
  have : IsGalois E K := hGal
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap E K))) :=
    isIso_SpecMap_iff.mpr (IsSepClosed.algebraMap_bijective E K)
  exact hsplitK.of_baseChange_of_isIso _

namespace AlgebraicFundamentalGroup

/-- Every element of the Weyl group of an integral root pairing moves each coweight by an
element of the coroot span. -/
theorem coweightEquiv_sub_mem_corootSpan {Idx M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing Idx ℤ M N) {w : RootPairing.Aut P} (hw : w ∈ P.weylGroup) (y : N) :
    w.coweightEquiv y - y ∈ P.corootSpan ℤ := by
  induction hw using RootPairing.weylGroup.induction generalizing y with
  | mem i =>
    rw [RootPairing.Equiv.reflection_coweightEquiv, RootPairing.coreflection_apply,
      sub_sub_cancel_left]
    exact neg_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  | one => simp
  | mul x z _ _ hx hz =>
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin,
      LinearEquiv.trans_apply]
    have := add_mem (hz (x.coweightEquiv y)) (hx y)
    rwa [sub_add_sub_cancel] at this

namespace Choice

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A cocharacter of a torus of the base-changed simply connected cover, pushed to the base
change of the chosen maximal torus along a compatible homomorphism, lies in the coroot
image. -/
theorem comp_mem_corootImage (b : Choice k G) {S : CommGroupScheme (Spec (CommRingCat.of E))}
    (iS : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj b.cover)
    (φ : S ⟶ (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
    (h : iS ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map b.covering ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map b.derivedInclusion =
      CommGroupScheme.groupHom φ ≫ (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion)
    (x : cocharacterLattice S) : x ≫ φ ∈ b.corootImage E := by
  refine b.mem_corootImage_of_lift (CommGroupScheme.groupHom x ≫ iS) (x ≫ φ) ?_
  rw [Functor.map_comp, Category.assoc, h, ← Category.assoc]
  rfl

/-- Over a separable closure, the coroots of every root datum of the base-changed chosen
maximal torus lie in the coroot image: they come from the simply connected cover through
the derived subgroup. -/
theorem corootSpan_le_corootImage [IsSepClosure k E] (hG : IsConnectedReductive G)
    (b : Choice k G) {J : Type u}
    {P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj
      b.torus)) (b.lattice E)}
    (hP : haveI := (connectedReductiveFieldExtensionStatement k E G hG).isAffineHom
      IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
        ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion) P) :
    P.corootSpan ℤ ≤ b.corootImage E := by
  have : IsSepClosed E := IsSepClosure.sep_closed k
  have hsplit := toriAreSplit_of_isSepClosed E
  have hGE := connectedReductiveFieldExtensionStatement k E G hG
  have := hGE.isAffineHom
  have := hGE.smooth
  have hcov := b.isCover.fieldBaseChange E
  have hD := hcov.isSimplyConnectedCover.isSemisimple.isConnectedReductive
  have hC := hcov.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  have := hD.isAffineHom
  have := hD.smooth
  have := hC.isAffineHom
  have hiE := isMaximalSplitTorus_baseChange (E := E) hG b
  obtain ⟨SD, j, e, hj, -, hje, SC, iC, f, hiC, hiCπ, hf, hcomp, -⟩ :=
    simplyConnectedDerivedCoverSplitTorus E _ _ _ _ _ hcov _ _ hiE
  have hjmax := hj.isMaximalTorus hsplit
  have hiCmax := hiC.isMaximalTorus hsplit
  obtain ⟨L, _, U, hU, -⟩ := rootDatumExistence E _ hD SD hj.1.1 j hjmax
  obtain ⟨K, _, V, hV, -⟩ := rootDatumExistence E _ hC SC hiC.1.1 iC hiCmax
  obtain ⟨g, -, hg, -⟩ := centralIsogenyRootDatumHom E _ _ hC hD SC SD hiC.1.1 hj.1.1 iC j
    hiCmax hjmax _ f hcov.isSimplyConnectedCover.isCentralIsogeny hiCπ K L V U hV hU
  have hspan := IsRootDatumOf.map_derived_corootSpan_eq_coweight_zero hP hP (𝟙 _)
    (Category.comp_id _) hGE _ hcov.isDerivedSubgroup j hjmax (hiE.isMaximalTorus hsplit) e
    hje.symm hiE.1.1 hj.1.1 hiE.1.2 hU 0 (by ext α; simp)
  have hzero : {p | P.root' p 0 = 0} = Set.univ := by ext p; simp
  rw [hzero, Set.image_univ] at hspan
  change Submodule.span ℤ (Set.range P.coroot) ≤ _
  rw [← hspan, Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  have hr : U.coroot r = V.coroot (g.indexEquiv r) ≫ f := by
    rw [← hg, RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]
  change RealTorusSpace.cocharacterMapInt e (U.coroot r) ∈ b.corootImage E
  rw [hr]
  change (V.coroot (g.indexEquiv r) ≫ f) ≫ e ∈ b.corootImage E
  rw [Category.assoc]
  refine b.comp_mem_corootImage iC (f ≫ e) ?_ _
  exact hcomp

end Choice

/-- A point normalizing a split maximal torus of a connected reductive group acts on the
cocharacters through a Weyl group element of any root datum of the torus. -/
theorem IsNormalizingPoint.exists_weylGroup {K : Type u} [Field K]
    {H : GroupScheme (Spec (CommRingCat.of K))} (hH : IsConnectedReductive H)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ H} (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : haveI := hH.isAffineHom; IsRootDatumOf i P)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) :
    ∃ w ∈ P.weylGroup, ∀ χ, w.weightEquiv χ = σ.inv ≫ χ := by
  have := hH.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hW := (weylGroup K H hH T hT i hi J P hP).1
  have hm : n ∈ normalizerPoints i := (mem_normalizerPoints i).2 ⟨σ, hn⟩
  have hmem : weylAction i ⟨n, hm⟩ ∈ weylImage i := MonoidHom.mem_range.2 ⟨_, rfl⟩
  rw [hW] at hmem
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 hmem
  refine ⟨w, hw, fun χ => ?_⟩
  have h1 : RootPairing.Equiv.weightHom P w χ = w.weightEquiv χ := rfl
  rw [← h1, hwe]
  -- The normalizer element must be given explicitly: unifying `↑?n` with `n` times out.
  exact weylAction_eq i (n := ⟨n, hm⟩) hn χ

/-- A point normalizing a split maximal torus of a connected reductive group moves every
cocharacter by an element of the coroot span of any root datum of the torus. -/
theorem IsNormalizingPoint.sub_mem_corootSpan {K : Type u} [Field K]
    {H : GroupScheme (Spec (CommRingCat.of K))} (hH : IsConnectedReductive H)
    {T : CommGroupScheme (Spec (CommRingCat.of K))} (hT : IsSplitTorus T.toGrp)
    {i : T.toGrp ⟶ H} (hi : IsMaximalTorus i) {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : haveI := hH.isAffineHom; IsRootDatumOf i P)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (ξ : cocharacterLattice T) :
    ξ ≫ σ.hom - ξ ∈ P.corootSpan ℤ := by
  obtain ⟨w, hw, hweight⟩ := IsNormalizingPoint.exists_weylGroup hH hT hi hP hn
  have hcoweight : ∀ y : cocharacterLattice T, w.coweightEquiv y = y ≫ σ.inv := fun y => by
    apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).1
    apply LinearMap.ext
    intro χ
    rw [LinearMap.flip_apply, LinearMap.flip_apply, ← RootPairing.Equiv.toLinearMap_weightEquiv,
      hweight, hP.1, latticePairing_apply, latticePairing_apply, Category.assoc]
  have key := coweightEquiv_sub_mem_corootSpan P hw (ξ ≫ σ.hom)
  rw [hcoweight, Category.assoc, Iso.hom_inv_id, Category.comp_id] at key
  rw [← neg_sub]
  exact neg_mem key

namespace Choice

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Over a separable closure, a geometric point normalizing the base change of the chosen
maximal torus acts on its cocharacters trivially modulo the coroot image. -/
theorem IsConjugationComparison.sub_mem_corootImage [IsSepClosure k E]
    (hG : IsConnectedReductive G) {b : Choice k G}
    {n : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {σ : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : b.IsConjugationComparison E b n σ) (ξ : b.lattice E) :
    ξ ≫ σ.hom - ξ ∈ b.corootImage E := by
  have : IsSepClosed E := IsSepClosure.sep_closed k
  have hGE := connectedReductiveFieldExtensionStatement k E G hG
  have := hGE.isAffineHom
  have hiE := isMaximalSplitTorus_baseChange (E := E) hG b
  have hiEmax := hiE.isMaximalTorus (toriAreSplit_of_isSepClosed E)
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence E _ hGE _ hiE.1.1 _ hiEmax
  exact corootSpan_le_corootImage hG b hP
    (IsNormalizingPoint.sub_mem_corootSpan hGE hiE.1.1 hiEmax hP h ξ)

end Choice

end AlgebraicFundamentalGroup

end Langlands.GroupScheme
