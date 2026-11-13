import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerRootModel
import Langlands.GroupScheme.Rational.DerivedRootDatumComparison
import Langlands.GroupScheme.Rational.DerivedTorusCentralComplement
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Roots of the derived subgroup of a split-torus centralizer -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {F : Type u} [Field F]

/-- Let `j : M ⟶ G` represent the centralizer of a split torus `a : A ⟶ G`, let
`t : T ⟶ G` be a split torus with root datum `P` that factors through a maximal
torus `tM` of `M` and contains `A` through `f`, and let `tD : TD ⟶ D` be a split
maximal torus of the actual derived subgroup `i : D ⟶ M` with a map `τ : TD ⟶ T`
compatible with the inclusions. Then for every root datum `Q` of `tD`, the roots
of `Q` correspond bijectively to the roots of `P` that vanish on `A`, by character
restriction along `τ` and cocharacter pushforward along `τ`. -/
theorem exists_derivedCentralizerRootEquiv
    {G M D : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    {A T TD : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ G) (hA : IsSplitTorus A.toGrp)
    (j : M ⟶ G) (hj : (torusCentralizer a).IsRepresentedBy j)
    (hM : IsConnectedReductive M)
    (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf t P)
    (tM : T.toGrp ⟶ M) (htM : tM ≫ j = t) (htMmax : IsMaximalTorus tM)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ t = a)
    (i : D ⟶ M) (hi : IsDerivedSubgroup i)
    (tD : TD.toGrp ⟶ D) (hTD : IsSplitTorus TD.toGrp) (htDmax : IsMaximalTorus tD)
    (τ : TD ⟶ T) (hsq : tD ≫ i = CommGroupScheme.groupHom τ ≫ tM)
    {K : Type u} {Q : RootDatum K (characterLattice TD) (cocharacterLattice TD)}
    (hQ : IsRootDatumOf tD Q) :
    ∃ φ : K ≃ {p : J // f ≫ P.root p = 0}, ∀ q,
      Q.root q = τ ≫ P.root (φ q) ∧ Q.coroot q ≫ τ = P.coroot (φ q) := by
  have : Smooth M.X.hom := hM.smooth
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have hjc : IsClosedSubgroup j := hA.isClosedSubgroup_torusCentralizer a hj
  have htc : IsClosedSubgroup t := by
    rw [← htM]
    exact htMmax.2.1.comp hjc
  have : IsClosedImmersion t.hom.hom.left := htc
  have : Finite (weylImage t) := splitTorusWeylImageFinite F G T hT t htc
  obtain ⟨L, _, R, hR, -⟩ := rootDatumExistence F M hM T hT tM htMmax
  have hfactor := relativeRoots_splitTorusCentralizer_factor a hA t tM j hj htM f hf
  have hroots : roots tM ⊆ roots t := by
    intro α hα
    change α ∈ relativeRoots tM at hα
    rw [hfactor] at hα
    exact hα.1
  let Emb := hP.sameTorusSubgroupEmbedding t tM j htM hR hroots
  have hs : Set.range R.root = P.root '' {p | f ≫ P.root p = 0} := by
    rw [hR.2.1]
    change relativeRoots tM = _
    rw [hfactor]
    ext α
    constructor
    · rintro ⟨hα, hzero⟩
      have hmem : α ∈ Set.range P.root := by
        rw [hP.2.1]
        exact hα
      obtain ⟨p, rfl⟩ := hmem
      exact ⟨p, hzero, rfl⟩
    · rintro ⟨p, hzero, rfl⟩
      refine ⟨?_, hzero⟩
      change P.root p ∈ roots t
      rw [← hP.2.1]
      exact Set.mem_range_self p
  have hrange : Set.range Emb.index = {p | f ≫ P.root p = 0} := Emb.range_index_eq _ hs
  have : Mono tM.hom.hom.left := htMmax.2.1.mono
  have : Finite (weylImage tM) :=
    splitTorusWeylImageFinite F M T hT tM htMmax.2.1
  let Z := derivedTorusCentralComplement τ tD tM i hM hi
    (htMmax.isMaximalSplitTorus hT) (htDmax.isMaximalSplitTorus hTD) hsq hR
  have := Z.flat
  have := Z.surjective
  let h := hR.derivedRootDatumHom τ Z.map tD tM i hsq hTD Z.isSplit Z.isCentral hi hT hQ
  let φ : K ≃ {p : J // f ≫ P.root p = 0} :=
    (h.indexEquiv.symm.trans (Equiv.ofInjective Emb.index Emb.index.injective)).trans
      (Equiv.subtypeEquivRight fun p => Set.ext_iff.mp hrange p)
  have hφ (q : K) : (φ q : J) = Emb.index (h.indexEquiv.symm q) := rfl
  refine ⟨φ, fun q => ⟨?_, ?_⟩⟩
  · rw [hφ, Emb.root_eq]
    have h1 := h.root_weightMap_apply R Q (h.indexEquiv.symm q)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  · rw [hφ, Emb.coroot_eq]
    exact h.coroot_coweightMap_apply R Q q

end Langlands.GroupScheme
