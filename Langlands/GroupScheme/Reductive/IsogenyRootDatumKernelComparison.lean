import Langlands.GroupScheme.Reductive.IsogenyUnipotentKernel
import Langlands.GroupScheme.Reductive.IsogenyKernelCentralityAdapter
import Langlands.GroupScheme.Reductive.IsogenyRootDatumComparisons
import Langlands.GroupScheme.Rational.GenericCocharacter
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Full-kernel comparisons from central actual root-datum maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open LocalSplitCell

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H}
    {q : G ⟶ H} {t : T ⟶ T'} {J J' : Type u} [Finite J] [Finite J']
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [Q.IsReduced] {p : ℕ}

/-- Centrality turns the actual character pullback into an exact root equation. -/
theorem root_pullback_eq_of_central_rootDatumIsogeny
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) (hf : f.IsCentral) (r : J) :
    t ≫ Q.root (f.indexEquiv.symm r) = P.root r := by
  rw [← hw, f.root_weightMap, hf]
  simp

/-- Exact root pullback and actual root representatives make the full dynamic
unipotent kernel trivial, including on nonreduced test schemes. -/
theorem IsRootDatumOf.unipotent_kernel_trivial_of_central_rootDatumIsogeny
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) (hf : f.IsCentral)
    (u : J → (Ga k ⟶ G))
    (hu : ∀ r, (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy (u r))
    (hv : ∀ r, (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy
      (u r ≫ q))
    (ν : cocharacterLattice T) (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X)
    (hx : x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z)
    (hq : x ≫ q.hom.hom = 1) : x = 1 :=
  hP.unipotent_kernel_trivial_of_root_correspondence hG hH hT hT' hi hi' hQ q t
    f.indexEquiv.symm (root_pullback_eq_of_central_rootDatumIsogeny f hw hf)
    u hu hv ν Z x hx hq

section Finite

variable [IsFinite q.hom.hom.left]

/-- A central actual root-datum map and matching root representatives give an
actual factorization of the entire ambient kernel through the source torus. -/
def kernelTorusFactorOfCentralRootDatumIsogeny
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) (hf : f.IsCentral)
    (u : J → (Ga k ⟶ G))
    (hu : ∀ r, (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy (u r))
    (hv : ∀ r, (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy
      (u r ≫ q)) : kernel q ⟶ T.toGrp := by
  have : Smooth G.X.hom := hG.smooth
  let ν := genericCocharacterOfIsSplitTorus hT i
  have hν : IsGenericCocharacter i ν := genericCocharacterOfIsSplitTorus_spec hT i
  refine kernelTorusFactorOfGenericUnipotentKernels hG q hT i hi ν hν ?_ ?_
  · exact hP.unipotent_kernel_trivial_of_central_rootDatumIsogeny
      hG hH hT hT' hi hi' hQ f hw hf u hu hv ν
  · rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact hP.unipotent_kernel_trivial_of_central_rootDatumIsogeny
      hG hH hT hT' hi hi' hQ f hw hf u hu hv (-ν)

theorem kernelTorusFactorOfCentralRootDatumIsogeny_comp
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) (hf : f.IsCentral)
    (u : J → (Ga k ⟶ G))
    (hu : ∀ r, (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy (u r))
    (hv : ∀ r, (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy
      (u r ≫ q)) :
    kernelTorusFactorOfCentralRootDatumIsogeny hG hH hT hT' hi hi' hP hQ f hw hf u hu hv ≫
      i = kernelι q := by
  unfold kernelTorusFactorOfCentralRootDatumIsogeny
  exact kernelTorusFactorOfGenericUnipotentKernels_comp _ _ _ _ _ _ _ _ _

/-- For a commuting torus square, centrality of the actual root-datum map
forces centrality of the full ambient kernel once root representatives match. -/
theorem isCentral_kernelι_of_central_rootDatumIsogeny
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hsquare : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) (hf : f.IsCentral)
    (u : J → (Ga k ⟶ G))
    (hu : ∀ r, (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy (u r))
    (hv : ∀ r, (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy
      (u r ≫ q)) : IsCentral (kernelι q) := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion i'.hom.hom.left := hi'.2.1
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let κ := kernelTorusFactorOfCentralRootDatumIsogeny
    hG hH hT hT' hi hi' hP hQ f hw hf u hu hv
  have hκ : κ ≫ i = kernelι q :=
    kernelTorusFactorOfCentralRootDatumIsogeny_comp
      hG hH hT hT' hi hi' hP hQ f hw hf u hu hv
  apply isCentral_kernelι_of_torusFactor q i i' (CommGroupScheme.groupHom t) hsquare κ hκ
  apply isCentral_kernelι_comp_of_roots_comapHom hT hT' i (CommGroupScheme.groupHom t)
  intro α hα
  rw [← hP.2.1] at hα
  obtain ⟨r, rfl⟩ := hα
  exact ⟨Q.root (f.indexEquiv.symm r),
    (root_pullback_eq_of_central_rootDatumIsogeny f hw hf r).symm⟩

end Finite

/-- An actual ambient isogeny with the preceding full central kernel is a
central isogeny; finite presentation follows over the locally Noetherian target. -/
theorem isCentralIsogeny_of_central_rootDatumIsogeny
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hq : IsIsogeny q) (hsquare : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) (hf : f.IsCentral)
    (u : J → (Ga k ⟶ G))
    (hu : ∀ r, (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy (u r))
    (hv : ∀ r, (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy
      (u r ≫ q)) : IsCentralIsogeny q := by
  have : IsFinite q.hom.hom.left := hq.1
  have : Smooth H.X.hom := hH.smooth
  have : IsLocallyNoetherian H.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact ⟨hq, inferInstance, isCentral_kernelι_of_central_rootDatumIsogeny
    hG hH hT hT' hi hi' hP hQ hsquare f hw hf u hu hv⟩

/-- Matching root representatives in the factor-one case complete the
centrality comparison for any supplied actual-map root-datum isogeny. -/
theorem isCentralIsogeny_iff_isCentral_rootDatumIsogeny_of_root_representations
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hq : IsIsogeny q) (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ)
    (hrep : f.IsCentral → ∀ r, ∃ u : Ga k ⟶ G,
      (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy u ∧
      (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy (u ≫ q)) :
    IsCentralIsogeny q ↔ f.IsCentral := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have : Smooth H.X.hom := hH.smooth
  constructor
  · intro hc
    exact hc.isCentral_rootDatumIsogeny hP hQ hT hT' ht hsquare f hw
  · intro hf
    choose u hu hv using hrep hf
    exact isCentralIsogeny_of_central_rootDatumIsogeny
      hG hH hT hT' hi hi' hP hQ hq hsquare f hw hf u hu hv

/-- The same root-representation input gives the ambient isomorphism comparison,
retaining centrality and bijectivity on the full character lattice. -/
theorem isIso_iff_central_bijective_rootDatumIsogeny_of_root_representations
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hq : IsIsogeny q) (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ)
    (hrep : f.IsCentral → ∀ r, ∃ u : Ga k ⟶ G,
      (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy u ∧
      (RelativeRoot.subgroup i' (Q.root (f.indexEquiv.symm r))).IsRepresentedBy (u ≫ q)) :
    IsIso q ↔ f.IsCentral ∧ Function.Bijective f.weightMap := by
  have : Smooth G.X.hom := hG.smooth
  exact isIso_iff_central_bijective_rootDatumIsogeny hT hT' hi hi'.2.1 hsquare
    (maximalTorusCentralizer k G hG T i hi) f hw
    (isCentralIsogeny_iff_isCentral_rootDatumIsogeny_of_root_representations
      hG hH hT hT' hi hi' hP hQ hq ht hsquare f hw hrep)

end Langlands.GroupScheme
