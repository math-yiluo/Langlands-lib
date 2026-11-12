import Langlands.GroupScheme.Rational.GenericParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.BruhatOpenCellProof
import Langlands.GroupScheme.Rational.DerivedCoverNormalizerLift
import Langlands.GroupScheme.Dynamic.FlagQuotientProof
import Langlands.GroupScheme.Dynamic.BruhatCellLimit
import Langlands.GroupScheme.Dynamic.ProperAffineExtension
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.FixedCosetFactorization

/-! # Proof: the rational Bruhat decomposition -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every rational point of a homogeneous quotient by a closed representative of a dynamic
parabolic of a connected reductive group lifts to a rational point of the group. -/
theorem exists_rational_lift_of_dynamicParabolic
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {P U : GroupScheme (Spec (CommRingCat.of k))} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP) (hPc : IsClosedSubgroup iP)
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iU)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iP).carrier T)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :
    ∃ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, h ≫ q = x := by
  let := hG.isAffineHom
  let := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Mono iP.hom.hom := hP.1
  have hlift' : ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = p := by
    rcases finite_or_infinite k with hfin | hinf
    · let : Finite k := hfin
      let : Smooth P.X.hom := (dynamicSmooth k G χ P iP).1 hP
      let : IsAffineHom P.X.hom := hPc.isAffineHom
      have hPconn := DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic G χ hP
      exact Dynamic.rational_lifts_of_finite_torsor k G P q iP hf
        finiteFieldTorsorPointStatement.{u} hPconn
    · let : Infinite k := hinf
      let : IsOpenImmersion (QuotientCell.multiplication iP iU.hom.hom).left :=
        oppositeCellStatement k G χ U P iU iP hU hP
      let seed := Dynamic.flagQuotientCell k iP iU q hf
      have hseed := Dynamic.range_identity_subset_flagQuotientCell k iP iU q hf
      rw [rationalPointEquiv_left] at hseed
      exact Dynamic.rational_lifts_of_reductive_density k G (SubgroupFunctor.range iP) q hf
        reductiveRationalPointDensity.{u} hG seed.1 seed.2 hseed
        (Dynamic.flagQuotientCell_comp k iP iU q hf)
  obtain ⟨h, hh⟩ := hlift' (rationalPointEquiv k Q x)
  refine ⟨(rationalPointEquiv k G.X).symm h, ?_⟩
  apply (rationalPointEquiv k Q).injective
  rw [rationalPointEquiv_natural, Equiv.apply_symm_apply, hh]

/-- **Rational Bruhat covering**, for arbitrary closed representatives of `P_G(ν ≫ i)` and
of the opposite contracting subgroup. Here `ν` is a cocharacter of a maximal split torus `i`
whose dynamic centralizer is the centralizer of the whole torus. -/
theorem exists_bruhat_factorization_of_represented
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hZχ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    {P U : GroupScheme (Spec (CommRingCat.of k))} {iP : P ⟶ G} {iU : U ⟶ G}
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (hPc : IsClosedSubgroup iP)
    (hU : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ (CommGroupScheme.groupHom ν ≫ i))).IsRepresentedBy
        iU)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ n ∈ normalizerPoints i,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
      ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
        g = p * n * q := by
  let := hG.isAffineHom
  let := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Mono iP.hom.hom := hP.1
  have hPpar : IsParabolicSubgroup iP :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG iP hPc _ hP.2
  -- the proper homogeneous quotient `G / P`
  obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqcc, hf⟩ :=
    smoothSubgroupQuotientExistence k G P iP hPc hPpar.smooth
  have hQproper : IsProper Q.hom :=
    parabolicSubgroupQuotientProper k G hG.connectedSpace P iP hPpar Q q
      hsep hft hqc hsm hsurj hqcc hf
  let : IsSeparated Q.hom := hsep
  let : IsProper Q.hom := hQproper
  let : Smooth q.left := hsm
  let : Surjective q.left := hsurj
  let : QuasiCompact q.left := hqcc
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range iP) q hf
  have hact : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q :=
    fun _ g h => Dynamic.flagQuotientSchemeAction_act_lift G _ q hf g h
  -- the orbit of the coset of `g` under `ν ≫ i` extends over the affine line
  obtain ⟨e, he⟩ := AffineLine.exists_extension_of_isProper Q
    ((a.restrict (CommGroupScheme.groupHom ν ≫ i)).gmOrbit (g ≫ q))
  have hfix := SchemeAction.IsGmOrbitExtension.isFixed_evalZero _ he
  -- a rational lift `h₀` of its limit; the cocharacter fixes its coset
  obtain ⟨h₀, hh₀⟩ :=
    exists_rational_lift_of_dynamicParabolic hG _ hP hPc hU q hf (Dynamic.evalZero e)
  have hfixed : ∀ (V : Over (Spec (CommRingCat.of k)))
      (t : V ⟶ (Gm (Spec (CommRingCat.of k))).toGrp.X),
      ((t ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom) * G.constantPoint h₀ V) ≫ q =
        G.constantPoint h₀ V ≫ q := by
    intro V t
    have e' := hfix V (Over.homMk V.hom (by simp)) t
    rw [SchemeAction.restrict_act, ← hh₀, ← Category.assoc] at e'
    change a.act (t ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom) (G.constantPoint h₀ V ≫ q) =
      G.constantPoint h₀ V ≫ q at e'
    rwa [hact] at e'
  have hle : SubgroupFunctor.range ((CommGroupScheme.groupHom ν ≫ i) ≫
      (G.innerIso h₀⁻¹).hom) ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
    rw [← hP.2]
    exact range_conjugate_le_of_fixed_coset _ iP q hf h₀ hfixed
  -- conjugate the cocharacter `h₀⁻¹ (ν ≫ i) h₀` of `P` into the torus inside `P(k)`
  obtain ⟨p, hp, ρ, hρ⟩ := exists_parabolic_conj_into_torus hG hi ν hZχ _ hle
  have hcancel : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (G.innerIso x).hom ≫ (G.innerIso x⁻¹).hom = 𝟙 G := fun x => by
    rw [← innerIso_mul_hom, inv_mul_cancel, innerIso_one_hom]
  have hcancel' : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (G.innerIso x⁻¹).hom ≫ (G.innerIso x).hom = 𝟙 G := fun x => by
    rw [← innerIso_mul_hom, mul_inv_cancel, innerIso_one_hom]
  have hnχ : CommGroupScheme.groupHom (Additive.ofMul ρ) ≫ i ≫
      (G.innerIso (h₀ * p⁻¹)).hom = CommGroupScheme.groupHom ν ≫ i := by
    change ρ ≫ i ≫ (G.innerIso (h₀ * p⁻¹)).hom = _
    rw [← Category.assoc, ← hρ, innerIso_mul_hom]
    simp only [Category.assoc]
    rw [reassoc_of% (hcancel p), hcancel' h₀, Category.comp_id]
  -- the point `n = h₀ p⁻¹` normalizes the torus
  have hn : h₀ * p⁻¹ ∈ normalizerPoints i := by
    apply hi.mem_normalizerPoints_of_commute_conjugate (h₀ * p⁻¹)
    intro V x y
    have hmem : x ≫ (i ≫ (G.innerIso (h₀ * p⁻¹)).hom).hom.hom ∈
        (torusCentralizer i).carrier V := by
      rw [← hZχ, ← hnχ]
      exact range_le_centralizer_groupHom_comp (i ≫ (G.innerIso (h₀ * p⁻¹)).hom)
        (Additive.ofMul ρ) V (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    simpa only [Category.id_comp] using hmem V (𝟙 V) y
  -- and lies over the limit
  have hnq : Dynamic.evalZero e = (h₀ * p⁻¹) ≫ q := by
    rw [← hh₀]
    apply (hf _ h₀ (h₀ * p⁻¹)).mpr
    rw [inv_mul_cancel_left, hP.2]
    exact ((Dynamic.parabolic _).carrier _).inv_mem hp
  -- the opposite cell at the limit places `g` in `P(k) n P(k)`
  obtain ⟨b₁, b₂, hg⟩ := Dynamic.BruhatCellLimit.exists_eq_mul_mul_of_mem_normalizerPoints
    iP i q a hact hf (CommGroupScheme.groupHom ν) hP (h₀ * p⁻¹) g hn he hnq
  refine ⟨h₀ * p⁻¹, hn, b₁ ≫ iP.hom.hom, ?_, b₂ ≫ iP.hom.hom, ?_, hg⟩
  · rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨b₁, rfl⟩
  · rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨b₂, rfl⟩

/-- **Rational Bruhat covering.** For a maximal split torus `i` of a connected reductive group
and a cocharacter `ν` of it whose dynamic centralizer is the centralizer of the whole torus,
every rational point lies in a double coset `P(k) n P(k)` of `P = P_G(ν ≫ i)` with `n`
normalizing `i`. -/
theorem exists_bruhat_factorization
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hZχ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ n ∈ normalizerPoints i,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
      ∃ q ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
        g = p * n * q := by
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact exists_bruhat_factorization_of_represented hG hi ν hZχ
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
    (Dynamic.Affine.isRepresentedBy_unipotentHom _) g

/-- **The rational Bruhat decomposition** (Borel–Tits 5.15, Milne 25.27): the exact published
statement `RationalBruhatStatement`, at an arbitrary universe. -/
theorem rationalBruhat : RationalBruhatStatement.{u} := by
  intro k _ G hG T i hi ν hν
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have hZ := genericCentralizer k G hG T i hi ν hν
  exact hasRationalBruhatDecomposition_of_parabolicCovering i ν hZ
    (exists_bruhat_factorization hG hi ν hZ)

/-- **Source comparison** (Borel–Tits 5.15, Milne 25.27 with the errata). For generic `ν`, the
canonical closed representative of the parabolic `P = P_G(ν ≫ i)` of `RationalBruhatStatement`
is a minimal rational parabolic subgroup, and the maximal split torus `i` lifts to a maximal
split torus of `P`. -/
theorem rationalBruhat_parabolic_isMinimal
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsMinimalParabolicSubgroup (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)) ∧
      ∃ iP : T.toGrp ⟶ Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i),
        IsMaximalSplitTorus iP ∧
          iP ≫ Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i) = i := by
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hmin := genericMinimalParabolic k G hG T i hi ν hν
  have hj := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν ≫ i)
  refine ⟨⟨Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic
      parabolicDynamic hG _, fun Q j' hj' hle => ?_⟩,
    hi.exists_lift_of_parabolic_le ν _ le_rfl hj
      (Dynamic.Affine.isClosedSubgroup_parabolicHom _)⟩
  rw [hj.2] at hle ⊢
  exact hmin.2 _ ⟨Q, j', hj', rfl⟩ hle

end Langlands.GroupScheme
