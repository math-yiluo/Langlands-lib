import Langlands.GroupScheme.Rational.UnipotentQuotientSplitTorusPreimageProof
import Langlands.GroupScheme.Rational.SolvableMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction
import Langlands.GroupScheme.Dynamic.SchemeCoordinates
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Cocharacters of a dynamic parabolic conjugated into a torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

section LimitQuotient

variable {S : Scheme.{u}} {G : GroupScheme S} {χ : (Gm S).toGrp ⟶ G} [IsSeparated G.X.hom]
  {P Z U : GroupScheme S} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)

include hU in
/-- The limit homomorphism of a smooth contracting subgroup is smooth: it is the second
projection of `U_G(χ) × Z_G(χ)` through the multiplication isomorphism. -/
theorem smooth_limitGroupHom [Smooth U.X.hom] :
    Smooth (limitGroupHom hP hZ).hom.hom.left := by
  rw [← multiplicationIso_inv_snd hP hZ hU, Over.comp_left]
  have : IsIso (multiplicationIso hP hZ hU).inv.left :=
    (Over.forget S).map_isIso (multiplicationIso hP hZ hU).inv
  have : Smooth (snd U.X Z.X).left := inferInstanceAs (Smooth (pullback.snd U.X.hom Z.X.hom))
  infer_instance

/-- The limit homomorphism is surjective: the centralizer inclusion is a section. -/
theorem surjective_limitGroupHom : Surjective (limitGroupHom hP hZ).hom.hom.left := by
  have h' : (centralizerToParabolic hP hZ).hom.hom.left ≫ (limitGroupHom hP hZ).hom.hom.left =
      𝟙 Z.X.left := by
    rw [← Over.comp_left, ← grp_comp_hom_hom, centralizerToParabolic_comp_limitGroupHom]
    rfl
  exact ⟨DynamicConnected.surjective_of_section _ _ h'⟩

include hU in
/-- The limit homomorphism is an fppf quotient by its kernel when the contracting subgroup is
smooth. -/
theorem isFppfQuotient_limitGroupHom [Smooth U.X.hom] :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι (limitGroupHom hP hZ)))
      (limitGroupHom hP hZ) := by
  have := smooth_limitGroupHom hP hZ hU
  exact ⟨inferInstance, surjective_limitGroupHom hP hZ, inferInstance, rfl⟩

end LimitQuotient

end Dynamic

variable {k : Type u} [Field k]

section Represented

variable {G : GroupScheme (Spec (CommRingCat.of k))} [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
  {P Z U : GroupScheme (Spec (CommRingCat.of k))} {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
  (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)

include hU in
/-- For a smooth connected representative of `P_G(χ)` and a split subtorus `z` of a
representative of `Z_G(χ)`, the inverse image of `z` under the limit homomorphism is a smooth
connected affine solvable closed subgroup scheme of the parabolic representative. -/
theorem exists_solvable_limitGroupHom_preimage [IsAffineHom Z.X.hom]
    [Smooth P.X.hom] [ConnectedSpace P.X.left] [IsAffineHom P.X.hom] [Smooth U.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (z : T.toGrp ⟶ Z) (hz : IsSplitSubtorus z) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ P),
      IsClosedSubgroup j ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧ IsAffineHom H.X.hom ∧
      IsSolvableGroupScheme H ∧
      ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (a : K ⟶ P) (g : K ⟶ T.toGrp),
        g ≫ z = a ≫ Dynamic.limitGroupHom hP hZ → ∃ f : K ⟶ H, f ≫ j = a := by
  have hKrep : (Dynamic.unipotent χ).IsRepresentedBy
      (kernelι (Dynamic.limitGroupHom hP hZ) ≫ iP) :=
    Dynamic.isRepresentedBy_kernel_limitGroupHom hP hZ
  have hr : IsClosedSubgroup (kernelι (Dynamic.limitGroupHom hP hZ)) :=
    inferInstanceAs (IsClosedImmersion (kernelι (Dynamic.limitGroupHom hP hZ)).hom.hom.left)
  have hKs := (dynamicSmooth k G χ _ _).2.2 hKrep
  have hKc := (dynamicConnected k G χ _ _).1 hKrep
  have hKu := dynamicUnipotentUnipotenceReduction unitriangularUnipotent unipotentClosedSubgroup
    k G χ _ _ hKrep
  exact unipotentQuotientSplitTorusPreimageStatement k P _ _ hr hKs hKc hKu Z _
    (Dynamic.isFppfQuotient_limitGroupHom hP hZ hU) T z hz

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

omit [Smooth G.X.hom] in
/-- The limit of a cocharacter of the parabolic representative factors through a maximal split
torus whose centralizer is the dynamic centralizer. -/
theorem exists_limit_factor_through_torus (hi : IsMaximalSplitTorus i)
    (hZχ : Dynamic.centralizer χ = torusCentralizer i) (z : T.toGrp ⟶ Z) (hz : z ≫ iZ = i)
    (ψP : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ P) :
    ∃ f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp,
      f ≫ z = ψP ≫ Dynamic.limitGroupHom hP hZ := by
  obtain ⟨f, hf⟩ := hi.exists_factor_of_commute isSplitTorus_gm
    (ψP ≫ Dynamic.limitGroupHom hP hZ ≫ iZ) (fun V x y => by
      have hmem : x ≫ (ψP ≫ Dynamic.limitGroupHom hP hZ ≫ iZ).hom.hom ∈
          (torusCentralizer i).carrier V := by
        rw [← hZχ, ← hZ.2]
        exact SubgroupFunctor.mem_range.mpr
          ⟨x ≫ (ψP ≫ Dynamic.limitGroupHom hP hZ).hom.hom, by
            simp only [Grp.comp_hom_hom, Category.assoc]⟩
      simpa only [Category.id_comp] using hmem V (𝟙 V) y)
  exact ⟨f, hZ.hom_ext (by simp only [Category.assoc, hz, hf])⟩

include hP hZ hU in
/-- The parabolic conjugation lemma for arbitrary closed representatives of the dynamic
subgroups. -/
theorem exists_parabolic_conj_into_torus_of_represented [ConnectedSpace G.X.left]
    (hPc : IsClosedSubgroup iP) (hZc : IsClosedSubgroup iZ) [Smooth U.X.hom]
    (hi : IsMaximalSplitTorus i) (hZχ : Dynamic.centralizer χ = torusCentralizer i)
    (hTZ : SubgroupFunctor.range i ≤ Dynamic.centralizer χ)
    (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψ : SubgroupFunctor.range ψ ≤ Dynamic.parabolic χ) :
    ∃ p ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
      ∃ ρ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp,
        ψ ≫ (G.innerIso p).hom = ρ ≫ i := by
  have : Smooth P.X.hom := (dynamicSmooth k G χ P iP).1 hP
  have : ConnectedSpace P.X.left := ((dynamicConnected k G χ P iP).2 inferInstance).1 hP
  have : IsAffineHom P.X.hom := hPc.isAffineHom
  have : IsAffineHom Z.X.hom := hZc.isAffineHom
  -- the torus inside the centralizer representative
  let z : T.toGrp ⟶ Z := hZ.factorHom i hTZ
  have hz : z ≫ iZ = i := hZ.factorHom_comp i hTZ
  have hzs : IsSplitSubtorus z :=
    ⟨hi.1.1, IsClosedSubgroup.of_comp hZc (by rw [hz]; exact hi.1.2)⟩
  -- the cocharacter inside the parabolic representative, and its limit
  let ψP : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ P := hP.factorHom ψ hψ
  have hψP : ψP ≫ iP = ψ := hP.factorHom_comp ψ hψ
  obtain ⟨f, hfz⟩ := exists_limit_factor_through_torus hP hZ hi hZχ z hz ψP
  -- the solvable preimage of the torus
  obtain ⟨H, j, hj, hHs, hHc, hHa, hHsolv, hlift⟩ :=
    exists_solvable_limitGroupHom_preimage hP hZ hU z hzs
  let := hHs
  let := hHc
  let := hHa
  obtain ⟨ψH, hψH⟩ := hlift (Gm (Spec (CommRingCat.of k))).toGrp ψP f hfz
  let fT : T.toGrp ⟶ P := z ≫ Dynamic.centralizerToParabolic hP hZ
  have hfT : fT ≫ iP = i := by
    simp only [fT, Category.assoc, Dynamic.centralizerToParabolic_comp, hz]
  have hfTq : 𝟙 T.toGrp ≫ z = fT ≫ Dynamic.limitGroupHom hP hZ := by
    simp only [fT, Category.id_comp, Category.assoc,
      Dynamic.centralizerToParabolic_comp_limitGroupHom, Category.comp_id]
  obtain ⟨tH, htH⟩ := hlift T.toGrp fT (𝟙 _) hfTq
  have hjP : IsClosedSubgroup (j ≫ iP) := hj.comp hPc
  have htHmax : IsMaximalSplitTorus tH :=
    IsMaximalSplitTorus.of_comp hjP (by rw [← Category.assoc, htH, hfT]; exact hi)
  -- conjugacy of maximal split tori in the solvable preimage
  obtain ⟨S, iS, ζ, hiS, hζ⟩ := cocharacterMaximalSplitTorus k H ψH
  obtain ⟨b, e, he⟩ := solvableMaximalSplitTorusConjugacy k H hHsolv S T iS tH hiS htHmax
  refine ⟨b ≫ (j ≫ iP).hom.hom, ?_, CommGroupScheme.groupHom ζ ≫ e.hom, ?_⟩
  · rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr
      ⟨b ≫ j.hom.hom, by simp only [Grp.comp_hom_hom, Category.assoc]⟩
  · have hψ' : ψ = ψH ≫ j ≫ iP := by rw [← Category.assoc, hψH, hψP]
    calc ψ ≫ (G.innerIso (b ≫ (j ≫ iP).hom.hom)).hom
        = ψH ≫ (j ≫ iP) ≫ (G.innerIso (b ≫ (j ≫ iP).hom.hom)).hom := by
          rw [hψ', Category.assoc]
      _ = ψH ≫ (H.innerIso b).hom ≫ (j ≫ iP) := by rw [innerIso_hom_comp]
      _ = (CommGroupScheme.groupHom ζ ≫ iS ≫ (H.innerIso b).hom) ≫ (j ≫ iP) := by
          rw [← hζ]
          simp only [Category.assoc]
      _ = (CommGroupScheme.groupHom ζ ≫ e.hom ≫ tH) ≫ (j ≫ iP) := by rw [he]
      _ = (CommGroupScheme.groupHom ζ ≫ e.hom) ≫ i := by
          simp only [Category.assoc]
          rw [← Category.assoc tH, htH, hfT]

end Represented

/-- Let `i : T ⟶ G` be a maximal split torus of a connected reductive group and `ν` a
cocharacter of `T` whose dynamic centralizer is the centralizer of the whole torus. Every
cocharacter `ψ` of `G` with range in `P_G(ν ≫ i)` is conjugate, by a rational point of
`P_G(ν ≫ i)`, to a cocharacter of `T`. -/
theorem exists_parabolic_conj_into_torus
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T)
    (hZχ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i)
    (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hψ : SubgroupFunctor.range ψ ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) :
    ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))),
      ∃ ρ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp,
        ψ ≫ (G.innerIso p).hom = ρ ≫ i := by
  let := hG.isAffineHom
  let := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom ν ≫ i)
  have : Smooth (Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ν ≫ i)).X.hom :=
    (dynamicSmooth k G _ _ _).2.2 hU
  exact exists_parabolic_conj_into_torus_of_represented
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (Dynamic.Affine.isRepresentedBy_centralizerHom _) hU
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom _) hi hZχ
    (range_le_centralizer_groupHom_comp i ν) ψ hψ

end Langlands.GroupScheme
