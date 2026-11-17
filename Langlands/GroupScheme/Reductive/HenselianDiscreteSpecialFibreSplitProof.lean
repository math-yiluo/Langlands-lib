import Langlands.GroupScheme.Reductive.HenselianDiscreteSpecialFibreSplitStatement
import Langlands.GroupScheme.Torus.HenselianSplitSubgroupLifting
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.RelativeLevi.DynamicProof
import Langlands.GroupScheme.RelativeLevi.BorelLocusProof
import Langlands.GroupScheme.RelativeLevi.BorelRangeTransport
import Langlands.GroupScheme.RelativeLevi.HenselianBorelReduction

/-! # Splitting and quasi-splitting from the special fibre over a henselian DVR -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- Over a henselian local ring, if the special fibre of a reductive group has a split
maximal torus, then so does its fibre at every field point. The split maximal torus of
the special fibre lifts to a closed split torus over the ring, which is maximal on the
closed fibre and therefore on every field-valued fibre. -/
theorem IsReductive.exists_split_maximalTorus_fieldPoint_of_specialFibre
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    (h : ∃ (T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
      (i : T.toGrp ⟶
        (GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj G),
        IsSplitTorus T.toGrp ∧ IsMaximalTorus i)
    {K : Type u} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of K)))
      (i : T.toGrp ⟶ (GroupScheme.baseChange b).obj G),
      IsSplitTorus T.toGrp ∧ IsMaximalTorus i := by
  obtain ⟨T, i, ⟨I, hI, ⟨e⟩⟩, hmax⟩ := h
  have := hI
  let := hG.smooth
  let := hG.isAffineHom
  let κ := IsLocalRing.ResidueField R
  let c := Spec.algebraMap R κ
  let H := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I
  let e₀ : ((CommGroupScheme.baseChange c).obj H).toGrp ≅ T.toGrp :=
    splitTorus.baseChangeIso c I ≪≫ e.symm
  let i₀ : (GroupScheme.baseChange c).obj H.toGrp ⟶ (GroupScheme.baseChange c).obj G :=
    e₀.hom ≫ i
  have hi₀ : IsClosedSubgroup i₀ := IsClosedSubgroup.iso_comp e₀ hmax.2.1
  obtain ⟨j, hj, hjc⟩ := exists_closed_splitHom_lift (k := κ)
    IsLocalRing.residue_surjective H.toGrp G (isSplitTorus_splitTorus I) i₀ hi₀
  have hmaxc : IsMaximalTorus (T := (CommGroupScheme.baseChange c).obj H)
      ((GroupScheme.baseChange c).map j) := by
    rw [hjc]
    exact IsMaximalTorus.iso_comp e₀ hmax
  have hres := isMaximalTorus_residueFibre_of_fieldPoint hj c hmaxc
  have hpt : c (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [hpt] at hres
  exact ⟨(CommGroupScheme.baseChange b).obj H, (GroupScheme.baseChange b).map j,
    (isSplitTorus_splitTorus I).baseChange b,
    hG.isMaximalTorus_fieldPoint_of_closedFibre (isSplitTorus_splitTorus I) j hj hres b⟩

/-- A geometric Borel on the fibre at a field point is a geometric Borel on the
residue fibre at the image of that point, provided the inclusion is closed. -/
theorem isGeometricBorelSubgroup_residueFibre_of_fieldPoint
    {S : Scheme.{u}} {B G : GroupScheme S} [IsAffineHom G.X.hom] {i : B ⟶ G}
    (hi : IsClosedSubgroup i) {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (h : IsGeometricBorelSubgroup ((GroupScheme.baseChange b).map i)) :
    IsGeometricBorelSubgroup
      (RelativeLevi.residueFiberHom i (b (IsLocalRing.closedPoint k))) := by
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  let c := Spec.map (fieldPointResidueMap b)
  let : Algebra (S.residueField s : Type u) k := (fieldPointResidueMap b).hom.toAlgebra
  let : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom a)
    infer_instance
  apply IsGeometricBorelSubgroup.of_baseChange (k := (S.residueField s : Type u)) (K := k)
    (hclosed := hi.baseChange a)
  change IsGeometricBorelSubgroup
    ((GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i))
  apply isGeometricBorelSubgroup_baseChange_comp a c i
  rw [show c ≫ a = b from fieldPointResidueMap_factorization b]
  exact h

/-- Over a henselian local ring, if the special fibre of a reductive group is
quasi-split, then so is its fibre at every field point. The geometric Borel of the
special fibre is a dynamic parabolic `P(χ₀)`; `χ₀` lifts to a cocharacter `χ` over the
ring, `P(χ)` is a relative parabolic which is a Borel on the closed fibre, hence on every
fibre because the Borel locus is open and every point specializes to the closed point. -/
theorem IsReductive.isQuasiSplit_fieldPoint_of_specialFibre
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))} (hG : IsReductive G)
    (hq : IsQuasiSplit
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj G))
    {K : Type u} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    IsQuasiSplit ((GroupScheme.baseChange b).obj G) := by
  let := hG.smooth
  let := hG.isAffineHom
  let κ := IsLocalRing.ResidueField R
  let c := Spec.algebraMap R κ
  obtain ⟨B₀, i₀, hi₀⟩ := hq.exists_isGeometricBorelSubgroup
  obtain ⟨χ₀, hχ₀⟩ := (parabolicDynamic κ _ hq.isConnectedReductive B₀ i₀
    hi₀.1.isClosedSubgroup).mp hi₀.isParabolicSubgroup
  obtain ⟨χ, hχ⟩ := HomScheme.exists_cocharacter_baseChange_eq (k := κ)
    IsLocalRing.residue_surjective G χ₀
  obtain ⟨⟨P, p, hp, -, hPrep⟩, ⟨U, u, -, -, hUrep⟩, ⟨Z, z, -, -, hZrep⟩⟩ :=
    dynamicBaseRepresentability (Spec (CommRingCat.of R)) G χ
  have hpar : IsRelativeParabolicSubgroup p :=
    (dynamicRelativeLevi _ G P U Z χ p u z hG hPrep hUrep hZrep).1
  have hpc : IsClosedSubgroup p := hp
  have hPc := hPrep.baseChange c
  rw [← Dynamic.parabolic_baseChange, hχ] at hPc
  have hrel₀ : IsRelativeBorelSubgroup ((GroupScheme.baseChange c).map p) :=
    (hi₀.isRelativeBorelSubgroup hq.isConnectedReductive).of_range_eq hPc.1
      (hχ₀.trans hPc.2.symm)
  have hgeo₀ := isGeometricBorelSubgroup_of_baseChange_comp c (𝟙 _) p
    (hrel₀.fieldPoint (hG.baseChange c) (𝟙 _))
  rw [Category.id_comp] at hgeo₀
  have hclosed := isGeometricBorelSubgroup_residueFibre_of_fieldPoint hpc c hgeo₀
  have hpt : c (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [hpt] at hclosed
  have hrel : IsRelativeBorelSubgroup p := by
    refine ⟨hpar, fun s => ?_⟩
    exact (IsLocalRing.specializes_closedPoint (R := R) s).mem_open
      (relativeBorelLocusClopen _ G P p hG hpar).isOpen hclosed
  exact ⟨hG.isConnectedReductive_baseChange b, _, _, hrel.fieldPoint hG b⟩

/-- Conrad, Exercise 5.5.3(ii): over a henselian discrete valuation ring, a
quasi-split (resp. split) special fibre of a reductive group scheme gives a
quasi-split (resp. split) generic fibre. -/
theorem henselianDiscreteSpecialFibreSplit :
    HenselianDiscreteSpecialFibreSplitStatement.{u} := by
  intro R _ _ _ _ K _ _ _ G hG G₀ G_K
  exact ⟨fun hq => hG.isQuasiSplit_fieldPoint_of_specialFibre hq _,
    fun h => hG.exists_split_maximalTorus_fieldPoint_of_specialFibre h _⟩

end Langlands.GroupScheme
