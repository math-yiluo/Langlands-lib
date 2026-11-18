import Langlands.GroupScheme.Reductive.RankOneFlagSetup
import Langlands.GroupScheme.Dynamic.SplitTorusLimitInduction
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.GmOrbitInversion
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.AlgebraicGeometry.ClosedRationalPoints
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.SchemeActionTranslation
import Langlands.AlgebraicGeometry.HartogsAffineConstancy
import Langlands.AlgebraicGeometry.KrullDimensionChain
import Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalksProof
import Langlands.GroupScheme.HomogeneousQuotientCurveOrbit

/-! # The rank-one flag variety is a curve

Open cells through the two torus-fixed points of `G/B`, and the dimension bound.
See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneFlag

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

namespace FlagData

variable (F : FlagData i) [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- **The open cell through a translate.** For a cocharacter `χ` of `T` whose centralizer is
the torus, and a translate `g · x₀` fixed by the torus and by `U(χ)`, the open cell
`U(-χ) · g · x₀`. -/
abbrev mkCell (ν : cocharacterLattice T)
    (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i)
    (g : pt k ⟶ G.X) (hT : (F.act.restrict i).IsFixed (g ≫ F.q))
    (hU : ∀ (W : Over (Spec (CommRingCat.of k))) (u : W ⟶ G.X),
      u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier W →
        (toUnit W ≫ g)⁻¹ * (u * (toUnit W ≫ g)) ∈ (SubgroupFunctor.range F.b).carrier W) :
    RankOneFlagCell.Cell F.act (g ≫ F.q) :=
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  { χ := CommGroupScheme.groupHom ν ≫ i
    M := Dynamic.Affine.unipotentScheme
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))
    Z := T.toGrp
    U := Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ν ≫ i)
    iM := Dynamic.Affine.unipotentHom _
    iZ := i
    iU := Dynamic.Affine.unipotentHom _
    hM := Dynamic.Affine.isRepresentedBy_unipotentHom _
    hZ := hZ
    hU := Dynamic.Affine.isRepresentedBy_unipotentHom _
    fixZ := hT
    fixU := by
      rw [F.isFixed_iff]
      intro W s
      apply hU
      rw [← (Dynamic.Affine.isRepresentedBy_unipotentHom
        (CommGroupScheme.groupHom ν ≫ i)).2]
      exact SubgroupFunctor.mem_range.mpr ⟨s, rfl⟩
    isOpenImmersion := Dynamic.isOpenImmersion_tripleCellMultiplication _
      (Dynamic.Affine.isRepresentedBy_unipotentHom _) hZ
      (Dynamic.Affine.isRepresentedBy_unipotentHom _) }

section CellFacts

variable {ν : cocharacterLattice T}
  {hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i}
  {g : pt k ⟶ G.X} {hT : (F.act.restrict i).IsFixed (g ≫ F.q)}
  {hU : ∀ (W : Over (Spec (CommRingCat.of k))) (u : W ⟶ G.X),
      u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier W →
        (toUnit W ≫ g)⁻¹ * (u * (toUnit W ≫ g)) ∈ (SubgroupFunctor.range F.b).carrier W}

instance mkCell_isAffineHom : IsAffineHom (F.mkCell ν hZ g hT hU).M.X.hom := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (Dynamic.Affine.isClosedSubgroup_unipotentHom _).isAffineHom

instance mkCell_locallyOfFiniteType : LocallyOfFiniteType (F.mkCell ν hZ g hT hU).M.X.hom := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (Dynamic.Affine.isClosedSubgroup_unipotentHom _).locallyOfFiniteType

instance mkCell_quasiCompact [IsAffineHom T.toGrp.X.hom] :
    QuasiCompact (Dynamic.tripleCellMultiplication (F.mkCell ν hZ g hT hU).iM
      (F.mkCell ν hZ g hT hU).iZ (F.mkCell ν hZ g hT hU).iU).left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom (F.mkCell ν hZ g hT hU).U.X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _).isAffineHom
  have : IsAffineHom (F.mkCell ν hZ g hT hU).Z.X.hom :=
    inferInstanceAs (IsAffineHom T.toGrp.X.hom)
  have : IsAffine (F.mkCell ν hZ g hT hU).Ω.left :=
    isAffine_of_isAffineHom (F.mkCell ν hZ g hT hU).Ω.hom
  infer_instance

theorem mkCell_isUnipotent : IsUnipotent (F.mkCell ν hZ g hT hU).M := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact dynamicUnipotentUnipotence k G _ _ _ (Dynamic.Affine.isRepresentedBy_unipotentHom _)

end CellFacts

end FlagData

/-- The opposite of `-ν` is `ν`. -/
theorem oppositeCocharacter_neg (ν : cocharacterLattice T) :
    Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-ν) ≫ i) =
      CommGroupScheme.groupHom ν ≫ i := by
  have hν : Gm.powerHom _ (-1) ≫ (-ν) = ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp, neg_neg]
  rw [Dynamic.oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ (-ν)) ≫ i = _
  rw [hν]

/-- The opposite of `ν` is `-ν`. -/
theorem oppositeCocharacter_pos (ν : cocharacterLattice T) :
    Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i) =
      CommGroupScheme.groupHom (-ν) ≫ i := by
  have hν : Gm.powerHom _ (-1) ≫ ν = -ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [Dynamic.oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i = _
  rw [hν]

/-- **Core data.** Flag data with a cocharacter `ν` whose centralizer and that of `-ν` are the
torus, such that conjugation by the Weyl point carries `U(ν)` into `U(-ν)`, and `U(-ν) ⊆ B`. -/
structure CoreData (i : T.toGrp ⟶ G) extends FlagData i where
  ν : cocharacterLattice T
  hZp : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i
  hZn : (Dynamic.centralizer (CommGroupScheme.groupHom (-ν) ≫ i)).IsRepresentedBy i
  hconj : ∀ (W : Over (Spec (CommRingCat.of k))) (u : W ⟶ G.X),
    u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier W →
      (toUnit W ≫ (n : pt k ⟶ G.X))⁻¹ * (u * (toUnit W ≫ (n : pt k ⟶ G.X))) ∈
        (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier W
  hB : Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i) ≤ SubgroupFunctor.range b

namespace CoreData

variable (D : CoreData i) [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The open cell `U(ν) · x₀`. -/
abbrev cell₀ : RankOneFlagCell.Cell D.act ((1 : pt k ⟶ G.X) ≫ D.q) :=
  D.mkCell (-D.ν) D.hZn 1 D.isFixed_x₀ (by
    intro W u hu
    rw [MonObj.comp_one, inv_one, one_mul, mul_one]
    exact D.hB W hu)

/-- The open cell `U(-ν) · x₁`. -/
abbrev cell₁ : RankOneFlagCell.Cell D.act ((D.n : pt k ⟶ G.X) ≫ D.q) :=
  D.mkCell D.ν D.hZp D.n D.isFixed_x₁ (fun W u hu => D.hB W (D.hconj W u hu))

instance cell₀_isAffineHom : IsAffineHom D.cell₀.M.X.hom :=
  FlagData.mkCell_isAffineHom D.toFlagData
instance cell₁_isAffineHom : IsAffineHom D.cell₁.M.X.hom :=
  FlagData.mkCell_isAffineHom D.toFlagData
instance cell₀_lft : LocallyOfFiniteType D.cell₀.M.X.hom :=
  FlagData.mkCell_locallyOfFiniteType D.toFlagData
instance cell₁_lft : LocallyOfFiniteType D.cell₁.M.X.hom :=
  FlagData.mkCell_locallyOfFiniteType D.toFlagData
instance cell₀_qc [IsAffineHom T.toGrp.X.hom] :
    QuasiCompact (Dynamic.tripleCellMultiplication D.cell₀.iM D.cell₀.iZ D.cell₀.iU).left :=
  FlagData.mkCell_quasiCompact D.toFlagData
instance cell₁_qc [IsAffineHom T.toGrp.X.hom] :
    QuasiCompact (Dynamic.tripleCellMultiplication D.cell₁.iM D.cell₁.iZ D.cell₁.iU).left :=
  FlagData.mkCell_quasiCompact D.toFlagData
theorem cell₀_isUnipotent : IsUnipotent D.cell₀.M := FlagData.mkCell_isUnipotent D.toFlagData
theorem cell₁_isUnipotent : IsUnipotent D.cell₁.M := FlagData.mkCell_isUnipotent D.toFlagData

theorem cell₀_χ : D.cell₀.χ = CommGroupScheme.groupHom (-D.ν) ≫ i := rfl

theorem cell₁_χ : D.cell₁.χ = CommGroupScheme.groupHom D.ν ≫ i := rfl

/-- Cocharacters of the torus centralize `±ν`. -/
theorem range_le_centralizer (c : cocharacterLattice T) (ν' : cocharacterLattice T)
    (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ν' ≫ i)).IsRepresentedBy i) :
    SubgroupFunctor.range (CommGroupScheme.groupHom c ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom ν' ≫ i) := by
  rw [← hZ.2]
  intro W g hg
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact SubgroupFunctor.mem_range.mpr ⟨s ≫ (CommGroupScheme.groupHom c).hom.hom, by
    rw [Category.assoc, ← Grp.comp_hom_hom]⟩

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- Fixedness under `ν` gives fixedness under `-ν`. -/
theorem isFixed_neg {Y : Over (Spec (CommRingCat.of k))} (b : SchemeAction G Y)
    (ν' : cocharacterLattice T) {w : pt k ⟶ Y}
    (hw : (b.restrict (CommGroupScheme.groupHom ν' ≫ i)).IsFixed w) :
    (b.restrict (CommGroupScheme.groupHom (-ν') ≫ i)).IsFixed w := by
  intro W c h
  have := hw W c (h ≫ ι[(Gm (Spec (CommRingCat.of k))).X])
  rw [SchemeAction.restrict_act] at this ⊢
  rw [Grp.comp_hom_hom, ← Category.assoc, GmOrbitInversion.comp_groupHom_neg, Category.assoc,
    ← Grp.comp_hom_hom, GmOrbitInversion.groupHom_powerHom_neg_one]
  exact this

variable [IsAlgClosed k]

/-- **Fixed points of `ν`.** Every rational point of `G/B` fixed by `ν` is `x₀` or `x₁`. -/
theorem eq_or_eq_of_isFixed_ν (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (w : pt k ⟶ D.X) (hw : (D.act.restrict (CommGroupScheme.groupHom D.ν ≫ i)).IsFixed w) :
    w = D.x₀ ∨ w = D.x₁ := by
  have hT' : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  refine SplitTorusLimitInduction.limit_induction (D.act.restrict i) hT
    (fun w => ((D.act.restrict i).restrict (CommGroupScheme.groupHom D.ν)).IsFixed w)
    (fun w => w = D.x₀ ∨ w = D.x₁) ?_ ?_ ?_ w
    ((RankOneFlagCell.isFixed_restrict_restrict_iff _ _ _ _).mpr hw)
  · intro c w e he hw
    exact SplitTorusLimitInduction.isFixed_evalZero_of_isFixed (D.act.restrict i) he hw
  · intro c w e he hw hR
    have he' := (RankOneFlagCell.isGmOrbitExtension_restrict_restrict_iff _ _ _ _ _).mp he
    have hw' := (RankOneFlagCell.isFixed_restrict_restrict_iff _ _ _ _).mp hw
    rcases hR with h | h
    · left
      have hmem := D.cell₀.mem_opens_of_limit (CommGroupScheme.groupHom c ≫ i)
        (range_le_centralizer c (-D.ν) D.hZn) w he' (by rw [h]; exact D.cell₀.mem_opens_x)
      apply D.cell₀.eq_of_isFixed w hmem
      rw [cell₀_χ, oppositeCocharacter_neg]
      exact hw'
    · right
      have hmem := D.cell₁.mem_opens_of_limit (CommGroupScheme.groupHom c ≫ i)
        (range_le_centralizer c D.ν D.hZp) w he' (by rw [h]; exact D.cell₁.mem_opens_x)
      apply D.cell₁.eq_of_isFixed w hmem
      rw [cell₁_χ, oppositeCocharacter_pos]
      exact isFixed_neg D.act D.ν hw'
  · intro w hfixT _
    exact D.eq_or_eq_of_isFixed hG hT hi hdep hfixT

theorem x₁_isFixed_ν : (D.act.restrict (CommGroupScheme.groupHom D.ν ≫ i)).IsFixed D.x₁ :=
  (RankOneFlagCell.isFixed_restrict_restrict_iff _ _ _ _).mp (D.isFixed_x₁.restrict _ (CommGroupScheme.groupHom D.ν))

theorem x₀_isFixed_neg : (D.act.restrict (CommGroupScheme.groupHom (-D.ν) ≫ i)).IsFixed D.x₀ :=
  (RankOneFlagCell.isFixed_restrict_restrict_iff _ _ _ _).mp (D.isFixed_x₀.restrict _ (CommGroupScheme.groupHom (-D.ν)))

/-- **The Weyl translate is outside the open cell through `x₀`.** -/
theorem x₁_not_mem (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i) :
    D.x₁.left (IsLocalRing.closedPoint k) ∉ D.cell₀.opens := by
  have hT' : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  intro h
  apply D.x₀_ne_x₁ hi
  refine (D.cell₀.eq_of_isFixed D.x₁ h ?_).symm
  rw [cell₀_χ, oppositeCocharacter_neg]
  exact D.x₁_isFixed_ν

/-- **Bruhat decomposition of the rational points.** A rational point outside the open cell
through `x₀` is `x₁`. -/
theorem eq_x₁_of_not_mem (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (x : pt k ⟶ D.X) (hx : x.left (IsLocalRing.closedPoint k) ∉ D.cell₀.opens) : x = D.x₁ := by
  have hT' : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  obtain ⟨e, he⟩ := SplitTorusLimitInduction.exists_isGmOrbitExtension (D.act.restrict i) D.ν x
  have hfix := he.isFixed_evalZero
  have he' := (RankOneFlagCell.isGmOrbitExtension_restrict_restrict_iff _ _ _ _ _).mp he
  rcases D.eq_or_eq_of_isFixed_ν hG hT hi hdep (Dynamic.evalZero e)
    ((RankOneFlagCell.isFixed_restrict_restrict_iff _ _ _ _).mp hfix) with h | h
  · exact absurd (D.cell₀.mem_opens_of_limit (CommGroupScheme.groupHom D.ν ≫ i)
      (range_le_centralizer D.ν (-D.ν) D.hZn) x he' (by rw [h]; exact D.cell₀.mem_opens_x)) hx
  · have hmem := D.cell₁.mem_opens_of_limit (CommGroupScheme.groupHom D.ν ≫ i)
      (range_le_centralizer D.ν D.ν D.hZp) x he' (by rw [h]; exact D.cell₁.mem_opens_x)
    exact D.cell₁.eq_of_limit D.cell₁_isUnipotent x hmem he' h

theorem bot_eq_closedPoint : (⊥ : PrimeSpectrum k) = IsLocalRing.closedPoint k :=
  Subsingleton.elim _ _

/-- **The complement of the open cell.** As a set, the complement of the open cell through
`x₀` is the single point `x₁`. -/
theorem not_mem_iff (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (y : D.X.left) :
    y ∉ D.cell₀.opens ↔ y = D.x₁.left (IsLocalRing.closedPoint k) := by
  constructor
  · intro hy
    have hsub := Langlands.AlgebraicGeometry.ClosedRationalPoints.subset_singleton_of_rationalPoints
      (Z := (D.cell₀.opens : Set D.X.left)ᶜ) D.cell₀.opens.isOpen.isClosed_compl.isLocallyClosed
      D.x₁ (fun x hx => D.eq_x₁_of_not_mem hG hT hi hdep x hx)
    exact hsub hy
  · rintro rfl
    exact D.x₁_not_mem hT hi

/-- **Noncontainment.** `U(ν)` is not contained in `B`. -/
theorem not_unipotent_le (hT : IsSplitTorus T.toGrp) (hi : IsMaximalTorus i)
    [ConnectedSpace G.X.left] :
    ¬ Dynamic.unipotent (CommGroupScheme.groupHom D.ν ≫ i) ≤ SubgroupFunctor.range D.b := by
  have hT' : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  intro hle
  have hrat : ∀ x : pt k ⟶ D.X, x.left (IsLocalRing.closedPoint k) ∈ D.cell₀.opens →
      x = D.x₀ := by
    intro x hx
    obtain ⟨x', rfl⟩ := D.cell₀.exists_lift_of_mem x hx
    obtain ⟨m, rfl⟩ := D.cell₀.exists_orbitLift_eq x'
    have hm : m ≫ D.cell₀.iM.hom.hom ∈ (SubgroupFunctor.range D.b).carrier (pt k) := by
      apply hle
      rw [← oppositeCocharacter_neg, ← cell₀_χ, ← D.cell₀.hM.2]
      exact SubgroupFunctor.mem_range.mpr ⟨m, rfl⟩
    rw [Category.assoc, RankOneFlagCell.Cell.orbitLift_incl, RankOneFlagCell.cellOrbit,
      ← Category.assoc, SchemeAction.comp_orbitMap, show toUnit (pt k) = 𝟙 (pt k) from
        toUnit_unique _ _, Category.id_comp, FlagData.x₀, D.act_lift, mul_one]
    apply (D.fibers _ _).mpr
    rw [mul_one]
    exact inv_mem hm
  have hsub := Langlands.AlgebraicGeometry.ClosedRationalPoints.subset_singleton_of_rationalPoints
    (Z := (D.cell₀.opens : Set D.X.left)) D.cell₀.opens.isOpen.isLocallyClosed D.x₀ hrat
  have : IrreducibleSpace G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  have : IrreducibleSpace D.X.left :=
    Function.Surjective.irreducibleSpace D.q.left.continuous D.q.left.surjective
  obtain ⟨y, hy₀, hy₁⟩ := nonempty_preirreducible_inter D.cell₀.opens.isOpen
    D.cell₁.opens.isOpen ⟨_, D.cell₀.mem_opens_x⟩ ⟨_, D.cell₁.mem_opens_x⟩
  have hy : y = D.x₀.left (IsLocalRing.closedPoint k) := hsub hy₀
  rw [hy] at hy₁
  apply D.x₀_ne_x₁ hi
  apply D.cell₁.eq_of_isFixed D.x₀ hy₁
  rw [cell₁_χ, oppositeCocharacter_pos]
  exact D.x₀_isFixed_neg

omit [IsAlgClosed k] in
theorem exists_lift [IsAlgClosed k] (x : pt k ⟶ D.X) : ∃ g : pt k ⟶ G.X, g ≫ D.q = x := by
  have : LocallyOfFiniteType (D.q.left ≫ D.X.hom) := by
    rw [Over.w D.q]
    infer_instance
  have : LocallyOfFiniteType D.q.left := locallyOfFiniteType_of_comp D.q.left D.X.hom
  obtain ⟨g, hg⟩ := exists_rationalPoint_lift_of_mem_range D.q.left x.left
    (D.q.left.surjective (x.left (IsLocalRing.closedPoint k)))
  have hgS : g ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w D.q, ← Category.assoc, hg]
    exact Over.w x
  exact ⟨Over.homMk g hgS, Over.OverMorphism.ext hg⟩

/-- **The flag variety is a curve.** -/
theorem topologicalKrullDim_le_one (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) :
    topologicalKrullDim D.X.left ≤ 1 := by
  have hT' : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  by_contra hdim
  have : CompactSpace D.X.left := QuasiCompact.compactSpace_of_compactSpace D.X.hom
  obtain ⟨y₀, y₁, c, h₀₁, h₁c, hne₀₁, hne₁c, hc⟩ :=
    Langlands.AlgebraicGeometry.KrullDimensionChain.exists_chain_of_not_le_one hdim
  obtain ⟨xc, hxc⟩ :=
    Langlands.AlgebraicGeometry.ClosedRationalPoints.exists_rationalPoint_of_isClosed c hc
  obtain ⟨g, hg⟩ := D.exists_lift xc
  let h : pt k ⟶ G.X := (D.n : pt k ⟶ G.X) * g⁻¹
  let τ := SchemeActionTranslation.translate D.act h
  have hτ : xc ≫ τ = D.x₁ := by
    rw [SchemeActionTranslation.comp_translate, show toUnit (pt k) = 𝟙 (pt k) from
      toUnit_unique _ _, Category.id_comp, ← hg, D.act_lift, mul_assoc, inv_mul_cancel, mul_one]
    rfl
  have hτc : τ.left c = D.x₁.left (IsLocalRing.closedPoint k) := by
    rw [← hxc, ← hτ]
    rfl
  obtain ⟨h₀₁', h₁c', hne₀₁', hne₁c'⟩ :=
    SchemeActionTranslation.chain_translate D.act h h₀₁ h₁c hne₀₁ hne₁c
  rw [hτc] at h₁c' hne₁c'
  -- the geometry of `X`
  obtain ⟨hsm, hred, hirr⟩ := HomogeneousQuotient.smooth_reduced_irreducible_quotient (G := G) D.q
  have : IsIntegral D.X.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : UniqueFactorizationMonoid
      (D.X.left.presheaf.stalk (D.x₁.left (IsLocalRing.closedPoint k))) :=
    Langlands.AlgebraicGeometry.smoothAlgClosedFactorialStalks k D.X.left D.X.hom hsm _
  obtain ⟨V, hV, ρ, hρ⟩ := D.cell₀.exists_chevalleyMap_injective D.cell₀_isUnipotent
  obtain ⟨c', hc'⟩ := Langlands.AlgebraicGeometry.HartogsAffineConstancy.exists_eq_const D.X.hom
    (W := D.cell₀.opens) (fun y => D.not_mem_iff hG hT hi hdep y) h₀₁' h₁c' hne₀₁' hne₁c'
    (Y := V.left) ρ.left
  -- `ρ` is constant, so the cell has a single rational point
  have hc'' : ρ.left = D.cell₀.scheme.hom ≫ c' := by
    rw [hc', ← Category.assoc]
    rfl
  have hval : ∀ z : pt k ⟶ D.cell₀.scheme, (z ≫ ρ).left = c' := by
    intro z
    rw [Over.comp_left, hc'', ← Category.assoc, Over.w z]
    exact Category.id_comp _
  have hconst : ∀ y y' : pt k ⟶ D.cell₀.scheme, y = y' := by
    intro y y'
    apply hρ
    apply Over.OverMorphism.ext
    rw [hval, hval]
  have hrat : ∀ x : pt k ⟶ D.X, x.left (IsLocalRing.closedPoint k) ∈ D.cell₀.opens →
      x = D.x₀ := by
    intro x hx
    obtain ⟨y, rfl⟩ := D.cell₀.exists_lift_of_mem x hx
    have hx₀ : D.x₀.left (IsLocalRing.closedPoint k) ∈ D.cell₀.opens := by
      rw [← bot_eq_closedPoint]
      exact D.cell₀.mem_opens_x
    obtain ⟨y₀', hy₀'⟩ := D.cell₀.exists_lift_of_mem D.x₀ hx₀
    rw [hconst y y₀', hy₀']
  have hsub := Langlands.AlgebraicGeometry.ClosedRationalPoints.subset_singleton_of_rationalPoints
    (Z := (D.cell₀.opens : Set D.X.left)) D.cell₀.opens.isOpen.isLocallyClosed D.x₀ hrat
  have hy₁ : τ.left y₁ ∈ D.cell₀.opens := by
    by_contra hy
    exact hne₁c' ((D.not_mem_iff hG hT hi hdep _).mp hy)
  have hy₀ : τ.left y₀ ∈ D.cell₀.opens := by
    by_contra hy
    have h0 := (D.not_mem_iff hG hT hi hdep _).mp hy
    rw [h0] at h₀₁'
    exact hne₁c' (h₁c'.antisymm h₀₁').eq
  exact hne₀₁' ((hsub hy₀).trans (hsub hy₁).symm)

end CoreData

end RankOneFlag

end Langlands.GroupScheme
