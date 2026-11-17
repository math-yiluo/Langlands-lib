import Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof

/-! # Rank-one cells from pointwise root support and lines

This conditional construction uses the independently supplied local root support and
root-space line data. It does not prove those structural inputs.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalRankOneRootCell

open Langlands.GroupScheme RankOneCellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A single positive adjoint weight and a supplied root line give the dynamic root group. -/
theorem exists_rootGroup_of_positiveSupport
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i)
    (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν)
    (hunique : haveI := hG.isAffineHom
      ∀ β ∈ roots i, 0 < latticePairing T β ν → β = α)
    (hline : haveI := hG.isAffineHom; Nonempty (k ≃ₗ[k] weightSpace i α)) :
    ∃ x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy x ∧
      ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
        (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ x.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction α U t a ≫ x.hom.hom := by
  have := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom T.X.hom := hi.2.1.isAffineHom
  let N := Standard.unipotentScheme i ν ∅
  let incl := Standard.unipotentHom i ν ∅
  have : IsAffine N.X.left := isAffine_of_isAffineHom N.X.hom
  have : Smooth N.X.hom := Standard.smooth_unipotentScheme_empty i ν hT
  let b := Standard.unipotentAction i ν hT
  obtain ⟨d, w, t, ht, htw, hε, hw, hmono⟩ :=
    TorusUnipotence.exists_positiveWeight_coordinates hT b ν
      (fun χ hχ => Standard.pairing_pos_of_mem_support i ν hT hχ)
  obtain ⟨P, hP, hmul⟩ := TorusUnipotence.exists_triangular_mul hT b ν ht htw hε hw hmono
  -- Every weight of the coordinates is `α`.
  have hwα : ∀ j, w j = α := by
    intro j
    have hj : w j ∈ positiveRelativeRoots i ν := by
      refine (Standard.actionWeightSpace_unipotentAction_ne_bot_iff i ν hT (w j)).mp
        fun hbot => ?_
      have h := TorusUnipotence.finrank_actionWeightSpace hT b ht htw hε (w j)
      rw [hbot, finrank_bot] at h
      have : Nonempty {j' // w j' = w j} := ⟨⟨j, rfl⟩⟩
      have : 0 < Nat.card {j' // w j' = w j} := Nat.card_pos
      omega
    exact hunique (w j) hj.1 hj.2
  -- There is exactly one coordinate.
  have hd : d = 1 := by
    have h1 := TorusUnipotence.finrank_actionWeightSpace hT b ht htw hε α
    rw [Standard.finrank_actionWeightSpace_unipotentAction i ν hT ⟨hα, hν⟩] at h1
    obtain ⟨eα⟩ := hline
    rw [← eα.finrank_eq, Module.finrank_self] at h1
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hwα), Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    exact h1.symm
  subst hd
  -- The single coordinate is additive.
  have hP0 : ∀ (B : Type u) [CommRing B] [Algebra k B] (f : Fin 1 ⊕ Fin 1 → B),
      aeval f (P 0) = algebraMap k B (constantCoeff (P 0)) := by
    intro B _ _ f
    apply MvPolynomial.aeval_eq_constantCoeff_of_vars
    intro v hv
    exact absurd (hP 0 v hv) (Fin.not_lt_zero _)
  have h0 : Lie.coordinateOrigin (Standard.unipotentScheme i ν ∅) (t 0) = 0 := hε 0
  have hcc : constantCoeff (P 0) = 0 := by
    have h := hmul k 1 1 0
    rw [mul_one, hP0, Lie.pointCoordinates_one] at h
    simpa [h0] using h.symm
  have hadd : ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints N B),
      Lie.pointCoordinates N (x * y) (t 0) =
        Lie.pointCoordinates N x (t 0) + Lie.pointCoordinates N y (t 0) := by
    intro B _ _ x y
    rw [hmul B x y 0, hP0, hcc, map_zero, add_zero]
  have hc : Function.Bijective
      (aeval (fun _ : Fin 1 => t 0) : MvPolynomial (Fin 1) k →ₐ[k] CharacterUnits.Coord N) := by
    have ht' : t = fun _ => t 0 := funext fun j => by rw [Subsingleton.elim j 0]
    rwa [ht'] at ht
  have hcα : t 0 ∈ CoordinateWeights.weightSpace b α := hwα 0 ▸ htw 0
  -- The vector group.
  let e := lineCoordinates hc hadd
  have he : RelativeRoot.IsNaturalVectorCoordinates e :=
    isNaturalVectorCoordinates_lineCoordinates hc hadd
  let Φ := RelativeRoot.vectorGroupIso e he
  have ehi : Φ.inv.hom.hom ≫ Φ.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) Φ.inv_hom_id
  have ehi' : Φ.hom.hom.hom ≫ Φ.inv.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) Φ.hom_inv_id
  refine ⟨Φ.inv ≫ incl, (Standard.isRepresentedBy_unipotentHom_empty i ν hT).precomp_iso Φ.symm,
    fun U s a => ?_⟩
  let n : U ⟶ N.X := a ≫ Φ.inv.hom.hom
  have hna : n ≫ Φ.hom.hom.hom = a := by
    change (a ≫ Φ.inv.hom.hom) ≫ Φ.hom.hom.hom = a
    rw [Category.assoc, ehi, Category.comp_id]
  have key : b.act s n ≫ Φ.hom.hom.hom = VectorGroup.weightPointAction α U s a := by
    apply VectorGroup.points_ext
    intro j
    rw [RelativeRoot.coordinates_comp_vectorGroupIso_hom,
      VectorGroup.coordinates_weightPointAction, ← hna,
      RelativeRoot.coordinates_comp_vectorGroupIso_hom]
    exact lineValue_act b α hcα s n
  have hact : b.act s n = VectorGroup.weightPointAction α U s a ≫ Φ.inv.hom.hom := by
    rw [← key, Category.assoc, ehi', Category.comp_id]
  have hcomp : ∀ y : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X,
      y ≫ (Φ.inv ≫ incl).hom.hom = (y ≫ Φ.inv.hom.hom) ≫ incl.hom.hom := fun y => by
    rw [Grp.comp_hom_hom, Category.assoc]
  rw [hcomp, hcomp, ← hact]
  exact (Standard.unipotentAction_act_comp i ν hT s n).symm

/-- Local root support and two root lines suffice for the full rank-one cell relation. -/
theorem exists_rootCell_of_support_lines
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (r : J)
    (hsupport : haveI := hG.isAffineHom
      ∀ β ∈ roots i, β = P.root r ∨ β = -P.root r)
    (hline : haveI := hG.isAffineHom
      Nonempty (k ≃ₗ[k] weightSpace i (P.root r)))
    (hnegline : haveI := hG.isAffineHom
      Nonempty (k ≃ₗ[k] weightSpace i (-P.root r))) :
    ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      RootCell.IsRootCell i (P.root r) (P.coroot r) xp xm := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  have hα : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  have pair : latticePairing T (P.root r) (P.coroot r) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two r
  have hν : 0 < latticePairing T (P.root r) (P.coroot r) := by omega
  have hpositive : ∀ β ∈ roots i,
      0 < latticePairing T β (P.coroot r) → β = P.root r := by
    intro β hβ hp
    rcases hsupport β hβ with heq | heq
    · exact heq
    · rw [heq, map_neg, LinearMap.neg_apply, pair] at hp
      omega
  have hnegative : ∀ β ∈ roots i,
      0 < latticePairing T β (-P.coroot r) → β = -P.root r := by
    intro β hβ hp
    rcases hsupport β hβ with heq | heq
    · rw [heq, map_neg, pair] at hp
      omega
    · exact heq
  have hC := rankOne_centralizer_isRepresentedBy dynamicCentralizerReductive
    hG hT i hi hrank (P.root r) hα (P.coroot r) hν.ne'
  obtain ⟨xp, hxp, hxpc⟩ := exists_rootGroup_of_positiveSupport hG hT i hi
    (P.root r) hα (P.coroot r) hν hpositive hline
  have hνneg : 0 < latticePairing T (-P.root r) (-P.coroot r) := by simpa using hν
  obtain ⟨xm, hxm, hxmc⟩ := exists_rootGroup_of_positiveSupport hG hT i hi
    (-P.root r) (hP.neg_mem_roots hα) (-P.coroot r) hνneg hnegative hnegline
  have hχ : CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      CommGroupScheme.groupHom (P.coroot r) ≫ i =
      CommGroupScheme.groupHom (-P.coroot r) ≫ i := by
    have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ P.coroot r = -P.coroot r := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ P.coroot r) ≫ i = _
    rw [hneg]
  have hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left :=
    Dynamic.isOpenImmersion_tripleCellMultiplication _ (hχ.symm ▸ hxm) hC hxp
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso i hT r
  have hn2 := RankOneRootCellRelation.exists_sq_eq_of_isNormalizingPoint hC pair hn
  let D : RankOneRootCellRelation.WeylData k :=
    { G := G, T := T, i := i, xp := xp, xm := xm, α := P.root r, hxp := hxpc, hxm := hxmc,
      open_cell := hopen, h := P.coroot r, pair := pair, n := n, hn := hn, hn2 := hn2,
      irreducible := DynamicConnected.irreducibleSpace_of_smooth G }
  exact ⟨D.xp, D.xm', D.isRootCell (inferInstanceAs (IsSeparated G.X.hom))⟩

/-- Choose the two parametrizations, retaining all root-cell clauses in the subtype. -/
def parametrizationsOfSupportLines
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hrank : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (r : J)
    (hsupport : haveI := hG.isAffineHom
      ∀ β ∈ roots i, β = P.root r ∨ β = -P.root r)
    (hline : haveI := hG.isAffineHom
      Nonempty (k ≃ₗ[k] weightSpace i (P.root r)))
    (hnegline : haveI := hG.isAffineHom
      Nonempty (k ≃ₗ[k] weightSpace i (-P.root r))) :
    { p : (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) ×
        (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) //
      RootCell.IsRootCell i (P.root r) (P.coroot r) p.1 p.2 } := by
  let h := exists_rootCell_of_support_lines hG hT i hi P hP hrank r hsupport hline hnegline
  exact ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme.LocalRankOneRootCell
