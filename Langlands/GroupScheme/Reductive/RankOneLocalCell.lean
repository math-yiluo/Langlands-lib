import Langlands.GroupScheme.Reductive.RankOneCellData

/-! # Rank-one cell data from local positivity and line facts

Variants of `rankOne_exists_rootGroup` and `rankOne_exists_cell` whose two
structural premises are facts about the given group `G` and cocharacter `ν`
rather than the published statements `RankOnePositiveRootUniquenessStatement`
and `SplitRootLieLineStatement`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RankOneCellData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

namespace RankOneLocalCell

/-- **The positive root group from local facts.** If `⟨α, ν⟩ > 0` for a root `α`, every root
positive on `ν` equals `α`, and the root space of `α` is a line, then the dynamic unipotent
subgroup of `ν` is represented by a homomorphism `x : 𝔾ₐ ⟶ G` on which `T` acts by conjugation
through `α`. -/
theorem exists_rootGroup
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν)
    (hpos : haveI := hG.isAffineHom;
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
    exact hpos (w j) hj.1 hj.2
  have hd : d = 1 := by
    have h1 := TorusUnipotence.finrank_actionWeightSpace hT b ht htw hε α
    rw [Standard.finrank_actionWeightSpace_unipotentAction i ν hT ⟨hα, hν⟩] at h1
    obtain ⟨eα⟩ := hline
    rw [← eα.finrank_eq, Module.finrank_self] at h1
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hwα), Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    exact h1.symm
  subst hd
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

/-- **The opposite root group from local facts.** If `⟨α, ν⟩ > 0`, `-α` is a root, every root
negative on `ν` equals `-α`, and the root space of `-α` is a line, then the dynamic unipotent
subgroup of the opposite of `ν` is represented by a homomorphism `x' : 𝔾ₐ ⟶ G` on which `T`
acts by conjugation through `-α`. -/
theorem exists_oppositeRootGroup
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (α : characterLattice T) (hα' : haveI := hG.isAffineHom; -α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν)
    (hneg : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, latticePairing T β ν < 0 → β = -α)
    (hline' : haveI := hG.isAffineHom; Nonempty (k ≃ₗ[k] weightSpace i (-α))) :
    ∃ x' : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy x' ∧
      ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
        (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ x'.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction (-α) U t a ≫ x'.hom.hom := by
  have hν' : 0 < latticePairing T (-α) (-ν) := by simpa using hν
  have hχ : CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      CommGroupScheme.groupHom ν ≫ i = CommGroupScheme.groupHom (-ν) ≫ i := by
    have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ ν = -ν := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i = _
    rw [hneg]
  rw [hχ]
  refine exists_rootGroup hG hT i hi (-α) hα' (-ν) hν' (fun β hβ hβν => ?_) hline'
  apply hneg β hβ
  simpa using hβν

/-- **The open cell from local facts.** If `α` and `-α` are roots, `⟨α, ν⟩ > 0`, the maximal
torus represents the dynamic centralizer of `ν`, the only roots positive (negative) on `ν` are
`α` (`-α`), and both root spaces are lines, then there are homomorphisms `xp xm : 𝔾ₐ ⟶ G`
representing the dynamic unipotent subgroups of `ν` and of its opposite, on which `T` acts by
conjugation through `α` and `-α`, such that `(Y, t, X) ↦ xm(Y) t xp(X)` is an open immersion. -/
theorem exists_cell
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (α : characterLattice T) (hα : haveI := hG.isAffineHom; α ∈ roots i)
    (hα' : haveI := hG.isAffineHom; -α ∈ roots i)
    (ν : cocharacterLattice T) (hν : 0 < latticePairing T α ν)
    (hZ : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i)
    (hpos : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, 0 < latticePairing T β ν → β = α)
    (hneg : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, latticePairing T β ν < 0 → β = -α)
    (hline : haveI := hG.isAffineHom; Nonempty (k ≃ₗ[k] weightSpace i α))
    (hline' : haveI := hG.isAffineHom; Nonempty (k ≃ₗ[k] weightSpace i (-α))) :
    ∃ xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy xp ∧
      (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy xm ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (a : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction α U t a ≫ xp.hom.hom) ∧
      (∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X)
          (b : U ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
        (t ≫ i.hom.hom) * (b ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
          VectorGroup.weightPointAction (-α) U t b ≫ xm.hom.hom) ∧
      IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := by
  have := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨xp, hxp, hxpc⟩ := exists_rootGroup hG hT i hi α hα ν hν hpos hline
  obtain ⟨xm, hxm, hxmc⟩ := exists_oppositeRootGroup hG hT i hi α hα' ν hν hneg hline'
  exact ⟨xp, xm, hxp, hxm, hxpc, hxmc,
    Dynamic.isOpenImmersion_tripleCellMultiplication _ hxm hZ hxp⟩

end RankOneLocalCell

end Langlands.GroupScheme
