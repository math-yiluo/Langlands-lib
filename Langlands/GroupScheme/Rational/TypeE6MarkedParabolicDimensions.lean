import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties
import Langlands.GroupScheme.Rational.TypeE6BranchCocharacter
import Langlands.GroupScheme.Rational.TypeE6ParabolicDimensions
import Langlands.LinearAlgebra.RootDatumFaceHeight

/-! # Parabolic dimensions of marked faces in type E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.CartanE6Root Langlands.LinearAlgebra.RootDatumFaceHeight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private local instance finiteTypeBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹LocallyOfFiniteType G.X.hom›

/-- Lie dimension for an affine finite-type field group is invariant under
scalar extension. -/
theorem Lie.dimension_fieldExtension
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] :
    Lie.dimension ((GroupScheme.baseChange (algebraBaseMap k L)).obj G) = Lie.dimension G :=
  TorusExistence.finrank_lieKernel_baseChange G L

section MarkedFace

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

open scoped Classical in
/-- A star-stable set of marked vertices can be prescribed as the positive
simple-root support of a scaled cocharacter of the actual maximal split torus. -/
theorem TitsIndexData.exists_scaled_cocharacter_of_marked_face
    (S : Set d.Vertex) (hmark : S ⊆ d.distinguishedVertices)
    (hstar : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) a, d.star σ a ∈ S ↔ a ∈ S) :
    ∃ (m : ℤ) (ν : cocharacterLattice d.splitTorus), 0 < m ∧
      ∀ a : d.Vertex, latticePairing d.splitTorus (d.rootRestriction a.val) ν =
        if a ∈ S then m else 0 := by
  classical
  let hT := d.maximalSplit.1.1
  let : Mono d.splitInclusion.hom.hom.left := d.maximalSplit.1.2.mono
  let hRoots := relativeRootSystem k G d.isSemisimple.isConnectedReductive _ _ d.maximalSplit
  let α (b : simpleRelativeRoots d.splitInclusion d.positiveCocharacter) :=
    (b : characterLattice d.splitTorus)
  obtain ⟨hOrbit, e, he⟩ := titsIndexRelativeSimpleRoots k G d
  let selected (b : simpleRelativeRoots d.splitInclusion d.positiveCocharacter) : Prop :=
    ∃ a : S, e (d.orbitClass ⟨a.val, hmark a.property⟩) = b
  obtain ⟨m, hm, ν, hν⟩ := hT.exists_scaled_pairings α
    (hRoots.linearIndependent_simpleRelativeRoots d.splitInclusion d.positiveCocharacter hT d.generic)
    (fun b => if selected b then 1 else 0)
  refine ⟨m, ν, hm, fun a => ?_⟩
  by_cases ha : a ∈ d.distinguishedVertices
  · let b := e (d.orbitClass ⟨a, ha⟩)
    have hS : selected b ↔ a ∈ S := by
      constructor
      · rintro ⟨j, hj⟩
        have hr : d.rootRestriction j.val.val = d.rootRestriction a.val := by
          rw [← he ⟨j.val, hmark j.property⟩, ← he ⟨a, ha⟩]
          exact congrArg Subtype.val hj
        obtain ⟨σ, hσ⟩ := (hOrbit ⟨j.val, hmark j.property⟩ ⟨a, ha⟩).mp hr
        change d.star σ j.val = a at hσ
        rw [← hσ]
        exact (hstar σ j.val).mpr j.property
      · intro h
        exact ⟨⟨a, h⟩, rfl⟩
    simpa only [show α b = d.rootRestriction a.val from he ⟨a, ha⟩,
      hS, mul_ite, mul_one, mul_zero] using hν b
  · have hz : d.rootRestriction a.val = 0 := by
      simpa only [TitsIndexData.distinguishedVertices, TitsIndexData.zeroVertices, Set.mem_compl_iff,
        Set.mem_ofPred_eq, not_ne_iff] using ha
    simp [hz, show a ∉ S from fun h => ha (hmark h)]

end MarkedFace

section SplitDimensions

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (p : SplitPinning G)

private theorem SplitPinning.dimension_parabolic_of_numbered_face
    (hsc : IsSimplyConnected G) (e : p.base.support ≃ Fin 6)
    (hE : ∀ a c, p.rootDatum.pairing a.val c.val = CartanMatrix.E 6 (e a) (e c))
    (s : Finset (Fin 6)) (m : ℤ) (hm : 0 < m)
    (ν : cocharacterLattice p.torus)
    (hν : ∀ a : p.base.support, p.rootDatum.root' a.val ν = if e a ∈ s then m else 0) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom
      (CommGroupScheme.groupHom ν ≫ p.inclusion)).isAffineHom
    Lie.dimension G = 78 ∧
      Lie.dimension (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ p.inclusion)) +
        parabolicCodimension s = 78 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hd, hex⟩ := typeE6ParabolicDimensions k G p hsc e hE
  obtain ⟨μ, hμ, _, hdim⟩ := hex s
  refine ⟨hd, ?_⟩
  let P := p.rootDatum
  have hsign (j : p.rootIndex) : P.root' j ν < 0 ↔ P.root' j μ < 0 := by
    obtain ⟨f, _, _, hf⟩ := p.base.exists_root_eq_sum_int j
    have hscale : 3 * P.root' j ν = m * P.root' j μ := by
      rw [root'_eq_sum p.base ν f hf, root'_eq_sum p.base μ f hf, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hν ⟨i, hi⟩, hμ ⟨i, hi⟩]
      split <;> ring
    have hle : 0 ≤ P.root' j ν ↔ 0 ≤ P.root' j μ := by
      rw [← mul_nonneg_iff_of_pos_left (b := P.root' j ν) (by decide : (0 : ℤ) < 3),
        hscale, mul_nonneg_iff_of_pos_left hm]
    simpa only [not_le] using hle.not
  let : IsAffineHom (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ p.inclusion)).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _).isAffineHom
  let : IsAffineHom (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom μ ≫ p.inclusion)).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _).isAffineHom
  have hcard : Nat.card {j : p.rootIndex // P.root' j ν < 0} =
      Nat.card {j : p.rootIndex // P.root' j μ < 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight hsign)
  have hνdim := p.dimension_parabolic_add_card_negative ν
  have hμdim := p.dimension_parabolic_add_card_negative μ
  change _ + Nat.card {j : p.rootIndex // P.root' j ν < 0} = _ at hνdim
  change _ + Nat.card {j : p.rootIndex // P.root' j μ < 0} = _ at hμdim
  rw [hcard] at hνdim
  have heq : Lie.dimension (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ p.inclusion)) =
      Lie.dimension (Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom μ ≫ p.inclusion)) :=
    Nat.add_right_cancel (hνdim.trans hμdim.symm)
  rw [heq]
  exact hdim

end SplitDimensions

section RationalDimensions

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- Over the ground field, the parabolic of the marked E6 face has the
absolute codimension computed from the numbered roots. -/
theorem TitsIndexData.dimension_parabolic_of_typeE6_face
    (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 6)
    (hE : ∀ a c, d.cartan a c = CartanMatrix.E 6 (e a) (e c))
    (s : Finset (Fin 6)) (m : ℤ) (hm : 0 < m)
    (ν : cocharacterLattice d.pinning.torus)
    (hν : ∀ a : d.Vertex, d.pinning.rootDatum.root' a.val
      (cocharacterLattice.baseChange (algebraBaseMap k (SeparableClosure k)) _ ν) =
        if e a ∈ s then m else 0) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let χ := CommGroupScheme.groupHom ν ≫ d.pinning.inclusion
    haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
    Lie.dimension G = 78 ∧ IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ) ∧
      Lie.dimension (Dynamic.Affine.parabolicScheme χ) + parabolicCodimension s = 78 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let E := SeparableClosure k
  let b := algebraBaseMap k E
  let G_E := (GroupScheme.baseChange b).obj G
  let : IsAffine G_E.X.left := isAffine_of_isAffineHom G_E.X.hom
  let p := d.pinning.toSplitPinning
  let νE := cocharacterLattice.baseChange b d.pinning.torus ν
  have h_E (a c : p.base.support) :
      p.rootDatum.pairing a.val c.val = CartanMatrix.E 6 (e a) (e c) := hE a c
  obtain ⟨hG, hP⟩ := p.dimension_parabolic_of_numbered_face
    (isSimplyConnectedFieldExtension k E G hsc) e h_E s m hm νE hν
  let χ := CommGroupScheme.groupHom ν ≫ d.pinning.inclusion
  let P := Dynamic.Affine.parabolicScheme χ
  let j := Dynamic.Affine.parabolicHom χ
  let hj := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  let hrep := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let : IsAffineHom P.X.hom := hj.isAffineHom
  let : LocallyOfFiniteType P.X.hom := hj.locallyOfFiniteType
  have hPpar : IsParabolicSubgroup j := (parabolicDynamic k G
    hsc.isSemisimple.isConnectedReductive P j hj).mpr ⟨χ, hrep.2⟩
  let χE := CommGroupScheme.groupHom νE ≫ p.inclusion
  let : IsAffineHom (Dynamic.Affine.parabolicScheme χE).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χE).isAffineHom
  have hχ : Dynamic.baseChangeCocharacter b χ = χE := by
    rw [show χ = CommGroupScheme.groupHom ν ≫ d.pinning.inclusion from rfl,
      Dynamic.baseChangeCocharacter_comp_hom]
    rfl
  have hPB : (Dynamic.parabolic χE).IsRepresentedBy ((GroupScheme.baseChange b).map j) := by
    rw [← hχ, Dynamic.parabolic_baseChange]
    exact hrep.baseChange b
  let a := hPB.isoOfIsRepresentedBy (Dynamic.Affine.isRepresentedBy_parabolicHom χE)
  have hDimP := (Lie.dimension_fieldExtension (L := E) P).symm.trans (Lie.dimension_eq_of_iso a)
  have hDimG := Lie.dimension_fieldExtension (L := E) G
  exact ⟨hDimG.symm.trans hG, hPpar, hDimP ▸ hP⟩

end RationalDimensions

/-- A star-stable set of distinguished E6 vertices is the omitted set of
an actual rational dynamic parabolic with the computed absolute codimension. -/
def TypeE6MarkedParabolicDimensionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (e : d.Vertex ≃ Fin 6), IsSimplyConnected G →
    (∀ a c, d.cartan a c = CartanMatrix.E 6 (e a) (e c)) →
    ∀ s : Finset (Fin 6),
      (∀ a : d.Vertex, e a ∈ s → a ∈ d.distinguishedVertices) →
      (∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex),
        e (d.star σ a) ∈ s ↔ e a ∈ s) →
      haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      Lie.dimension G = 78 ∧
      ∃ (m : ℤ) (ν : cocharacterLattice d.splitTorus), 0 < m ∧
        (∀ a : d.Vertex, d.pinning.rootDatum.root' a.val
          (cocharacterLattice.baseChange (algebraBaseMap k (SeparableClosure k)) _ (ν ≫ d.torusMap)) =
            if e a ∈ s then m else 0) ∧
        let χ := CommGroupScheme.groupHom ν ≫ d.splitInclusion
        haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
        IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ) ∧
          Lie.dimension (Dynamic.Affine.parabolicScheme χ) + parabolicCodimension s = 78

theorem typeE6MarkedParabolicDimensions : TypeE6MarkedParabolicDimensionsStatement.{u} := by
  classical
  intro k _ G _ _ d e hsc hE s hmark hstar
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let S : Set d.Vertex := {a | e a ∈ s}
  obtain ⟨m, ν, hm, hν⟩ := d.exists_scaled_cocharacter_of_marked_face S hmark hstar
  let b := algebraBaseMap k (SeparableClosure k)
  have hv (a : d.Vertex) : d.pinning.rootDatum.root' a.val
      (cocharacterLattice.baseChange b _ (ν ≫ d.torusMap)) = if e a ∈ s then m else 0 := by
    change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root a.val) _ = _
    rw [d.pinning.isRootDatum.1, cocharacterLattice.baseChange_comp,
      ← TitsIndexExistence.latticePairing_restriction d.maximalSplit.1.1 d.torusMap _ ν]
    change latticePairing d.splitTorus (d.rootRestriction a.val) ν = _
    by_cases ha : e a ∈ s
    · have hS : a ∈ S := ha
      simpa only [ite_eq_left ha, ite_eq_left hS] using hν a
    · have hS : a ∉ S := ha
      simpa only [ite_eq_right ha, ite_eq_right hS] using hν a
  obtain ⟨hG, hP, hdim⟩ := d.dimension_parabolic_of_typeE6_face hsc e hE s m hm
    (ν ≫ d.torusMap) hv
  have hχ : CommGroupScheme.groupHom (ν ≫ d.torusMap) ≫ d.pinning.inclusion =
      CommGroupScheme.groupHom ν ≫ d.splitInclusion := by
    change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom d.torusMap) ≫ d.pinning.inclusion = _
    rw [Category.assoc, d.square]
  let dim (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) : Prop :=
    haveI := (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
    Lie.dimension (Dynamic.Affine.parabolicScheme χ) + parabolicCodimension s = 78
  exact ⟨hG, m, ν, hm, hv, hχ ▸ hP, (congrArg dim hχ).mp hdim⟩

end Langlands.GroupScheme
