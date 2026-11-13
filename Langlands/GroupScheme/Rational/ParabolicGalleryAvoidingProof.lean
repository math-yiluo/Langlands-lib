import Langlands.GroupScheme.Rational.ParabolicGalleryStatement
import Langlands.GroupScheme.Rational.RationalCocharacterWallModels
import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.PositiveLeviCentralizer
import Langlands.Global.AdelicRestrictionSplitCentreCanonical

/-! # Rank-one galleries avoiding a central split torus: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.FiniteHyperplaneSegment
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalCocharacter

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

omit [IsAffineHom G.X.hom] in
/-- The whole centralizer of a split component of a specified Levi of an
actual rational parabolic is exactly the image of that Levi. -/
theorem torusCentralizer_eq_range_of_isRationalParabolicWithLevi
    (hG : IsConnectedReductive G) {a : A.toGrp ⟶ L} (ha : IsSplitComponent a)
    {j : L ⟶ G} {F : SubgroupFunctor G} (hF : IsRationalParabolicWithLevi j F) :
    torusCentralizer (a ≫ j) = SubgroupFunctor.range j := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨R, r, l, hr, hl, hlr, -⟩ := hF
  subst hlr
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG R L A r l a hr hl ha
  apply le_antisymm
  · rw [pres.levi_eq_splitComponentCocharacter]
    exact torusCentralizer_le_dynamicCentralizer _ _
  · exact IsCentral.range_le_torusCentralizer_comp a ha.1.2 (l ≫ r)

/-- Every actual rational parabolic with the specified Levi is the parabolic
of a regular rational direction in a split component of that Levi. -/
theorem exists_regular_parabolic_eq (hG : IsConnectedReductive G)
    {a : A.toGrp ⟶ L} (ha : IsSplitComponent a) {j : L ⟶ G}
    {F : SubgroupFunctor G} (hF : IsRationalParabolicWithLevi j F) :
    ∃ x : Space A, Regular (rootForms (a ≫ j)) x ∧
      parabolic ha.1.1.1 (a ≫ j) x = F := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hT := torusCentralizer_eq_range_of_isRationalParabolicWithLevi hG ha hF
  obtain ⟨R, r, l, hr, hl, hlr, hrF⟩ := hF
  subst hlr hrF
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG R L A r l a hr hl ha
  refine ⟨rationalCocharacterEvaluation pres.splitComponentCocharacter, ?_, ?_⟩
  · apply regular_ofIntegral_of_centralizer_eq ha.1.1.1
    rw [hT, pres.levi_eq_splitComponentCocharacter]
  · rw [parabolic_ofIntegral, pres.parabolic_eq_splitComponentCocharacter]

/-- Equal intersections with the centralizer of an integral direction force
equal strict signs on every actual root orthogonal to that direction. -/
theorem mul_pos_of_inf_dynamicCentralizer_eq (hG : IsConnectedReductive G)
    (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G) (ν₀ : cocharacterLattice A)
    {x y : Space A} (hx : Regular (rootForms i) x) (hy : Regular (rootForms i) y)
    (h : parabolic hA i x ⊓ Dynamic.centralizer (CommGroupScheme.groupHom ν₀ ≫ i) =
      parabolic hA i y ⊓ Dynamic.centralizer (CommGroupScheme.groupHom ν₀ ≫ i))
    (α : relativeRoots i) (hα : latticePairing A (α : characterLattice A) ν₀ = 0) :
    0 < rootForms i α x * rootForms i α y := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let d := Dynamic.rationalParabolicModel hG (CommGroupScheme.groupHom ν₀ ≫ i)
  let jH := d.m ≫ d.p
  have hjHc : IsClosedSubgroup jH :=
    d.levi.isClosedSubgroup.comp d.parabolic.isClosedSubgroup
  have hM := d.levi.isConnectedReductive
  let : IsAffineHom d.M.X.hom := hM.isAffineHom
  let : Smooth d.M.X.hom := hM.smooth
  let : ConnectedSpace d.M.X.left := hM.connectedSpace
  let : LocallyOfFiniteType d.M.X.hom := inferInstance
  let iH := Dynamic.torusFactor i (CommGroupScheme.groupHom ν₀) d.centralizer_rep
  have hiH : iH ≫ jH = i :=
    Dynamic.torusFactor_comp i (CommGroupScheme.groupHom ν₀) d.centralizer_rep
  have hαH : (α : characterLattice A) ∈ relativeRoots iH :=
    mem_relativeRoots_of_pairing_eq_zero i ν₀ d.centralizer_rep iH hiH α.property hα
  have hcomap : (parabolic hA i x).comap jH = (parabolic hA i y).comap jH := by
    have key (F F' : SubgroupFunctor G)
        (hFF : F ⊓ SubgroupFunctor.range jH = F' ⊓ SubgroupFunctor.range jH) :
        F.comap jH ≤ F'.comap jH := by
      intro T z hz
      rw [SubgroupFunctor.mem_comap] at hz ⊢
      have hmem : z ≫ jH.hom.hom ∈ (F ⊓ SubgroupFunctor.range jH).carrier T :=
        ⟨hz, SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩⟩
      rw [hFF] at hmem
      exact hmem.1
    rw [d.centralizer_rep.2] at *
    exact le_antisymm (key _ _ h) (key _ _ h.symm)
  have hpar (v : Space A) :
      Dynamic.parabolic
          (CommGroupScheme.groupHom (integralRealization hA v).cocharacter ≫ iH) =
        (parabolic hA i v).comap jH := by
    rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup _ jH hjHc, Category.assoc, hiH]
    rfl
  have heq : Dynamic.parabolic
        (CommGroupScheme.groupHom (integralRealization hA x).cocharacter ≫ iH) =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (integralRealization hA y).cocharacter ≫ iH) := by
    rw [hpar, hpar, hcomap]
  have h₁ := (IntegralRealization.parabolic_le_iff hA iH _ _).1 heq.le _ hαH
  have h₂ := (IntegralRealization.parabolic_le_iff hA iH _ _).1 heq.ge _ hαH
  have hx₀ := hx α
  have hy₀ := hy α
  simp only [rootForms, rootForm_apply] at hx₀ hy₀ ⊢
  rcases lt_or_gt_of_ne hx₀ with hxn | hxp
  · have hyn : y (toRat (α : characterLattice A)) < 0 :=
      lt_of_not_ge fun hy' => (not_le_of_gt hxn) (h₂ hy')
    exact mul_pos_of_neg_of_neg hxn hyn
  · exact mul_pos hxp (lt_of_le_of_ne (h₁ hxp.le) (Ne.symm hy₀))

/-- At a wall model whose vanishing roots all pair nontrivially with the
integral direction `ν ≫ g`, the central torus `b = g ≫ a` is not central in the
wall Levi. -/
theorem not_isCentral_wallModel (hG : IsConnectedReductive G)
    {B : CommGroupScheme (Spec (CommRingCat.of k))} (hB : IsSplitTorus B.toGrp)
    {a : A.toGrp ⟶ L} (ha : IsSplitComponent a) {j : L ⟶ G} (hjc : IsClosedSubgroup j)
    (hj : (torusCentralizer (a ≫ j)).IsRepresentedBy j)
    {g : B.toGrp ⟶ A.toGrp} {b : B.toGrp ⟶ L} (hg : g ≫ a = b)
    (ν : cocharacterLattice B)
    {x y w : Space A} (hw : IsWallDirection (a ≫ j) x y w)
    (hkeep : ∀ α ∈ relativeRoots (a ≫ j),
      latticePairing A α (ν ≫ (Additive.ofMul g : B ⟶ A)) = 0 → w (toRat α) ≠ 0) :
    ¬ IsCentral (b ≫ (hw.wallModel hG ha hjc hj).wall.l ≫
      (hw.wallModel hG ha hjc hj).wall.q) := by
  intro hc
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let wm := hw.wallModel hG ha hjc hj
  let d := wm.wall
  have hM := d.levi.isConnectedReductive
  let : IsAffineHom d.M.X.hom := hM.isAffineHom
  let : Smooth d.M.X.hom := hM.smooth
  let : LocallyOfFiniteType d.M.X.hom := inferInstance
  let iM : A.toGrp ⟶ d.M := a ≫ d.l ≫ d.q
  have hiM : iM ≫ d.m ≫ d.p = a ≫ j := by
    have hlc := d.levi_comp
    simp only [iM, Category.assoc] at hlc ⊢
    rw [hlc]
  obtain ⟨α, hα, hαw⟩ := hw.root
  have hαM : α ∈ relativeRoots iM :=
    (IsWallDirection.mem_relativeRoots_iff (integralRealization ha.1.1.1 w)
      wm.centralizer_rep iM hiM).2 ⟨hα, hαw⟩
  have hc' : IsCentral (CommGroupScheme.groupHom (Additive.ofMul g : B ⟶ A) ≫ iM) := by
    change IsCentral (g ≫ a ≫ d.l ≫ d.q)
    rw [← Category.assoc, hg]
    exact hc
  have h0 := root_restrict_eq_zero_of_isCentral iM (Additive.ofMul g : B ⟶ A) hB hc' hαM
  apply hkeep α hα _ hαw
  rw [latticePairing_apply, Category.assoc, h0, Limits.comp_zero, map_zero]

end Langlands.GroupScheme.RationalCocharacter

namespace Langlands.GroupScheme

open RationalCocharacter

/-- Two actual rational parabolics with the same embedded Levi which agree inside
the centralizer of a central split subtorus of that Levi are joined by a finite
gallery of actual rank-one walls at each of which the subtorus is noncentral. -/
theorem rationalParabolicGalleryAvoiding :
    RationalParabolicGalleryAvoidingStatement.{u} := by
  intro k _ G hG L B j b hb hbc F F' hF hF' hFF'
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨R, r, l, hr, hl, hlr, -⟩ := id hF
  have hL := hl.isConnectedReductive
  let : IsAffineHom L.X.hom := hL.isAffineHom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : Smooth L.X.hom := hL.smooth
  let : LocallyOfFiniteType L.X.hom := inferInstance
  obtain ⟨A, a, ha⟩ := exists_isSplitComponent L
  have hA : IsSplitTorus A.toGrp := ha.1.1.1
  have hjc : IsClosedSubgroup j := by
    rw [← hlr]
    exact hl.isClosedSubgroup.comp hr.isClosedSubgroup
  have hj : (torusCentralizer (a ≫ j)).IsRepresentedBy j :=
    ⟨RepresentedParabolicLeviIntersection.mono_of_isClosedSubgroup hjc,
      (torusCentralizer_eq_range_of_isRationalParabolicWithLevi hG ha hF).symm⟩
  obtain ⟨x, hx, rfl⟩ := exists_regular_parabolic_eq hG ha hF
  obtain ⟨y, hy, rfl⟩ := exists_regular_parabolic_eq hG ha hF'
  obtain ⟨g, hg⟩ := ha.exists_factor hb.1 hbc
  obtain ⟨ν, hν⟩ := hb.1.exists_genericCocharacter (b ≫ j)
  let ν₀ : cocharacterLattice A := ν ≫ (Additive.ofMul g : B ⟶ A)
  have hcent : Dynamic.centralizer (CommGroupScheme.groupHom ν₀ ≫ a ≫ j) =
      torusCentralizer (b ≫ j) := by
    change Dynamic.centralizer ((CommGroupScheme.groupHom ν ≫ g) ≫ a ≫ j) = _
    rw [Category.assoc, ← Category.assoc g, hg]
    exact IsSplitTorus.dynamicCentralizer_eq_torusCentralizer hb.1 (b ≫ j) ν hν
  let keep : relativeRoots (a ≫ j) → Prop :=
    fun α => latticePairing A (α : characterLattice A) ν₀ = 0
  have hprotect : ∀ α, keep α →
      0 < rootForms (a ≫ j) α x * rootForms (a ≫ j) α y := fun α hα =>
    mul_pos_of_inf_dynamicCentralizer_eq hG hA (a ≫ j) ν₀ hx hy
      (by rw [hcent]; exact hFF') α hα
  have : Finite (relativeRoots (a ≫ j)) := (hA.finite_relativeRoots (a ≫ j)).to_subtype
  have hgal := reflTransGen_chamberStep (rootForms (a ≫ j)) keep hx hy hprotect
  have key : ∀ v v', ChamberStep (rootForms (a ≫ j)) keep v v' →
      Relation.ReflTransGen (IsRationalRankOneWallAvoiding b j)
        (parabolic hA (a ≫ j) v) (parabolic hA (a ≫ j) v') := by
    rintro v v' (hvv' | hvv')
    · rw [parabolic_eq_of_sameChamber hA (a ≫ j) hvv']
    · obtain ⟨w, hw, hkeepw⟩ := exists_isWallDirection_of_wallAdjacent hvv'
      exact Relation.ReflTransGen.single
        ⟨isRationalParabolicWithLevi_of_regular hG hA (a ≫ j) hj hw.regular,
          isRationalParabolicWithLevi_of_regular hG hA (a ≫ j) hj hw.regular',
          (hw.wallModel hG ha hjc hj).wall,
          not_isCentral_wallModel hG hb.1 ha hjc hj hg ν hw
            fun α hα h0 => hkeepw ⟨α, hα⟩ h0⟩
  exact ⟨hF, hF', Relation.ReflTransGen.lift' (parabolic hA (a ≫ j)) key x y hgal⟩

end Langlands.GroupScheme
