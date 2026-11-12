import Langlands.BruhatTits.SpecialCompact.RootDepthWeakContraction
import Langlands.BruhatTits.SpecialCompact.WeakIwahoriBasisReduction
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # From the original depth product to literal Iwahori intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type u} [Group H]

/-- Two disjointness assertions distinguish the three actual factors. -/
theorem tripleSubgroupProduct_injective_of_disjoint
    (M N Nbar P : Subgroup H) (hbar : Disjoint Nbar P)
    (hM : M ≤ P) (hN : N ≤ P) (hMN : Disjoint M N) :
    Function.Injective (fun t : Nbar × M × N =>
      (t.1 : H) * (t.2.1 : H) * (t.2.2 : H)) := by
  intro a b hab
  let toPair (t : Nbar × M × N) : Nbar × P :=
    (t.1, ⟨(t.2.1 : H) * (t.2.2 : H),
      P.mul_mem (hM t.2.1.property) (hN t.2.2.property)⟩)
  have hp : toPair a = toPair b :=
    Subgroup.mul_injective_of_disjoint hbar (by
      simpa only [toPair, mul_assoc] using hab)
  have hfirst : a.1 = b.1 := congrArg (fun t : Nbar × P => t.1) hp
  have hlast : a.2 = b.2 :=
    Subgroup.mul_injective_of_disjoint hMN
      (congrArg (fun t : Nbar × P => (t.2 : H)) hp)
  exact Prod.ext hfirst hlast

/-- Multiplication of two prescribed radical subgroups and the literal
middle intersection, retaining its original value in `K`. -/
def orderedSubgroupIntersectionProduct
    (K M V Vbar : Subgroup H) (hV : V ≤ K) (hVbar : Vbar ≤ K) :
    Vbar × ↥(K ⊓ M) × V → K :=
  fun t => ⟨(t.1 : H) * (t.2.1 : H) * (t.2.2 : H),
    K.mul_mem (K.mul_mem (hVbar t.1.property) t.2.1.property.1)
      (hV t.2.2.property)⟩

/-- If a prescribed triangular product covers `K`, uniqueness in the
ambient cell forces both literal radical intersections to be its factors. -/
theorem radicalIntersections_eq_of_surjective
    (K M N Nbar V Vbar : Subgroup H)
    (hV : V ≤ K) (hVbar : Vbar ≤ K) (hVN : V ≤ N) (hVbarNbar : Vbar ≤ Nbar)
    (hcell : Function.Injective (fun t : Nbar × M × N =>
      (t.1 : H) * (t.2.1 : H) * (t.2.2 : H)))
    (hsurj : Function.Surjective (orderedSubgroupIntersectionProduct K M V Vbar hV hVbar)) :
    K ⊓ N = V ∧ K ⊓ Nbar = Vbar := by
  constructor
  · apply le_antisymm
    · intro g hg
      obtain ⟨t, ht⟩ := hsurj ⟨g, hg.1⟩
      have htuple :
          ((⟨t.1, hVbarNbar t.1.property⟩ : Nbar),
            (⟨t.2.1, t.2.1.property.2⟩ : M), (⟨t.2.2, hVN t.2.2.property⟩ : N)) =
          (1, 1, (⟨g, hg.2⟩ : N)) := by
        apply hcell
        simpa only [orderedSubgroupIntersectionProduct, Subgroup.coe_one, one_mul] using
          congrArg (fun z : K => (z : H)) ht
      have hn : (t.2.2 : H) = g :=
        congrArg (fun z : Nbar × M × N => (z.2.2 : H)) htuple
      exact hn ▸ t.2.2.property
    · exact le_inf hV hVN
  · apply le_antisymm
    · intro g hg
      obtain ⟨t, ht⟩ := hsurj ⟨g, hg.1⟩
      have htuple :
          ((⟨t.1, hVbarNbar t.1.property⟩ : Nbar),
            (⟨t.2.1, t.2.1.property.2⟩ : M), (⟨t.2.2, hVN t.2.2.property⟩ : N)) =
          ((⟨g, hg.2⟩ : Nbar), 1, 1) := by
        apply hcell
        simpa only [orderedSubgroupIntersectionProduct, Subgroup.coe_one, mul_one] using
          congrArg (fun z : K => (z : H)) ht
      have hn : (t.1 : H) = g :=
        congrArg (fun z : Nbar × M × N => (z.1 : H)) htuple
      exact hn ▸ t.1.property
    · exact le_inf hVbar hVbarNbar

/-- The same covering product and ambient uniqueness give precisely the
ordered bijection of the three literal intersections. -/
theorem hasIwahoriIntersectionDecomposition_of_surjective
    (K M N Nbar V Vbar : Subgroup H)
    (hV : V ≤ K) (hVbar : Vbar ≤ K) (hVN : V ≤ N) (hVbarNbar : Vbar ≤ Nbar)
    (hcell : Function.Injective (fun t : Nbar × M × N =>
      (t.1 : H) * (t.2.1 : H) * (t.2.2 : H)))
    (hsurj : Function.Surjective (orderedSubgroupIntersectionProduct K M V Vbar hV hVbar)) :
    HasIwahoriIntersectionDecomposition K M N Nbar := by
  constructor
  · intro a b hab
    have htuple :
        ((⟨a.1, a.1.property.2⟩ : Nbar),
          (⟨a.2.1, a.2.1.property.2⟩ : M), (⟨a.2.2, a.2.2.property.2⟩ : N)) =
        ((⟨b.1, b.1.property.2⟩ : Nbar),
          (⟨b.2.1, b.2.1.property.2⟩ : M), (⟨b.2.2, b.2.2.property.2⟩ : N)) := by
      apply hcell
      exact congrArg (fun z : K => (z : H)) hab
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : Nbar × M × N => (z.1 : H)) htuple)
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun z : Nbar × M × N => (z.2.1 : H)) htuple)
      · exact Subtype.ext (congrArg (fun z : Nbar × M × N => (z.2.2 : H)) htuple)
  · intro g
    obtain ⟨t, ht⟩ := hsurj g
    exact ⟨(⟨t.1, hVbar t.1.property, hVbarNbar t.1.property⟩, t.2.1,
      ⟨t.2.2, hV t.2.2.property, hVN t.2.2.property⟩), ht⟩

end Groups

section Standard

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (nu : cocharacterLattice S)

/-- One standard cocharacter suffices for uniqueness of the actual
opposite-radical, Levi, radical multiplication. -/
theorem standardTripleProduct_injective
    (hneg : ∀ a ∈ relativeRoots i, -a ∈ relativeRoots i)
    {J : Set (characterLattice S)} {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i nu J zeta) :
    Function.Injective (fun t :
      standardOppositeUnipotentPoints i nu J × standardLeviPoints i nu J ×
        standardUnipotentPoints i nu J =>
      (t.1 : rationalPoints G) * (t.2.1 : rationalPoints G) *
        (t.2.2 : rationalPoints G)) := by
  apply tripleSubgroupProduct_injective_of_disjoint _ _ _ (standardParabolicPoints i nu J)
  · rw [Subgroup.disjoint_def]
    intro g hgminus hgplus
    let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have hminus := standardUnipotent_le_dynamicUnipotent i (-nu)
      (hzeta.neg i nu hneg) (Over.mk (𝟙 _)) hgminus
    rw [groupHom_neg_comp_eq_oppositeCocharacter] at hminus
    exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (CommGroupScheme.groupHom zeta ≫ i) hminus
      (standardParabolic_le_dynamicParabolic i nu hzeta (Over.mk (𝟙 _)) hgplus)
  · exact standardLevi_le_standardParabolic i nu J (Over.mk (𝟙 _))
  · exact standardUnipotent_le_standardParabolic i nu J (Over.mk (𝟙 _))
  · rw [Subgroup.disjoint_def]
    intro g hM hN
    exact StandardLeviIntersection.eq_one_of_mem_standardLevi_of_mem_standardUnipotent
      i nu hzeta hM hN

end Standard

section MoyPrasad

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration)
    (x : P.Apartment) (nu : cocharacterLattice P.S)
    (J : Set (characterLattice P.S)) (r : NNReal)

/-- The original generated opposite-depth subgroup, literal Moy–Prasad
Levi intersection and generated positive-depth subgroup, multiplied into
the same original Moy–Prasad group. Surjectivity is a separate obligation. -/
def moyPrasadRadicalDepthProduct :
    standardRadicalDepth P.toValuationBuildingData x (-nu) (Neg.neg '' J) r ×
      ↥(Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J) ×
      standardRadicalDepth P.toValuationBuildingData x nu J r → Zf.moyPrasad x r :=
  orderedSubgroupIntersectionProduct _ _ _ _
    (standardRadicalDepth_le_moyPrasad P Zf x nu J r)
    (standardRadicalDepth_le_moyPrasad P Zf x (-nu) (Neg.neg '' J) r)

/-- Surjectivity of this actual depth product identifies both literal
radical intersections and supplies their ordered Iwahori decomposition. -/
theorem moyPrasad_intersections_and_iwahori_of_surjective
    {zeta : cocharacterLattice P.S} (hzeta : IsStandardCocharacter P.i nu J zeta)
    (hsurj : Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r)) :
    (Zf.moyPrasad x r ⊓ standardUnipotentPoints P.i nu J =
      standardRadicalDepth P.toValuationBuildingData x nu J r) ∧
    (Zf.moyPrasad x r ⊓ standardOppositeUnipotentPoints P.i nu J =
      standardRadicalDepth P.toValuationBuildingData x (-nu) (Neg.neg '' J) r) ∧
    HasIwahoriIntersectionDecomposition (Zf.moyPrasad x r)
      (standardLeviPoints P.i nu J) (standardUnipotentPoints P.i nu J)
      (standardOppositeUnipotentPoints P.i nu J) := by
  have hcell := standardTripleProduct_injective P.i nu
    (relativeRootNegation F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus) hzeta
  have hV := standardRadicalDepth_le_moyPrasad P Zf x nu J r
  have hVbar := standardRadicalDepth_le_moyPrasad P Zf x (-nu) (Neg.neg '' J) r
  have hVN := standardRadicalDepth_le_standardUnipotentPoints
    P.toValuationBuildingData x nu J r
  have hVbarNbar := standardRadicalDepth_le_standardUnipotentPoints
    P.toValuationBuildingData x (-nu) (Neg.neg '' J) r
  have hi := radicalIntersections_eq_of_surjective _ _ _ _ _ _
    hV hVbar hVN hVbarNbar hcell hsurj
  exact ⟨hi.1, hi.2, hasIwahoriIntersectionDecomposition_of_surjective _ _ _ _ _ _
    hV hVbar hVN hVbarNbar hcell hsurj⟩

/-- For a generic standard chamber, the actual product covering alone
supplies the remaining Iwahori and weak-chamber clauses at this depth. -/
theorem moyPrasad_iwahori_and_weak_of_surjective
    (hnu : IsGenericCocharacter P.i nu) (hJ : J ⊆ simpleRelativeRoots P.i nu)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ P.S.toGrp}
    (hA : IsCompatibleStandardSplitComponent P.i nu J A q)
    (hsurj : Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r)) :
    HasIwahoriIntersectionDecomposition (Zf.moyPrasad x r)
      (standardLeviPoints P.i nu J) (standardUnipotentPoints P.i nu J)
      (standardOppositeUnipotentPoints P.i nu J) ∧
    WeakChamberContraction (Zf.moyPrasad x r)
      (standardUnipotentPoints P.i nu J) (standardOppositeUnipotentPoints P.i nu J)
      (standardComponentCAplus P.i nu J q) := by
  obtain ⟨zeta, hzeta⟩ := (standardCocharacter F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus nu hnu J hJ).1
  obtain ⟨hpos, hneg, hIwahori⟩ :=
    moyPrasad_intersections_and_iwahori_of_surjective P Zf x nu J r hzeta hsurj
  exact ⟨hIwahori, weakChamberContraction_of_intersection_eq_standardRadicalDepth
    P.toValuationBuildingData x nu hnu hJ hA (Zf.moyPrasad x r) r hpos hneg⟩

end MoyPrasad

end Langlands.BruhatTits.SpecialCompact
