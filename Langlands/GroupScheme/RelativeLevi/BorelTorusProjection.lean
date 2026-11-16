import Langlands.GroupScheme.RelativeLevi.BorelDynamicPresentationProof
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalProof
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalUniqueness
import Langlands.GroupScheme.RelativeLevi.LeviCoverDescent
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # A Borel projection onto a supplied maximal torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B : GroupScheme S} {i : B ⟶ G}

/-- A supplied maximal torus in a relative Borel is itself a relative Levi. -/
theorem IsRelativeBorelSubgroup.isRelativeLeviSubgroup_of_maximalTorus
    (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ B)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i)) :
    IsRelativeLeviSubgroup t := by
  let : IsAffineHom B.X.hom := hi.1.isAffineHom
  let : Mono i.hom.hom := hi.1.mono
  have ht : IsClosedSubgroup t :=
    IsClosedSubgroup.of_comp (relativeParabolicClosed S G B i hG hi.1) htG
  have hti : SubgroupFunctor.range (t ≫ i) ≤ SubgroupFunctor.range i := by
    intro V x hx
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr
      ⟨a ≫ t.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  obtain ⟨𝒰, h𝒰⟩ :=
    relativeBorelDynamicPresentation S G B i T (t ≫ i) hG hT htG hmax hi hti
  obtain ⟨U, r, hr, _⟩ := relativeUnipotentRadical S G B i hG hi.1
  refine ⟨ht, hT.smooth, U, r, hr, ?_⟩
  apply RelativeLevi.subgroupMultiplication_isIso_of_etaleCover 𝒰 t r
  intro a
  let b := 𝒰.f a
  let : Etale b := 𝒰.map_prop a
  let G' := (GroupScheme.baseChange b).obj G
  let B' := (GroupScheme.baseChange b).obj B
  let T' := (CommGroupScheme.baseChange b).obj T
  let i' := (GroupScheme.baseChange b).map i
  let t' := (GroupScheme.baseChange b).map t
  have hG' : IsReductive G' := hG.baseChange b
  let : Smooth G'.X.hom := hG'.smooth
  let : IsAffineHom G'.X.hom := hG'.isAffineHom
  obtain ⟨_, ν, hp, hc, _⟩ := h𝒰 a
  let χ := CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map (t ≫ i)
  have hP : (Dynamic.parabolic χ).IsRepresentedBy i' :=
    ⟨inferInstanceAs (Mono ((Over.pullback b).map i.hom.hom)), hp⟩
  have hZ : (Dynamic.centralizer χ).IsRepresentedBy
      ((GroupScheme.baseChange b).map (t ≫ i)) :=
    ⟨(htG.baseChange b).mono_overHom, hc.symm⟩
  obtain ⟨V, v, _, _, hv⟩ := (dynamicBaseRepresentability (𝒰.X a) G' χ).2.1
  have hl : IsRelativeLeviSubgroup t' :=
    (dynamicRelativeLevi (𝒰.X a) G' B' V T'.toGrp χ i' v
      ((GroupScheme.baseChange b).map (t ≫ i)) hG' hP hv hZ).2.2 t'
        ((GroupScheme.baseChange b).map_comp t i).symm
  obtain ⟨V', v', hv', hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication t' v') := hmul
  have hr' : IsRelativeUnipotentRadical ((GroupScheme.baseChange b).map r) :=
    hr.baseChange_etale b
  have heq : SubgroupFunctor.range ((GroupScheme.baseChange b).map r) =
      SubgroupFunctor.range v' :=
    RelativeLevi.radical_range_eq_of_dynamic_parabolic dynamicRelativeLevi
      hG' χ hP _ v' hr' hv'
  exact RelativeLevi.subgroupMultiplication_isIso_of_range_eq
    t' ((GroupScheme.baseChange b).map r) t' v'
    (ht.baseChange b) hr'.isClosedSubgroup (ht.baseChange b) hv'.isClosedSubgroup rfl heq

namespace RelativeLevi

/-- A relative Levi has an actual smooth fppf projection, split by its
inclusion, with the original relative unipotent radical as full kernel. -/
theorem exists_fppfRetraction {L P : GroupScheme S} {l : L ⟶ P}
    (hl : IsRelativeLeviSubgroup l) :
    ∃ (U : GroupScheme S) (r : U ⟶ P) (q : P ⟶ L),
      IsRelativeUnipotentRadical r ∧ IsIso (subgroupMultiplication l r) ∧
        l ≫ q = 𝟙 L ∧ Smooth q.hom.hom.left ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  let : Smooth U.X.hom := hr.smooth
  let q := leviRetraction l r hr.isNormal
  have hs : Smooth q.hom.hom.left := smooth_leviRetraction l r hr.isNormal
  let : Smooth q.hom.hom.left := hs
  have hsection : l ≫ q = 𝟙 L := levi_comp_leviRetraction l r hr.isNormal
  have hsection' : l.hom.hom.left ≫ q.hom.hom.left = 𝟙 L.X.left :=
    congrArg (fun f => f.hom.hom.left) hsection
  let : Surjective (l.hom.hom.left ≫ q.hom.hom.left) := by
    rw [hsection']
    infer_instance
  have hsurj : Surjective q.hom.hom.left := Surjective.of_comp l.hom.hom.left _
  refine ⟨U, r, q, hr, hmul, hsection, hs, inferInstance, hsurj, inferInstance, ?_⟩
  apply SubgroupFunctor.ext
  intro V
  apply SetLike.ext
  intro x
  exact (mem_range_kernelι_iff q x).trans
    (comp_leviRetraction_eq_one_iff l r hr.isNormal x)

/-- Actual retraction data for a relative Levi, including its original
unipotent radical and the full fppf kernel identification. -/
structure FppfRetractionData {L P : GroupScheme S} (l : L ⟶ P) where
  radical : GroupScheme S
  radicalInclusion : radical ⟶ P
  projection : P ⟶ L
  isRelativeUnipotentRadical : IsRelativeUnipotentRadical radicalInclusion
  multiplication_isIso : IsIso (subgroupMultiplication l radicalInclusion)
  section_eq : l ≫ projection = 𝟙 L
  smooth : Smooth projection.hom.hom.left
  isFppfQuotient : RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range radicalInclusion) projection

/-- Choose the actual smooth fppf retraction constructed for a relative Levi. -/
noncomputable def fppfRetractionData {L P : GroupScheme S} {l : L ⟶ P}
    (hl : IsRelativeLeviSubgroup l) : FppfRetractionData l :=
  Classical.choice (show Nonempty (FppfRetractionData l) from by
    obtain ⟨U, r, q, hr, hmul, hsection, hsmooth, hq⟩ := exists_fppfRetraction hl
    exact ⟨⟨U, r, q, hr, hmul, hsection, hsmooth, hq⟩⟩)

end RelativeLevi

/-- Construct the sectioned smooth fppf projection of a relative Borel onto
the supplied ambient maximal torus, retaining its actual unipotent radical. -/
theorem IsRelativeBorelSubgroup.exists_maximalTorus_fppfRetraction
    (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ B)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i)) :
    ∃ (U : GroupScheme S) (r : U ⟶ B) (q : B ⟶ T.toGrp),
      IsRelativeUnipotentRadical r ∧ IsIso (subgroupMultiplication t r) ∧
        t ≫ q = 𝟙 T.toGrp ∧ Smooth q.hom.hom.left ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q :=
  RelativeLevi.exists_fppfRetraction
    (hi.isRelativeLeviSubgroup_of_maximalTorus hG T t hT htG hmax)

/-- Actual sectioned smooth fppf projection data onto a supplied ambient
maximal torus of a relative Borel. -/
noncomputable def IsRelativeBorelSubgroup.maximalTorusFppfRetractionData
    (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ B)
    (hT : RelativeTorus.IsTorus T.toGrp)
    (htG : IsClosedSubgroup (t ≫ i))
    (hmax : IsFibrewiseMaximalTorus (t ≫ i)) :
    RelativeLevi.FppfRetractionData t :=
  RelativeLevi.fppfRetractionData
    (hi.isRelativeLeviSubgroup_of_maximalTorus hG T t hT htG hmax)

end Langlands.GroupScheme
