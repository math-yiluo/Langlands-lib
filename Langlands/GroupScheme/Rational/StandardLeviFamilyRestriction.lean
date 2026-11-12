import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter

/-! # Ambient standard families restricted to a standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

/-- Standard subgroup functors of an ambient reductive group restrict to
standard subgroup functors of a represented standard Levi, indexed by the
intersection of the two ambient simple-root subsets. -/
def StandardLeviFamilyRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (J K : Set (characterLattice T)),
        J ⊆ simpleRelativeRoots i ν → K ⊆ simpleRelativeRoots i ν →
        ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (hL : IsConnectedReductive L)
          (j : L ⟶ G) (hj : (standardLevi i ν J).IsRepresentedBy j),
          IsClosedSubgroup j →
          haveI := hL.isAffineHom
          let iL := standardLeviTorusFactor i ν J hj
          standardParabolic iL ν (J ∩ K) = (standardParabolic i ν K).comap j ∧
            standardLevi iL ν (J ∩ K) = (standardLevi i ν K).comap j ∧
            standardUnipotent iL ν (J ∩ K) = (standardUnipotent i ν K).comap j

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardLeviFamilyRestrictionInstance1 (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- Restricting a standard cocharacter to a standard Levi replaces its
vanishing subset by its intersection with the Levi's simple roots. -/
theorem IsStandardCocharacter.standardLevi_inter
    {J K : Set (characterLattice T)} {j : L ⟶ G}
    (hj : (standardLevi i ν J).IsRepresentedBy j)
    [IsAffineHom L.X.hom]
    (hsimple : simpleRelativeRoots (standardLeviTorusFactor i ν J hj) ν = J)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν K ζ) :
    IsStandardCocharacter (standardLeviTorusFactor i ν J hj) ν (J ∩ K) ζ := by
  refine ⟨?_, fun α hα => hζ.2.1 α hα.2, ?_⟩
  · rw [hsimple]
    exact Set.inter_subset_left
  · intro α hα hαJK
    have hαJ : α ∈ J := hsimple ▸ hα
    apply hζ.2.2 α (hJ hαJ)
    exact fun hαK => hαJK ⟨hαJ, hαK⟩

/-- On every test scheme, an ambient standard family restricted to a
represented standard Levi is indexed by the intersection of the two root
subsets. No nesting of those subsets is required. -/
theorem standardLeviStandardFamilies_inter
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν)
    (hL : IsConnectedReductive L) (j : L ⟶ G)
    (hj : (standardLevi i ν J).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    haveI := hL.isAffineHom
    let iL := standardLeviTorusFactor i ν J hj
    standardParabolic iL ν (J ∩ K) = (standardParabolic i ν K).comap j ∧
      standardLevi iL ν (J ∩ K) = (standardLevi i ν K).comap j ∧
      standardUnipotent iL ν (J ∩ K) = (standardUnipotent i ν K).comap j := by
  have := hL.isAffineHom
  have := hi.isSplitSubtorus.mono
  let iL := standardLeviTorusFactor i ν J hj
  have hcomp : iL ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  have hiL : IsMaximalSplitTorus iL :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν J hj hjc
  obtain ⟨hsimple, hνL, _⟩ :=
    standardLeviStandardFamilies dynamicLie standardCocharacter
      k G hG T i hi ν hν J hJ L hL j hj hjc
  obtain ⟨⟨ζ, hζ⟩, hGcomparison⟩ :=
    standardCocharacter k G hG T i hi ν hν K hK
  have hζL : IsStandardCocharacter iL ν (J ∩ K) ζ :=
    hζ.standardLevi_inter i ν hj hsimple hJ
  have hLcomparison :=
    (standardCocharacter k L hL T iL hiL ν hνL (J ∩ K) hζL.1).2 ζ hζL
  rcases hGcomparison ζ hζ with ⟨hP, hM, hU⟩
  rcases hLcomparison with ⟨hPL, hML, hUL⟩
  change standardParabolic iL ν (J ∩ K) = (standardParabolic i ν K).comap j ∧
    standardLevi iL ν (J ∩ K) = (standardLevi i ν K).comap j ∧
    standardUnipotent iL ν (J ∩ K) = (standardUnipotent i ν K).comap j
  rw [hPL, hML, hUL, hP, hM, hU]
  have hχ : (CommGroupScheme.groupHom ζ ≫ iL) ≫ j =
      CommGroupScheme.groupHom ζ ≫ i := by rw [Category.assoc, hcomp]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hχ] using
      Dynamic.parabolic_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom ζ ≫ iL) j hjc
  · simpa only [hχ] using
      Dynamic.centralizer_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom ζ ≫ iL) j hjc
  · simpa only [hχ] using
      Dynamic.unipotent_eq_comap_of_isClosedSubgroup (CommGroupScheme.groupHom ζ ≫ iL) j hjc

/-- The intersection restriction statement, with all structural inputs supplied
by published proofs. -/
theorem standardLeviFamilyRestriction : StandardLeviFamilyRestrictionStatement.{u} := by
  intro k _ G hG T i hi
  have := hG.isAffineHom
  intro ν hν J K hJ hK L hL j hj hjc
  exact standardLeviStandardFamilies_inter i ν hG hi hν J K hJ hK hL j hj hjc

/-- The preceding comparison for the actual canonical Levi. Its connected
reductivity is supplied by the published standard-Levi theorem. -/
theorem standardLeviStandardFamilies_inter_canonical
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν) :
    let iL := standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
    standardParabolic iL ν (J ∩ K) =
        (standardParabolic i ν K).comap (Standard.leviHom i ν J) ∧
      standardLevi iL ν (J ∩ K) =
        (standardLevi i ν K).comap (Standard.leviHom i ν J) ∧
      standardUnipotent iL ν (J ∩ K) =
        (standardUnipotent i ν K).comap (Standard.leviHom i ν J) := by
  have hL := (standardLeviSplitComponentStatement k G hG T i hi ν hν J hJ).1
  exact standardLeviStandardFamilies_inter i ν hG hi hν J K hJ hK hL
    (Standard.leviHom i ν J) (Standard.isRepresentedBy_leviHom i ν J)
    (Standard.isClosedSubgroup_leviHom i ν J)

/-- An ambient exact all-test line stabilizer restricts to the exact standard
parabolic of the canonical Levi indexed by the intersection. -/
theorem standardLevi_inter_coordinateLine_stabilizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J K : Set (characterLattice T))
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (b : n)
    (hstab : ∀ (Q : Over (Spec (CommRingCat.of k))) (x : Q ⟶ G.X),
      x ∈ (standardParabolic i ν K).carrier Q ↔
        ∃ a : Γ(Q.left, ⊤)ˣ,
          (ρ.pointMatrix Q x : Matrix n n Γ(Q.left, ⊤)) *ᵥ Pi.single b 1 =
            (a : Γ(Q.left, ⊤)) • (Pi.single b 1 : n → Γ(Q.left, ⊤))) :
    let iL := standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
    ∀ (Q : Over (Spec (CommRingCat.of k))) (x : Q ⟶ (Standard.leviScheme i ν J).X),
      x ∈ (standardParabolic iL ν (J ∩ K)).carrier Q ↔
        ∃ a : Γ(Q.left, ⊤)ˣ,
          ((ρ.restrict (Standard.leviHom i ν J)).pointMatrix Q x :
            Matrix n n Γ(Q.left, ⊤)) *ᵥ Pi.single b 1 =
              (a : Γ(Q.left, ⊤)) • (Pi.single b 1 : n → Γ(Q.left, ⊤)) := by
  intro iL Q x
  rw [(standardLeviStandardFamilies_inter_canonical i ν hG hi hν J K hJ hK).1,
    SubgroupFunctor.mem_comap, MatrixRepresentation.pointMatrix_restrict]
  exact hstab Q (x ≫ (Standard.leviHom i ν J).hom.hom)

end Langlands.GroupScheme
