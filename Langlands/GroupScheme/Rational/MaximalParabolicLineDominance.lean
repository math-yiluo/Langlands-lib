import Langlands.GroupScheme.Rational.RankOneStandardParabolicLineCharacter
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # The line character of a maximal standard parabolic is dominant -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily

section WeylFix

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G H : GroupScheme S}

/-- A normalizing point lying in a represented subgroup that contains the torus fixes the
torus restriction of every character of that subgroup. -/
theorem weylAction_torusCharacterRestrict_of_factor
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] {F : SubgroupFunctor G} {z : H ⟶ G}
    (hz : F.IsRepresentedBy z) (iH : T.toGrp ⟶ H) (hiH : iH ≫ z = i)
    (n : normalizerPoints i) (nH : Over.mk (𝟙 S) ⟶ H.X)
    (hn : nH ≫ z.hom.hom = (n : Over.mk (𝟙 S) ⟶ G.X)) (eta : rationalCharacters H) :
    weylAction i n (torusCharacterRestrict iH eta) = torusCharacterRestrict iH eta := by
  have : Mono iH.hom.hom.left := by
    have h : iH.hom.hom.left ≫ z.hom.hom.left = i.hom.hom.left := by
      rw [← hiH]
      rfl
    have : Mono (iH.hom.hom.left ≫ z.hom.hom.left) := by
      rw [h]
      infer_instance
    exact mono_of_mono _ z.hom.hom.left
  have hσ := isNormalizingPoint_normalizingAut i n
  have hH : IsNormalizingPoint iH nH (normalizingAut i n) := by
    apply hz.hom_ext
    rw [Category.assoc, Category.assoc, innerIso_hom_comp, hn, ← Category.assoc, hiH]
    exact hσ
  have h2 := weylAction_eq iH (n := ⟨nH, _, hH⟩) hH (torusCharacterRestrict iH eta)
  rw [weylAction_torusCharacterRestrict] at h2
  rw [weylAction_apply]
  exact h2.symm

end WeylFix

namespace MatrixRepresentation

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {n : Type} [Fintype n] [DecidableEq n]

theorem coordinateLineCharacter_congr {ρ₁ ρ₂ : MatrixRepresentation G n} (h : ρ₁ = ρ₂)
    (j : n) (h₁ : ρ₁.PreservesCoordinateLine j) (h₂ : ρ₂.PreservesCoordinateLine j) :
    ρ₁.coordinateLineCharacter j h₁ = ρ₂.coordinateLineCharacter j h₂ := by
  subst h
  rfl

/-- The torus line character only depends on the composite torus map. -/
theorem torusCoordinateLineCharacter_restrict_comp (ρ : MatrixRepresentation G n)
    (i : T.toGrp ⟶ G) (z : H ⟶ G) (iH : T.toGrp ⟶ H) (hiH : iH ≫ z = i) (j : n)
    (hT : (ρ.restrict i).PreservesCoordinateLine j)
    (hT' : ((ρ.restrict z).restrict iH).PreservesCoordinateLine j) :
    (ρ.restrict z).torusCoordinateLineCharacter iH j hT' =
      ρ.torusCoordinateLineCharacter i j hT := by
  have he : (ρ.restrict z).restrict iH = ρ.restrict i := by
    rw [restrict_comp, hiH]
  change Additive.ofMul (((ρ.restrict z).restrict iH).coordinateLineCharacter j hT') =
    Additive.ofMul ((ρ.restrict i).coordinateLineCharacter j hT)
  rw [coordinateLineCharacter_congr he]

/-- The torus line character is the restriction of the line character of any intermediate
subgroup preserving the same line. -/
theorem torusCoordinateLineCharacter_eq_restrict (ρ : MatrixRepresentation G n)
    (i : T.toGrp ⟶ G) (z : H ⟶ G) (iH : T.toGrp ⟶ H) (hiH : iH ≫ z = i) (j : n)
    (hT : (ρ.restrict i).PreservesCoordinateLine j)
    (hH : (ρ.restrict z).PreservesCoordinateLine j) :
    ρ.torusCoordinateLineCharacter i j hT =
      torusCharacterRestrict iH ((ρ.restrict z).coordinateLineRationalCharacter j hH) := by
  have hT' : ((ρ.restrict z).restrict iH).PreservesCoordinateLine j := by
    rw [restrict_comp, hiH]
    exact hT
  have hc := (ρ.restrict z).coordinateLineCharacter_restrict iH j hH hT'
  rw [← torusCoordinateLineCharacter_restrict_comp ρ i z iH hiH j hT hT']
  change Additive.ofMul (((ρ.restrict z).restrict iH).coordinateLineCharacter j hT') =
    Additive.ofMul (iH ≫ (ρ.restrict z).coordinateLineCharacter j hH)
  rw [hc]

/-- An exact line stabilizer containing the range of a homomorphism gives line preservation
after restriction along it. -/
theorem HasExactCoordinateLineStabilizer.preservesCoordinateLine_restrict
    {ρ : MatrixRepresentation G n} {F : SubgroupFunctor G} {j : n}
    (hstab : ρ.HasExactCoordinateLineStabilizer F j) (z : H ⟶ G)
    (hz : SubgroupFunctor.range z ≤ F) :
    (ρ.restrict z).PreservesCoordinateLine j := by
  intro Q y
  simpa only [pointMatrix_restrict] using (hstab Q (y ≫ z.hom.hom)).mp (hz Q ⟨y, rfl⟩)

end MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The standard relative Weyl subgroup of `K` fixes the torus restriction of every character
of the standard Levi of `K`. -/
theorem schemeWeylCharacterAction_standardLevi_restrict [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
    (K : Set (characterLattice T)) (eta : rationalCharacters (Standard.leviScheme i ν K))
    {w : relativeWeylGroup i} (hw : w ∈ standardRelativeWeylGroup i ν K) :
    schemeWeylCharacterAction i w
        (torusCharacterRestrict
          (standardLeviTorusFactor i ν K (Standard.isRepresentedBy_leviHom i ν K)) eta) =
      torusCharacterRestrict
        (standardLeviTorusFactor i ν K (Standard.isRepresentedBy_leviHom i ν K)) eta := by
  obtain ⟨n, hnL, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hw
  have hj := Standard.isRepresentedBy_leviHom i ν K
  have hr : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      (SubgroupFunctor.range (Standard.leviHom i ν K)).carrier (Over.mk (𝟙 _)) := by
    rw [hj.2]
    exact hnL
  obtain ⟨nL, hnL'⟩ := hr
  rw [schemeWeylCharacterAction_mk]
  exact weylAction_torusCharacterRestrict_of_factor i hj _
    (standardLeviTorusFactor_comp i ν K hj) n nL hnL' eta

/-- **Dominance of a maximal-parabolic line character.** For a simple relative root `α`, a
Chevalley representation with exact line stabilizer `P_(Δ \ {α})` gives a line preserved by the
minimal standard parabolic and by the torus. Its torus character `ψ` is fixed by the standard
relative Weyl subgroup of `Δ \ {α}`, and every element of the standard relative Weyl subgroup
of `{α}` acting by a reflection `χ ↦ χ - f χ • α` with `f α = 2` has `f ψ > 0`. -/
theorem exists_maximalParabolic_dominant_line [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : α ∈ simpleRelativeRoots i ν) :
    haveI := hi.isSplitSubtorus.mono
    ∃ (d : ℕ) (j : Fin (d + 1)) (ρ : MatrixRepresentation G (Fin (d + 1)))
      (_ : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j)
      (hT : (ρ.restrict i).PreservesCoordinateLine j),
      (∀ w ∈ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {α}),
        schemeWeylCharacterAction i w (ρ.torusCoordinateLineCharacter i j hT) =
          ρ.torusCoordinateLineCharacter i j hT) ∧
      ∀ (f : characterLattice T →+ ℤ), f α = 2 →
        ∀ w ∈ standardRelativeWeylGroup i ν {α},
          (∀ χ, schemeWeylCharacterAction i w χ = χ - f χ • α) →
            0 < f (ρ.torusCoordinateLineCharacter i j hT) := by
  have := hi.isSplitSubtorus.mono
  set J := simpleRelativeRoots i ν \ {α} with hJdef
  have hJ : J ⊆ simpleRelativeRoots i ν := Set.sdiff_subset
  obtain ⟨d, j, ρ, hρ⟩ := Chevalley.exists_line_stabilizer k G
    (Standard.parabolicScheme i ν J) (Standard.parabolicHom i ν J)
    (Standard.isClosedSubgroup_parabolicHom i ν J)
  have hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν J) j := by
    simpa only [MatrixRepresentation.HasExactCoordinateLineStabilizer,
      (Standard.isRepresentedBy_parabolicHom i ν J).2] using hρ
  have hLP : standardLevi i ν J ≤ standardParabolic i ν J :=
    standardLevi_le_standardParabolic i ν J
  have hP : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j := by
    apply hstab.preservesCoordinateLine_restrict
    rw [(Standard.isRepresentedBy_parabolicHom i ν ∅).2]
    exact ((standardParabolicOrder k G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.mp
      (Set.empty_subset _)
  have hT : (ρ.restrict i).PreservesCoordinateLine j :=
    hstab.preservesCoordinateLine_restrict i ((range_le_standardLevi i ν J).trans hLP)
  have hLJ : (ρ.restrict (Standard.leviHom i ν J)).PreservesCoordinateLine j := by
    apply hstab.preservesCoordinateLine_restrict
    rw [(Standard.isRepresentedBy_leviHom i ν J).2]
    exact hLP
  refine ⟨d, j, ρ, hP, hT, ?_, ?_⟩
  · intro w hw
    rw [ρ.torusCoordinateLineCharacter_eq_restrict i (Standard.leviHom i ν J)
      (standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J))
      (standardLeviTorusFactor_comp i ν J _) j hT hLJ]
    exact schemeWeylCharacterAction_standardLevi_restrict i ν J _ hw
  · intro f hfα w hw hrefl
    -- the rank-one standard Levi of `α`
    let L := Standard.leviScheme i ν {α}
    let zL := Standard.leviHom i ν {α}
    have hjL := Standard.isRepresentedBy_leviHom i ν {α}
    let iL := standardLeviTorusFactor i ν {α} hjL
    have hJα : ({α} : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
      Set.singleton_subset_iff.mpr hα
    have hL := (standardLeviSplitComponentStatement k G hG T i hi ν hν {α} hJα).1
    have : IsAffineHom L.X.hom := hL.isAffineHom
    have hiL : IsMaximalSplitTorus iL :=
      hi.isMaximalSplitTorus_standardLeviTorusFactor i ν {α} hjL
        (Standard.isClosedSubgroup_leviHom i ν {α})
    have : Mono iL.hom.hom.left := hiL.isSplitSubtorus.mono
    obtain ⟨hsimple, hνL, _⟩ := standardLeviStandardFamilies dynamicLie standardCocharacter
      k G hG T i hi ν hν {α} hJα L hL zL hjL (Standard.isClosedSubgroup_leviHom i ν {α})
    let _ : Fintype (relativeWeylGroup iL) :=
      relativeWeylGroupFintype iL (relativeRootSystem k L hL T iL hiL)
    have hinter : ({α} : Set (characterLattice T)) ∩ J = ∅ := by
      ext β
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl
      simp [hJdef]
    have hstabL := standardLevi_inter_coordinateLine_stabilizer i ν hG hi hν
      {α} J hJα hJ ρ j hstab
    rw [hinter] at hstabL
    obtain ⟨hTline, d', b, hd', hb, eta, hrel⟩ :=
      MatrixRepresentation.positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer
        iL hL hiL ν hνL α hsimple (ρ.restrict zL) j hstabL
    rw [ρ.torusCoordinateLineCharacter_restrict_comp i zL iL
      (standardLeviTorusFactor_comp i ν {α} hjL) j hT hTline] at hrel
    set ψ := ρ.torusCoordinateLineCharacter i j hT
    set X := torusCharacterRestrict iL eta
    have hX : schemeWeylCharacterAction i w X = X :=
      schemeWeylCharacterAction_standardLevi_restrict i ν {α} eta hw
    rw [hrefl] at hX
    have hfX : f X = 0 := by
      have h := congrArg f hX
      rw [map_sub, map_zsmul, hfα, smul_eq_mul] at h
      omega
    have h := congrArg f hrel
    rw [map_nsmul, map_add, map_nsmul, hfX, hfα, zero_add, nsmul_eq_mul, nsmul_eq_mul] at h
    have hd'z : (0 : ℤ) < d' := by exact_mod_cast hd'
    have hbz : (0 : ℤ) < b := by exact_mod_cast hb
    by_contra hneg
    push Not at hneg
    nlinarith

end Langlands.GroupScheme
