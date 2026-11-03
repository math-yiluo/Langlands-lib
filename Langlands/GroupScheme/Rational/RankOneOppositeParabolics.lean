import Langlands.GroupScheme.Dynamic.TrivialUnipotentCentralizer
import Langlands.GroupScheme.Dynamic.UnipotentTorusAction
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.RankOnePseudoParabolicMinimality
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyStatement
import Langlands.GroupScheme.Rational.NormalizerConjugacyCorrection
import Langlands.GroupScheme.Rational.RootMovementOppositeParabolics
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # Proper opposing rank-one parabolics and a rational normalizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Properness

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The split-torus unipotence input supplies the full-parabolic centrality
criterion for every cocharacter of a smooth affine group with trivial
ground-field unipotent radical. -/
theorem Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_torusActionUnipotence
    (hUnip : RelativeRoot.TorusActionUnipotenceStatement.{u})
    (hR : HasTrivialUnipotentRadical G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Dynamic.parabolic χ = ⊤ ↔ Dynamic.centralizer χ = ⊤ := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent χ hR
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)
    (Dynamic.isUnipotent_of_torusActionUnipotence χ hUnip
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
      (Dynamic.Affine.isClosedSubgroup_unipotentHom χ))

/-- A nonzero actual root pairing makes the dynamic parabolic proper, under
the explicit split-torus unipotence input. No root-negation premise is used. -/
theorem Dynamic.parabolic_ne_top_of_root_pairing_ne_zero
    (hUnip : RelativeRoot.TorusActionUnipotenceStatement.{u})
    (hR : HasTrivialUnipotentRadical G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (hne : latticePairing T a ν ≠ 0) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤ := by
  intro hP
  have hZ := (Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_torusActionUnipotence
    hUnip hR (CommGroupScheme.groupHom ν ≫ i)).mp hP
  have hc := (isCentral_iff_dynamicCentralizer_eq_top _).mpr hZ
  have hcomp := root_restrict_eq_zero_of_isCentral i ν isSplitTorus_gm hc ha
  apply hne
  rw [latticePairing_apply, hcomp, map_zero]

/-- The two cocharacters `ν` and `-ν` both give proper parabolics whenever an
actual root has nonzero pairing with `ν`. -/
theorem Dynamic.opposite_parabolics_ne_top_of_root_pairing_ne_zero
    (hUnip : RelativeRoot.TorusActionUnipotenceStatement.{u})
    (hR : HasTrivialUnipotentRadical G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (hne : latticePairing T a ν ≠ 0) :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≠ ⊤ ∧
      Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i) ≠ ⊤ :=
  ⟨Dynamic.parabolic_ne_top_of_root_pairing_ne_zero hUnip hR i ν ha hne,
    Dynamic.parabolic_ne_top_of_root_pairing_ne_zero hUnip hR i (-ν) ha
      (by simpa only [map_neg] using neg_ne_zero.mpr hne)⟩

end Properness

section RepresentedConjugacy

variable {B : Scheme.{u}} {G P Q : GroupScheme B}
    {j : P ⟶ G} {l : Q ⟶ G}
    {F H : SubgroupFunctor G}

/-- Conjugacy of actual representatives gives containment after pullback by
the same rational inner automorphism, on every scheme test. -/
theorem SubgroupConjugate.le_comap_of_isRepresentedBy
    (hj : F.IsRepresentedBy j) (hl : H.IsRepresentedBy l)
    (g : Over.mk (𝟙 B) ⟶ G.X) (e : P ≅ Q)
    (he : j ≫ (G.innerIso g).hom = e.hom ≫ l) :
    F ≤ H.comap (G.innerIso g).hom := by
  intro U x hx
  rw [← hj.2, SubgroupFunctor.mem_range] at hx
  obtain ⟨p, rfl⟩ := hx
  rw [SubgroupFunctor.mem_comap, ← hl.2, SubgroupFunctor.mem_range]
  refine ⟨p ≫ e.hom.hom.hom, ?_⟩
  have hh := congrArg (fun f : P ⟶ G => f.hom.hom) he
  change (p ≫ e.hom.hom.hom) ≫ l.hom.hom =
    (p ≫ j.hom.hom) ≫ (G.innerIso g).hom.hom.hom
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    (congrArg (p ≫ ·) hh).symm

end RepresentedConjugacy

namespace RelativeRoot

section RankOne

variable {k : Type u} [Field k]
    {G P Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth P.X.hom] [ConnectedSpace P.X.left]
    [Smooth Q.X.hom] [ConnectedSpace Q.X.left]
    (hUnip : TorusActionUnipotenceStatement.{u})
    (hTconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hMinConj : MinimalPseudoParabolicConjugacyStatement.{u})
    (hR : HasTrivialUnipotentRadical G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ∈ relativeRoots i)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)
    (j : P ⟶ G) (l : Q ⟶ G)
    (hjc : IsClosedSubgroup j) (hlc : IsClosedSubgroup l)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j)
    (hl : (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ i)).IsRepresentedBy l)

include hUnip hTconj hR hi ha hcyclic hpos hjc hlc hj hl

/-- Both opposing rank-one parabolics are minimal among all ground-field
pseudo-parabolics. Their properness is derived from the same actual root, so
root negation is unnecessary. Smoothness and connectedness of the supplied
representatives and the two structural inputs remain explicit. -/
theorem isMinimalPseudoParabolic_opposing_rankOne :
    IsMinimalPseudoParabolicSubgroup j ∧ IsMinimalPseudoParabolicSubgroup l := by
  have hp := Dynamic.opposite_parabolics_ne_top_of_root_pairing_ne_zero
    hUnip hR i ν ha (ne_of_gt hpos)
  have hcyclic' : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • (-a) := by
    intro α hα
    obtain ⟨n, hn⟩ := hcyclic α hα
    exact ⟨-n, by simpa only [neg_smul, smul_neg, neg_neg] using hn⟩
  exact ⟨isMinimalPseudoParabolic_of_rankOne_of_trivialUnipotentRadical
      hTconj T i hi a hcyclic ν hpos hp.1 P j hjc hj hR,
    isMinimalPseudoParabolic_of_rankOne_of_trivialUnipotentRadical
      hTconj T i hi (-a) hcyclic' (-ν) (by simpa using hpos) hp.2 Q l hlc hl hR⟩

include hMinConj

/-- Construct an actual rational normalizer and an inclusion-compatible
isomorphism carrying the positive rank-one parabolic to the negative one.
Maximal split-torus conjugacy and minimal pseudo-parabolic conjugacy remain
explicit structural inputs. -/
def rankOneOppositeParabolicNormalizer :
    (n : normalizerPoints i) ×
      {e : P ≅ Q // j ≫ (G.innerIso n.val).hom = e.hom ≫ l} := by
  have : IsAffineHom Q.X.hom := hlc.isAffineHom
  have hmin := isMinimalPseudoParabolic_opposing_rankOne
    hUnip hTconj hR T i hi a ha hcyclic ν hpos j l hjc hlc hj hl
  have hconj := hMinConj k G inferInstance inferInstance inferInstance
    P Q j l hmin.1 hmin.2
  apply hconj.normalizerCorrection hTconj hi hjc hlc
  · rw [hj.2]
    exact ((range_le_torusCentralizer i).trans
      (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν))).trans
      (Dynamic.centralizer_le_parabolic _)
  · rw [hl.2]
    exact ((range_le_torusCentralizer i).trans
      (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom (-ν)))).trans
      (Dynamic.centralizer_le_parabolic _)

/-- The constructed normalizer moves the actual cyclic root. This uses a
nonzero Lie-weight vector rather than a nonidentity rational root point. -/
theorem rankOneOppositeParabolicNormalizer_moves_root :
    let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    weylAction i (rankOneOppositeParabolicNormalizer
      hUnip hTconj hMinConj hR T i hi a ha hcyclic ν hpos
        j l hjc hlc hj hl).1 a ≠ a := by
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let d := rankOneOppositeParabolicNormalizer
    hUnip hTconj hMinConj hR T i hi a ha hcyclic ν hpos j l hjc hlc hj hl
  apply weylAction_ne_of_parabolic_le_opposite_comap i ν ha.2 hpos d.1
  rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
  exact SubgroupConjugate.le_comap_of_isRepresentedBy hj hl d.1.val d.2.val d.2.property

end RankOne
end RelativeRoot
end Langlands.GroupScheme
