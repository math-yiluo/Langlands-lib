import Langlands.GroupScheme.Reductive.AffineSplitIsogenyB2Relations
import Langlands.GroupScheme.Reductive.AffineSplitIsogenyRankOneMap
import Langlands.GroupScheme.Reductive.PoweredWeylActions

/-! # Square and fixed conjugation of the actual powered Weyl family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {H : GroupScheme (Spec (CommRingCat.of R))}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}

/-- A powered genuine target root map has the exact source-character formula. -/
theorem hasRootConjugationFormula_rootMap (a : J) (w : Ga R ⟶ H)
    (hw : IsRootParametrization i' (Q.root (f.indexEquiv.symm a)) w) :
    HasRootConjugationFormula (torusMap _ f ≫ i') (P.root a)
      (rootMap f hchar (f.indexEquiv.symm a) w) := by
  intro Z t x
  simpa only [Equiv.apply_symm_apply] using
    rootMap_equivariant f hchar (f.indexEquiv.symm a) i' w hw Z t x

/-- The square and fixed-conjugation laws needed at simple source roots. -/
def PoweredWeylActionRelations {b : P.Base} (W : ∀ α, SimpleWord P b α)
    (u' : J' → (Ga R ⟶ H)) : Prop :=
  let v := poweredRootFamily f hchar u'
  let w := weylFamily P W v
  (∀ c ∈ b.support, ∀ a, wordConj P v [c, c] (w a) =
    scaleHom (((P.pairingIn ℤ a c).negOnePow : ℤ) : R) ≫ w a) ∧
  (∀ c ∈ b.support, ∀ a, P.root c ≠ -P.root a →
    IsogenyNoCone.NoMixedRoot P c a →
    P.root (P.reflectionPerm c c) ≠ -P.root a →
    IsogenyNoCone.NoMixedRoot P (P.reflectionPerm c c) a →
      wordConj P v [c] (w a) = w a)

variable [DecidableEq I'] [IsAffineHom H.X.hom]
  {b : P.Base} {b' : Q.Base}
  (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
  (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
  (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')

include hd

/-- Word transport supplies source-character equivariance for every powered Weyl map. -/
theorem hasRootConjugationFormula_poweredWeylFamily (a : J) :
    HasRootConjugationFormula (torusMap _ f ≫ i') (P.root a)
      (weylFamily P W (poweredRootFamily f hchar u') a) := by
  rw [weylFamily_powered_eq f hchar hb W u']
  exact hasRootConjugationFormula_rootMap f hchar a _
    (hd.isRootParametrization (f.indexEquiv.symm a))

/-- The actual powered Weyl map satisfies the source Cartan square sign, from
genuine target rank-one laws and the standard coordinate pairings. -/
theorem wordConj_square_poweredWeylFamily
    (hPpair : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)
    (hQpair : ∀ m n, Q.toLinearMap m n = ∑ j, m j * n j)
    (c a : J)
    (hL : RankOneLaws i' (Q.coroot (f.indexEquiv.symm c))
      (u' (f.indexEquiv.symm c))
      (u' (Q.reflectionPerm (f.indexEquiv.symm c) (f.indexEquiv.symm c)))) :
    wordConj P (poweredRootFamily f hchar u') [c, c]
        (weylFamily P W (poweredRootFamily f hchar u') a) =
      scaleHom (((P.pairingIn ℤ a c).negOnePow : ℤ) : R) ≫
        weylFamily P W (poweredRootFamily f hchar u') a := by
  exact wordConj_square_of_rankOneLaws P (torusMap _ f ≫ i') hPpair
    (poweredRootFamily f hchar u') c a _
    (rankOneLaws_poweredRootFamily f hPpair hQpair hchar i' u' c hL)
    (hasRootConjugationFormula_poweredWeylFamily f hchar hb W u' hd a)

/-- Both source no-cone conditions imply that a simple powered Weyl product fixes
the powered Weyl map. The genuine target cone need not be empty. -/
theorem wordConj_fixed_poweredWeylFamily [IsLocalRing R] (hi' : IsClosedSubgroup i')
    {c a : J} (hc : c ∈ b.support)
    (hnp : P.root c ≠ -P.root a) (hcone : IsogenyNoCone.NoMixedRoot P c a)
    (hnm : P.root (P.reflectionPerm c c) ≠ -P.root a)
    (hconem : IsogenyNoCone.NoMixedRoot P (P.reflectionPerm c c) a) :
    wordConj P (poweredRootFamily f hchar u') [c]
        (weylFamily P W (poweredRootFamily f hchar u') a) =
      weylFamily P W (poweredRootFamily f hchar u') a := by
  have hm : IsRootParametrization i'
      (Q.root (f.indexEquiv.symm (P.reflectionPerm c c)))
      (u' (f.indexEquiv.symm (P.reflectionPerm c c))) := by
    simpa only [f.indexEquiv_symm_reflectionPerm] using
      (hd.param (f.indexEquiv.symm c) (hb c hc)).2
  exact PoweredWeylActions.wordConj_fixed_of_source_noCone f hd.reductive i' hi'
    hd.maximal hd.rootDatum hchar (poweredRootFamily f hchar u') c a
    (weylFamily P W (poweredRootFamily f hchar u') a)
    (u' (f.indexEquiv.symm c)) (u' (f.indexEquiv.symm (P.reflectionPerm c c)))
    (weylFamily Q (targetSimpleWords f hb W) u' (f.indexEquiv.symm a))
    (rootPower f hchar (f.indexEquiv.symm c))
    (rootPower f hchar (f.indexEquiv.symm (P.reflectionPerm c c)))
    (rootPower f hchar (f.indexEquiv.symm a))
    (hd.param (f.indexEquiv.symm c) (hb c hc)).1 hm
    (hd.isRootParametrization (f.indexEquiv.symm a)) rfl rfl
    (weylFamily_powered_eq f hchar hb W u' a) hnp hcone hnm hconem

/-- Genuine target laws and the original characteristic condition supply the
actual powered square and fixed-conjugation relations. -/
theorem poweredWeylActionRelations [IsLocalRing R] (hi' : IsClosedSubgroup i')
    (hPpair : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)
    (hQpair : ∀ m n, Q.toLinearMap m n = ∑ j, m j * n j)
    (hL : ∀ c ∈ b.support,
      RankOneLaws i' (Q.coroot (f.indexEquiv.symm c))
        (u' (f.indexEquiv.symm c))
        (u' (Q.reflectionPerm (f.indexEquiv.symm c) (f.indexEquiv.symm c)))) :
    PoweredWeylActionRelations f hchar W u' := by
  constructor
  · intro c hc a
    exact wordConj_square_poweredWeylFamily f hchar hb W u' hd hPpair hQpair c a
      (hL c hc)
  · intro c hc a hnp hcone hnm hconem
    exact wordConj_fixed_poweredWeylFamily f hchar hb W u' hd hi'
      hc hnp hcone hnm hconem

end Langlands.GroupScheme.AffineRootDatumIsogeny
