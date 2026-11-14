import Langlands.GroupScheme.RelativeLevi.ConjugatorUniquenessBaseChange
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Reductivity of a relative Levi subgroup -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
    {P L U : GroupScheme (Spec (CommRingCat.of k))}
    (l : L ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]
    [IsAffineHom P.X.hom]

/-- An actual complement to a represented unipotent radical has trivial
unipotent radical. -/
theorem hasTrivialUnipotentRadical_of_radical_complement
    (hl : IsClosedSubgroup l) (hr : IsUnipotentRadical r) :
    HasTrivialUnipotentRadical L := by
  let : IsClosedImmersion l.hom.hom.left := hl
  let : IsAffineHom L.X.hom := by
    rw [← Over.w l.hom.hom]
    infer_instance
  let : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  let : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  let : Smooth U.X.hom := hr.smooth
  let q := leviRetraction l r hr.isNormal
  let : Smooth q.hom.hom.left := smooth_leviRetraction l r hr.isNormal
  let : QuasiCompact q.hom.hom.left := inferInstance
  have hsection : l.hom.hom.left ≫ q.hom.hom.left = 𝟙 L.X.left := by
    change (l ≫ q).hom.hom.left = (𝟙 L : L ⟶ L).hom.hom.left
    rw [levi_comp_leviRetraction]
  let : Surjective (l.hom.hom.left ≫ q.hom.hom.left) := by
    rw [hsection]
    infer_instance
  let : Surjective q.hom.hom.left := Surjective.of_comp l.hom.hom.left _
  apply hr.hasTrivialUnipotentRadical_of_smooth_quotient q
  apply SubgroupFunctor.ext
  intro T
  apply SetLike.ext
  intro x
  exact (mem_range_kernelι_iff q x).trans
    (comp_leviRetraction_eq_one_iff l r hr.isNormal x)

/-- A smooth closed complement to a represented unipotent radical in a
connected affine group is pseudo-reductive. -/
theorem isPseudoReductive_of_radical_complement
    [ConnectedSpace P.X.left] (hl : IsClosedSubgroup l)
    (hs : Smooth L.X.hom) (hr : IsUnipotentRadical r) :
    IsPseudoReductive L := by
  let : IsClosedImmersion l.hom.hom.left := hl
  have haff : IsAffineHom L.X.hom := by
    rw [← Over.w l.hom.hom]
    infer_instance
  let q := leviRetraction l r hr.isNormal
  have hsection : l.hom.hom.left ≫ q.hom.hom.left = 𝟙 L.X.left := by
    change (l ≫ q).hom.hom.left = (𝟙 L : L ⟶ L).hom.hom.left
    rw [levi_comp_leviRetraction]
  let : Surjective (l.hom.hom.left ≫ q.hom.hom.left) := by
    rw [hsection]
    infer_instance
  let : Surjective q.hom.hom.left := Surjective.of_comp l.hom.hom.left _
  exact ⟨hs, haff, q.hom.hom.left.surjective.connectedSpace q.hom.hom.left.continuous,
    hasTrivialUnipotentRadical_of_radical_complement l r hl hr⟩

end Field

section Base

variable {S : Scheme.{u}} {G P L : GroupScheme S} {i : P ⟶ G} {l : L ⟶ P}

/-- The geometric fibres of a relative parabolic in a reductive group are
connected. -/
theorem IsRelativeParabolicSubgroup.connectedSpace_geometricFiber
    (hp : IsRelativeParabolicSubgroup i) (hG : IsReductive G) (s : S) :
    ConnectedSpace (geometricFiber P s).X.left := by
  let b := S.fromSpecResidueField s
  let c := toAlgebraicClosure (S.residueField s)
  let Pk := (baseChange b).obj P
  let Gk := (baseChange b).obj G
  have hGk := hG.isConnectedReductive_residueFiber s
  let : Smooth Gk.X.hom := hGk.smooth
  let : IsAffineHom Gk.X.hom := hGk.isAffineHom
  let : ConnectedSpace Gk.X.left := hGk.connectedSpace
  let : Smooth P.X.hom := hp.smooth
  let : IsAffineHom P.X.hom := hp.isAffineHom
  let : Smooth Pk.X.hom := by
    change Smooth (pullback.snd P.X.hom b)
    infer_instance
  let : IsAffineHom Pk.X.hom := by
    change IsAffineHom (pullback.snd P.X.hom b)
    infer_instance
  let : ConnectedSpace Pk.X.left := (hp.residueFiber s).connectedSpace
  have hc := Pk.connectedSpace_baseChange_of_smooth_affine c
  exact (Scheme.homeoOfIso ((Over.forget _).mapIso
    ((Grp.forget _).mapIso (baseChangeCompIso b c P)))).connectedSpace_iff.mpr hc

/-- A relative Levi subgroup of a relative parabolic in a reductive group is
itself reductive, without additional hypotheses on the base scheme. -/
theorem IsRelativeLeviSubgroup.isReductive
    (hl : IsRelativeLeviSubgroup l) (hp : IsRelativeParabolicSubgroup i)
    (hG : IsReductive G) : IsReductive L := by
  let : IsAffineHom P.X.hom := hp.isAffineHom
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : Smooth L.X.hom := hl.smooth
  have haff : IsAffineHom L.X.hom := by
    rw [← Over.w l.hom.hom]
    infer_instance
  refine ⟨hl.smooth, haff, fun s => ?_⟩
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let b := geometricPoint S s
  let : IsIso (subgroupMultiplication l r) := hmul
  let := RelativeLevi.isIso_subgroupMultiplication_baseChange b l r
  let : IsAffineHom (geometricFiber P s).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom b)
    infer_instance
  let : ConnectedSpace (geometricFiber P s).X.left :=
    hp.connectedSpace_geometricFiber hG s
  apply isPseudoReductive_of_radical_complement
    ((baseChange b).map l) ((baseChange b).map r)
    (hl.isClosedSubgroup.baseChange b)
  · change Smooth (pullback.snd L.X.hom b)
    infer_instance
  · exact hr.geometricFiber s

/-- Retain the actual source group of a relative Levi embedding together with
its derived reductivity. -/
def RelativeLevi.reductiveSource (hl : IsRelativeLeviSubgroup l)
    (hp : IsRelativeParabolicSubgroup i) (hG : IsReductive G) :
    {H : GroupScheme S // IsReductive H} :=
  ⟨L, hl.isReductive hp hG⟩

end Base

end Langlands.GroupScheme
