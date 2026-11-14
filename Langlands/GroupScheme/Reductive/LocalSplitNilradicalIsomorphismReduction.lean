import Langlands.GroupScheme.Reductive.ReductiveNilradicalIsomorphismReflectionStatement
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismTheoremStatement
import Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismProof
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Reduction of local split isomorphism to nilradical reflection -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The reduced local isomorphism theorem and nilradical reflection imply
the unchanged isomorphism theorem over every commutative local ring. -/
theorem localSplitIsomorphismTheorem_of_nilradicalReflection
    (hReflect : ReductiveNilradicalIsomorphismReflectionStatement.{u}) :
    LocalSplitIsomorphismTheoremStatement.{u} := by
  intro R _ _ G H _ _ hG hH I I' _ _ i i' hi hi' hmax hmax' J J' P Q hP hQ hf
  let A := R ⧸ nilradical R
  have hn : nilradical R ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (nilradical_le_prime (IsLocalRing.maximalIdeal R))
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hn
  letI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk (nilradical R))
    Ideal.Quotient.mk_surjective
  letI : IsReduced A := (Ideal.isRadical_iff_quotient_reduced (nilradical R)).mp
    (Ideal.radical_isRadical (0 : Ideal R))
  letI : Smooth G.X.hom := hG.smooth
  letI : Smooth H.X.hom := hH.smooth
  letI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  letI : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R A)))
  have hiA : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) G I i) :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi.baseChange (algebraBaseMap R A))
  have hiA' : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) H I' i') :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I').symm
      (hi'.baseChange (algebraBaseMap R A))
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := A) G I i) :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
  have hmaxA' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I')
      (splitTorus.baseChangeHom (K := A) H I' i') :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I' H i' hmax'
  have eA := localSplitReducedIsomorphismTheorem A
    ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap R A)).obj H)
    (hG.baseChange (algebraBaseMap R A)) (hH.baseChange (algebraBaseMap R A))
    I I' (splitTorus.baseChangeHom (K := A) G I i)
    (splitTorus.baseChangeHom (K := A) H I' i') hiA hiA' hmaxA hmaxA'
    J J' P Q (hP.baseChange_implicit (A := A)) (hQ.baseChange_implicit (A := A)) hf
  exact hReflect R G H hG hH eA

end Langlands.GroupScheme
