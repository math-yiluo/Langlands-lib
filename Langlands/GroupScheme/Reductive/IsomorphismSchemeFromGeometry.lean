import Langlands.GroupScheme.IsomorphismSchemeSingleCoverDescent
import Langlands.GroupScheme.IsomorphismEtaleCoverSigma
import Langlands.GroupScheme.OuterIsomorphismTransport
import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryStatement
import Langlands.GroupScheme.Adjoint.RelativeExistenceStatement
import Langlands.GroupScheme.Adjoint.RelativeReductivity
import Langlands.GroupScheme.Reductive.GenericFpqcIsomorphismCover
import Langlands.GroupScheme.Reductive.GenericIsomorphismSchemeExistenceStatement

/-! # Full reductive Isom schemes from three explicit geometric inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Aut geometry and a supplied relative adjoint quotient descend a single local isomorphism. -/
def reductiveIsomorphismSchemeOfSingleIsomorphism
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    {S U : Scheme.{u}} {G H A : GroupScheme S} {q : G ⟶ A}
    (hq : IsRelativeAdjointQuotient q)
    (b : U ⟶ S) [Etale b] [Surjective b]
    (e : (baseChange b).obj G ≅ (baseChange b).obj H) :
    GroupIsomorphismScheme G H := by
  apply Classical.choice
  obtain ⟨I, hSmooth, _, hOuter⟩ := hAut U ((baseChange b).obj G)
    (hq.isReductive.baseChange b)
  obtain ⟨O, hEtale, hSeparated, hAffine, _, _⟩ :=
    hOuter ((baseChange b).obj A) ((baseChange b).map q) (hq.baseChange b)
  let J := I.postcompose e
  let O' : OuterIsomorphismScheme J (hq.innerAction.baseChange b) :=
    (O.postcompose e).changeActingGroup (hq.innerAction.baseChange b) (Iso.refl _)
      (by
        intro T d g
        simp only [hq.innerAction_baseChange, Iso.refl_hom, Grp.id_hom_hom,
          Category.comp_id])
  let : Smooth J.parameter.hom := hSmooth
  let : Etale O'.parameter.hom := hEtale
  let : IsSeparated O'.parameter.hom := hSeparated
  let : IsAffineHom O'.classMap.left := hAffine
  have ha : hq.innerAction.IsFaithful :=
    AutomorphicAction.isFaithful_of_isFppfQuotient_center
      hq.isQuotient hq.innerAction hq.innerAction_restrict
  exact ⟨GroupIsomorphismScheme.ofSingleLocalOuterQuotient b hq.innerAction ha J O'⟩

/-- Three explicit geometric existence statements give the original full generic-DVR Isom scheme. -/
def genericIsomorphismSchemeOfGeometry
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hEtale : ReductiveFpqcLocalIsomorphismStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H) :
    GroupIsomorphismScheme G H := by
  apply Classical.choice
  obtain ⟨A, q, hA, hq⟩ := hAdj _ G hG
  let : IsAffineHom A.X.hom := hA
  have hqr : IsRelativeAdjointQuotient q := hq.isRelativeAdjointQuotient hG
  let C := genericFpqcIsomorphismCover R K hG hH f
  obtain ⟨𝒰, e⟩ := C.exists_etaleCover hEtale hG hH
  let b : (∐ 𝒰.X) ⟶ Spec (CommRingCat.of R) := Sigma.desc 𝒰.f
  let : Etale b := 𝒰.sigma.map_prop PUnit.unit
  let : Surjective b := ⟨fun x => by
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact ⟨Sigma.ι 𝒰.X i y, by simp [b, ← Scheme.Hom.comp_apply]⟩⟩
  exact ⟨reductiveIsomorphismSchemeOfSingleIsomorphism hAut hqr b
    (LocalGroupIso.isoOnSigma 𝒰 (fun i => Classical.choice (e i)))⟩

/-- The unchanged target follows conditionally from precisely the three supplied inputs. -/
theorem genericIsomorphismSchemeExistence_of_geometry
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hEtale : ReductiveFpqcLocalIsomorphismStatement.{u}) :
    GenericIsomorphismSchemeExistenceStatement.{u} := by
  intro R _ _ _ K _ _ _ G H hG hH f
  exact ⟨genericIsomorphismSchemeOfGeometry hAut hAdj hEtale R K hG hH f⟩

end Langlands.GroupScheme
