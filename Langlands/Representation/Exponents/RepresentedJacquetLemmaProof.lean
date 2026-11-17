import Langlands.Representation.Exponents.RepresentedIwahoriContractionProof
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof

/-! # Jacquet's lemma for compact open subgroups with an Iwahori decomposition: proof

Proof of `RepresentedJacquetLemmaStatement` (Renard 2026, VI.6.1 Théorème, printed p.176 /
PDF p.182). The Levi `M` has a split component `A` and a compatible root presentation of
`P`; the proved `representedIwahoriContraction` gives an element of `A(F)` whose image in
`G(F)` satisfies `Jacquet.IsIwahoriContraction`, and the published weak Jacquet lemma
`Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction` gives the surjectivity, using the
finite dimensionality of `V^K` from admissibility.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- **Jacquet's lemma** (Renard 2026, VI.6.1 Théorème) for a compact open subgroup with an
Iwahori decomposition along an arbitrary actual rational parabolic: for every admissible
complex representation `V`, the Jacquet quotient map sends `V^K` onto the `K ∩ M(F)`-fixed
vectors of `V_N`. -/
theorem representedJacquetLemma : RepresentedJacquetLemmaStatement.{u, v} := by
  intro k _ _ _ _ _ G hG _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar
    hnbar hmulbar hP hPP K hK hfac V _ _ ρ hρ
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  -- a split component of `M` and a compatible root presentation of `P`
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k M hm.isConnectedReductive).1
  obtain ⟨pres⟩ := parabolicRootPresentationExistence k G hG P M A p m a hp hm ha
  -- a contracting element of `A(F)`
  obtain ⟨⟨t₀, ht₀⟩, hpow⟩ := representedIwahoriContraction k G hG P Pbar M N Nbar p m n hp hm
    hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP K hK hfac A a pres
  obtain ⟨r₀, hr₀⟩ := hpow t₀ ht₀
  exact Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction ρ hρ.1 hK (hr₀ r₀ le_rfl)
    (pointImage_le_normalizer p m n hn) (hρ.2 K)

end Langlands.Aubert.General.RepresentedParabolic
