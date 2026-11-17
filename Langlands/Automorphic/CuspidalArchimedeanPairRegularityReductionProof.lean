import Langlands.Automorphic.CuspidalArchimedeanComponentStatement

/-!
# Archimedean pair regularity from the component statements

A proof of `Langlands.Automorphic.CuspidalArchimedeanPairRegularityReductionStatement`: the
admissibility, irreducibility, genericity and unitarizability of the archimedean
standard-module components of actual cuspidal realizations, together with the archimedean
case of Getz–Hahn (2024), Theorem 11.5.2, for carriers in `Type`, give the archimedean pair
regularity of unitary cuspidal realizations on `Re(s) ≥ 1`. All six inputs are hypotheses of
the statement; none is proved here. See the paired Markdown.
-/

set_option autoImplicit false

universe u

namespace Langlands.Automorphic

/-- **Reduction of the archimedean pair regularity** (the archimedean input of Getz–Hahn
2024, p. 309). At a real (resp. complex) place, the standard modules of the two parameters
are irreducible, admissible, generic and unitarizable `(𝔤, K)`-modules by the four component
hypotheses, and each is its own standard-module parameter through the identity map, so the
archimedean case of Getz–Hahn, Theorem 11.5.2, applies to them. -/
theorem cuspidalArchimedeanPairRegularityReduction :
    CuspidalArchimedeanPairRegularityReductionStatement.{u} := by
  intro hAdm hIrr hGen hUnit hReal hComplex F _ _ _ r t T T' hT hT'
  refine ⟨fun v ds ds' hds hds' s hs => ?_, fun v ds ds' hds hds' s hs => ?_⟩
  · exact hReal (r + 1) (t + 1) _ _
      (Archimedean.realStandardRep (r + 1) ds) (Archimedean.realStandardLie (r + 1) ds)
      (Archimedean.realStandardRep (t + 1) ds') (Archimedean.realStandardLie (t + 1) ds')
      ds ds'
      (Archimedean.isRealGKModule_realStandardModule (r + 1) ds)
      ((hIrr F r T).1 v ds hds) (hAdm.1 (r + 1) ds) ((hGen F r T).1 v ds hds)
      ((hUnit F r T hT).1 v ds hds)
      ⟨hds.1, LinearMap.id, Function.injective_id,
        Archimedean.isRealStandardIntertwiner_id (r + 1) ds⟩
      (Archimedean.isRealGKModule_realStandardModule (t + 1) ds')
      ((hIrr F t T').1 v ds' hds') (hAdm.1 (t + 1) ds') ((hGen F t T').1 v ds' hds')
      ((hUnit F t T' hT').1 v ds' hds')
      ⟨hds'.1, LinearMap.id, Function.injective_id,
        Archimedean.isRealStandardIntertwiner_id (t + 1) ds'⟩
      s hs
  · exact hComplex (r + 1) (t + 1) _ _
      (Archimedean.complexStandardRep (r + 1) ds) (Archimedean.complexStandardLie (r + 1) ds)
      (Archimedean.complexStandardRep (t + 1) ds')
      (Archimedean.complexStandardLie (t + 1) ds')
      ds ds'
      (Archimedean.isComplexGKModule_complexStandardModule (r + 1) ds)
      ((hIrr F r T).2 v ds hds) (hAdm.2 (r + 1) ds) ((hGen F r T).2 v ds hds)
      ((hUnit F r T hT).2 v ds hds)
      ⟨hds.1, LinearMap.id, Function.injective_id,
        Archimedean.isComplexStandardIntertwining_id (r + 1) ds⟩
      (Archimedean.isComplexGKModule_complexStandardModule (t + 1) ds')
      ((hIrr F t T').2 v ds' hds') (hAdm.2 (t + 1) ds') ((hGen F t T').2 v ds' hds')
      ((hUnit F t T' hT').2 v ds' hds')
      ⟨hds'.1, LinearMap.id, Function.injective_id,
        Archimedean.isComplexStandardIntertwining_id (t + 1) ds'⟩
      s hs

end Langlands.Automorphic
