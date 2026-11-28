import Langlands.Global.AdelicIrreducibleSubrepresentationFiniteVectorAutomorphyProof

/-! # Irreducible subrepresentations in the square-integrable form spectrum -/

set_option autoImplicit false

namespace Langlands.Global

/-- For a presented parabolic isomorphic to `G`, each irreducible subrepresentation of
`L²([G])` lies in the closed span defining `squareIntegrableFormSpectrum`. -/
theorem irreducibleSubrepresentationFormSpectrum :
    IrreducibleSubrepresentationFormSpectrumStatement :=
  irreducibleSubrepresentationFormSpectrum_of_finiteVectorAutomorphy
    irreducibleSubrepresentationFiniteVectorAutomorphy

end Langlands.Global
