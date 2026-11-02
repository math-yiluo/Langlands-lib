import Langlands.Global.Arithmetic.FieldRealizationStatement
import Langlands.Global.Arithmetic.LocalNormalModel
import Langlands.Global.Arithmetic.GaloisModelRealization

/-! # Totally real Galois realization of finite p-adic extensions -/

namespace Langlands.Global

universe u v

open FieldRealization

/-- The totally real realization statement for independently sized local fields. -/
theorem totallyRealGaloisRealization :
    TotallyRealGaloisRealizationStatement.{u, v} := by
  intro p hp F E hAlg hTower hGal
  let := hp
  let := hAlg
  let := hTower
  let := hGal
  exact totallyRealRealization_of_galoisModel F E
    (localNormalClosure p E) (localNormalModel p E)
    (localNormalModelEmbedding p E) (localNormalModelEmbedding_adjoin p E)

end Langlands.Global
