import Langlands.GroupScheme.SmoothConnectedNormalizerStatement
import Langlands.GroupScheme.SmoothNormalizer.Global

/-! # Closed normalizers of smooth connected subgroup schemes -/

universe u

namespace Langlands.GroupScheme

/-- **Conrad, Reductive group schemes, Proposition 2.1.6 (subgroup case).** Over every scheme,
the normalizer of a smooth closed subgroup with geometrically connected fibres of a smooth affine
group scheme is represented by a closed subgroup scheme which is locally of finite
presentation. -/
theorem smoothConnectedNormalizer : SmoothConnectedNormalizerStatement.{u} :=
  fun _ G H _ _ i hi hHs hHc => SmoothNormalizer.exists_normalizer G H i hi hHs hHc

end Langlands.GroupScheme
