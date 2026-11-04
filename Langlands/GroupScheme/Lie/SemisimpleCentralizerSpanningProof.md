# Descent and spanning by noncentral semisimple tangent centralizers

The theorem `semisimpleCentralizerSpanning` proves the exact published
universe-general
`Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningStatement.{u}` without
additional outer assumptions. Worker 1296 authored the shared wrapper;
Worker 1487 prepared this pair for submission as a structural input to the
no-torus unipotence theorem.

The proof introduces the field, smooth connected affine group and geometric
noncentral semisimple premise quantified in the statement. Smoothness supplies
local finite type. The existing actual scalar-extension construction provides
natural finite coordinates `finiteCoordinates G` on every test algebra. Apply
`semisimpleCentralizer_spanning_of_geometric_semisimple` to these coordinates,
taking the extension to be the actual algebraic closure. The algebraic base map
is definitionally the one used in the statement, and the defining supremum
`noncentralSemisimpleCentralizerSpan` is exactly its spanning conclusion.

The imported theorem proves spanning over any infinite field and same-universe
extension, assuming affineness, local finite type, finite coordinates and the
explicit geometric premise. Its proof constructs a noncentral semisimple
replacement at every nonnilpotent actual adjoint vector using actual translation
Jordan components in characteristic zero and simultaneous prime powers in prime
characteristic. Polynomial nonnilpotent-locus spanning and actual adjoint scalar
extension give the claimed descent and tangent-centralizer supremum. Connectedness
is retained by this exact target but is not needed by the stronger imported
theorem. No Cartan-generation assertion follows without its remaining structural
inputs.
