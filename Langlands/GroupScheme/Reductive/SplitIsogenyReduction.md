# Reduction of the fixed-torus isogeny criterion

`splitIsogenyExtension_of_rootDatum_and_existence` takes
`IsogenyRootDatumStatement` and `SplitIsogenyExistenceStatement` as explicit
assumptions and derives `SplitIsogenyExtensionStatement`, in every universe.
The definitions retain arbitrary fields, actual character and cocharacter
maps, the field characteristic exponent and general root factors. Both
assumed statements concern actual group isogenies, including their full
possibly nonsmooth kernels.

For necessity, the proof applies the induced-map assertion to an extending
group isogeny and retains its root-datum map and both lattice comparison
equations. For sufficiency, it applies realization to the supplied
root-datum isogeny. The resulting torus map and the originally specified
map give the same pullback of every actual character. The published
`IsSplitTorus.hom_ext_of_characters` theorem identifies them, so the
realizing group isogeny extends the original map. The cocharacter equations
remain part of the input and conclusion, although character separation alone
is sufficient for the uniqueness step.

`splitIsogenyTheorem_of_rootDatum_and_existence` bundles the supplied
realization proof with this derived fixed-torus extension proof to construct
`SplitIsogenyTheoremStatement`. It is a conditional constructor: this module
supplies neither geometric input and does not by itself prove the general
split isogeny theorem.

This is an internal logical and categorical deduction from the two explicit
geometric hypotheses and the published character-separation theorem. The
extension reduction was developed in the parent program by Worker 3483;
Worker 668 prepared the paired module for review and added the final
constructor. Its proof route uses the specified maps throughout and assumes
no equality of root factors with one.
