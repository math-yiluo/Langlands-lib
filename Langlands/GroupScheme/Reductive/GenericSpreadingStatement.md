# Generic reductivity on a principal open

`Langlands.GroupScheme.GenericReductivitySpreadingStatement` is an auxiliary
spreading statement for an actual group scheme `G` over `Spec R`, where `R` is
an arbitrary Noetherian domain and `K` is its supplied fraction field. It assumes
that the structural map of `G` is smooth and affine and that its actual pullback
along `Spec.algebraMap R K` satisfies the Library's `IsConnectedReductive`.
It asserts an element `r : R` with `r ≠ 0` such that, for every field
`k : Type u` and every `Algebra R k`, the condition `algebraMap R k r ≠ 0`
implies `IsConnectedReductive` for the actual pullback along
`Spec.algebraMap R k`. Thus the conclusion tests all field-valued points of
`D(r)`, including all extensions of residue fields. All rings, fields, schemes
and fibre maps remain the supplied objects, uniformly in universe `u`.

The statement is a derived packaging of Brian Conrad, *Reductive group schemes*
(2014 SGA3 notes), registered source
`conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Definition 3.1.1 and its discussion are on printed/PDF pp.81–82;
Proposition 3.1.9(1) and its proof are on pp.85–88; Proposition 3.1.12 and its
proof are on pp.89–90. These passages were read in the registered original.
No Conrad errata file was found in the project's source or public-note indices.

Here is the mathematical derivation that a proof must implement. Apply
Proposition 3.1.9(1) to the generic point: the identity components of the geometric
fibres are reductive over an open neighbourhood of that point. Choose a basic
open `D(r)` contained in that neighbourhood. Since `R` is a domain and the
neighbourhood contains the generic point, `r` is nonzero. Over the irreducible
base `D(r)`, Proposition 3.1.12 makes every fibre connected because the generic
fibre is connected. This supplies a reductive group family on `D(r)` in the
source's Definition 3.1.1. Its field-valued pullbacks are connected reductive:
each field-valued point factors through the residue field of its image, and
connected reductivity is preserved under that field extension. The Library
already proves arbitrary field-extension preservation in
`Langlands.GroupScheme.connectedReductiveFieldExtensionStatement`, from
`Langlands.GroupScheme.Reductive.FieldExtensionProof`.

A future Lean proof must establish the comparisons with the Library's precise
field predicate, including its smoothness, affine structural map, connected
underlying scheme, and trivial geometric unipotent radical. It must also
identify each residue-field factorization with the actual specified pullback.
The source's use of smooth affine families is compatible with finite
presentation: an affine smooth morphism is quasi-compact and quasi-separated
and locally of finite presentation, hence of finite presentation. No separate
finite-type datum is required in this statement.

This file only defines the proposition. It provides no proof of reductive
openness, no integral model, no parabolic spreading and no arithmetic prime
set. Its Noetherian hypothesis suffices for the intended application to actual
finite S-integer rings; their Noetherianity is proved in
`Langlands.Global.AdelicSIntegersNoetherianProof`. The arithmetic enlargement
that inverts `r` remains a separate comparison step.
