# Strictly Henselian lifting from complete-local deformation

Worker 872, using Worker 517's split-residue Noetherian coefficient models.
This derived reduction keeps the unchanged complete-local deformation
statement as an explicit mathematical input.

`exists_clopen_over_henselian` takes a flat affine finitely presented group
`D` over a Noetherian local ring `P` with split special fibre, and assumes
etale completion approximation for `P`. For any actual local map from `P`
into a Henselian local ring `A`, it constructs a clopen homomorphism from
some diagonalizable group over `A` into `D_A`, whose special fibre is an
isomorphism. The source retains the full finitely generated character
group of the chosen split special fibre, including its torsion.

The proof chooses that special-fibre diagonalization, lifts its inverse
homomorphism to the completion using the input deformation proposition,
and realizes a homomorphism with the same residue map over an etale
`P`-algebra `E`. Since `E` is Noetherian, the clopen-transfer construction
applies to its induced residue point over `A`. Henselian lifting produces
a coefficient map into the prescribed `A`; localizing `E` at that point
proves both immersion properties before their transfer to `A`. Functorial
evaluation and the exact coefficient reduction make the special fibre an
isomorphism. No Noetherianity is imposed on `A`.

`multiplicativeTypeStrictHenselianLift_of_completeLocalDeformation` proves
the exact unchanged `MultiplicativeTypeStrictHenselianLiftStatement` from
that one explicit deformation proposition. A prescribed special-fibre
isomorphism first makes the original special fibre diagonalizable.
`Descent.SplitResidueNoetherianModel.nonempty_model` supplies a Noetherian
local coefficient model mapping locally into `A`, with diagonalizable
special fibre and etale approximation. The preceding construction gives
a clopen lift over `A` from some diagonalizable source. The actual model
isomorphism transports its target to `H`. Finally published local Hom
comparison, packaged in `PrescribedDiagonalizableLift`, reparametrizes its
source to the prescribed `D_A(M)` and recovers `e.hom` exactly.

The implemented route only uses the special-fibre diagonalization; the
all-geometric-fibres multiplicative-type hypothesis of the unchanged target
is therefore unused. It retains arbitrary universe, non-Noetherian bases,
nonsmooth targets and torsion in characters. The deformation proposition
remains an argument, not an axiom or an asserted proof of the exact target.
