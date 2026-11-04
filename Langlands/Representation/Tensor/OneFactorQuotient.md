# Quotients of a tensor representation with one acting factor

This internal construction returns an actual surjective equivariant linear map
from `BinaryTensor.firstFactor ρ W` to `ρ` whenever the complex vector space `W`
is nontrivial. The group and both carriers have independent universes. No
topology, smoothness, irreducibility, admissibility or finite dimension is
assumed.

`firstFactorContraction ρ φ` contracts the second tensor coordinate against
`φ : Module.Dual ℂ W`. On a pure tensor it is `φ(w) • v`. It is equivariant
because the group acts on the first coordinate only. The implemented linear
map is `TensorProduct.rid` after `φ.lTensor V`.

`firstFactorContraction_surjective` uses a supplied vector `w` with `φ(w)=1`:
each `v` has preimage `v ⊗ w`. `firstFactorQuotient ρ W` chooses a nonzero
vector and then a linear functional taking value one there, by Mathlib's
`Module.Projective.exists_dual_eq_one`. Every complex vector space is free
and projective. Classical choice selects an actual map with its surjectivity
proof retained in a subtype.

This is a derived tensor-algebra adapter. The existing
`FiniteTensor.trivialContraction` in `Tensor.ExternalSubquotient` contracts a
trivially acted left coordinate. The present right-coordinate version has the
one-factor action as its literal source and imports only its generic API and
Mathlib linear algebra. It supplies no derivative formula or nonvanishing
assertion about a derivative. The full special-head irreducibility criterion
remains open.

The source exports four declarations under `Langlands.BinaryTensor`:

```lean
firstFactorContraction (ρ : Representation ℂ G V) (φ : Module.Dual ℂ W) :
  (firstFactor ρ W).IntertwiningMap ρ

firstFactorContraction_tmul (ρ : Representation ℂ G V)
  (φ : Module.Dual ℂ W) (v : V) (w : W) :
  firstFactorContraction ρ φ (v ⊗ₜ w) = φ w • v

firstFactorContraction_surjective (ρ : Representation ℂ G V)
  (φ : Module.Dual ℂ W) {w : W} (hw : φ w = 1) :
  Function.Surjective (firstFactorContraction ρ φ)

firstFactorQuotient (ρ : Representation ℂ G V) (W : Type uW)
  [AddCommGroup W] [Module ℂ W] [Nontrivial W] :
  {q : (firstFactor ρ W).IntertwiningMap ρ // Function.Surjective q}
```

Here `G : Type uG` is a group, and `V : Type uV` and `W : Type uW`
have additive commutative group and complex module structures. There is no
relation between the three universes. In the last declaration the displayed
binders supply the structures on its explicit `W`.

The proof of equivariance compares the two linear maps on pure tensors by
`TensorProduct.ext'`. Both sides equal `φ(w) • ρ(g)(v)`, by the first-factor
action formula, tensor contraction and complex linearity of `ρ(g)`. The
surjectivity proof is the explicit preimage calculation above. The choice
argument is conducted inside `Nonempty` and then eliminated by
`Classical.choice`, producing data without eliminating an existential directly
into a type. Neither a representation-theoretic simplicity result nor a
derivative comparison is used.

The complete import audit has six project modules including this module and
seven distinct external frontier imports. All five inherited Lean/Markdown
pairs match published Library commit
`009c0cdd8e42a73269501f1a61cf7b40cc67d0f0`. No derivative, mirabolic, segment,
head, socle, Jacquet or classification module is imported. The host's excluded
conclusions and restricted support-bound intermediates do not enter this
construction. `ExternalSubquotient` is mentioned for comparison only and is
not imported. The audited project imports are:

- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof`
- `Langlands.Representation.Smooth.SmoothPart.BasicStatement`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Tensor.OneFactor`
- `Langlands.Representation.Tensor.OneFactorQuotient`

The complete external import frontier is:

- `Mathlib.Basic.Complex.Basic`
- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Mathlib.LinearAlgebra.Dual.Lemmas`
- `Mathlib.RepresentationTheory.Intertwining`
- `Mathlib.RepresentationTheory.Invariants`
- `Mathlib.RepresentationTheory.Subrepresentation`
- `Mathlib.Topology.Algebra.OpenSubgroup`
