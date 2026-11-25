# Matrix norms in cyclic product coordinates

An algebra coordinate isomorphism `E ≃ₐ[F] (Fin (m + 1) → L)` with both
directions continuous induces `cyclicProductGLCoordinates` on general
linear groups. It applies the algebra isomorphism to every matrix entry,
then uses `splitGLCoordinates` to pass to the matrices on the factors.
The scalar extension of a base matrix has the same base change in every
coordinate.

Suppose `σ` shifts to the following coordinate at each nonfinal index
and acts by `τ` on the zeroth coordinate at the wraparound. Let `y` be the
ordered product of the components of `x ∈ GL_n(E)`. The zeroth component
of `cyclicNorm σ ((m + 1) * d) x` is `cyclicNorm τ d y`. The proof follows
the first coordinate through each factor in one cycle, then through the
successive whole cycles. The wraparound applies another power of `τ` to
the product of the components in each whole cycle.

When `σ ^ ((m + 1) * d) = 1`, the cyclic shift identity makes every
component of the full norm conjugate to its zeroth component. The conjugator
from the zeroth component to the component at index `i` is the zeroth
component of the prefix `cyclicNorm σ i x`, with conjugation written
`a⁻¹ * N * a`. Thus a norm association in the product projects to a norm
association in the field coordinate. Conversely, an associated conjugator
for `y` lifts by composing with these prefix conjugators in the individual
coordinates. Finally, every `y` is the product of a tuple with `y` in the
first coordinate and identity matrices in the rest. This gives the equivalence
of `IsNorm` in `cyclicProductGLCoordinates_isNorm_iff`, as well as the
fixed-element `IsNormAssociated` equivalence.

Two consequences for orbital integrals follow, for `F` a nonarchimedean
local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), `L` a field, Borel σ-algebras on the
general linear groups, and `κ = cyclicProductGLCoordinates (n := n) c hc hc'`:

- `vanishesOffNorms_cyclicProduct_iff c hc hc' hshift hwrap
  (hσ : σ ^ ((m + 1) * d) = 1) (μF : Measure (GeneralLinear n F))
  (f : GeneralLinear n F → ℂ) :
  VanishesOffNorms σ ((m + 1) * d) μF f ↔ VanishesOffNorms τ d μF f`:
  the regular non-norms are the same for `(σ, (m + 1) d)` and `(τ, d)` by
  `cyclicProductGLCoordinates_isNorm_iff`.
- `IsAssociatedMeasure.cyclicProduct c hc hc' hshift hwrap` (with
  `[IsTopologicalRing E] [IsModuleTopology F E] [IsTopologicalRing L]`)
  `{δ : GeneralLinear n E} {γ : GeneralLinear n F}
  {μδ : Measure (sigmaCentralizer σ n δ)} {μγ : Measure (glCentralizer γ)}
  {μZ : Measure (sigmaCentralizer τ n (List.ofFn (κ δ)).prod)}
  (hZ : Measure.map Subtype.val μZ = Measure.map (fun z : sigmaCentralizer σ n δ => κ z.val 0) μδ)
  (h : IsAssociatedMeasure σ ((m + 1) * d) δ γ μδ μγ) :
  IsAssociatedMeasure τ d (List.ofFn (κ δ)).prod γ μZ μγ`. If `μδ` is
  associated through `a`, then `μZ` is associated through `b = κ(a)₀`:
  `b⁻¹ N_τ(β) b = γ` by the zeroth-coordinate norm identity and
  `cyclicProductGLCoordinates_baseChange`, and the measure identity of the
  association of `μδ`, pushed forward by `z ↦ κ(z)₀`, gives that of `μZ`.
  The hypothesis `hZ` holds for the image of `μδ` under
  `cyclicProductCentralizerEquiv`, which is `z ↦ κ(z)₀` on the
  σ-centralizer.

These internal lemmas give the norm calculation for the unit comparison
in Henniart–Lemaire, I.2.1–I.2.2, printed pp. 10–12 (PDF pp. 18–20).
The product coordinates and their shift laws are supplied as input.
