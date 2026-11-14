# The diagonal-closure and smoothening construction of an intersection model

`Langlands.GroupScheme.IntegralModel.smoothIntersection` proves exactly
`Langlands.GroupScheme.IntegralModel.SmoothIntersectionStatement.{u}` at
arbitrary universe `u`. It follows Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Corollary A.6.6, printed p. 647 / PDF p. 678. The registered
source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The inputs are a Henselian discrete valuation ring `R : Type u` with
algebraically closed residue field, a supplied fraction field `K : Type u`,
a smooth affine group scheme `G` over `K`, and two supplied integral models
`M N : IntegralModel R K G`. Each model includes an actual affine flat
finite-type group scheme over `R` and its specified generic identification
with `G`. The proof gives a smooth model `L` of the same `G`, compatible
model homomorphisms `L.Hom M (𝟙 G)` and `L.Hom N (𝟙 G)`, and the literal
subgroup equality

```lean
L.integralPoints = M.integralPoints ⊓ N.integralPoints
```

inside the original `rationalPoints G`. Both supplied models and their
generic identifications are retained; the inputs may be nonsmooth.

The implemented construction first forms the actual product integral
model `M.product N`. The generic diagonal is `HomScheme.graphHom (𝟙 G)`;
`HomScheme.isClosedImmersion_graphHom` proves it closed, using that `G`
is affine and hence separated. The schematic-closure existence theorem
supplies a model `C` of the original `G` and a compatible closed inclusion
into the product model. Composing this inclusion with `productFst` and
`productSnd` gives generic-identity model maps `α : C.Hom M (𝟙 G)` and
`β : C.Hom N (𝟙 G)`.

The closure's `Hom.IsSchematicClosure.integralPoints_eq_comap` and the
published `product_integralPoints_comap_diagonal` identify
`C.integralPoints` literally with `M.integralPoints ⊓ N.integralPoints`.
Smoothening supplies a smooth model `L` and its compatible map
`π : L.Hom C (𝟙 G)`. The theorem `IsSmoothening.integralPoints_eq` identifies
`L.integralPoints` with `C.integralPoints`, using surjectivity on actual
`R`-sections and compatibility with the specified generic identification.
Composition with `α` and `β` supplies the two required output maps.
Transitivity of the two subgroup equalities finishes the proof.

The helper `smoothIntersection_of_closure_smoothening` implements this
argument with the two existence propositions as inputs.
`smoothIntersection_of_smoothening` discharges closure using the published
theorem `Langlands.GroupScheme.integralModelSchematicClosure` from
`Langlands.GroupScheme.IntegralModel.SchematicClosureProof`. The final
theorem `smoothIntersection` discharges smoothening using the published
`Langlands.GroupScheme.IntegralModel.smoothening_exists` from
`Langlands.GroupScheme.IntegralModel.SmootheningProof`. Thus its type has
no additional premise. These supporting reductions are internal derived
results recording the proof's two construction steps.

The proof follows the diagonal-closure and smoothening route of KP A.6.6,
with smoothening as in §A.6, printed pp. 645–646 / PDF pp. 676–677.
As explained in the statement's paired Markdown, the formal target is a
derived model formulation over any Henselian DVR with algebraically closed
residue field, taking the generic group directly over its supplied fraction
field. Allowing nonsmooth input models uses the same construction. The
theorem asserts no universal property for the intersection model.

The registered *Corrections and additions* (2024), source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 37 adds the Chapter 8 perfect-residue-field convention, satisfied
here by the algebraically closed residue field. PDF pp. 49–50 give no
correction to Corollary A.6.6.
