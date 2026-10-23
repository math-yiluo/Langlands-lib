# Canonical tensor comparison for rigidified pullback

This module constructs the canonical isomorphism between pullback of a tensor
product and tensor product of the pullbacks in the categories of rigidified
modules and rigidified line bundles. It then proves preservation of tensor on
relative compatible-isomorphism classes. All schemes have universe `u`.

The main constructions retain three explicit published propositions:

- `pullbackTensorComparisonIsIsoStatement`: invertibility of the fixed canonical
  tensor comparison for every scheme morphism;
- `PullbackTensorCompositionStatement`: its compatibility with the fixed
  composite-pullback comparison;
- `PullbackTensorLeftUnitorStatement`: its compatibility with the fixed
  pullback-unit map and the explicit left tensor unitor.

These are hypotheses about specified maps. This module derives the rigidified
compatibility equation from them; it does not prove those three propositions.
Neither the right-unitor equation nor tensor symmetry is needed.

## Square and unit calculations

Write `C_f(M,N)` for the canonical comparison
`f*(M ⊗ N) → f*M ⊗ f*N`, `u_f : f*O → O` for `pullbackUnitIso`,
and `λ_M : O ⊗ M → M` for the explicit left unitor.
`tensorMap_id` is the identity law of the existing tensor bifunctor.
`pullbackCongr_tensor` proves compatibility of `C` with equality transport of
scheme morphisms by equality induction and this identity law.

`pullbackUnit_tensor` derives

`C_f(O,O) ≫ (u_f ⊗ u_f) ≫ λ_O = f*(λ_O) ≫ u_f`.

The proof factors the tensor of the two unit maps into two successive tensor
maps, uses naturality of the left unitor, and applies the stated left-unit
compatibility equation. Cancelling the isomorphism `(u_f ⊗ u_f) ≫ λ_O`
gives `pullbackUnit_tensor_inv`:

`u_f⁻¹ ≫ f*(λ_O⁻¹) ≫ C_f(O,O) = λ_O⁻¹ ≫ (u_f⁻¹ ⊗ u_f⁻¹)`.

Next consider an arbitrary commuting square with maps
`ε : S → X`, `ε' : S' → X'`, `f : X' → X`, and `g : S' → S`,
and equality `ε' ≫ f = g ≫ ε`. No section or Cartesian hypothesis is required.
The existing `squarePullbackIso`, denoted `q`, is the composite

`g* ε* ≅ (g ≫ ε)* ≅ (ε' ≫ f)* ≅ ε'* f*`.

`pullbackComp_inv_tensor` first derives the inverse form of the composition
compatibility equation by cancelling the tensor of the two forward composition
isomorphisms. Combining that inverse equation, equality transport, and the
forward composition equation proves `squarePullbackIso_tensor`:

`q_(M⊗N) ≫ ε'*(C_f(M,N)) ≫ C_ε'(f*M,f*N)`

`= g*(C_ε(M,N)) ≫ C_g(ε*M,ε*N) ≫ (q_M ⊗ q_N)`.

The tensor maps combine by the existing bifunctor composition law. No new
comparison map is chosen.

## Rigidified comparison

For a rigidified module `(M, α : O_S ≅ ε*M)`, the existing square pullback
has rigidification `u_g⁻¹ ≫ g*(α) ≫ q_M`. The tensor rigidification is
`λ_O⁻¹ ≫ (α ⊗ β) ≫ C_ε(M,N)⁻¹`.

`RigidifiedModule.pullbackTensor_compatibility` proves that the map
`C_f(M,N)` carries the pullback of the tensor rigidification to the tensor of
the pulled-back rigidifications. It postcomposes the desired equation with the
invertible `C_ε'(f*M,f*N)`. The square calculation, functoriality of pullback,
and naturality of `C_g` reduce it to the inverse unit equation above and
composition of tensor maps. This argument applies to all rigidified modules;
local freeness is not used.

`RigidifiedModule.pullbackTensorIso` equips the component of
`asIso (pullbackTensorComparison f)` with precisely that proved compatibility.
`RigidifiedLineBundle.pullbackTensorIso` lifts it to the existing full
subcategories of locally free rank-one modules. Its endpoints use the already
constructed tensor and pullback functors, whose local rank-one properties have
been proved. Thus it is an actual compatible isomorphism of the constructed
objects.

For a section `ε` of `f : X → S`, `classesPullback_tensor` specializes this
isomorphism to the square induced by any morphism `h : T → U` in `Over S`.
Induction on both quotient representatives and quotient soundness prove

`h*(q ⊗ r) = h*q ⊗ h*r`.

The quotient relation is isomorphism compatible with rigidification. Neither
pullback identity/composition coherence for that quotient nor a completed group
structure is needed for this single naturality equation.

## Provenance and scope

This is a derived compatibility construction for the tensor and pullback
operations in Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI,
paragraph (6.2), printed p.88 (PDF p.92). That paragraph specifies
`α : O_T ≅ ε_T*L`, compatible morphisms, tensoring of rigidifications, and
pullback along test-scheme morphisms. The implementation uses the Library's
opposite ordering of the relative fibre-product factors, consistently with its
existing `relativeSpace` and `relativeSection`.

The categorical calculations for arbitrary commuting squares do not require the
additional hypotheses in (6.2) used for comparison with the relative Picard
sheaf or for triviality of automorphisms. The proofs above are internal
calculations of the fixed maps, with the three stated premises explicit. This
module supplies no associativity or inverse for rigidified tensor, no Picard
sheaf comparison, and no representability result.
