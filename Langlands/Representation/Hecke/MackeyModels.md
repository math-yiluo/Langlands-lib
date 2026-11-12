# Actual tensor and smooth Hom bifunctors for Mackey isomorphisms

Source: Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.11, printed pp.82–83 / PDF pp.88–89,
using the tensor and smooth Hom of III.1.15.

This unit gives categorical packaging of the original published constructions.
`algebraicTensorBifunctor` uses `Representation.tprod` and the tensor product
of intertwiners. `algebraicHomBifunctor` uses `Representation.linHom` with
its actual conjugation action. Its first variable is contravariant and its
second variable is covariant: a pair `(f : V' → V, g : W → W')` sends `L`
to `g ∘ L ∘ f`. The underlying intertwiners are the published
`Renard.Smooth.TensorHom.precompose` and `postcompose`; the functor laws
are checked on vectors.

`smoothTensorBifunctor` lifts the actual algebraic tensor to smooth
representations using the published `tensor_smooth` proof. Thus its action
on elementary tensors is diagonal. `smoothHomBifunctor` is the algebraic
Hom composite followed by the already published smooth-part functor.
Its carrier consists of the smooth vectors in the full algebraic linear
Hom space, with action `(gL)(v) = ρ_W(g)L(ρ_V(g⁻¹)v)`.
No arbitrary replacement Hom carrier or supplied action law is used.

The four Mackey model functors are literal composites of these bifunctors,
continuous pullback and the actual smooth transports of the Chapter I Hecke
induction functors:

| Model | Value |
| --- | --- |
| `mackeyHomLeft` | `Hom(V,I(W))₀` |
| `mackeyHomRight` | `I(Hom(Fφ(V),W)₀)` |
| `mackeyTensorLeft` | `P(W) ⊗ V` |
| `mackeyTensorRight` | `P(W ⊗ Fφ(V))` |

The Hom models have domain `SmoothRep(G)ᵒᵖ × SmoothRep(H)`; the tensor models
have domain `SmoothRep(H) × SmoothRep(G)`. A natural isomorphism between the
respective model functors therefore includes naturality in both variables,
with the required contravariance for Hom.

The models consume an explicit equivalence proof for the exact published
Hecke functor on `G`, as required by `smoothI` and `smoothP`. They do not
assume the Mackey comparison or prove that equivalence. The group universes
`uG`, `uH` and carrier parameter `v` remain independent; both smooth
representation categories use the stable carrier universe `max uG v`.
The core tensor/Hom bifunctors themselves work at every carrier universe.

Existence of the Mackey natural isomorphisms, and the additional
pseudo-forgetful/forgetful hypothesis in the tensor assertion, belong to
the separate statement unit.
