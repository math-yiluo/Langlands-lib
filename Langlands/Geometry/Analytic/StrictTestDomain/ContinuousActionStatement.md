# A criterion for joint continuity on a strict-affinoid spectrum

Author: Worker 36.

`PointwiseContinuousSpectrumActionStatement` concerns the existing
concrete `PresentedStrictAffinoidAlgebra` and `BanachSpectrum`, together
with the published bounded automorphism action from
`RationalAutomorphism`. It is a proposition definition; this pair does
not supply its Lean proof.

Let `K` be an ultrametric normed field, `P` a presented strict affinoid
`K`-algebra, `G` a topological group, and `ρ : G →* Aut P` a group
homomorphism into the automorphism group of the category of actual
bounded `K`-algebra maps. Assume that for each fixed `a : P` the orbit
map

```text
g ↦ (ρ g).hom(a)
```

is continuous into `P` with its norm topology. The conclusion is joint
continuity of

```text
G × BanachSpectrum P → BanachSpectrum P
(g, x) ↦ (ρ g) • x.
```

Here the existing point action evaluates as
`((ρ g) • x)(a) = x((ρ g).inv(a))`: the inverse algebra map supplies the
left action, and the right group factor acts first. There is no assumed
topology or continuity predicate on `Aut P`. Continuity is assumed only
for the algebra-element orbit maps, not for the resulting spectrum
action. Each algebra automorphism and its inverse are bounded by their
own constants; there is no common norm bound assumption.

The statement permits independent universes for the field and group.
It does not assume completeness of `K`, a nontrivial valuation, a
nonzero quotient, a nonempty spectrum, local compactness of `G`, or
open stabilizers of spectrum points. The published construction of
`P` supplies its normed algebra carrier; no new analytic-space axioms
are added here.

The proof route is derived. Continuity of inversion in `G`, combined
with the orbit hypothesis and the homomorphism law, gives continuity
of `g ↦ (ρ g).inv(a)` for each fixed `a`. Parametric pullback continuity
for bounded ring maps then gives the displayed conclusion. The
reusable analytic step is the separate spectrum joint-continuity
target: normalized spectrum seminorms satisfy
`|x(a)-x(b)| ≤ ‖a-b‖`, uniformly in `x`, which upgrades fixed-element
evaluation continuity to joint evaluation continuity. This is a
proposed route, not a claim that either proof has been published.

The same operators already act on chosen unit-radius rational
presentations by the forward algebra map. The published theorem
`RationalAutomorphism.locus_smul` identifies the translated rational
locus with its image under the point action. Applying it to `ρ g`
relates the action in this statement to those actual rational domains.
The current statement does not place a topology on the set of rational
presentations or assert continuity of section transport.

The spectrum context is Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), printed/PDF p. 4, Definitions 1.2.3 and
1.2.5 and Exercise 1.2.4, registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The criterion is internally derived from those spectrum definitions
and the Library's bounded algebra automorphisms.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces* (1995-1996), section 1.1, printed/PDF pp. 1-2, supplies the
motivation and the remaining scope boundary. It defines continuity of
an analytic action using a topology on analytic automorphisms, built
from compact analytic domains and bounds on analytic functions.
The target here asserts continuity only of the underlying spectrum
action from the explicit algebra-orbit hypothesis. It neither
identifies that hypothesis with Berkovich's automorphism topology nor
constructs a full analytic `G`-space or an equivariant etale site.
The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
