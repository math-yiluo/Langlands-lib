# Split maximal tori over strictly Henselian local rings

`Langlands.GroupScheme.StrictHenselianSplitMaximalTorusStatement` is a
proposition target for every universe `u`. For a commutative Henselian local
ring `R` with separably closed residue field and an actual reductive group
scheme `G` over `Spec R`, it asks for a commutative group scheme `T` over the
same base and an actual homomorphism `i : T.toGrp ⟶ G` such that:

- `T` is a split torus over `Spec R`, in the Library sense of an isomorphism
  with a finite product of the actual multiplicative group scheme;
- the underlying scheme map of `i` is a closed immersion;
- for every point `s` of `Spec R`, the actual pullback of `i` along
  `Spec κ(s) → Spec R` satisfies the Library predicate `IsMaximalTorus`.

The source of each pulled-back inclusion is explicitly the commutative
base change of this same `T`. The maximality predicate says that this source
is a torus and the inclusion is closed, and any factorization through a
larger closed torus has an isomorphism as its first map. No replacement
inclusions or independently chosen fibre tori occur in the proposition.
The ring may have arbitrary characteristic and need not be Noetherian,
a domain, a valuation ring, or complete. `IsReductive G` supplies smoothness,
affineness, and the connected reductive geometric fibres.

This is a derived specialization of Brian Conrad, *Reductive group schemes*
(2014), registered as `conrad-2014-reductive-group-schemes`, source SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`:

- Definition 3.2.1, PDF/internal p.91, defines a maximal torus by geometric
  fibrewise maximality. That geometric condition implies the ordinary
  residue-field maximality required by the Library predicate here.
- Theorem 3.2.6 and Corollary 3.2.7, PDF/internal pp.94–95, give the smooth
  surjective scheme of maximal tori and existence of a maximal torus etale
  locally on the base. Over a strictly Henselian local ring a pointed etale
  neighbourhood of the closed point has a section, yielding a maximal
  torus over the original base.
- Proposition B.3.4, PDF/internal pp.290–291, says that a group of
  multiplicative type over a Henselian local base splits over a finite
  etale cover. Such covers of a strictly Henselian local base split, so
  the torus just obtained is split over `R` itself.

The global integral inclusion is needed in the supplied-model classification
route for `IntegralModel.BuildingComparisonStatement`. This target is distinct
from `RelativeSplitTorusLiftingStatement`, which starts with a prescribed
residue-fibre torus and gives a compatible lift only on an etale neighbourhood.
The present proposition asserts existence of a split torus over the original
strictly Henselian base with maximality on all residue fibres. It does not ask
for a lift of a prescribed closed-fibre inclusion.

This file states that structural prerequisite. It supplies no proof of its
existence and no integral split-group classification, canonical building
model, building comparison, stabilizer identity, or unique fixed point.
